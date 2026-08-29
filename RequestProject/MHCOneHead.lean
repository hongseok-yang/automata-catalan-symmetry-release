/-
# Head elimination: every multihead machine has a single-head equivalent

The first of the two reductions behind the worktape-model restatement of the
logspace trio (`WRPWorktape.lean`): a multihead bounded-counter transducer
`MHC Alpha Gamma h c` is simulated by a **single-head** machine
`MHC Alpha Gamma 1 (h + (h + c))` whose counters store, for each original
head `a`, the two distances `δ_a = pos_a ∸ i` and `γ_a = i ∸ pos_a` to the
single physical head at position `i` (plus the original counters).

One simulated step is realised by a **two-sweep cycle**: a right sweep
`⊢ → ⊣` that keeps the distance pairs in sync (each move decrements the
positive `δ`s and increments the `γ`s of the passed heads) and records, in
the finite control, the symbol under every original head (a head sits at the
current cell exactly when its `δ` is zero and unrecorded) together with the
coincidence pattern (two heads coincide exactly when they are recorded at
the same cell); then a left sweep `⊣ → ⊢` that restores the `δ`s; then a
single `consult` step that feeds the recorded observation to the original
transition function, emits its output, and applies its head moves and
counter operations directly to the distance and original counters
(`HeadMove.left`/`CounterOp.dec` agree — both are truncated).

Main results: `oneHead M` (the machine), `oneHead_spaceBound` (linear
counters, from `SpaceBound M C`), `oneHead_computes_iff` (it computes the
same partial map), and the packaged
`isLogspaceMH_oneHead : IsLogspaceMH f → single-head IsLogspaceMH data`.
Everything is axiom-clean.
-/
import RequestProject.Multihead

namespace MHCOneHead

open TwoDFT
open Multihead
open Logspace (CounterOp)

section Generic

variable {Alpha Gamma : Type*} {h c : ℕ}

/-! ## The tape alphabet is finite -/

/-- `TapeSym Alpha` is finite when `Alpha` is (used for the finiteness of the
simulator's control states, which record tape symbols). -/
instance instFintypeTapeSym [Fintype Alpha] : Fintype (TapeSym Alpha) :=
  Fintype.ofEquiv (Option (Option Alpha))
    { toFun := fun x => match x with
        | none => TapeSym.lmark
        | some none => TapeSym.rmark
        | some (some a) => TapeSym.letter a
      invFun := fun s => match s with
        | TapeSym.lmark => none
        | TapeSym.rmark => some none
        | TapeSym.letter a => some (some a)
      left_inv := fun x => by rcases x with - | - | a <;> rfl
      right_inv := fun s => by rcases s with - | a | - <;> rfl }

/-! ## Counter layout: `δ`-block, `γ`-block, original block -/

/-- The `δ`-counter of original head `a`: its distance ahead of the physical
head (`pos a ∸ i`). -/
def cδ (a : Fin h) : Fin (h + (h + c)) := Fin.castAdd (h + c) a

/-- The `γ`-counter of original head `a`: its distance behind the physical
head (`i ∸ pos a`). -/
def cγ (a : Fin h) : Fin (h + (h + c)) := Fin.natAdd h (Fin.castAdd c a)

/-- The copy of original counter `j`. -/
def cO (j : Fin c) : Fin (h + (h + c)) := Fin.natAdd h (Fin.natAdd h j)

/-- The encoded counter bank: distances to head position `i`, plus the
original counters. -/
def encCnt (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (i : ℕ) : Fin (h + (h + c)) → ℕ :=
  Fin.addCases (fun a => pos a - i)
    (Fin.addCases (fun a => i - pos a) (fun j => cnt j))

@[simp] theorem encCnt_δ (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (i : ℕ) (a : Fin h) :
    encCnt pos cnt i (cδ a) = pos a - i := by
  simp [encCnt, cδ]

@[simp] theorem encCnt_γ (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (i : ℕ) (a : Fin h) :
    encCnt pos cnt i (cγ a) = i - pos a := by
  simp [encCnt, cγ]

@[simp] theorem encCnt_O (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (i : ℕ) (j : Fin c) :
    encCnt pos cnt i (cO j) = cnt j := by
  simp [encCnt, cO]

/-! ## Control states -/

/-- The three phases of a simulation cycle. -/
inductive Mode | sweepR | sweepL | consult
  deriving DecidableEq

instance : Fintype Mode :=
  ⟨⟨{Mode.sweepR, Mode.sweepL, Mode.consult}, by decide⟩, fun x => by cases x <;> decide⟩

/-- The control data of the simulator: the phase, the symbols recorded so far
under the original heads, and the coincidence bits recorded so far. -/
structure Ph (Alpha : Type*) (h : ℕ) where
  mode : Mode
  syms : Fin h → Option (TapeSym Alpha)
  coin : Fin h → Fin h → Option Bool

instance [Fintype Alpha] [DecidableEq Alpha] : Fintype (Ph Alpha h) :=
  Fintype.ofEquiv
    (Mode × (Fin h → Option (TapeSym Alpha)) × (Fin h → Fin h → Option Bool))
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2⟩
      invFun := fun p => (p.mode, p.syms, p.coin)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The empty recording state (a fresh cycle). -/
def phStart (Alpha : Type*) (h : ℕ) : Ph Alpha h :=
  ⟨Mode.sweepR, fun _ => none, fun _ _ => none⟩

/-! ## Recording -/

/-- Record the current symbol for every pending head (`pending a` = head `a`
sits at the current cell and is unrecorded). -/
def recSyms (syms : Fin h → Option (TapeSym Alpha)) (s : TapeSym Alpha)
    (pending : Fin h → Bool) : Fin h → Option (TapeSym Alpha) :=
  fun a => if pending a then some s else syms a

/-- Record the coincidence bits: two pending heads coincide; a pending head
differs from every previously recorded one. -/
def recCoin (coin : Fin h → Fin h → Option Bool) (recorded pending : Fin h → Bool) :
    Fin h → Fin h → Option Bool :=
  fun a b =>
    if pending a && pending b then some true
    else if pending a && recorded b then some false
    else if recorded a && pending b then some false
    else coin a b

/-! ## Per-sweep counter operations -/

/-- Right-sweep counter update: decrement the positive `δ`s, increment the
`γ`s of the already-passed heads (`δ = 0`). -/
def opsR (z : Fin (h + (h + c)) → Bool) : Fin (h + (h + c)) → CounterOp :=
  Fin.addCases (fun a => if z (cδ a) then CounterOp.keep else CounterOp.dec)
    (Fin.addCases (fun a => if z (cδ a) then CounterOp.inc else CounterOp.keep)
      (fun _ => CounterOp.keep))

/-- Left-sweep counter update: decrement the positive `γ`s, increment the
`δ`s of the heads at or beyond the current cell (`γ = 0`). -/
def opsL (z : Fin (h + (h + c)) → Bool) : Fin (h + (h + c)) → CounterOp :=
  Fin.addCases (fun a => if z (cγ a) then CounterOp.inc else CounterOp.keep)
    (Fin.addCases (fun a => if z (cγ a) then CounterOp.keep else CounterOp.dec)
      (fun _ => CounterOp.keep))

/-- The consult-step counter update: apply the simulated head moves to the
`δ`s (`left ↦ dec` matches the truncated `HeadMove.apply`), keep the `γ`s
(zero at `⊢`), and apply the simulated counter operations. -/
def opsM (mv : Fin h → HeadMove) (ops : Fin c → CounterOp) :
    Fin (h + (h + c)) → CounterOp :=
  Fin.addCases (fun a => match mv a with
      | HeadMove.left => CounterOp.dec
      | HeadMove.stay => CounterOp.keep
      | HeadMove.right => CounterOp.inc)
    (Fin.addCases (fun _ => CounterOp.keep) ops)

@[simp] theorem opsR_δ (z : Fin (h + (h + c)) → Bool) (a : Fin h) :
    opsR z (cδ a) = if z (cδ a) then CounterOp.keep else CounterOp.dec := by
  simp [opsR, cδ]

@[simp] theorem opsR_γ (z : Fin (h + (h + c)) → Bool) (a : Fin h) :
    opsR z (cγ a) = if z (cδ a) then CounterOp.inc else CounterOp.keep := by
  simp [opsR, cγ]

@[simp] theorem opsR_O (z : Fin (h + (h + c)) → Bool) (j : Fin c) :
    opsR z (cO j) = CounterOp.keep := by
  simp [opsR, cO]

@[simp] theorem opsL_δ (z : Fin (h + (h + c)) → Bool) (a : Fin h) :
    opsL z (cδ a) = if z (cγ a) then CounterOp.inc else CounterOp.keep := by
  simp [opsL, cδ]

@[simp] theorem opsL_γ (z : Fin (h + (h + c)) → Bool) (a : Fin h) :
    opsL z (cγ a) = if z (cγ a) then CounterOp.keep else CounterOp.dec := by
  simp [opsL, cγ]

@[simp] theorem opsL_O (z : Fin (h + (h + c)) → Bool) (j : Fin c) :
    opsL z (cO j) = CounterOp.keep := by
  simp [opsL, cO]

@[simp] theorem opsM_δ (mv : Fin h → HeadMove) (ops : Fin c → CounterOp) (a : Fin h) :
    opsM mv ops (cδ a) = match mv a with
      | HeadMove.left => CounterOp.dec
      | HeadMove.stay => CounterOp.keep
      | HeadMove.right => CounterOp.inc := by
  simp [opsM, cδ]

@[simp] theorem opsM_γ (mv : Fin h → HeadMove) (ops : Fin c → CounterOp) (a : Fin h) :
    opsM mv ops (cγ a) = CounterOp.keep := by
  simp [opsM, cγ]

@[simp] theorem opsM_O (mv : Fin h → HeadMove) (ops : Fin c → CounterOp) (j : Fin c) :
    opsM mv ops (cO j) = ops j := by
  simp [opsM, cO]

end Generic

section Machine

variable {Alpha Gamma : Type} {h c : ℕ}

/-- The simulator's transition function.  See the file header for the cycle
structure. -/
def stepF (M : MHC Alpha Gamma h c) (st : M.Q × Ph Alpha h) (s : TapeSym Alpha)
    (z : Fin (h + (h + c)) → Bool) :
    Option ((M.Q × Ph Alpha h) × (Fin 1 → HeadMove) ×
      (Fin (h + (h + c)) → CounterOp) × List Gamma) :=
  match st.2.mode with
  | Mode.sweepR =>
      let pending : Fin h → Bool := fun a => z (cδ a) && (st.2.syms a).isNone
      let recorded : Fin h → Bool := fun a => (st.2.syms a).isSome
      let syms' := recSyms st.2.syms s pending
      let coin' := recCoin st.2.coin recorded pending
      match s with
      | TapeSym.rmark =>
          some ((st.1, ⟨Mode.sweepL, syms', coin'⟩), fun _ => HeadMove.left, opsL z, [])
      | _ =>
          some ((st.1, ⟨Mode.sweepR, syms', coin'⟩), fun _ => HeadMove.right, opsR z, [])
  | Mode.sweepL =>
      match s with
      | TapeSym.lmark =>
          some ((st.1, ⟨Mode.consult, st.2.syms, st.2.coin⟩), fun _ => HeadMove.stay,
            fun _ => CounterOp.keep, [])
      | _ =>
          some ((st.1, ⟨Mode.sweepL, st.2.syms, st.2.coin⟩), fun _ => HeadMove.left,
            opsL z, [])
  | Mode.consult =>
      match M.η st.1 (fun a => (st.2.syms a).getD TapeSym.lmark)
          (fun a b => (st.2.coin a b).getD false) (fun j => z (cO j)) with
      | none => none
      | some (mq', mv, ops, u) =>
          some ((mq', phStart Alpha h), fun _ => HeadMove.stay, opsM mv ops, u)

/-- **The single-head simulator.** -/
def oneHead [Fintype Alpha] [DecidableEq Alpha] (M : MHC Alpha Gamma h c) :
    MHC Alpha Gamma 1 (h + (h + c)) where
  Q := M.Q × Ph Alpha h
  fintypeQ := letI := M.fintypeQ; inferInstance
  q0 := (M.q0, phStart Alpha h)
  F := fun st => M.F st.1 ∧ st.2.mode = Mode.consult
  η := fun st syms _ z => stepF M st (syms 0) z
  rmark_no_right := by
    intro q syms coin zs r hr a hrm
    have h0 : syms a = syms 0 := by rw [Fin.eq_zero a]
    rw [h0] at hrm
    rw [hrm] at hr
    unfold stepF at hr
    rcases hmode : q.2.mode with _ | _ | _ <;> rw [hmode] at hr
    · -- sweepR at ⊣ turns left
      have heq := Option.some.inj hr
      rw [← heq]
      simp
    · -- sweepL moves left
      have heq := Option.some.inj hr
      rw [← heq]
      simp
    · -- consult stays
      rcases hη : M.η q.1 (fun a => (q.2.syms a).getD TapeSym.lmark)
          (fun a b => (q.2.coin a b).getD false) (fun j => zs (cO j)) with _ | val
      · rw [hη] at hr; exact absurd hr (by simp)
      · rw [hη] at hr
        obtain ⟨mq', mv, ops, u⟩ := val
        have heq := Option.some.inj hr
        rw [← heq]
        simp

/-! ## The intended recording state at head position `i` -/

/-- The symbols recorded after the right sweep has passed position `i`:
head `a` is recorded exactly when `pos a < i`. -/
def symsAt (w : List Alpha) (pos : Fin h → ℕ) (i : ℕ) : Fin h → Option (TapeSym Alpha) :=
  fun a => if pos a < i then some (tapeSym w (pos a)) else none

/-- The coincidence bits recorded after the right sweep has passed
position `i`. -/
def coinAt (pos : Fin h → ℕ) (i : ℕ) : Fin h → Fin h → Option Bool :=
  fun a b => if pos a < i ∧ pos b < i then some (pos a == pos b) else none

theorem symsAt_zero (w : List Alpha) (pos : Fin h → ℕ) :
    symsAt w pos 0 = fun _ => none := by
  funext a
  simp [symsAt]

theorem coinAt_zero (pos : Fin h → ℕ) :
    coinAt pos 0 = fun _ _ => none := by
  funext a b
  simp [coinAt]

theorem symsAt_getD (w : List Alpha) (pos : Fin h → ℕ) {i : ℕ}
    (hpos : ∀ a, pos a < i) (a : Fin h) :
    (symsAt w pos i a).getD TapeSym.lmark = tapeSym w (pos a) := by
  simp [symsAt, hpos a]

theorem coinAt_getD (pos : Fin h → ℕ) {i : ℕ} (hpos : ∀ a, pos a < i)
    (a b : Fin h) :
    (coinAt pos i a b).getD false = (pos a == pos b) := by
  simp [coinAt, hpos a, hpos b]

/-! ## One recording step -/

/-- The zero-pattern of the encoded counters. -/
def zAt (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (i : ℕ) : Fin (h + (h + c)) → Bool :=
  fun t => encCnt pos cnt i t == 0

@[simp] theorem zAt_δ (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (i : ℕ) (a : Fin h) :
    zAt pos cnt i (cδ a) = decide (pos a ≤ i) := by
  simp only [zAt, encCnt_δ]
  rcases (by omega : pos a ≤ i ∨ i < pos a) with hc | hc
  · simp [Nat.sub_eq_zero_of_le hc, hc]
  · have h1 : pos a - i ≠ 0 := by omega
    have h2 : ¬ (pos a ≤ i) := by omega
    simp [h1, h2]

@[simp] theorem zAt_γ (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (i : ℕ) (a : Fin h) :
    zAt pos cnt i (cγ a) = decide (i ≤ pos a) := by
  simp only [zAt, encCnt_γ]
  rcases (by omega : i ≤ pos a ∨ pos a < i) with hc | hc
  · simp [Nat.sub_eq_zero_of_le hc, hc]
  · have h1 : i - pos a ≠ 0 := by omega
    have h2 : ¬ (i ≤ pos a) := by omega
    simp [h1, h2]

@[simp] theorem zAt_O (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (i : ℕ) (j : Fin c) :
    zAt pos cnt i (cO j) = (cnt j == 0) := by
  simp [zAt]

/-- The pending predicate at position `i` picks out exactly the heads at
cell `i`. -/
theorem pending_at (w : List Alpha) (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (i : ℕ)
    (a : Fin h) :
    (zAt pos cnt i (cδ a) && (symsAt w pos i a).isNone) = decide (pos a = i) := by
  rw [zAt_δ]
  simp only [symsAt]
  rcases lt_trichotomy (pos a) i with hc | hc | hc
  · simp [hc]
    omega
  · simp [hc]
  · have h1 : ¬ (pos a ≤ i) := by omega
    have h2 : ¬ (pos a < i) := by omega
    simp [h1, h2]
    omega

/-- Recording at cell `i` advances the symbol table from `i` to `i + 1`. -/
theorem recSyms_at (w : List Alpha) (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (i : ℕ) :
    recSyms (symsAt w pos i) (tapeSym w i)
      (fun a => zAt pos cnt i (cδ a) && (symsAt w pos i a).isNone)
      = symsAt w pos (i + 1) := by
  funext a
  rw [recSyms, pending_at]
  rcases lt_trichotomy (pos a) i with hc | hc | hc
  · rw [if_neg (by simp; omega)]
    simp only [symsAt]
    rw [if_pos hc, if_pos (by omega)]
  · rw [if_pos (by simp [hc])]
    simp only [symsAt]
    rw [if_pos (by omega), hc]
  · rw [if_neg (by simp; omega)]
    simp only [symsAt]
    rw [if_neg (by omega), if_neg (by omega)]

/-- Recording at cell `i` advances the coincidence table from `i` to
`i + 1`. -/
theorem recCoin_at (w : List Alpha) (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (i : ℕ) :
    recCoin (coinAt pos i) (fun a => (symsAt w pos i a).isSome)
      (fun a => zAt pos cnt i (cδ a) && (symsAt w pos i a).isNone)
      = coinAt pos (i + 1) := by
  funext a b
  rw [recCoin]
  simp only [pending_at]
  have hrec : ∀ x : Fin h, (symsAt w pos i x).isSome = decide (pos x < i) := by
    intro x
    simp only [symsAt]
    rcases Nat.lt_or_ge (pos x) i with hc | hc
    · simp [hc]
    · rw [if_neg (by omega)]
      simp
      omega
  rw [hrec a, hrec b]
  rcases lt_trichotomy (pos a) i with ha | ha | ha <;>
    rcases lt_trichotomy (pos b) i with hb | hb | hb
  -- a < i, b < i : both recorded, table unchanged
  · rw [if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp; omega)]
    simp only [coinAt]
    rw [if_pos ⟨ha, hb⟩, if_pos ⟨by omega, by omega⟩]
  -- a < i, b = i : recorded–pending, `false`
  · rw [if_neg (by simp; omega), if_neg (by simp; omega),
      if_pos (by simp; omega)]
    simp only [coinAt]
    rw [if_pos ⟨by omega, by omega⟩]
    have : (pos a == pos b) = false := by
      simp
      omega
    rw [this]
  -- a < i, b > i
  · rw [if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp; omega)]
    simp only [coinAt]
    rw [if_neg (by omega), if_neg (by omega)]
  -- a = i, b < i : pending–recorded, `false`
  · rw [if_neg (by simp; omega), if_pos (by simp; omega)]
    simp only [coinAt]
    rw [if_pos ⟨by omega, by omega⟩]
    have : (pos a == pos b) = false := by
      simp
      omega
    rw [this]
  -- a = i, b = i : pending–pending, `true`
  · rw [if_pos (by simp; omega)]
    simp only [coinAt]
    rw [if_pos ⟨by omega, by omega⟩]
    have : (pos a == pos b) = true := by
      simp
      omega
    rw [this]
  -- a = i, b > i
  · rw [if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp; omega)]
    simp only [coinAt]
    rw [if_neg (by omega), if_neg (by omega)]
  -- a > i, b < i
  · rw [if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp; omega)]
    simp only [coinAt]
    rw [if_neg (by omega), if_neg (by omega)]
  -- a > i, b = i
  · rw [if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp; omega)]
    simp only [coinAt]
    rw [if_neg (by omega), if_neg (by omega)]
  -- a > i, b > i
  · rw [if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp; omega)]
    simp only [coinAt]
    rw [if_neg (by omega), if_neg (by omega)]

/-! ## Counter updates along the sweeps -/

/-- The right-sweep operations advance the encoded counters from `i` to
`i + 1`. -/
theorem encCnt_opsR (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (i : ℕ) :
    (fun t => (opsR (zAt pos cnt i) t).apply (encCnt pos cnt i t))
      = encCnt pos cnt (i + 1) := by
  funext t
  refine Fin.addCases (fun a => ?_) (fun t' => Fin.addCases (fun a => ?_) (fun j => ?_) t') t
  · show (opsR (zAt pos cnt i) (cδ a)).apply (encCnt pos cnt i (cδ a))
      = encCnt pos cnt (i + 1) (cδ a)
    rw [opsR_δ, zAt_δ, encCnt_δ, encCnt_δ]
    rcases (by omega : pos a ≤ i ∨ i < pos a) with hc | hc
    · rw [if_pos (by simp [hc])]
      simp
      omega
    · rw [if_neg (by simp; omega)]
      simp
      omega
  · show (opsR (zAt pos cnt i) (cγ a)).apply (encCnt pos cnt i (cγ a))
      = encCnt pos cnt (i + 1) (cγ a)
    rw [opsR_γ, zAt_δ, encCnt_γ, encCnt_γ]
    rcases (by omega : pos a ≤ i ∨ i < pos a) with hc | hc
    · rw [if_pos (by simp [hc])]
      simp
      omega
    · rw [if_neg (by simp; omega)]
      simp
      omega
  · show (opsR (zAt pos cnt i) (cO j)).apply (encCnt pos cnt i (cO j))
      = encCnt pos cnt (i + 1) (cO j)
    rw [opsR_O, encCnt_O, encCnt_O]
    rfl

/-- The left-sweep operations move the encoded counters from `i` to `i - 1`. -/
theorem encCnt_opsL (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (i : ℕ) (hi : 1 ≤ i) :
    (fun t => (opsL (zAt pos cnt i) t).apply (encCnt pos cnt i t))
      = encCnt pos cnt (i - 1) := by
  funext t
  refine Fin.addCases (fun a => ?_) (fun t' => Fin.addCases (fun a => ?_) (fun j => ?_) t') t
  · show (opsL (zAt pos cnt i) (cδ a)).apply (encCnt pos cnt i (cδ a))
      = encCnt pos cnt (i - 1) (cδ a)
    rw [opsL_δ, zAt_γ, encCnt_δ, encCnt_δ]
    rcases (by omega : i ≤ pos a ∨ pos a < i) with hc | hc
    · rw [if_pos (by simp [hc])]
      simp
      omega
    · rw [if_neg (by simp; omega)]
      simp
      omega
  · show (opsL (zAt pos cnt i) (cγ a)).apply (encCnt pos cnt i (cγ a))
      = encCnt pos cnt (i - 1) (cγ a)
    rw [opsL_γ, zAt_γ, encCnt_γ, encCnt_γ]
    rcases (by omega : i ≤ pos a ∨ pos a < i) with hc | hc
    · rw [if_pos (by simp [hc])]
      simp
      omega
    · rw [if_neg (by simp; omega)]
      simp
      omega
  · show (opsL (zAt pos cnt i) (cO j)).apply (encCnt pos cnt i (cO j))
      = encCnt pos cnt (i - 1) (cO j)
    rw [opsL_O, encCnt_O, encCnt_O]
    rfl

/-- The consult-step operations at `⊢` turn the encoded counters into the
encoding of the stepped simulated configuration. -/
theorem encCnt_opsM (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (mv : Fin h → HeadMove)
    (ops : Fin c → CounterOp) :
    (fun t => (opsM mv ops t).apply (encCnt pos cnt 0 t))
      = encCnt (fun a => (mv a).apply (pos a)) (fun j => (ops j).apply (cnt j)) 0 := by
  funext t
  refine Fin.addCases (fun a => ?_) (fun t' => Fin.addCases (fun a => ?_) (fun j => ?_) t') t
  · show (opsM mv ops (cδ a)).apply (encCnt pos cnt 0 (cδ a))
      = encCnt (fun a => (mv a).apply (pos a)) (fun j => (ops j).apply (cnt j)) 0 (cδ a)
    rw [opsM_δ, encCnt_δ, encCnt_δ]
    cases mv a <;> simp
  · show (opsM mv ops (cγ a)).apply (encCnt pos cnt 0 (cγ a))
      = encCnt (fun a => (mv a).apply (pos a)) (fun j => (ops j).apply (cnt j)) 0 (cγ a)
    rw [opsM_γ, encCnt_γ, encCnt_γ]
    simp
  · show (opsM mv ops (cO j)).apply (encCnt pos cnt 0 (cO j))
      = encCnt (fun a => (mv a).apply (pos a)) (fun j => (ops j).apply (cnt j)) 0 (cO j)
    rw [opsM_O, encCnt_O, encCnt_O]

/-! ## Step equations for the simulator -/

variable (M : MHC Alpha Gamma h c)

theorem stepF_sweepR (mq : M.Q) (syms : Fin h → Option (TapeSym Alpha))
    (coin : Fin h → Fin h → Option Bool) (s : TapeSym Alpha)
    (hs : s ≠ TapeSym.rmark) (z : Fin (h + (h + c)) → Bool) :
    stepF M (mq, ⟨Mode.sweepR, syms, coin⟩) s z =
      some ((mq, ⟨Mode.sweepR,
          recSyms syms s (fun a => z (cδ a) && (syms a).isNone),
          recCoin coin (fun a => (syms a).isSome)
            (fun a => z (cδ a) && (syms a).isNone)⟩),
        fun _ => HeadMove.right, opsR z, []) := by
  rcases s with _ | a | _
  · rfl
  · rfl
  · exact absurd rfl hs

theorem stepF_sweepR_rmark (mq : M.Q) (syms : Fin h → Option (TapeSym Alpha))
    (coin : Fin h → Fin h → Option Bool) (z : Fin (h + (h + c)) → Bool) :
    stepF M (mq, ⟨Mode.sweepR, syms, coin⟩) TapeSym.rmark z =
      some ((mq, ⟨Mode.sweepL,
          recSyms syms TapeSym.rmark (fun a => z (cδ a) && (syms a).isNone),
          recCoin coin (fun a => (syms a).isSome)
            (fun a => z (cδ a) && (syms a).isNone)⟩),
        fun _ => HeadMove.left, opsL z, []) := rfl

theorem stepF_sweepL (mq : M.Q) (syms : Fin h → Option (TapeSym Alpha))
    (coin : Fin h → Fin h → Option Bool) (s : TapeSym Alpha)
    (hs : s ≠ TapeSym.lmark) (z : Fin (h + (h + c)) → Bool) :
    stepF M (mq, ⟨Mode.sweepL, syms, coin⟩) s z =
      some ((mq, ⟨Mode.sweepL, syms, coin⟩), fun _ => HeadMove.left, opsL z, []) := by
  rcases s with _ | a | _
  · exact absurd rfl hs
  · rfl
  · rfl

theorem stepF_sweepL_lmark (mq : M.Q) (syms : Fin h → Option (TapeSym Alpha))
    (coin : Fin h → Fin h → Option Bool) (z : Fin (h + (h + c)) → Bool) :
    stepF M (mq, ⟨Mode.sweepL, syms, coin⟩) TapeSym.lmark z =
      some ((mq, ⟨Mode.consult, syms, coin⟩), fun _ => HeadMove.stay,
        fun _ => CounterOp.keep, []) := rfl

theorem stepF_consult (mq : M.Q) (syms : Fin h → Option (TapeSym Alpha))
    (coin : Fin h → Fin h → Option Bool) (s : TapeSym Alpha)
    (z : Fin (h + (h + c)) → Bool) :
    stepF M (mq, ⟨Mode.consult, syms, coin⟩) s z =
      (M.η mq (fun a => (syms a).getD TapeSym.lmark)
        (fun a b => (coin a b).getD false) (fun j => z (cO j))).map
        (fun r => ((r.1, phStart Alpha h), fun _ => HeadMove.stay,
          opsM r.2.1 r.2.2.1, r.2.2.2)) := by
  show (match M.η mq (fun a => (syms a).getD TapeSym.lmark)
      (fun a b => (coin a b).getD false) (fun j => z (cO j)) with
    | none => none
    | some (mq', mv, ops, u) =>
        some ((mq', phStart Alpha h), fun _ => HeadMove.stay, opsM mv ops, u)) = _
  rcases M.η mq (fun a => (syms a).getD TapeSym.lmark)
      (fun a b => (coin a b).getD false) (fun j => z (cO j)) with _ | ⟨mq', mv, ops, u⟩
  · rfl
  · rfl

/-! ## Generic `MHC` run helpers (determinism plumbing) -/

/-- `StepsN.head` with the successor configuration supplied up to equality. -/
theorem _root_.Multihead.MHC.StepsN.head' {Alpha Gamma : Type*} {h c : ℕ}
    {M : MHC Alpha Gamma h c} {w : List Alpha} {q : M.Q} {pos1 : Fin h → ℕ}
    {cnt1 : Fin c → ℕ} {q' : M.Q} {mv : Fin h → HeadMove} {ops : Fin c → CounterOp}
    {u out : List Gamma} {e : M.Config} {N : ℕ} {pos2 : Fin h → ℕ} {cnt2 : Fin c → ℕ}
    (hη : M.η q (fun a => tapeSym w (pos1 a)) (fun a b => pos1 a == pos1 b)
      (fun j => cnt1 j == 0) = some (q', mv, ops, u))
    (hpos : (fun a => (mv a).apply (pos1 a)) = pos2)
    (hcnt : (fun j => (ops j).apply (cnt1 j)) = cnt2)
    (rest : M.StepsN w (q', pos2, cnt2) out e N) :
    M.StepsN w (q, pos1, cnt1) (u ++ out) e (N + 1) := by
  subst hpos
  subst hcnt
  exact Multihead.MHC.StepsN.head hη rest

/-- Two runs of the same length from the same configuration coincide. -/
theorem _root_.Multihead.MHC.stepsN_same_len {Alpha Gamma : Type*} {h c : ℕ}
    {M : MHC Alpha Gamma h c} {w : List Alpha} :
    ∀ {cfg e₁ e₂ : M.Config} {o₁ o₂ : List Gamma} {N : ℕ},
      M.StepsN w cfg o₁ e₁ N → M.StepsN w cfg o₂ e₂ N → o₁ = o₂ ∧ e₁ = e₂ := by
  intro cfg e₁ e₂ o₁ o₂ N h₁
  induction h₁ generalizing o₂ e₂ with
  | refl cfg =>
      intro h₂
      cases h₂
      exact ⟨rfl, rfl⟩
  | head hη rest ih =>
      intro h₂
      cases h₂ with
      | head hη' rest' =>
          rw [hη] at hη'
          injection hη' with htuple
          injection htuple with hq hrest
          injection hrest with hmv hrest'
          injection hrest' with hops hu
          subst hq; subst hmv; subst hops; subst hu
          obtain ⟨ho, he⟩ := ih rest'
          exact ⟨by rw [ho], he⟩

/-- No run outlives a halting run: a halting run's length bounds the length of
every run from the same configuration. -/
theorem _root_.Multihead.MHC.stepsN_le_of_halted {Alpha Gamma : Type*} {h c : ℕ}
    {M : MHC Alpha Gamma h c} {w : List Alpha} {cfg e₁ e₂ : M.Config}
    {o₁ o₂ : List Gamma} {N₁ N₂ : ℕ}
    (h₁ : M.StepsN w cfg o₁ e₁ N₁) (hh : M.Halted w e₁)
    (h₂ : M.StepsN w cfg o₂ e₂ N₂) : N₂ ≤ N₁ := by
  by_contra hlt
  obtain ⟨mid, p₁, p₂, -, hpre, hsuf⟩ := Multihead.MHC.stepsN_split h₂ N₁ (by omega)
  obtain ⟨-, hmid⟩ := Multihead.MHC.stepsN_same_len h₁ hpre
  obtain ⟨k, hk⟩ : ∃ k, N₂ - N₁ = k + 1 := ⟨N₂ - N₁ - 1, by omega⟩
  rw [hk] at hsuf
  obtain ⟨mq, mpos, mcnt⟩ := mid
  rw [hmid] at hh
  cases hsuf with
  | head hη rest =>
      exact Multihead.MHC.not_halted_of_step hη hh

/-- Every machine either runs for `K` steps or halts earlier. -/
theorem _root_.Multihead.MHC.exists_run_upto {Alpha Gamma : Type*} {h c : ℕ}
    {M : MHC Alpha Gamma h c} (w : List Alpha) :
    ∀ K : ℕ, ∃ (out : List Gamma) (e : M.Config) (K' : ℕ), K' ≤ K ∧
      M.StepsN w M.initConfig out e K' ∧ (K' = K ∨ M.Halted w e) := by
  intro K
  induction K with
  | zero => exact ⟨[], M.initConfig, 0, le_refl 0, Multihead.MHC.StepsN.refl _, Or.inl rfl⟩
  | succ K ih =>
      obtain ⟨out, e, K', hle, hrun, hcase⟩ := ih
      rcases hcase with rfl | hhalt
      · obtain ⟨eq, epos, ecnt⟩ := e
        rcases hη : M.η eq (fun a => tapeSym w (epos a)) (fun a b => epos a == epos b)
            (fun j => ecnt j == 0) with _ | ⟨q', mv, ops, u⟩
        · refine ⟨out, (eq, epos, ecnt), K', by omega, hrun, Or.inr ?_⟩
          show M.η eq (fun a => tapeSym w (epos a)) (fun a b => epos a == epos b)
            (fun j => ecnt j == 0) = none
          exact hη
        · exact ⟨out ++ (u ++ []),
            (q', fun a => (mv a).apply (epos a), fun j => (ops j).apply (ecnt j)),
            K' + 1, le_refl _,
            hrun.trans (Multihead.MHC.StepsN.head hη (Multihead.MHC.StepsN.refl _)),
            Or.inl rfl⟩
      · exact ⟨out, e, K', by omega, hrun, Or.inr hhalt⟩

/-! ## The sweep runs -/

/-- Position `≤ |w|` reads a non-`⊣` symbol. -/
theorem tapeSym_ne_rmark {w : List Alpha} {i : ℕ} (hi : i ≤ w.length) :
    tapeSym w i ≠ TapeSym.rmark := by
  unfold tapeSym
  by_cases h0 : i = 0
  · rw [if_pos h0]
    simp
  · rw [if_neg h0, dif_pos (by omega : i - 1 < w.length)]
    simp

/-- A positive position reads a non-`⊢` symbol. -/
theorem tapeSym_ne_lmark {w : List Alpha} {i : ℕ} (hi : 1 ≤ i) :
    tapeSym w i ≠ TapeSym.lmark := by
  unfold tapeSym
  rw [if_neg (by omega)]
  split
  · simp
  · simp

section Runs

variable [Fintype Alpha] [DecidableEq Alpha] {M : MHC Alpha Gamma h c}

/-- The simulator's transition, unfolded (definitional). -/
theorem oneHead_η_apply (st : M.Q × Ph Alpha h) (s : TapeSym Alpha)
    (coin : Fin 1 → Fin 1 → Bool) (z : Fin (h + (h + c)) → Bool) :
    (oneHead M).η st (fun _ => s) coin z = stepF M st s z := rfl

/-- The simulator's halting predicate, unfolded (definitional). -/
theorem oneHead_halted (w : List Alpha) (st : M.Q × Ph Alpha h) (i : ℕ)
    (bank : Fin (h + (h + c)) → ℕ) :
    (oneHead M).Halted w (st, (fun _ => i), bank) ↔
      stepF M st (tapeSym w i) (fun t => bank t == 0) = none := Iff.rfl

/-- **The right sweep**: from any position `i` with fuel `k = (n+1) - i`, the
simulator scans to `⊣`, recording as it goes, then turns; it arrives in the
left-sweep phase at position `n` with the full tables and the counters intact,
in `k + 1` steps, emitting nothing. -/
theorem sweepR_run (w : List Alpha) (mq : M.Q) (pos : Fin h → ℕ) (cnt : Fin c → ℕ) :
    ∀ k i, i + k = w.length + 1 →
      (oneHead M).StepsN w
        ((mq, ⟨Mode.sweepR, symsAt w pos i, coinAt pos i⟩), fun _ => i,
          encCnt pos cnt i)
        []
        ((mq, ⟨Mode.sweepL, symsAt w pos (w.length + 2), coinAt pos (w.length + 2)⟩),
          fun _ => w.length, encCnt pos cnt w.length)
        (k + 1) := by
  intro k
  induction k with
  | zero =>
      intro i hi
      have hieq : i = w.length + 1 := by omega
      subst hieq
      have hsym : tapeSym w (w.length + 1) = TapeSym.rmark := tapeSym_ge w _ (by omega)
      have hη : (oneHead M).η (mq, ⟨Mode.sweepR, symsAt w pos (w.length + 1),
            coinAt pos (w.length + 1)⟩)
          (fun _ : Fin 1 => tapeSym w (w.length + 1))
          (fun _ _ : Fin 1 => ((w.length + 1) == (w.length + 1)))
          (fun t => encCnt pos cnt (w.length + 1) t == 0)
          = some ((mq, ⟨Mode.sweepL, symsAt w pos (w.length + 2),
              coinAt pos (w.length + 2)⟩),
            fun _ => HeadMove.left, opsL (zAt pos cnt (w.length + 1)), []) := by
        rw [oneHead_η_apply, show (fun t => encCnt pos cnt (w.length + 1) t == 0)
          = zAt pos cnt (w.length + 1) from rfl]
        rw [hsym, stepF_sweepR_rmark]
        rw [← hsym]
        rw [recSyms_at w pos cnt (w.length + 1), recCoin_at w pos cnt (w.length + 1)]
      refine Multihead.MHC.StepsN.head' hη ?_ ?_ (Multihead.MHC.StepsN.refl _)
      · funext a
        simp
      · rw [encCnt_opsL pos cnt (w.length + 1) (by omega)]
        simp
  | succ k ih =>
      intro i hi
      have hile : i ≤ w.length := by omega
      have hsym : tapeSym w i ≠ TapeSym.rmark := tapeSym_ne_rmark hile
      have hη : (oneHead M).η (mq, ⟨Mode.sweepR, symsAt w pos i, coinAt pos i⟩)
          (fun _ : Fin 1 => tapeSym w i) (fun _ _ : Fin 1 => (i == i))
          (fun t => encCnt pos cnt i t == 0)
          = some ((mq, ⟨Mode.sweepR, symsAt w pos (i + 1), coinAt pos (i + 1)⟩),
            fun _ => HeadMove.right, opsR (zAt pos cnt i), []) := by
        rw [oneHead_η_apply, show (fun t => encCnt pos cnt i t == 0)
          = zAt pos cnt i from rfl]
        rw [stepF_sweepR M mq _ _ _ hsym]
        rw [recSyms_at w pos cnt i, recCoin_at w pos cnt i]
      refine Multihead.MHC.StepsN.head' hη ?_ ?_ (ih (i + 1) (by omega))
      · funext a
        simp
      · rw [encCnt_opsR pos cnt i]

/-- **The left sweep**: from position `i` the simulator walks back to `⊢`
and switches to `consult`, in `i + 1` steps, carrying the tables and the
counters. -/
theorem sweepL_run (w : List Alpha) (mq : M.Q) (pos : Fin h → ℕ) (cnt : Fin c → ℕ)
    (S : Fin h → Option (TapeSym Alpha)) (Co : Fin h → Fin h → Option Bool) :
    ∀ i, (oneHead M).StepsN w
        ((mq, ⟨Mode.sweepL, S, Co⟩), fun _ => i, encCnt pos cnt i)
        []
        ((mq, ⟨Mode.consult, S, Co⟩), fun _ => 0, encCnt pos cnt 0)
        (i + 1) := by
  intro i
  induction i with
  | zero =>
      have hη : (oneHead M).η (mq, ⟨Mode.sweepL, S, Co⟩)
          (fun _ : Fin 1 => tapeSym w 0) (fun _ _ : Fin 1 => ((0 : ℕ) == 0))
          (fun t => encCnt pos cnt 0 t == 0)
          = some ((mq, ⟨Mode.consult, S, Co⟩), fun _ => HeadMove.stay,
            fun _ => CounterOp.keep, []) := by
        rw [oneHead_η_apply, show (fun t => encCnt pos cnt 0 t == 0)
          = zAt pos cnt 0 from rfl]
        rw [tapeSym_zero, stepF_sweepL_lmark]
      refine Multihead.MHC.StepsN.head' hη ?_ ?_ (Multihead.MHC.StepsN.refl _)
      · funext a
        simp
      · funext t
        simp
  | succ i ih =>
      have hsym : tapeSym w (i + 1) ≠ TapeSym.lmark := tapeSym_ne_lmark (by omega)
      have hη : (oneHead M).η (mq, ⟨Mode.sweepL, S, Co⟩)
          (fun _ : Fin 1 => tapeSym w (i + 1)) (fun _ _ : Fin 1 => ((i + 1) == (i + 1)))
          (fun t => encCnt pos cnt (i + 1) t == 0)
          = some ((mq, ⟨Mode.sweepL, S, Co⟩), fun _ => HeadMove.left,
            opsL (zAt pos cnt (i + 1)), []) := by
        rw [oneHead_η_apply, show (fun t => encCnt pos cnt (i + 1) t == 0)
          = zAt pos cnt (i + 1) from rfl]
        rw [stepF_sweepL M mq _ _ _ hsym]
      refine Multihead.MHC.StepsN.head' hη ?_ ?_ ih
      · funext a
        simp
      · rw [encCnt_opsL pos cnt (i + 1) (by omega)]
        simp

/-- **One full cycle** on a defined transition: the simulator carries out one
simulated step, emitting exactly its output and re-entering the fresh phase
with the stepped configuration encoded. -/
theorem cycle (w : List Alpha) (mq : M.Q) (pos : Fin h → ℕ) (cnt : Fin c → ℕ)
    {mq' : M.Q} {mv : Fin h → HeadMove} {ops : Fin c → CounterOp} {u : List Gamma}
    (hpos : ∀ a, pos a ≤ w.length + 1)
    (hη : M.η mq (fun a => tapeSym w (pos a)) (fun a b => pos a == pos b)
      (fun j => cnt j == 0) = some (mq', mv, ops, u)) :
    ∃ N, 1 ≤ N ∧ (oneHead M).StepsN w
      ((mq, phStart Alpha h), fun _ => 0, encCnt pos cnt 0) u
      ((mq', phStart Alpha h), fun _ => 0,
        encCnt (fun a => (mv a).apply (pos a)) (fun j => (ops j).apply (cnt j)) 0)
      N := by
  have hph : (phStart Alpha h : Ph Alpha h)
      = ⟨Mode.sweepR, symsAt w pos 0, coinAt pos 0⟩ := by
    rw [phStart, symsAt_zero, coinAt_zero]
  have h1 := sweepR_run (M := M) w mq pos cnt (w.length + 1) 0 (by omega)
  have h2 := sweepL_run (M := M) w mq pos cnt
    (symsAt w pos (w.length + 2)) (coinAt pos (w.length + 2)) w.length
  have hposlt : ∀ a, pos a < w.length + 2 := fun a => by have := hpos a; omega
  have hη3 : (oneHead M).η (mq, ⟨Mode.consult, symsAt w pos (w.length + 2),
        coinAt pos (w.length + 2)⟩)
      (fun _ : Fin 1 => tapeSym w 0) (fun _ _ : Fin 1 => ((0 : ℕ) == 0))
      (fun t => encCnt pos cnt 0 t == 0)
      = some ((mq', phStart Alpha h), fun _ => HeadMove.stay, opsM mv ops, u) := by
    rw [oneHead_η_apply, show (fun t => encCnt pos cnt 0 t == 0)
      = zAt pos cnt 0 from rfl]
    rw [stepF_consult]
    have hs : (fun a => ((symsAt w pos (w.length + 2)) a).getD TapeSym.lmark)
        = fun a => tapeSym w (pos a) := funext fun a => symsAt_getD w pos hposlt a
    have hc : (fun a b => ((coinAt pos (w.length + 2)) a b).getD false)
        = fun a b => (pos a == pos b) := funext fun a => funext fun b =>
          coinAt_getD pos hposlt a b
    have hz : (fun j => zAt pos cnt 0 (cO j)) = fun j => (cnt j == 0) :=
      funext fun j => zAt_O pos cnt 0 j
    rw [hs, hc, hz, hη]
    rfl
  have h3 := Multihead.MHC.StepsN.head' (pos2 := fun _ => 0)
    (cnt2 := encCnt (fun a => (mv a).apply (pos a)) (fun j => (ops j).apply (cnt j)) 0)
    hη3 (funext fun a => by simp) (encCnt_opsM pos cnt mv ops)
    (Multihead.MHC.StepsN.refl _)
  refine ⟨(w.length + 1 + 1) + ((w.length + 1) + (0 + 1)), by omega, ?_⟩
  rw [hph]
  have hout : ([] : List Gamma) ++ ([] ++ (u ++ [])) = u := by simp
  rw [← hout]
  exact h1.trans (h2.trans h3)

/-- **The halting cycle**: on an undefined transition the simulator reaches a
halting configuration, emitting nothing, whose acceptance is the simulated
machine's. -/
theorem cycle_halt (w : List Alpha) (mq : M.Q) (pos : Fin h → ℕ) (cnt : Fin c → ℕ)
    (hpos : ∀ a, pos a ≤ w.length + 1)
    (hη : M.η mq (fun a => tapeSym w (pos a)) (fun a b => pos a == pos b)
      (fun j => cnt j == 0) = none) :
    ∃ e N, (oneHead M).StepsN w
      ((mq, phStart Alpha h), fun _ => 0, encCnt pos cnt 0) [] e N ∧
      (oneHead M).Halted w e ∧ ((oneHead M).F e.1 ↔ M.F mq) := by
  have hph : (phStart Alpha h : Ph Alpha h)
      = ⟨Mode.sweepR, symsAt w pos 0, coinAt pos 0⟩ := by
    rw [phStart, symsAt_zero, coinAt_zero]
  have h1 := sweepR_run (M := M) w mq pos cnt (w.length + 1) 0 (by omega)
  have h2 := sweepL_run (M := M) w mq pos cnt
    (symsAt w pos (w.length + 2)) (coinAt pos (w.length + 2)) w.length
  have hposlt : ∀ a, pos a < w.length + 2 := fun a => by have := hpos a; omega
  refine ⟨((mq, ⟨Mode.consult, symsAt w pos (w.length + 2),
      coinAt pos (w.length + 2)⟩), fun _ => 0, encCnt pos cnt 0),
      (w.length + 1 + 1) + (w.length + 1), ?_, ?_, ?_⟩
  · rw [hph]
    have hout : ([] : List Gamma) ++ [] = [] := by simp
    rw [← hout]
    exact h1.trans h2
  · rw [oneHead_halted, show (fun t => encCnt pos cnt 0 t == 0)
      = zAt pos cnt 0 from rfl]
    rw [stepF_consult]
    have hs : (fun a => ((symsAt w pos (w.length + 2)) a).getD TapeSym.lmark)
        = fun a => tapeSym w (pos a) := funext fun a => symsAt_getD w pos hposlt a
    have hc : (fun a b => ((coinAt pos (w.length + 2)) a b).getD false)
        = fun a b => (pos a == pos b) := funext fun a => funext fun b =>
          coinAt_getD pos hposlt a b
    have hz : (fun j => zAt pos cnt 0 (cO j)) = fun j => (cnt j == 0) :=
      funext fun j => zAt_O pos cnt 0 j
    rw [hs, hc, hz, hη]
    rfl
  · show (M.F mq ∧ Mode.consult = Mode.consult) ↔ M.F mq
    simp

/-! ## The top-level simulation -/

omit [Fintype Alpha] [DecidableEq Alpha] in
/-- The simulated head positions stay in `[0, n+1]` across a defined step
(the end-marker discipline of `M`). -/
theorem mhc_pos_step_le {w : List Alpha} {mq : M.Q} {pos : Fin h → ℕ}
    {cnt : Fin c → ℕ} {q' : M.Q} {mv : Fin h → HeadMove} {ops : Fin c → CounterOp}
    {u : List Gamma}
    (hη : M.η mq (fun a => tapeSym w (pos a)) (fun a b => pos a == pos b)
      (fun j => cnt j == 0) = some (q', mv, ops, u))
    (hpos : ∀ a, pos a ≤ w.length + 1) :
    ∀ a, (mv a).apply (pos a) ≤ w.length + 1 := by
  intro a
  cases hmv : mv a with
  | left =>
      simp only [HeadMove.apply_left]
      have := hpos a
      omega
  | stay =>
      simp only [HeadMove.apply_stay]
      exact hpos a
  | right =>
      simp only [HeadMove.apply_right]
      by_cases hle : pos a ≤ w.length
      · omega
      · exfalso
        have hrm : (fun a => tapeSym w (pos a)) a = TapeSym.rmark := by
          show tapeSym w (pos a) = TapeSym.rmark
          exact tapeSym_ge w (pos a) (by omega)
        exact M.rmark_no_right mq _ _ _ _ hη a hrm hmv

/-- The encoded initial counter bank is the all-zero bank. -/
theorem encCnt_init :
    encCnt (fun _ : Fin h => 0) (fun _ : Fin c => 0) 0
      = fun _ : Fin (h + (h + c)) => 0 := by
  funext t
  refine Fin.addCases (fun a => ?_) (fun t' => Fin.addCases (fun a => ?_) (fun j => ?_) t') t
  · show encCnt (fun _ : Fin h => 0) (fun _ : Fin c => 0) 0 (cδ a) = 0
    rw [encCnt_δ]
  · show encCnt (fun _ : Fin h => 0) (fun _ : Fin c => 0) 0 (cγ a) = 0
    rw [encCnt_γ]
  · show encCnt (fun _ : Fin h => 0) (fun _ : Fin c => 0) 0 (cO j) = 0
    rw [encCnt_O]

/-- **The forward simulation**: every simulated run is realised by the
single-head machine, cycle by cycle, with at least one step per simulated
step. -/
theorem simulate (w : List Alpha) :
    ∀ {cfgM eM : M.Config} {out : List Gamma} {K : ℕ},
      M.StepsN w cfgM out eM K → (∀ a, cfgM.2.1 a ≤ w.length + 1) →
      ∃ N, K ≤ N ∧ (oneHead M).StepsN w
        ((cfgM.1, phStart Alpha h), fun _ => 0, encCnt cfgM.2.1 cfgM.2.2 0) out
        ((eM.1, phStart Alpha h), fun _ => 0, encCnt eM.2.1 eM.2.2 0) N := by
  intro cfgM eM out K hrun
  induction hrun with
  | refl cfg =>
      intro hpos
      exact ⟨0, le_refl 0, Multihead.MHC.StepsN.refl _⟩
  | @head q pos cnt q' mv ops u out' e' N' hη rest ih =>
      intro hpos
      have hpos0 : ∀ a, pos a ≤ w.length + 1 := fun a => hpos a
      have hpos' : ∀ a, (mv a).apply (pos a) ≤ w.length + 1 :=
        mhc_pos_step_le hη hpos0
      obtain ⟨N₁, hle₁, hN₁⟩ := ih hpos'
      obtain ⟨N₂, hN₂1, hN₂⟩ := cycle w q pos cnt hpos0 hη
      exact ⟨N₂ + N₁, by omega, hN₂.trans hN₁⟩

/-- **The single-head machine computes the same partial map.** -/
theorem oneHead_computes_iff (w : List Alpha) (out : List Gamma) :
    (oneHead M).Computes w out ↔ M.Computes w out := by
  constructor
  · -- backward: reconstruct the simulated run by determinism
    rintro ⟨eN, ⟨N₀, hrunN⟩, hhN, hFN⟩
    obtain ⟨outM, eM, K', hle, hrunM, hcase⟩ :=
      Multihead.MHC.exists_run_upto (M := M) w (N₀ + 1)
    obtain ⟨mq₂, pos₂, cnt₂⟩ := eM
    have hposi : ∀ a, (M.initConfig.2.1 : Fin h → ℕ) a ≤ w.length + 1 :=
      fun a => Nat.zero_le _
    obtain ⟨N₁, hge, hN₁⟩ := simulate w hrunM hposi
    have hN₁' : (oneHead M).StepsN w (oneHead M).initConfig outM
        ((mq₂, phStart Alpha h), fun _ => 0, encCnt pos₂ cnt₂ 0) N₁ := by
      have hinit : ((oneHead M).initConfig : (oneHead M).Config)
          = (((M.initConfig.1 : M.Q), phStart Alpha h), fun _ => 0,
            encCnt M.initConfig.2.1 M.initConfig.2.2 0) := by
        show ((M.q0, phStart Alpha h), (fun _ => 0 : Fin 1 → ℕ),
            (fun _ => 0 : Fin (h + (h + c)) → ℕ)) = _
        rw [show (M.initConfig : M.Config) = (M.q0, fun _ => 0, fun _ => 0) from rfl,
          encCnt_init]
      rw [hinit]
      exact hN₁
    rcases hcase with hKeq | hhaltM
    · exfalso
      have hle₂ := Multihead.MHC.stepsN_le_of_halted hrunN hhN hN₁'
      omega
    · have hpos₂ : ∀ a, pos₂ a ≤ w.length + 1 := by
        intro a
        exact Multihead.MHC.head_le_of_stepsN hrunM a
      obtain ⟨e', N₂, hrun₂, hh₂, hFiff⟩ := cycle_halt w mq₂ pos₂ cnt₂ hpos₂ hhaltM
      have hfull : (oneHead M).StepsN w (oneHead M).initConfig (outM ++ []) e'
          (N₁ + N₂) := hN₁'.trans hrun₂
      obtain ⟨ho, he, -⟩ :=
        Multihead.MHC.stepsN_unique hrunN hhN hfull hh₂
      have hF' : (oneHead M).F e'.1 := he ▸ hFN
      have hFM : M.F mq₂ := hFiff.mp hF'
      rw [ho, List.append_nil]
      exact ⟨(mq₂, pos₂, cnt₂), ⟨K', hrunM⟩, hhaltM, hFM⟩
  · -- forward: simulate the halting run
    rintro ⟨⟨mq₂, pos₂, cnt₂⟩, ⟨K, hrunM⟩, hhaltM, hFM⟩
    have hposi : ∀ a, (M.initConfig.2.1 : Fin h → ℕ) a ≤ w.length + 1 :=
      fun a => Nat.zero_le _
    obtain ⟨N₁, hge, hN₁⟩ := simulate w hrunM hposi
    have hpos₂ : ∀ a, pos₂ a ≤ w.length + 1 := by
      intro a
      exact Multihead.MHC.head_le_of_stepsN hrunM a
    obtain ⟨e', N₂, hrun₂, hh₂, hFiff⟩ := cycle_halt w mq₂ pos₂ cnt₂ hpos₂ hhaltM
    have hinit : ((oneHead M).initConfig : (oneHead M).Config)
        = (((M.initConfig.1 : M.Q), phStart Alpha h), fun _ => 0,
          encCnt M.initConfig.2.1 M.initConfig.2.2 0) := by
      show ((M.q0, phStart Alpha h), (fun _ => 0 : Fin 1 → ℕ),
          (fun _ => 0 : Fin (h + (h + c)) → ℕ)) = _
      rw [show (M.initConfig : M.Config) = (M.q0, fun _ => 0, fun _ => 0) from rfl,
        encCnt_init]
    refine ⟨e', ⟨N₁ + N₂, ?_⟩, hh₂, hFiff.mpr hFM⟩
    have hfull := hN₁.trans hrun₂
    rw [List.append_nil] at hfull
    rw [hinit]
    exact hfull

/-! ## The space bound -/

omit [Fintype Alpha] [DecidableEq Alpha] in
/-- Reading `⊣` places the head beyond the word. -/
theorem le_of_tapeSym_rmark {w : List Alpha} {i : ℕ}
    (hrm : tapeSym w i = TapeSym.rmark) : w.length + 1 ≤ i := by
  by_contra hlt
  exact tapeSym_ne_rmark (by omega) hrm

omit [Fintype Alpha] [DecidableEq Alpha] in
/-- Reading `⊢` places the head at `0`. -/
theorem eq_zero_of_tapeSym_lmark {w : List Alpha} {i : ℕ}
    (hlm : tapeSym w i = TapeSym.lmark) : i = 0 := by
  by_contra hne
  exact tapeSym_ne_lmark (by omega) hlm

/-- **The master reachability invariant** of the simulator: the counters
encode the distances to an `M`-reachable simulated configuration, and the
phase tables record exactly the sweep progress. -/
def SimInv (M : MHC Alpha Gamma h c) (w : List Alpha) : (oneHead M).Config → Prop :=
  fun cfgN =>
    ∃ (pos : Fin h → ℕ) (cnt : Fin c → ℕ) (outM : List Gamma) (KM : ℕ),
      M.StepsN w M.initConfig outM (cfgN.1.1, pos, cnt) KM ∧
      (∀ a, pos a ≤ w.length + 1) ∧
      cfgN.2.1 0 ≤ w.length + 1 ∧
      cfgN.2.2 = encCnt pos cnt (cfgN.2.1 0) ∧
      (cfgN.1.2.mode = Mode.sweepR →
        cfgN.1.2.syms = symsAt w pos (cfgN.2.1 0) ∧
        cfgN.1.2.coin = coinAt pos (cfgN.2.1 0)) ∧
      (cfgN.1.2.mode = Mode.sweepL →
        cfgN.1.2.syms = symsAt w pos (w.length + 2) ∧
        cfgN.1.2.coin = coinAt pos (w.length + 2)) ∧
      (cfgN.1.2.mode = Mode.consult →
        cfgN.2.1 0 = 0 ∧
        cfgN.1.2.syms = symsAt w pos (w.length + 2) ∧
        cfgN.1.2.coin = coinAt pos (w.length + 2))

/-- The invariant holds initially. -/
theorem simInv_init (w : List Alpha) : SimInv M w (oneHead M).initConfig := by
  refine ⟨fun _ => 0, fun _ => 0, [], 0, Multihead.MHC.StepsN.refl _,
    fun a => Nat.zero_le _, Nat.zero_le _, ?_, ?_, ?_, ?_⟩
  · show (fun _ => 0) = encCnt (fun _ => 0) (fun _ => 0) 0
    rw [encCnt_init]
  · intro _
    constructor
    · show (fun _ => none) = symsAt w (fun _ => 0) 0
      rw [symsAt_zero]
    · show (fun _ _ => none) = coinAt (fun _ => 0) 0
      rw [coinAt_zero]
  · intro hcon
    have hcon' : Mode.sweepR = Mode.sweepL := hcon
    simp at hcon'
  · intro hcon
    have hcon' : Mode.sweepR = Mode.consult := hcon
    simp at hcon'

/-- **The invariant is preserved by every simulator step.** -/
theorem simInv_step (w : List Alpha) (q : (oneHead M).Q) (pos1 : Fin 1 → ℕ)
    (cnt1 : Fin (h + (h + c)) → ℕ) (q' : (oneHead M).Q) (mv : Fin 1 → HeadMove)
    (ops : Fin (h + (h + c)) → CounterOp) (u : List Gamma)
    (hP : SimInv M w (q, pos1, cnt1))
    (hη : (oneHead M).η q (fun a => tapeSym w (pos1 a))
      (fun a b => pos1 a == pos1 b) (fun j => cnt1 j == 0) = some (q', mv, ops, u)) :
    SimInv M w (q', fun a => (mv a).apply (pos1 a), fun j => (ops j).apply (cnt1 j)) := by
  obtain ⟨mq, mode, syms, coin⟩ := q
  obtain ⟨pos, cnt, outM, KM, hrunM, hposM, hi, hbank, hswR, hswL, hcons⟩ := hP
  have hi' : pos1 0 ≤ w.length + 1 := hi
  have hsymfun : (fun a : Fin 1 => tapeSym w (pos1 a))
      = fun _ => tapeSym w (pos1 0) := funext fun a => by rw [Fin.eq_zero a]
  rw [hsymfun, oneHead_η_apply] at hη
  have hbank' : cnt1 = encCnt pos cnt (pos1 0) := hbank
  rw [show (fun j => cnt1 j == 0) = zAt pos cnt (pos1 0) from by
    funext j; rw [hbank']; rfl] at hη
  rcases mode with _ | _ | _
  · -- sweepR
    obtain ⟨hsy, hco⟩ := hswR rfl
    have hsy' : syms = symsAt w pos (pos1 0) := hsy
    have hco' : coin = coinAt pos (pos1 0) := hco
    subst hsy'
    subst hco'
    by_cases hrm : tapeSym w (pos1 0) = TapeSym.rmark
    · -- turn at ⊣
      have hieq : pos1 0 = w.length + 1 := by
        have := le_of_tapeSym_rmark hrm
        omega
      rw [hrm, stepF_sweepR_rmark, ← hrm,
        recSyms_at w pos cnt (pos1 0), recCoin_at w pos cnt (pos1 0)] at hη
      injection hη with htuple
      injection htuple with hq hrest
      injection hrest with hmv hrest'
      injection hrest' with hops hu
      subst hq; subst hmv; subst hops; subst hu
      refine ⟨pos, cnt, outM, KM, hrunM, hposM, ?_, ?_, ?_, ?_, ?_⟩
      · show HeadMove.left.apply (pos1 0) ≤ w.length + 1
        simp only [HeadMove.apply_left]
        omega
      · show (fun j => (opsL (zAt pos cnt (pos1 0)) j).apply (cnt1 j))
          = encCnt pos cnt (HeadMove.left.apply (pos1 0))
        rw [show (fun j => (opsL (zAt pos cnt (pos1 0)) j).apply (cnt1 j))
            = fun j => (opsL (zAt pos cnt (pos1 0)) j).apply (encCnt pos cnt (pos1 0) j)
          from by funext j; rw [hbank']]
        rw [encCnt_opsL pos cnt (pos1 0) (by omega)]
        rfl
      · intro hcon
        exact absurd hcon (by simp)
      · intro _
        constructor
        · show symsAt w pos (pos1 0 + 1) = symsAt w pos (w.length + 2)
          rw [hieq]
        · show coinAt pos (pos1 0 + 1) = coinAt pos (w.length + 2)
          rw [hieq]
      · intro hcon
        exact absurd hcon (by simp)
    · -- keep sweeping right
      have hile : pos1 0 ≤ w.length := by
        by_contra hgt
        exact hrm (tapeSym_ge w (pos1 0) (by omega))
      rw [stepF_sweepR M mq _ _ _ hrm,
        recSyms_at w pos cnt (pos1 0), recCoin_at w pos cnt (pos1 0)] at hη
      injection hη with htuple
      injection htuple with hq hrest
      injection hrest with hmv hrest'
      injection hrest' with hops hu
      subst hq; subst hmv; subst hops; subst hu
      refine ⟨pos, cnt, outM, KM, hrunM, hposM, ?_, ?_, ?_, ?_, ?_⟩
      · show HeadMove.right.apply (pos1 0) ≤ w.length + 1
        simp only [HeadMove.apply_right]
        omega
      · show (fun j => (opsR (zAt pos cnt (pos1 0)) j).apply (cnt1 j))
          = encCnt pos cnt (HeadMove.right.apply (pos1 0))
        rw [show (fun j => (opsR (zAt pos cnt (pos1 0)) j).apply (cnt1 j))
            = fun j => (opsR (zAt pos cnt (pos1 0)) j).apply (encCnt pos cnt (pos1 0) j)
          from by funext j; rw [hbank']]
        rw [encCnt_opsR pos cnt (pos1 0)]
        rfl
      · intro _
        exact ⟨rfl, rfl⟩
      · intro hcon
        exact absurd hcon (by simp)
      · intro hcon
        exact absurd hcon (by simp)
  · -- sweepL
    obtain ⟨hsy, hco⟩ := hswL rfl
    have hsy' : syms = symsAt w pos (w.length + 2) := hsy
    have hco' : coin = coinAt pos (w.length + 2) := hco
    subst hsy'
    subst hco'
    by_cases hlm : tapeSym w (pos1 0) = TapeSym.lmark
    · -- switch to consult at ⊢
      have hieq : pos1 0 = 0 := eq_zero_of_tapeSym_lmark hlm
      rw [hlm, stepF_sweepL_lmark] at hη
      injection hη with htuple
      injection htuple with hq hrest
      injection hrest with hmv hrest'
      injection hrest' with hops hu
      subst hq; subst hmv; subst hops; subst hu
      refine ⟨pos, cnt, outM, KM, hrunM, hposM, ?_, ?_, ?_, ?_, ?_⟩
      · show HeadMove.stay.apply (pos1 0) ≤ w.length + 1
        simp only [HeadMove.apply_stay]
        exact hi'
      · show (fun j => CounterOp.keep.apply (cnt1 j))
          = encCnt pos cnt (HeadMove.stay.apply (pos1 0))
        rw [show (fun j => CounterOp.keep.apply (cnt1 j)) = cnt1 from by
          funext j; simp]
        exact hbank'
      · intro hcon
        exact absurd hcon (by simp)
      · intro hcon
        exact absurd hcon (by simp)
      · intro _
        exact ⟨hieq, rfl, rfl⟩
    · -- keep sweeping left
      rw [stepF_sweepL M mq _ _ _ hlm] at hη
      injection hη with htuple
      injection htuple with hq hrest
      injection hrest with hmv hrest'
      injection hrest' with hops hu
      subst hq; subst hmv; subst hops; subst hu
      have hipos : 1 ≤ pos1 0 := by
        by_contra h0
        exact hlm (by rw [show pos1 0 = 0 from by omega, tapeSym_zero])
      refine ⟨pos, cnt, outM, KM, hrunM, hposM, ?_, ?_, ?_, ?_, ?_⟩
      · show HeadMove.left.apply (pos1 0) ≤ w.length + 1
        simp only [HeadMove.apply_left]
        omega
      · show (fun j => (opsL (zAt pos cnt (pos1 0)) j).apply (cnt1 j))
          = encCnt pos cnt (HeadMove.left.apply (pos1 0))
        rw [show (fun j => (opsL (zAt pos cnt (pos1 0)) j).apply (cnt1 j))
            = fun j => (opsL (zAt pos cnt (pos1 0)) j).apply (encCnt pos cnt (pos1 0) j)
          from by funext j; rw [hbank']]
        rw [encCnt_opsL pos cnt (pos1 0) hipos]
        rfl
      · intro hcon
        exact absurd hcon (by simp)
      · intro _
        exact ⟨rfl, rfl⟩
      · intro hcon
        exact absurd hcon (by simp)
  · -- consult
    obtain ⟨hi0, hsy, hco⟩ := hcons rfl
    have hi0' : pos1 0 = 0 := hi0
    have hsy' : syms = symsAt w pos (w.length + 2) := hsy
    have hco' : coin = coinAt pos (w.length + 2) := hco
    subst hsy'
    subst hco'
    have hposlt : ∀ a, pos a < w.length + 2 := fun a => by have := hposM a; omega
    rw [stepF_consult] at hη
    rw [show (fun a => ((symsAt w pos (w.length + 2)) a).getD TapeSym.lmark)
        = fun a => tapeSym w (pos a) from funext fun a => symsAt_getD w pos hposlt a,
      show (fun a b => ((coinAt pos (w.length + 2)) a b).getD false)
        = fun a b => (pos a == pos b) from funext fun a => funext fun b =>
          coinAt_getD pos hposlt a b,
      show (fun j => zAt pos cnt (pos1 0) (cO j)) = fun j => (cnt j == 0) from
        funext fun j => zAt_O pos cnt (pos1 0) j] at hη
    obtain ⟨⟨mq', mvM, opsM', uM⟩, hηM, heq⟩ := Option.map_eq_some_iff.mp hη
    injection heq with hq hrest
    injection hrest with hmv hrest'
    injection hrest' with hops hu
    subst hq; subst hmv; subst hops; subst hu
    refine ⟨fun a => (mvM a).apply (pos a), fun j => (opsM' j).apply (cnt j),
      outM ++ (uM ++ []), KM + 1,
      hrunM.trans (Multihead.MHC.StepsN.head hηM (Multihead.MHC.StepsN.refl _)),
      mhc_pos_step_le hηM hposM, ?_, ?_, ?_, ?_, ?_⟩
    · show HeadMove.stay.apply (pos1 0) ≤ w.length + 1
      simp only [HeadMove.apply_stay]
      exact hi'
    · show (fun j => (opsM mvM opsM' j).apply (cnt1 j))
        = encCnt _ _ (HeadMove.stay.apply (pos1 0))
      rw [show (fun j => (opsM mvM opsM' j).apply (cnt1 j))
          = fun j => (opsM mvM opsM' j).apply (encCnt pos cnt (pos1 0) j)
        from by funext j; rw [hbank']]
      rw [hi0', encCnt_opsM]
      simp only [HeadMove.apply_stay]
    · intro _
      constructor
      · show (fun _ => none) = symsAt w (fun a => (mvM a).apply (pos a))
          (HeadMove.stay.apply (pos1 0))
        simp only [HeadMove.apply_stay, hi0']
        rw [symsAt_zero]
      · show (fun _ _ => none) = coinAt (fun a => (mvM a).apply (pos a))
          (HeadMove.stay.apply (pos1 0))
        simp only [HeadMove.apply_stay, hi0']
        rw [coinAt_zero]
    · intro hcon
      have hcon' : Mode.sweepR = Mode.sweepL := hcon
      simp at hcon'
    · intro hcon
      have hcon' : Mode.sweepR = Mode.consult := hcon
      simp at hcon'

/-- **The simulator is space-bounded**: with `SpaceBound M C`, every counter
of the single-head simulator stays `≤ (C+1)·(n+1)`. -/
theorem oneHead_spaceBound {C : ℕ} (hSB : Multihead.SpaceBound M C) :
    Multihead.SpaceBound (oneHead M) (C + 1) := by
  intro w out e N hrun t
  have hInv : SimInv M w e :=
    Multihead.MHC.stepsN_invariant
      (P := SimInv M w)
      (fun q pos1 cnt1 q' mv ops u hP hη => simInv_step w q pos1 cnt1 q' mv ops u hP hη)
      hrun (simInv_init w)
  obtain ⟨pos, cnt, outM, KM, hrunM, hposM, hi, hbank, -⟩ := hInv
  have hcntM : ∀ j, cnt j ≤ C * (w.length + 1) := fun j => hSB w outM _ KM hrunM j
  have hmul : w.length + 1 ≤ (C + 1) * (w.length + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hmul2 : C * (w.length + 1) ≤ (C + 1) * (w.length + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [show (e.2.2 t : ℕ) = encCnt pos cnt (e.2.1 0) t from by rw [hbank]]
  refine Fin.addCases (fun a => ?_) (fun t' => Fin.addCases (fun a => ?_) (fun j => ?_) t') t
  · show encCnt pos cnt (e.2.1 0) (cδ a) ≤ (C + 1) * (w.length + 1)
    rw [encCnt_δ]
    have := hposM a
    omega
  · show encCnt pos cnt (e.2.1 0) (cγ a) ≤ (C + 1) * (w.length + 1)
    rw [encCnt_γ]
    omega
  · show encCnt pos cnt (e.2.1 0) (cO j) ≤ (C + 1) * (w.length + 1)
    rw [encCnt_O]
    have := hcntM j
    omega

/-- **Head elimination, packaged**: every logspace map of the multihead model
is a logspace map of the single-head model. -/
theorem isLogspaceMH_oneHead {f : List Alpha → Option (List Gamma)}
    (hf : Multihead.IsLogspaceMH f) :
    ∃ (c' C' : ℕ) (N : MHC Alpha Gamma 1 c'), Multihead.SpaceBound N C' ∧
      ∀ w out, f w = some out ↔ N.Computes w out := by
  obtain ⟨h', c', C, M', hSB, hM⟩ := hf
  exact ⟨h' + (h' + c'), C + 1, oneHead M', oneHead_spaceBound hSB,
    fun w out => (hM w out).trans (oneHead_computes_iff w out).symm⟩

end Runs

end Machine

end MHCOneHead
