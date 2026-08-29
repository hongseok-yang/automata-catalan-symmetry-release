/-
# Binary counters: every single-head machine has a worktape equivalent

The second reduction behind the worktape-model restatement of the logspace
trio (`WRPWorktape.lean`): a single-head bounded-counter machine
`MHC Alpha Gamma 1 c` is simulated by a worktape transducer
`LogspaceTM.LogTM` whose input head moves exactly as the machine's single
head and whose `c` counters are held **in binary** on `c` tracks of the
worktape (work alphabet `Fin c → Option Bool`, one little-endian bit list
per track).

One simulated step is a cycle at worktape cell `0`: a `consult` step feeds
the machine's transition the physical input symbol and the **maintained
zero-flags**, emits its output and moves the input head; then, per counter,
a `dispatch`/`run`/`ret` excursion applies the counter operation in binary —
an increment walks the carry, a decrement walks the borrow (decrements of a
zero counter are skipped: `CounterOp.dec` is truncated), and the walk
doubles as the recomputation of the counter's zero-flag before returning to
cell `0`.

The correctness layer represents each track by a `List Bool`
(`TapeRep`, `bitsVal`, `incBits`, `decBits`) and proves the excursions by
structural induction on the lists.

Main results: `toTM M` (the machine), `toTM_computes_iff`,
`toTM_spaceBound` (`O(log n)` cells, from `SpaceBound M C`), and the
packaged `isLogspaceTM_of_isLogspaceMH` (composing with the head
elimination `MHCOneHead.isLogspaceMH_oneHead`).  Everything is
axiom-clean.
-/
import RequestProject.MHCOneHead
import RequestProject.LogspaceTM

namespace MHCToTM

open TwoDFT
open Multihead
open Logspace (CounterOp)
open LogspaceTM

/-! ## The bit layer -/

/-- The value of a little-endian bit list. -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsVal bs

/-- Binary increment (little-endian): flip the trailing `true`s, set the
first `false` (or append a fresh `true`). -/
def incBits : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: incBits bs

/-- Binary decrement (little-endian; correct on lists of positive value):
flip the trailing `false`s, clear the first `true`. -/
def decBits : List Bool → List Bool
  | [] => []
  | true :: bs => false :: bs
  | false :: bs => true :: decBits bs

@[simp] theorem bitsVal_nil : bitsVal [] = 0 := rfl

@[simp] theorem bitsVal_cons (b : Bool) (bs : List Bool) :
    bitsVal (b :: bs) = (if b then 1 else 0) + 2 * bitsVal bs := rfl

theorem bitsVal_incBits : ∀ bs : List Bool, bitsVal (incBits bs) = bitsVal bs + 1
  | [] => rfl
  | false :: bs => by simp [incBits]; omega
  | true :: bs => by
      simp [incBits, bitsVal_incBits bs]
      ring

theorem bitsVal_decBits : ∀ bs : List Bool, bitsVal bs ≠ 0 →
    bitsVal (decBits bs) = bitsVal bs - 1
  | [], h => absurd rfl h
  | true :: bs, _ => by simp [decBits]
  | false :: bs, h => by
      have hbs : bitsVal bs ≠ 0 := by
        simp at h
        omega
      simp [decBits, bitsVal_decBits bs hbs]
      omega

theorem length_decBits : ∀ bs : List Bool, (decBits bs).length = bs.length
  | [] => rfl
  | true :: bs => by simp [decBits]
  | false :: bs => by simp [decBits, length_decBits bs]

/-- A list has value `0` exactly when it has no `true` bit. -/
theorem bitsVal_eq_zero_iff : ∀ bs : List Bool, bitsVal bs = 0 ↔ ∀ b ∈ bs, b = false
  | [] => by simp
  | b :: bs => by
      simp only [bitsVal_cons, List.mem_cons]
      constructor
      · intro h
        have hb : b = false := by
          cases b
          · rfl
          · simp at h
        subst hb
        simp at h
        intro x hx
        rcases hx with rfl | hx
        · rfl
        · exact (bitsVal_eq_zero_iff bs).mp h x hx
      · intro h
        have hb : b = false := h b (Or.inl rfl)
        have hbs : bitsVal bs = 0 :=
          (bitsVal_eq_zero_iff bs).mpr fun x hx => h x (Or.inr hx)
        subst hb
        simp [hbs]

/-- Increment either keeps the length or extends an all-`true` list by one —
and in the latter case the old length is forced by the value. -/
theorem incBits_length_or : ∀ bs : List Bool,
    (incBits bs).length = bs.length ∨
    ((incBits bs).length = bs.length + 1 ∧ bitsVal bs + 1 = 2 ^ bs.length)
  | [] => Or.inr ⟨rfl, by simp⟩
  | false :: bs => Or.inl (by simp [incBits])
  | true :: bs => by
      rcases incBits_length_or bs with hl | ⟨hl, hv⟩
      · exact Or.inl (by simp [incBits, hl])
      · refine Or.inr ⟨by simp [incBits, hl], ?_⟩
        simp only [bitsVal_cons, List.length_cons, pow_succ]
        simp
        omega

/-! ## Control states -/

/-- The micro-state of a counter excursion: walking a carry, walking a
borrow, or scanning the remainder for a set bit. -/
inductive UpdSt | carry | borrow | scan (seen : Bool)
  deriving DecidableEq

instance : Fintype UpdSt :=
  ⟨⟨{UpdSt.carry, UpdSt.borrow, UpdSt.scan false, UpdSt.scan true}, by decide⟩,
    fun x => by cases x with
      | scan b => cases b <;> decide
      | _ => decide⟩

instance : Fintype CounterOp :=
  ⟨⟨{CounterOp.inc, CounterOp.dec, CounterOp.keep}, by decide⟩,
    fun x => by cases x <;> decide⟩

/-- The phases of a simulation cycle: `consult` the machine at cell `0`;
`dispatch` the next counter operation; `run` one counter excursion on one
track; `ret`urn to cell `0`. -/
inductive TPh (c : ℕ)
  | consult (zs : Fin c → Bool)
  | dispatch (jj : Fin (c + 1)) (ops : Fin c → CounterOp) (zs : Fin c → Bool)
  | run (j : Fin c) (ops : Fin c → CounterOp) (zs : Fin c → Bool) (st : UpdSt)
  | ret (jj : Fin (c + 1)) (ops : Fin c → CounterOp) (zs : Fin c → Bool)

instance {c : ℕ} : Fintype (TPh c) :=
  Fintype.ofEquiv ((Fin c → Bool) ⊕ (Fin (c+1) × (Fin c → CounterOp) × (Fin c → Bool))
      ⊕ (Fin c × (Fin c → CounterOp) × (Fin c → Bool) × UpdSt)
      ⊕ (Fin (c+1) × (Fin c → CounterOp) × (Fin c → Bool)))
    { toFun := fun x => match x with
        | Sum.inl zs => TPh.consult zs
        | Sum.inr (Sum.inl ⟨jj, ops, zs⟩) => TPh.dispatch jj ops zs
        | Sum.inr (Sum.inr (Sum.inl ⟨j, ops, zs, st⟩)) => TPh.run j ops zs st
        | Sum.inr (Sum.inr (Sum.inr ⟨jj, ops, zs⟩)) => TPh.ret jj ops zs
      invFun := fun p => match p with
        | TPh.consult zs => Sum.inl zs
        | TPh.dispatch jj ops zs => Sum.inr (Sum.inl ⟨jj, ops, zs⟩)
        | TPh.run j ops zs st => Sum.inr (Sum.inr (Sum.inl ⟨j, ops, zs, st⟩))
        | TPh.ret jj ops zs => Sum.inr (Sum.inr (Sum.inr ⟨jj, ops, zs⟩))
      left_inv := fun x => by
        rcases x with zs | ⟨jj, ops, zs⟩ | ⟨j, ops, zs, st⟩ | ⟨jj, ops, zs⟩ <;> rfl
      right_inv := fun p => by cases p <;> rfl }

/-! ## The machine -/

section Machine

variable {Alpha Gamma : Type} {c : ℕ}

/-- The simulator's transition function.  See the file header for the cycle
structure. -/
def stepG (M : MHC Alpha Gamma 1 c) (st : M.Q × TPh c) (s : TapeSym Alpha)
    (d : Fin c → Option Bool) (w0 : Bool) :
    Option ((M.Q × TPh c) × HeadMove × (Fin c → Option Bool) × HeadMove × List Gamma) :=
  match st.2 with
  | TPh.consult zs =>
      match M.η st.1 (fun _ => s) (fun _ _ => true) zs with
      | none => none
      | some (mq', mv, ops, u) =>
          some ((mq', TPh.dispatch 0 ops zs), mv 0, d, HeadMove.stay, u)
  | TPh.dispatch jj ops zs =>
      if hjj : (jj : ℕ) < c then
        match ops ⟨jj, hjj⟩ with
        | CounterOp.keep => some ((st.1, TPh.dispatch ⟨(jj : ℕ) + 1, by omega⟩ ops zs),
            HeadMove.stay, d, HeadMove.stay, [])
        | CounterOp.inc => some ((st.1, TPh.run ⟨jj, hjj⟩ ops zs UpdSt.carry),
            HeadMove.stay, d, HeadMove.stay, [])
        | CounterOp.dec =>
            if zs ⟨jj, hjj⟩ then
              some ((st.1, TPh.dispatch ⟨(jj : ℕ) + 1, by omega⟩ ops zs),
                HeadMove.stay, d, HeadMove.stay, [])
            else some ((st.1, TPh.run ⟨jj, hjj⟩ ops zs UpdSt.borrow),
              HeadMove.stay, d, HeadMove.stay, [])
      else some ((st.1, TPh.consult zs), HeadMove.stay, d, HeadMove.stay, [])
  | TPh.run j ops zs us =>
      match us with
      | UpdSt.carry =>
          match d j with
          | some true => some ((st.1, TPh.run j ops zs UpdSt.carry),
              HeadMove.stay, Function.update d j (some false), HeadMove.right, [])
          | _ => some ((st.1, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops
                (Function.update zs j false)),
              HeadMove.stay, Function.update d j (some true), HeadMove.left, [])
      | UpdSt.borrow =>
          match d j with
          | some false => some ((st.1, TPh.run j ops zs UpdSt.borrow),
              HeadMove.stay, Function.update d j (some true), HeadMove.right, [])
          | some true =>
              if w0 then some ((st.1, TPh.run j ops zs (UpdSt.scan false)),
                HeadMove.stay, Function.update d j (some false), HeadMove.right, [])
              else some ((st.1, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops
                    (Function.update zs j false)),
                HeadMove.stay, Function.update d j (some false), HeadMove.left, [])
          | none => some ((st.1, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops zs),
              HeadMove.stay, d, HeadMove.left, [])
      | UpdSt.scan seen =>
          match d j with
          | some b => some ((st.1, TPh.run j ops zs (UpdSt.scan (seen || b))),
              HeadMove.stay, d, HeadMove.right, [])
          | none => some ((st.1, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops
                (Function.update zs j (!seen))),
              HeadMove.stay, d, HeadMove.left, [])
  | TPh.ret jj ops zs =>
      if w0 then some ((st.1, TPh.dispatch jj ops zs), HeadMove.stay, d, HeadMove.stay, [])
      else some ((st.1, TPh.ret jj ops zs), HeadMove.stay, d, HeadMove.left, [])

/-- **The worktape simulator** of a single-head machine: the input head is
the machine's head; the counters live in binary on the tracks. -/
def toTM (M : MHC Alpha Gamma 1 c) : LogTM Alpha Gamma where
  Q := M.Q × TPh c
  fintypeQ := letI := M.fintypeQ; inferInstance
  Delta := Fin c → Option Bool
  fintypeDelta := inferInstance
  blank := fun _ => none
  q0 := (M.q0, TPh.consult (fun _ => true))
  F := fun st => M.F st.1 ∧ ∃ zs, st.2 = TPh.consult zs
  η := fun st s d w0 => stepG M st s d w0
  rmark_no_right := by
    intro q d z r hr
    obtain ⟨mq, ph⟩ := q
    rcases ph with zs | ⟨jj, ops, zs⟩ | ⟨j, ops, zs, us⟩ | ⟨jj, ops, zs⟩
    · -- consult: the input move is the machine's, and `M` obeys the discipline
      simp only [stepG] at hr
      rcases hη : M.η mq (fun _ => TapeSym.rmark) (fun _ _ => true) zs
          with _ | ⟨mq', mv, ops', u⟩
      · rw [hη] at hr
        exact absurd hr (by simp)
      · rw [hη] at hr
        have heq := Option.some.inj hr
        rw [← heq]
        exact M.rmark_no_right mq _ _ _ _ hη 0 rfl
    · -- dispatch: stays
      simp only [stepG] at hr
      by_cases hjj : (jj : ℕ) < c
      · rw [dif_pos hjj] at hr
        rcases hop : ops ⟨jj, hjj⟩ with _ | _ | _ <;> rw [hop] at hr
        · have heq := Option.some.inj hr
          rw [← heq]
          simp
        · by_cases hz : zs ⟨jj, hjj⟩
          · rw [if_pos hz] at hr
            have heq := Option.some.inj hr
            rw [← heq]
            simp
          · rw [if_neg hz] at hr
            have heq := Option.some.inj hr
            rw [← heq]
            simp
        · have heq := Option.some.inj hr
          rw [← heq]
          simp
      · rw [dif_neg hjj] at hr
        have heq := Option.some.inj hr
        rw [← heq]
        simp
    · -- run: stays
      simp only [stepG] at hr
      rcases us with _ | _ | seen
      · rcases hd : d j with _ | b
        · rw [hd] at hr
          have heq := Option.some.inj hr
          rw [← heq]
          simp
        · rcases b with _ | _ <;> rw [hd] at hr
          · have heq := Option.some.inj hr
            rw [← heq]
            simp
          · have heq := Option.some.inj hr
            rw [← heq]
            simp
      · rcases hd : d j with _ | b
        · rw [hd] at hr
          have heq := Option.some.inj hr
          rw [← heq]
          simp
        · rcases b with _ | _ <;> rw [hd] at hr
          · have heq := Option.some.inj hr
            rw [← heq]
            simp
          · by_cases hz : z = true
            · rw [if_pos hz] at hr
              have heq := Option.some.inj hr
              rw [← heq]
              simp
            · rw [if_neg hz] at hr
              have heq := Option.some.inj hr
              rw [← heq]
              simp
      · rcases hd : d j with _ | b <;> rw [hd] at hr
        · have heq := Option.some.inj hr
          rw [← heq]
          simp
        · have heq := Option.some.inj hr
          rw [← heq]
          simp
    · -- ret: stays
      simp only [stepG] at hr
      by_cases hz : z = true
      · rw [if_pos hz] at hr
        have heq := Option.some.inj hr
        rw [← heq]
        simp
      · rw [if_neg hz] at hr
        have heq := Option.some.inj hr
        rw [← heq]
        simp

end Machine

/-! ## Generic `LogTM` run helpers -/

/-- Two runs of the same length from the same configuration coincide. -/
theorem _root_.LogspaceTM.LogTM.stepsN_same_len {Alpha Gamma : Type*}
    {M : LogTM Alpha Gamma} {w : List Alpha} :
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
          injection hrest with hmvI hrest'
          injection hrest' with hd hrest''
          injection hrest'' with hmvW hu
          subst hq; subst hmvI; subst hd; subst hmvW; subst hu
          obtain ⟨ho, he⟩ := ih rest'
          exact ⟨by rw [ho], he⟩

/-! ## Space-bounded runs

`BStepsN M w B cfg out e N` strengthens `StepsN` with the guarantee that
**every** configuration along the run --- the endpoint of every prefix ---
keeps its work head within cell `B`.  By determinism the prefix endpoints
are exactly the configurations the run visits, so this is the honest
"the run stays within `B` work cells" statement, and it composes along
`trans`. -/

/-- A run all of whose configurations keep the work head `≤ B`. -/
def _root_.LogspaceTM.LogTM.BStepsN {Alpha Gamma : Type*} (M : LogTM Alpha Gamma)
    (w : List Alpha) (B : ℕ) (cfg : M.Config) (out : List Gamma) (e : M.Config)
    (N : ℕ) : Prop :=
  M.StepsN w cfg out e N ∧
    ∀ K out' cfg', K ≤ N → M.StepsN w cfg out' cfg' K → cfg'.2.2.1 ≤ B

theorem _root_.LogspaceTM.LogTM.BStepsN.refl {Alpha Gamma : Type*}
    {M : LogTM Alpha Gamma} {w : List Alpha} {B : ℕ} {cfg : M.Config}
    (h : cfg.2.2.1 ≤ B) : LogspaceTM.LogTM.BStepsN M w B cfg [] cfg 0 := by
  refine ⟨LogspaceTM.LogTM.StepsN.refl _, ?_⟩
  intro K out' cfg' hK hrun
  have hK0 : K = 0 := by omega
  subst hK0
  cases hrun
  exact h

/-- The endpoint of a bounded run is bounded. -/
theorem _root_.LogspaceTM.LogTM.BStepsN.end_le {Alpha Gamma : Type*}
    {M : LogTM Alpha Gamma} {w : List Alpha} {B : ℕ} {cfg e : M.Config}
    {out : List Gamma} {N : ℕ}
    (h : LogspaceTM.LogTM.BStepsN M w B cfg out e N) : e.2.2.1 ≤ B :=
  h.2 N out e (le_refl N) h.1

/-- One bounded step in front of a bounded run. -/
theorem _root_.LogspaceTM.LogTM.BStepsN.head'' {Alpha Gamma : Type*}
    {M : LogTM Alpha Gamma} {w : List Alpha} {B : ℕ} {q : M.Q} {i wh : ℕ}
    {T : ℕ → M.Delta} {q' : M.Q} {mvI : HeadMove} {dw : M.Delta} {mvW : HeadMove}
    {u out : List Gamma} {e : M.Config} {N : ℕ} {i2 wh2 : ℕ} {T2 : ℕ → M.Delta}
    (hη : M.η q (tapeSym w i) (T wh) (wh == 0) = some (q', mvI, dw, mvW, u))
    (hi : mvI.apply i = i2) (hwh : mvW.apply wh = wh2)
    (hT : Function.update T wh dw = T2) (hB : wh ≤ B)
    (rest : LogspaceTM.LogTM.BStepsN M w B (q', i2, wh2, T2) out e N) :
    LogspaceTM.LogTM.BStepsN M w B (q, i, wh, T) (u ++ out) e (N + 1) := by
  subst hi
  subst hwh
  subst hT
  refine ⟨LogspaceTM.LogTM.StepsN.head hη rest.1, ?_⟩
  intro K out' cfg' hK hrun
  cases hrun with
  | refl => exact hB
  | head hη' rest' =>
      rw [hη] at hη'
      injection hη' with htuple
      injection htuple with hq hrest
      injection hrest with hmvI hrest'
      injection hrest' with hd hrest''
      injection hrest'' with hmvW hu
      subst hq; subst hmvI; subst hd; subst hmvW; subst hu
      exact rest.2 _ _ _ (by omega) rest'

/-- Bounded runs compose. -/
theorem _root_.LogspaceTM.LogTM.BStepsN.trans {Alpha Gamma : Type*}
    {M : LogTM Alpha Gamma} {w : List Alpha} {B : ℕ}
    {c₁ c₂ c₃ : M.Config} {o₁ o₂ : List Gamma} {N₁ N₂ : ℕ}
    (h₁ : LogspaceTM.LogTM.BStepsN M w B c₁ o₁ c₂ N₁)
    (h₂ : LogspaceTM.LogTM.BStepsN M w B c₂ o₂ c₃ N₂) :
    LogspaceTM.LogTM.BStepsN M w B c₁ (o₁ ++ o₂) c₃ (N₁ + N₂) := by
  refine ⟨h₁.1.trans h₂.1, ?_⟩
  intro K out' cfg' hK hrun
  rcases (by omega : K ≤ N₁ ∨ N₁ < K) with hle | hgt
  · exact h₁.2 _ _ _ hle hrun
  · obtain ⟨mid, p₁, p₂, -, hpre, hsuf⟩ :=
      LogspaceTM.LogTM.stepsN_split hrun N₁ (by omega)
    obtain ⟨-, hmid⟩ := LogspaceTM.LogTM.stepsN_same_len h₁.1 hpre
    rw [← hmid] at hsuf
    exact h₂.2 _ _ _ (by omega) hsuf

/-- No run outlives a halting run. -/
theorem _root_.LogspaceTM.LogTM.stepsN_le_of_halted {Alpha Gamma : Type*}
    {M : LogTM Alpha Gamma} {w : List Alpha} {cfg e₁ e₂ : M.Config}
    {o₁ o₂ : List Gamma} {N₁ N₂ : ℕ}
    (h₁ : M.StepsN w cfg o₁ e₁ N₁) (hh : M.Halted w e₁)
    (h₂ : M.StepsN w cfg o₂ e₂ N₂) : N₂ ≤ N₁ := by
  by_contra hlt
  obtain ⟨mid, p₁, p₂, -, hpre, hsuf⟩ := LogspaceTM.LogTM.stepsN_split h₂ N₁ (by omega)
  obtain ⟨-, hmid⟩ := LogspaceTM.LogTM.stepsN_same_len h₁ hpre
  obtain ⟨k, hk⟩ : ∃ k, N₂ - N₁ = k + 1 := ⟨N₂ - N₁ - 1, by omega⟩
  rw [hk] at hsuf
  obtain ⟨mq, mi, mwh, mT⟩ := mid
  rw [hmid] at hh
  cases hsuf with
  | head hη rest =>
      exact LogspaceTM.LogTM.not_halted_of_step hη hh

section Runs

variable {Alpha Gamma : Type} {c : ℕ} {M : MHC Alpha Gamma 1 c}

/-- The simulator's transition, unfolded (definitional). -/
theorem toTM_η (st : M.Q × TPh c) (s : TapeSym Alpha) (d : Fin c → Option Bool)
    (w0 : Bool) : (toTM M).η st s d w0 = stepG M st s d w0 := rfl

/-! ## Step equations -/

theorem stepG_consult_eq (mq : M.Q) (zs : Fin c → Bool) (s : TapeSym Alpha)
    (d : Fin c → Option Bool) (w0 : Bool) :
    stepG M (mq, TPh.consult zs) s d w0
      = (M.η mq (fun _ => s) (fun _ _ => true) zs).map
          (fun r => ((r.1, TPh.dispatch 0 r.2.2.1 zs), r.2.1 0, d,
            HeadMove.stay, r.2.2.2)) := by
  simp only [stepG]
  rcases M.η mq (fun _ => s) (fun _ _ => true) zs with _ | ⟨mq', mv, ops, u⟩ <;> rfl

theorem stepG_dispatch_done (mq : M.Q) (jj : Fin (c + 1)) (ops : Fin c → CounterOp)
    (zs : Fin c → Bool) (s : TapeSym Alpha) (d : Fin c → Option Bool) (w0 : Bool)
    (hjj : ¬ ((jj : ℕ) < c)) :
    stepG M (mq, TPh.dispatch jj ops zs) s d w0
      = some ((mq, TPh.consult zs), HeadMove.stay, d, HeadMove.stay, []) := by
  simp only [stepG]
  rw [dif_neg hjj]

theorem stepG_dispatch_lt (mq : M.Q) (jj : Fin (c + 1)) (ops : Fin c → CounterOp)
    (zs : Fin c → Bool) (s : TapeSym Alpha) (d : Fin c → Option Bool) (w0 : Bool)
    (hjj : (jj : ℕ) < c) :
    stepG M (mq, TPh.dispatch jj ops zs) s d w0
      = match ops ⟨jj, hjj⟩ with
        | CounterOp.keep => some ((mq, TPh.dispatch ⟨(jj : ℕ) + 1, by omega⟩ ops zs),
            HeadMove.stay, d, HeadMove.stay, [])
        | CounterOp.inc => some ((mq, TPh.run ⟨jj, hjj⟩ ops zs UpdSt.carry),
            HeadMove.stay, d, HeadMove.stay, [])
        | CounterOp.dec =>
            if zs ⟨jj, hjj⟩ then
              some ((mq, TPh.dispatch ⟨(jj : ℕ) + 1, by omega⟩ ops zs),
                HeadMove.stay, d, HeadMove.stay, [])
            else some ((mq, TPh.run ⟨jj, hjj⟩ ops zs UpdSt.borrow),
              HeadMove.stay, d, HeadMove.stay, []) := by
  simp only [stepG]
  rw [dif_pos hjj]

theorem stepG_run_carry (mq : M.Q) (j : Fin c) (ops : Fin c → CounterOp)
    (zs : Fin c → Bool) (s : TapeSym Alpha) (d : Fin c → Option Bool) (w0 : Bool) :
    stepG M (mq, TPh.run j ops zs UpdSt.carry) s d w0
      = match d j with
        | some true => some ((mq, TPh.run j ops zs UpdSt.carry),
            HeadMove.stay, Function.update d j (some false), HeadMove.right, [])
        | _ => some ((mq, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops
              (Function.update zs j false)),
            HeadMove.stay, Function.update d j (some true), HeadMove.left, []) := by
  simp only [stepG]

theorem stepG_run_borrow (mq : M.Q) (j : Fin c) (ops : Fin c → CounterOp)
    (zs : Fin c → Bool) (s : TapeSym Alpha) (d : Fin c → Option Bool) (w0 : Bool) :
    stepG M (mq, TPh.run j ops zs UpdSt.borrow) s d w0
      = match d j with
        | some false => some ((mq, TPh.run j ops zs UpdSt.borrow),
            HeadMove.stay, Function.update d j (some true), HeadMove.right, [])
        | some true =>
            if w0 then some ((mq, TPh.run j ops zs (UpdSt.scan false)),
              HeadMove.stay, Function.update d j (some false), HeadMove.right, [])
            else some ((mq, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops
                  (Function.update zs j false)),
              HeadMove.stay, Function.update d j (some false), HeadMove.left, [])
        | none => some ((mq, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops zs),
            HeadMove.stay, d, HeadMove.left, []) := by
  simp only [stepG]

theorem stepG_run_scan (mq : M.Q) (j : Fin c) (ops : Fin c → CounterOp)
    (zs : Fin c → Bool) (seen : Bool) (s : TapeSym Alpha) (d : Fin c → Option Bool)
    (w0 : Bool) :
    stepG M (mq, TPh.run j ops zs (UpdSt.scan seen)) s d w0
      = match d j with
        | some b => some ((mq, TPh.run j ops zs (UpdSt.scan (seen || b))),
            HeadMove.stay, d, HeadMove.right, [])
        | none => some ((mq, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops
              (Function.update zs j (!seen))),
            HeadMove.stay, d, HeadMove.left, []) := by
  simp only [stepG]

theorem stepG_ret (mq : M.Q) (jj : Fin (c + 1)) (ops : Fin c → CounterOp)
    (zs : Fin c → Bool) (s : TapeSym Alpha) (d : Fin c → Option Bool) (w0 : Bool) :
    stepG M (mq, TPh.ret jj ops zs) s d w0
      = if w0 then some ((mq, TPh.dispatch jj ops zs), HeadMove.stay, d,
          HeadMove.stay, [])
        else some ((mq, TPh.ret jj ops zs), HeadMove.stay, d, HeadMove.left, []) := by
  simp only [stepG]

end Runs

section Excursions

variable {Alpha Gamma : Type} {c : ℕ} {M : MHC Alpha Gamma 1 c}

/-! ## Tape-write bookkeeping -/

/-- Writing value `v` on track `j` of cell `off`. -/
def wr (T : ℕ → Fin c → Option Bool) (off : ℕ) (j : Fin c) (v : Option Bool) :
    ℕ → Fin c → Option Bool :=
  Function.update T off (Function.update (T off) j v)

@[simp] theorem wr_here (T : ℕ → Fin c → Option Bool) (off : ℕ) (j : Fin c)
    (v : Option Bool) : wr T off j v off j = v := by
  simp [wr]

theorem wr_ne_cell (T : ℕ → Fin c → Option Bool) (off : ℕ) (j : Fin c)
    (v : Option Bool) {k : ℕ} (hk : k ≠ off) : wr T off j v k = T k := by
  simp [wr, Function.update_of_ne hk]

theorem wr_ne_track (T : ℕ → Fin c → Option Bool) (off : ℕ) (j : Fin c)
    (v : Option Bool) (k : ℕ) {j' : Fin c} (hj : j' ≠ j) :
    wr T off j v k j' = T k j' := by
  by_cases hk : k = off
  · subst hk
    simp [wr, Function.update_of_ne hj]
  · rw [wr_ne_cell T off j v hk]

/-! ## The return walk -/

/-- From any cell, the return phase walks to `⊢` (cell `0`) and dispatches,
leaving the tape unchanged. -/
theorem ret_run (mq : M.Q) (jj : Fin (c + 1)) (ops : Fin c → CounterOp)
    (zs : Fin c → Bool) (w : List Alpha) (i : ℕ) (T : ℕ → Fin c → Option Bool)
    (B : ℕ) :
    ∀ wh, wh ≤ B → LogspaceTM.LogTM.BStepsN (toTM M) w B
      ((mq, TPh.ret jj ops zs), i, wh, T) []
      ((mq, TPh.dispatch jj ops zs), i, 0, T) (wh + 1) := by
  intro wh
  induction wh with
  | zero =>
      intro hB
      have hη : (toTM M).η (mq, TPh.ret jj ops zs) (tapeSym w i) (T 0) ((0 : ℕ) == 0)
          = some ((mq, TPh.dispatch jj ops zs), HeadMove.stay, T 0, HeadMove.stay, []) := by
        rw [toTM_η, stepG_ret]
        rfl
      refine LogspaceTM.LogTM.BStepsN.head'' hη rfl rfl ?_ hB
        (LogspaceTM.LogTM.BStepsN.refl (Nat.zero_le B))
      exact Function.update_eq_self 0 T
  | succ wh ih =>
      intro hB
      have hη : (toTM M).η (mq, TPh.ret jj ops zs) (tapeSym w i) (T (wh + 1))
          ((wh + 1 : ℕ) == 0)
          = some ((mq, TPh.ret jj ops zs), HeadMove.stay, T (wh + 1), HeadMove.left, []) := by
        rw [toTM_η, stepG_ret]
        rfl
      refine LogspaceTM.LogTM.BStepsN.head'' hη rfl (by simp) ?_ hB
        (ih (by omega))
      exact Function.update_eq_self (wh + 1) T

/-! ## The carry walk -/

/-- **The increment excursion**: from cell `off` holding `bs` on track `j`,
walk the carry, resolve, and enter the return phase with the track holding
`incBits bs` (all other cells and tracks untouched) and the zero-flag
cleared. -/
theorem carry_run (mq : M.Q) (j : Fin c) (ops : Fin c → CounterOp)
    (zs : Fin c → Bool) (w : List Alpha) (i : ℕ) (B : ℕ) :
    ∀ (bs : List Bool) (off : ℕ) (T : ℕ → Fin c → Option Bool),
      (∀ k, T (off + k) j = bs[k]?) → off + bs.length ≤ B →
      ∃ (T' : ℕ → Fin c → Option Bool) (wh' N : ℕ),
        LogspaceTM.LogTM.BStepsN (toTM M) w B
          ((mq, TPh.run j ops zs UpdSt.carry), i, off, T) []
          ((mq, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops (Function.update zs j false)),
            i, wh', T') N ∧
        (∀ k, T' (off + k) j = (incBits bs)[k]?) ∧
        (∀ k j', j' ≠ j → T' k j' = T k j') ∧
        (∀ k, k < off → T' k j = T k j) := by
  intro bs
  induction bs with
  | nil =>
      intro off T hrep hB
      have hd : T off j = none := by
        have := hrep 0
        simpa using this
      have hη : (toTM M).η (mq, TPh.run j ops zs UpdSt.carry) (tapeSym w i)
          (T off) ((off : ℕ) == 0)
          = some ((mq, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops
              (Function.update zs j false)),
            HeadMove.stay, Function.update (T off) j (some true), HeadMove.left, []) := by
        rw [toTM_η, stepG_run_carry, hd]
      refine ⟨wr T off j (some true), off - 1, 1,
        LogspaceTM.LogTM.BStepsN.head'' hη rfl (by simp) rfl (by omega)
          (LogspaceTM.LogTM.BStepsN.refl (show off - 1 ≤ B by omega)), ?_, ?_, ?_⟩
      · intro k
        cases k with
        | zero => simp [incBits]
        | succ k =>
            rw [wr_ne_cell T off j (some true) (by omega)]
            have := hrep (k + 1)
            simpa [incBits] using this
      · intro k j' hj
        exact wr_ne_track T off j (some true) k hj
      · intro k hk
        rw [wr_ne_cell T off j (some true) (by omega)]
  | cons b bs ih =>
      intro off T hrep hB
      have hd : T off j = some b := by
        have := hrep 0
        simpa using this
      cases b with
      | false =>
          have hη : (toTM M).η (mq, TPh.run j ops zs UpdSt.carry) (tapeSym w i)
              (T off) ((off : ℕ) == 0)
              = some ((mq, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops
                  (Function.update zs j false)),
                HeadMove.stay, Function.update (T off) j (some true),
                HeadMove.left, []) := by
            rw [toTM_η, stepG_run_carry, hd]
          refine ⟨wr T off j (some true), off - 1, 1,
            LogspaceTM.LogTM.BStepsN.head'' hη rfl (by simp) rfl (by omega)
              (LogspaceTM.LogTM.BStepsN.refl (show off - 1 ≤ B by omega)), ?_, ?_, ?_⟩
          · intro k
            cases k with
            | zero => simp [incBits]
            | succ k =>
                rw [wr_ne_cell T off j (some true) (by omega)]
                have := hrep (k + 1)
                simpa [incBits] using this
          · intro k j' hj
            exact wr_ne_track T off j (some true) k hj
          · intro k hk
            rw [wr_ne_cell T off j (some true) (by omega)]
      | true =>
          have hη : (toTM M).η (mq, TPh.run j ops zs UpdSt.carry) (tapeSym w i)
              (T off) ((off : ℕ) == 0)
              = some ((mq, TPh.run j ops zs UpdSt.carry),
                HeadMove.stay, Function.update (T off) j (some false),
                HeadMove.right, []) := by
            rw [toTM_η, stepG_run_carry, hd]
          have hrep1 : ∀ k, (wr T off j (some false)) (off + 1 + k) j = bs[k]? := by
            intro k
            rw [wr_ne_cell T off j (some false) (by omega)]
            have := hrep (k + 1)
            rw [show off + (k + 1) = off + 1 + k from by omega] at this
            simpa using this
          obtain ⟨T', wh', N, hrun, hj', hoth, hlow⟩ :=
            ih (off + 1) (wr T off j (some false)) hrep1 (by simp at hB; omega)
          refine ⟨T', wh', N + 1,
            LogspaceTM.LogTM.BStepsN.head'' hη rfl (by simp) rfl (by omega) hrun,
            ?_, ?_, ?_⟩
          · intro k
            cases k with
            | zero =>
                rw [show off + 0 = off from by omega,
                  hlow off (by omega), wr_here]
                simp [incBits]
            | succ k =>
                have := hj' k
                rw [show off + 1 + k = off + (k + 1) from by omega] at this
                rw [this]
                simp [incBits]
          · intro k j' hj
            rw [hoth k j' hj, wr_ne_track T off j (some false) k hj]
          · intro k hk
            rw [hlow k (by omega), wr_ne_cell T off j (some false) (by omega)]

end Excursions

section Excursions2

variable {Alpha Gamma : Type} {c : ℕ} {M : MHC Alpha Gamma 1 c}

/-- **The scan excursion**: walk the remainder of the track, accumulate
whether any bit is set, and enter the return phase with the zero-flag set
accordingly.  The tape is untouched. -/
theorem scan_run (mq : M.Q) (j : Fin c) (ops : Fin c → CounterOp)
    (zs : Fin c → Bool) (w : List Alpha) (i : ℕ) (B : ℕ) :
    ∀ (bs : List Bool) (off : ℕ) (T : ℕ → Fin c → Option Bool) (seen : Bool),
      (∀ k, T (off + k) j = bs[k]?) → off + bs.length ≤ B →
      ∃ (wh' N : ℕ),
        LogspaceTM.LogTM.BStepsN (toTM M) w B
          ((mq, TPh.run j ops zs (UpdSt.scan seen)), i, off, T) []
          ((mq, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops
            (Function.update zs j (!(seen || bs.any id)))), i, wh', T) N := by
  intro bs
  induction bs with
  | nil =>
      intro off T seen hrep hB
      have hd : T off j = none := by
        have := hrep 0
        simpa using this
      have hη : (toTM M).η (mq, TPh.run j ops zs (UpdSt.scan seen)) (tapeSym w i)
          (T off) ((off : ℕ) == 0)
          = some ((mq, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops
              (Function.update zs j (!seen))),
            HeadMove.stay, T off, HeadMove.left, []) := by
        rw [toTM_η, stepG_run_scan, hd]
      refine ⟨off - 1, 1, ?_⟩
      have hgoal : Function.update zs j (!(seen || List.any [] id))
          = Function.update zs j (!seen) := by
        simp
      rw [hgoal]
      exact LogspaceTM.LogTM.BStepsN.head'' hη rfl (by simp)
        (Function.update_eq_self off T) (by omega)
        (LogspaceTM.LogTM.BStepsN.refl (show off - 1 ≤ B by omega))
  | cons b bs ih =>
      intro off T seen hrep hB
      have hd : T off j = some b := by
        have := hrep 0
        simpa using this
      have hη : (toTM M).η (mq, TPh.run j ops zs (UpdSt.scan seen)) (tapeSym w i)
          (T off) ((off : ℕ) == 0)
          = some ((mq, TPh.run j ops zs (UpdSt.scan (seen || b))),
            HeadMove.stay, T off, HeadMove.right, []) := by
        rw [toTM_η, stepG_run_scan, hd]
      have hrep1 : ∀ k, T (off + 1 + k) j = bs[k]? := by
        intro k
        have := hrep (k + 1)
        rw [show off + (k + 1) = off + 1 + k from by omega] at this
        simpa using this
      obtain ⟨wh', N, hrun⟩ := ih (off + 1) T (seen || b) hrep1 (by simp at hB; omega)
      refine ⟨wh', N + 1, ?_⟩
      have hgoal : Function.update zs j (!(seen || b || bs.any id))
          = Function.update zs j (!(seen || List.any (b :: bs) id)) := by
        simp [Bool.or_assoc]
      rw [← hgoal]
      exact LogspaceTM.LogTM.BStepsN.head'' hη rfl (by simp)
        (Function.update_eq_self off T) (by omega) hrun

/-- **The borrow excursion away from `⊢`** (`off ≥ 1`): walk the borrow to
the first set bit, clear it, and enter the return phase with the track
holding `decBits bs` and the zero-flag cleared. -/
theorem borrow_run (mq : M.Q) (j : Fin c) (ops : Fin c → CounterOp)
    (zs : Fin c → Bool) (w : List Alpha) (i : ℕ) (B : ℕ) :
    ∀ (bs : List Bool) (off : ℕ) (T : ℕ → Fin c → Option Bool),
      1 ≤ off → bs.any id = true →
      (∀ k, T (off + k) j = bs[k]?) → off + bs.length ≤ B →
      ∃ (T' : ℕ → Fin c → Option Bool) (wh' N : ℕ),
        LogspaceTM.LogTM.BStepsN (toTM M) w B
          ((mq, TPh.run j ops zs UpdSt.borrow), i, off, T) []
          ((mq, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops (Function.update zs j false)),
            i, wh', T') N ∧
        (∀ k, T' (off + k) j = (decBits bs)[k]?) ∧
        (∀ k j', j' ≠ j → T' k j' = T k j') ∧
        (∀ k, k < off → T' k j = T k j) := by
  intro bs
  induction bs with
  | nil =>
      intro off T hoff hne hrep _
      simp at hne
  | cons b bs ih =>
      intro off T hoff hne hrep hB
      have hd : T off j = some b := by
        have := hrep 0
        simpa using this
      have hw0 : ((off : ℕ) == 0) = false := by
        simp
        omega
      cases b with
      | true =>
          have hη : (toTM M).η (mq, TPh.run j ops zs UpdSt.borrow) (tapeSym w i)
              (T off) ((off : ℕ) == 0)
              = some ((mq, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops
                  (Function.update zs j false)),
                HeadMove.stay, Function.update (T off) j (some false),
                HeadMove.left, []) := by
            rw [toTM_η, stepG_run_borrow, hd, hw0]
            rfl
          refine ⟨wr T off j (some false), off - 1, 1,
            LogspaceTM.LogTM.BStepsN.head'' hη rfl (by simp) rfl (by omega)
              (LogspaceTM.LogTM.BStepsN.refl (show off - 1 ≤ B by omega)), ?_, ?_, ?_⟩
          · intro k
            cases k with
            | zero => simp [decBits]
            | succ k =>
                rw [wr_ne_cell T off j (some false) (by omega)]
                have := hrep (k + 1)
                simpa [decBits] using this
          · intro k j' hj
            exact wr_ne_track T off j (some false) k hj
          · intro k hk
            rw [wr_ne_cell T off j (some false) (by omega)]
      | false =>
          have hne' : bs.any id = true := by
            simpa using hne
          have hη : (toTM M).η (mq, TPh.run j ops zs UpdSt.borrow) (tapeSym w i)
              (T off) ((off : ℕ) == 0)
              = some ((mq, TPh.run j ops zs UpdSt.borrow),
                HeadMove.stay, Function.update (T off) j (some true),
                HeadMove.right, []) := by
            rw [toTM_η, stepG_run_borrow, hd]
          have hrep1 : ∀ k, (wr T off j (some true)) (off + 1 + k) j = bs[k]? := by
            intro k
            rw [wr_ne_cell T off j (some true) (by omega)]
            have := hrep (k + 1)
            rw [show off + (k + 1) = off + 1 + k from by omega] at this
            simpa using this
          obtain ⟨T', wh', N, hrun, hj', hoth, hlow⟩ :=
            ih (off + 1) (wr T off j (some true)) (by omega) hne' hrep1
              (by simp at hB; omega)
          refine ⟨T', wh', N + 1,
            LogspaceTM.LogTM.BStepsN.head'' hη rfl (by simp) rfl (by omega) hrun,
            ?_, ?_, ?_⟩
          · intro k
            cases k with
            | zero =>
                rw [show off + 0 = off from by omega,
                  hlow off (by omega), wr_here]
                simp [decBits]
            | succ k =>
                have := hj' k
                rw [show off + 1 + k = off + (k + 1) from by omega] at this
                rw [this]
                simp [decBits]
          · intro k j' hj
            rw [hoth k j' hj, wr_ne_track T off j (some true) k hj]
          · intro k hk
            rw [hlow k (by omega), wr_ne_cell T off j (some true) (by omega)]

/-- **The borrow excursion from `⊢`** (the machine's actual entry point):
resolve the borrow, recompute the zero-flag of the result, and enter the
return phase with the track holding `decBits bs`. -/
theorem borrow_run_start (mq : M.Q) (j : Fin c) (ops : Fin c → CounterOp)
    (zs : Fin c → Bool) (w : List Alpha) (i : ℕ) (B : ℕ) (bs : List Bool)
    (T : ℕ → Fin c → Option Bool) (hne : bs.any id = true)
    (hrep : ∀ k, T k j = bs[k]?) (hB : bs.length ≤ B) :
    ∃ (T' : ℕ → Fin c → Option Bool) (wh' N : ℕ) (zflag : Bool),
      LogspaceTM.LogTM.BStepsN (toTM M) w B
        ((mq, TPh.run j ops zs UpdSt.borrow), i, 0, T) []
        ((mq, TPh.ret ⟨(j : ℕ) + 1, by omega⟩ ops (Function.update zs j zflag)),
          i, wh', T') N ∧
      (∀ k, T' k j = (decBits bs)[k]?) ∧
      (∀ k j', j' ≠ j → T' k j' = T k j') ∧
      (zflag = true ↔ bitsVal (decBits bs) = 0) := by
  have hrep0 : ∀ k, T (0 + k) j = bs[k]? := by
    intro k
    rw [show 0 + k = k from by omega]
    exact hrep k
  rcases bs with _ | ⟨b, bs⟩
  · simp at hne
  · have hd : T 0 j = some b := by
      have := hrep 0
      simpa using this
    cases b with
    | true =>
        -- resolve at `⊢`: clear the bit and scan the tail
        have hη : (toTM M).η (mq, TPh.run j ops zs UpdSt.borrow) (tapeSym w i)
            (T 0) ((0 : ℕ) == 0)
            = some ((mq, TPh.run j ops zs (UpdSt.scan false)),
              HeadMove.stay, Function.update (T 0) j (some false),
              HeadMove.right, []) := by
          rw [toTM_η, stepG_run_borrow, hd]
          rfl
        have hrep1 : ∀ k, (wr T 0 j (some false)) (1 + k) j = bs[k]? := by
          intro k
          rw [wr_ne_cell T 0 j (some false) (by omega),
            show 1 + k = k + 1 from by omega]
          have := hrep (k + 1)
          simpa using this
        obtain ⟨wh', N, hrun⟩ :=
          scan_run mq j ops zs w i B bs 1 (wr T 0 j (some false)) false hrep1
            (by simp at hB; omega)
        refine ⟨wr T 0 j (some false), wh', N + 1, !(false || bs.any id),
          LogspaceTM.LogTM.BStepsN.head'' hη rfl (by simp) rfl (Nat.zero_le B) hrun,
          ?_, ?_, ?_⟩
        · intro k
          cases k with
          | zero => simp [decBits]
          | succ k =>
              rw [wr_ne_cell T 0 j (some false) (by omega)]
              have := hrep (k + 1)
              simpa [decBits] using this
        · intro k j' hj
          exact wr_ne_track T 0 j (some false) k hj
        · simp only [decBits, Bool.false_or]
          constructor
          · intro h
            have hall : ∀ x ∈ bs, x = false := by
              intro x hx
              have := List.any_eq_false.mp (by
                cases hany : bs.any id
                · rfl
                · rw [hany] at h
                  simp at h) x hx
              simpa using this
            simp only [bitsVal_cons]
            have := (bitsVal_eq_zero_iff bs).mpr hall
            simp [this]
          · intro h
            have hz : bitsVal bs = 0 := by
              simp [bitsVal_cons] at h
              omega
            have := (bitsVal_eq_zero_iff bs).mp hz
            cases hany : bs.any id
            · rfl
            · obtain ⟨x, hx, hxt⟩ := List.any_eq_true.mp hany
              have := this x hx
              simp [this] at hxt
    | false =>
        -- pass the bit and borrow further right
        have hne' : bs.any id = true := by
          simpa using hne
        have hη : (toTM M).η (mq, TPh.run j ops zs UpdSt.borrow) (tapeSym w i)
            (T 0) ((0 : ℕ) == 0)
            = some ((mq, TPh.run j ops zs UpdSt.borrow),
              HeadMove.stay, Function.update (T 0) j (some true),
              HeadMove.right, []) := by
          rw [toTM_η, stepG_run_borrow, hd]
        have hrep1 : ∀ k, (wr T 0 j (some true)) (1 + k) j = bs[k]? := by
          intro k
          rw [wr_ne_cell T 0 j (some true) (by omega),
            show 1 + k = k + 1 from by omega]
          have := hrep (k + 1)
          simpa using this
        obtain ⟨T', wh', N, hrun, hj', hoth, hlow⟩ :=
          borrow_run mq j ops zs w i B bs 1 (wr T 0 j (some true)) (by omega) hne' hrep1
            (by simp at hB; omega)
        refine ⟨T', wh', N + 1, false,
          LogspaceTM.LogTM.BStepsN.head'' hη rfl (by simp) rfl (Nat.zero_le B) hrun,
          ?_, ?_, ?_⟩
        · intro k
          cases k with
          | zero =>
              rw [hlow 0 (by omega), wr_here]
              simp [decBits]
          | succ k =>
              have := hj' k
              rw [show 1 + k = k + 1 from by omega] at this
              rw [this]
              simp [decBits]
        · intro k j' hj
          rw [hoth k j' hj, wr_ne_track T 0 j (some true) k hj]
        · constructor
          · intro h
            exact absurd h (by simp)
          · intro h
            simp [decBits, bitsVal_cons] at h

end Excursions2

section Chain

variable {Alpha Gamma : Type} {c : ℕ} {M : MHC Alpha Gamma 1 c}

/-- Bool-equation form of a zero-flag characterisation. -/
theorem flag_eq_of_iff {a : Bool} {n : ℕ} (h : a = true ↔ n = 0) : a = (n == 0) := by
  cases a
  · cases hn : (n == 0)
    · rfl
    · have : n = 0 := by simpa using hn
      simp [this] at h
  · have : n = 0 := h.mp rfl
    simp [this]

/-- A list of nonzero value has a set bit. -/
theorem any_of_bitsVal_ne {bs : List Bool} (h : bitsVal bs ≠ 0) : bs.any id = true := by
  cases hany : bs.any id
  · exfalso
    apply h
    refine (bitsVal_eq_zero_iff bs).mpr ?_
    intro x hx
    have := List.any_eq_false.mp hany x hx
    simpa using this
  · rfl

/-- **The dispatch chain**: process the counter operations for the tracks
`≥ jj`, ending at `consult` with the updated tracks and correct flags. -/
theorem dispatch_chain (mq : M.Q) (ops : Fin c → CounterOp) (w : List Alpha) (i : ℕ)
    (B : ℕ) :
    ∀ (fuel : ℕ) (jj : Fin (c + 1)), c - (jj : ℕ) = fuel →
    ∀ (bss : Fin c → List Bool) (zs : Fin c → Bool) (T : ℕ → Fin c → Option Bool),
      (∀ j k, T k j = (bss j)[k]?) →
      (∀ j, zs j = (bitsVal (bss j) == 0)) →
      (∀ j : Fin c, (jj : ℕ) ≤ (j : ℕ) → (bss j).length ≤ B) →
      ∃ (T' : ℕ → Fin c → Option Bool) (bss' : Fin c → List Bool)
        (zs' : Fin c → Bool) (N : ℕ),
        LogspaceTM.LogTM.BStepsN (toTM M) w B
          ((mq, TPh.dispatch jj ops zs), i, 0, T) []
          ((mq, TPh.consult zs'), i, 0, T') N ∧
        (∀ j k, T' k j = (bss' j)[k]?) ∧
        (∀ j, bitsVal (bss' j) = if (jj : ℕ) ≤ (j : ℕ)
          then (ops j).apply (bitsVal (bss j)) else bitsVal (bss j)) ∧
        (∀ j, (bss' j).length ≤ (bss j).length ∨
          2 ^ ((bss' j).length - 1) ≤ bitsVal (bss' j)) ∧
        (∀ j, zs' j = (bitsVal (bss' j) == 0)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro jj hfuel bss zs T hrep hzs hL
      have hjj : ¬ ((jj : ℕ) < c) := by omega
      have hη : (toTM M).η (mq, TPh.dispatch jj ops zs) (tapeSym w i)
          (T 0) ((0 : ℕ) == 0)
          = some ((mq, TPh.consult zs), HeadMove.stay, T 0, HeadMove.stay, []) := by
        rw [toTM_η, stepG_dispatch_done _ _ _ _ _ _ _ hjj]
      refine ⟨T, bss, zs, 1,
        LogspaceTM.LogTM.BStepsN.head'' hη rfl rfl (Function.update_eq_self 0 T)
          (Nat.zero_le B) (LogspaceTM.LogTM.BStepsN.refl (Nat.zero_le B)),
        hrep, ?_, ?_, hzs⟩
      · intro j
        rw [if_neg (by omega)]
      · intro j
        exact Or.inl (le_refl _)
  | succ fuel ih =>
      intro jj hfuel bss zs T hrep hzs hL
      have hjj : (jj : ℕ) < c := by omega
      set j : Fin c := ⟨jj, hjj⟩ with hjdef
      have hjj1 : ((⟨(jj : ℕ) + 1, by omega⟩ : Fin (c + 1)) : ℕ) = (jj : ℕ) + 1 := rfl
      rcases hop : ops j with _ | _ | _
      · -- inc: excursion
        have hη : (toTM M).η (mq, TPh.dispatch jj ops zs) (tapeSym w i)
            (T 0) ((0 : ℕ) == 0)
            = some ((mq, TPh.run j ops zs UpdSt.carry), HeadMove.stay, T 0,
              HeadMove.stay, []) := by
          rw [toTM_η, stepG_dispatch_lt _ _ _ _ _ _ _ hjj, hop]
        have hrepj : ∀ k, T (0 + k) j = (bss j)[k]? := by
          intro k
          rw [show 0 + k = k from by omega]
          exact hrep j k
        have hLj : (bss j).length ≤ B := hL j (le_refl _)
        obtain ⟨T₁, wh₁, N₁, hrun₁, htrk, hoth, -⟩ :=
          carry_run mq j ops zs w i B (bss j) 0 T hrepj (by omega)
        have hret := ret_run (M := M) mq ⟨(j : ℕ) + 1, by omega⟩ ops
          (Function.update zs j false) w i T₁ B wh₁ hrun₁.end_le
        set bss₁ : Fin c → List Bool := Function.update bss j (incBits (bss j))
          with hbss₁
        have hrep₁ : ∀ j' k, T₁ k j' = (bss₁ j')[k]? := by
          intro j' k
          by_cases hj' : j' = j
          · subst hj'
            have := htrk k
            rw [show 0 + k = k from by omega] at this
            rw [this, hbss₁, Function.update_self]
          · rw [hoth k j' hj', hbss₁, Function.update_of_ne hj']
            exact hrep j' k
        have hzs₁ : ∀ j', (Function.update zs j false) j'
            = (bitsVal (bss₁ j') == 0) := by
          intro j'
          by_cases hj' : j' = j
          · subst hj'
            rw [Function.update_self, hbss₁, Function.update_self,
              bitsVal_incBits]
            simp
          · rw [Function.update_of_ne hj', hbss₁, Function.update_of_ne hj']
            exact hzs j'
        have hL₁ : ∀ j' : Fin c, (jj : ℕ) + 1 ≤ (j' : ℕ) → (bss₁ j').length ≤ B := by
          intro j' hj'
          have hne : j' ≠ j := by
            intro hcon
            have hvv : (j' : ℕ) = (jj : ℕ) := by rw [hcon, hjdef]
            omega
          rw [hbss₁, Function.update_of_ne hne]
          exact hL j' (by omega)
        obtain ⟨T', bss', zs', N', hrun', hrep', hval', hlen', hzs'⟩ :=
          ih ⟨(jj : ℕ) + 1, by omega⟩ (by show c - ((jj : ℕ) + 1) = fuel; omega) bss₁
            (Function.update zs j false) T₁ hrep₁ hzs₁ hL₁
        refine ⟨T', bss', zs', (N₁ + (wh₁ + 1 + N')) + 1, ?_, hrep', ?_, ?_, hzs'⟩
        · have hcomp := hrun₁.trans (hret.trans hrun')
          have h1 := LogspaceTM.LogTM.BStepsN.head'' hη rfl rfl
            (Function.update_eq_self 0 T) (Nat.zero_le B) hcomp
          simpa using h1
        · intro j'
          have := hval' j'
          by_cases hj' : j' = j
          · subst hj'
            rw [this, if_neg (by show ¬ ((jj : ℕ) + 1 ≤ (jj : ℕ)); omega), hbss₁,
              Function.update_self, bitsVal_incBits,
              if_pos (by show (jj : ℕ) ≤ (jj : ℕ); omega), hop]
            rfl
          · rw [this, hbss₁, Function.update_of_ne hj']
            have hne : (j' : ℕ) ≠ (jj : ℕ) := fun hcon =>
              hj' (Fin.ext (by simpa using hcon))
            by_cases hle : (jj : ℕ) ≤ (j' : ℕ)
            · rw [if_pos (by show (jj : ℕ) + 1 ≤ (j' : ℕ); omega), if_pos hle]
            · rw [if_neg (by show ¬ ((jj : ℕ) + 1 ≤ (j' : ℕ)); omega), if_neg hle]
        · intro j'
          have hrec := hlen' j'
          by_cases hj' : j' = j
          · subst hj'
            rcases hrec with hrec | hrec
            · rw [hbss₁, Function.update_self] at hrec
              rcases incBits_length_or (bss j) with hl | ⟨hl, hv⟩
              · exact Or.inl (by omega)
              · right
                have hval'' := hval' j
                rw [if_neg (by show ¬ ((jj : ℕ) + 1 ≤ (jj : ℕ)); omega), hbss₁,
                  Function.update_self, bitsVal_incBits] at hval''
                rw [hl] at hrec
                rw [hval'', hv]
                exact Nat.pow_le_pow_right (by omega) (by omega)
            · exact Or.inr hrec
          · rw [hbss₁, Function.update_of_ne hj'] at hrec
            exact hrec
      · -- dec: guarded or excursion
        by_cases hz : zs j
        · -- zero counter: skip (truncated decrement)
          have hη : (toTM M).η (mq, TPh.dispatch jj ops zs) (tapeSym w i)
              (T 0) ((0 : ℕ) == 0)
              = some ((mq, TPh.dispatch ⟨(jj : ℕ) + 1, by omega⟩ ops zs),
                HeadMove.stay, T 0, HeadMove.stay, []) := by
            rw [toTM_η, stepG_dispatch_lt _ _ _ _ _ _ _ hjj, hop, if_pos hz]
          have hv0 : bitsVal (bss j) = 0 := by
            have := hzs j
            rw [hz] at this
            simpa using this.symm
          obtain ⟨T', bss', zs', N', hrun', hrep', hval', hlen', hzs'⟩ :=
            ih ⟨(jj : ℕ) + 1, by omega⟩ (by show c - ((jj : ℕ) + 1) = fuel; omega) bss zs T hrep hzs
              (fun j' hj' => hL j'
                (by have h : (jj : ℕ) + 1 ≤ (j' : ℕ) := hj'; omega))
          refine ⟨T', bss', zs', N' + 1, ?_, hrep', ?_, ?_, hzs'⟩
          · have h1 := LogspaceTM.LogTM.BStepsN.head'' hη rfl rfl
              (Function.update_eq_self 0 T) (Nat.zero_le B) hrun'
            simpa using h1
          · intro j'
            have := hval' j'
            by_cases hj' : j' = j
            · subst hj'
              rw [this, if_neg (by show ¬ ((jj : ℕ) + 1 ≤ (jj : ℕ)); omega),
              if_pos (by show (jj : ℕ) ≤ (jj : ℕ); omega), hop, hv0]
              rfl
            · have hne : (j' : ℕ) ≠ (jj : ℕ) := fun hcon =>
                hj' (Fin.ext (by simpa using hcon))
              rw [this]
              by_cases hle : (jj : ℕ) ≤ (j' : ℕ)
              · rw [if_pos (by show (jj : ℕ) + 1 ≤ (j' : ℕ); omega), if_pos hle]
              · rw [if_neg (by show ¬ ((jj : ℕ) + 1 ≤ (j' : ℕ)); omega), if_neg hle]
          · exact hlen'
        · -- nonzero counter: borrow excursion
          have hη : (toTM M).η (mq, TPh.dispatch jj ops zs) (tapeSym w i)
              (T 0) ((0 : ℕ) == 0)
              = some ((mq, TPh.run j ops zs UpdSt.borrow), HeadMove.stay, T 0,
                HeadMove.stay, []) := by
            rw [toTM_η, stepG_dispatch_lt _ _ _ _ _ _ _ hjj, hop,
              if_neg (by simpa using hz)]
          have hvne : bitsVal (bss j) ≠ 0 := by
            intro hcon
            apply hz
            rw [hzs j, hcon]
            rfl
          obtain ⟨T₁, wh₁, N₁, zflag, hrun₁, htrk, hoth, hzf⟩ :=
            borrow_run_start mq j ops zs w i B (bss j) T
              (any_of_bitsVal_ne hvne) (hrep j) (hL j (le_refl _))
          have hret := ret_run (M := M) mq ⟨(j : ℕ) + 1, by omega⟩ ops
            (Function.update zs j zflag) w i T₁ B wh₁ hrun₁.end_le
          set bss₁ : Fin c → List Bool := Function.update bss j (decBits (bss j))
            with hbss₁
          have hrep₁ : ∀ j' k, T₁ k j' = (bss₁ j')[k]? := by
            intro j' k
            by_cases hj' : j' = j
            · subst hj'
              rw [htrk k, hbss₁, Function.update_self]
            · rw [hoth k j' hj', hbss₁, Function.update_of_ne hj']
              exact hrep j' k
          have hzs₁ : ∀ j', (Function.update zs j zflag) j'
              = (bitsVal (bss₁ j') == 0) := by
            intro j'
            by_cases hj' : j' = j
            · subst hj'
              rw [Function.update_self, hbss₁, Function.update_self]
              exact flag_eq_of_iff hzf
            · rw [Function.update_of_ne hj', hbss₁, Function.update_of_ne hj']
              exact hzs j'
          have hL₁ : ∀ j' : Fin c, (jj : ℕ) + 1 ≤ (j' : ℕ) → (bss₁ j').length ≤ B := by
            intro j' hj'
            have hne : j' ≠ j := by
              intro hcon
              have hvv : (j' : ℕ) = (jj : ℕ) := by rw [hcon, hjdef]
              omega
            rw [hbss₁, Function.update_of_ne hne]
            exact hL j' (by omega)
          obtain ⟨T', bss', zs', N', hrun', hrep', hval', hlen', hzs'⟩ :=
            ih ⟨(jj : ℕ) + 1, by omega⟩ (by show c - ((jj : ℕ) + 1) = fuel; omega) bss₁
              (Function.update zs j zflag) T₁ hrep₁ hzs₁ hL₁
          refine ⟨T', bss', zs', (N₁ + (wh₁ + 1 + N')) + 1, ?_, hrep', ?_, ?_, hzs'⟩
          · have hcomp := hrun₁.trans (hret.trans hrun')
            have h1 := LogspaceTM.LogTM.BStepsN.head'' hη rfl rfl
              (Function.update_eq_self 0 T) (Nat.zero_le B) hcomp
            simpa using h1
          · intro j'
            have := hval' j'
            by_cases hj' : j' = j
            · subst hj'
              rw [this, if_neg (by show ¬ ((jj : ℕ) + 1 ≤ (jj : ℕ)); omega), hbss₁,
                Function.update_self, bitsVal_decBits _ hvne,
                if_pos (by show (jj : ℕ) ≤ (jj : ℕ); omega), hop]
              rfl
            · rw [this, hbss₁, Function.update_of_ne hj']
              have hne : (j' : ℕ) ≠ (jj : ℕ) := fun hcon =>
                hj' (Fin.ext (by simpa using hcon))
              by_cases hle : (jj : ℕ) ≤ (j' : ℕ)
              · rw [if_pos (by show (jj : ℕ) + 1 ≤ (j' : ℕ); omega), if_pos hle]
              · rw [if_neg (by show ¬ ((jj : ℕ) + 1 ≤ (j' : ℕ)); omega), if_neg hle]
          · intro j'
            have hrec := hlen' j'
            by_cases hj' : j' = j
            · subst hj'
              rcases hrec with hrec | hrec
              · rw [hbss₁, Function.update_self, length_decBits] at hrec
                exact Or.inl hrec
              · exact Or.inr hrec
            · rw [hbss₁, Function.update_of_ne hj'] at hrec
              exact hrec
      · -- keep: skip
        have hη : (toTM M).η (mq, TPh.dispatch jj ops zs) (tapeSym w i)
            (T 0) ((0 : ℕ) == 0)
            = some ((mq, TPh.dispatch ⟨(jj : ℕ) + 1, by omega⟩ ops zs),
              HeadMove.stay, T 0, HeadMove.stay, []) := by
          rw [toTM_η, stepG_dispatch_lt _ _ _ _ _ _ _ hjj, hop]
        obtain ⟨T', bss', zs', N', hrun', hrep', hval', hlen', hzs'⟩ :=
          ih ⟨(jj : ℕ) + 1, by omega⟩ (by show c - ((jj : ℕ) + 1) = fuel; omega) bss zs T hrep hzs
            (fun j' hj' => hL j'
              (by have h : (jj : ℕ) + 1 ≤ (j' : ℕ) := hj'; omega))
        refine ⟨T', bss', zs', N' + 1, ?_, hrep', ?_, ?_, hzs'⟩
        · have h1 := LogspaceTM.LogTM.BStepsN.head'' hη rfl rfl
            (Function.update_eq_self 0 T) (Nat.zero_le B) hrun'
          simpa using h1
        · intro j'
          have := hval' j'
          by_cases hj' : j' = j
          · subst hj'
            rw [this, if_neg (by show ¬ ((jj : ℕ) + 1 ≤ (jj : ℕ)); omega),
            if_pos (by show (jj : ℕ) ≤ (jj : ℕ); omega), hop]
            rfl
          · have hne : (j' : ℕ) ≠ (jj : ℕ) := fun hcon =>
              hj' (Fin.ext (by simpa using hcon))
            rw [this]
            by_cases hle : (jj : ℕ) ≤ (j' : ℕ)
            · rw [if_pos (by show (jj : ℕ) + 1 ≤ (j' : ℕ); omega), if_pos hle]
            · rw [if_neg (by show ¬ ((jj : ℕ) + 1 ≤ (j' : ℕ)); omega), if_neg hle]
        · exact hlen'

end Chain

section Cycle

variable {Alpha Gamma : Type} {c : ℕ} {M : MHC Alpha Gamma 1 c}

/-- **One full cycle** on a defined transition. -/
theorem tm_cycle (mq : M.Q) (cnt : Fin c → ℕ) (bss : Fin c → List Bool)
    (w : List Alpha) (i : ℕ) (T : ℕ → Fin c → Option Bool) (B : ℕ)
    (hrep : ∀ j k, T k j = (bss j)[k]?) (hval : ∀ j, bitsVal (bss j) = cnt j)
    (hL : ∀ j, (bss j).length ≤ B)
    {mq' : M.Q} {mv : Fin 1 → HeadMove} {ops : Fin c → CounterOp} {u : List Gamma}
    (hη : M.η mq (fun _ => tapeSym w i) (fun _ _ => true) (fun j => (cnt j == 0))
      = some (mq', mv, ops, u)) :
    ∃ (T' : ℕ → Fin c → Option Bool) (bss' : Fin c → List Bool) (N : ℕ), 1 ≤ N ∧
      LogspaceTM.LogTM.BStepsN (toTM M) w B
        ((mq, TPh.consult (fun j => (cnt j == 0))), i, 0, T) u
        ((mq', TPh.consult (fun j => ((ops j).apply (cnt j) == 0))),
          (mv 0).apply i, 0, T') N ∧
      (∀ j k, T' k j = (bss' j)[k]?) ∧
      (∀ j, bitsVal (bss' j) = (ops j).apply (cnt j)) ∧
      (∀ j, (bss' j).length ≤ (bss j).length ∨
        2 ^ ((bss' j).length - 1) ≤ bitsVal (bss' j)) := by
  have hη1 : (toTM M).η (mq, TPh.consult (fun j => (cnt j == 0))) (tapeSym w i)
      (T 0) ((0 : ℕ) == 0)
      = some ((mq', TPh.dispatch 0 ops (fun j => (cnt j == 0))), mv 0, T 0,
        HeadMove.stay, u) := by
    rw [toTM_η, stepG_consult_eq, hη]
    rfl
  have hzs0 : ∀ j, (fun j => (cnt j == 0)) j = (bitsVal (bss j) == 0) := by
    intro j
    rw [hval j]
  obtain ⟨T', bss', zs', N', hrun', hrep', hval', hlen', hzs'⟩ :=
    dispatch_chain (M := M) mq' ops w ((mv 0).apply i) B c 0 (by simp) bss
      (fun j => (cnt j == 0)) T hrep hzs0 (fun j _ => hL j)
  have hzsfun : zs' = fun j => ((ops j).apply (cnt j) == 0) := by
    funext j
    rw [hzs' j, hval' j, if_pos (by simp), hval j]
  rw [hzsfun] at hrun'
  refine ⟨T', bss', N' + 1, by omega, ?_, hrep', ?_, ?_⟩
  · have h1 := LogspaceTM.LogTM.BStepsN.head'' hη1 rfl rfl
      (Function.update_eq_self 0 T) (Nat.zero_le B) hrun'
    simpa using h1
  · intro j
    rw [hval' j, if_pos (by simp), hval j]
  · exact hlen'

/-- **The halting cycle**: an undefined transition halts the simulator at the
consult configuration, whose acceptance is the machine's. -/
theorem tm_cycle_halt (mq : M.Q) (cnt : Fin c → ℕ) (w : List Alpha) (i : ℕ)
    (T : ℕ → Fin c → Option Bool)
    (hη : M.η mq (fun _ => tapeSym w i) (fun _ _ => true) (fun j => (cnt j == 0))
      = none) :
    (toTM M).Halted w ((mq, TPh.consult (fun j => (cnt j == 0))), i, 0, T) ∧
    ((toTM M).F (mq, TPh.consult (fun j => (cnt j == 0))) ↔ M.F mq) := by
  constructor
  · show (toTM M).η (mq, TPh.consult (fun j => (cnt j == 0))) (tapeSym w i)
      (T 0) ((0 : ℕ) == 0) = none
    rw [toTM_η, stepG_consult_eq, hη]
    rfl
  · show (M.F mq ∧ ∃ zs, TPh.consult (fun j => (cnt j == 0)) = TPh.consult zs) ↔ M.F mq
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, _, rfl⟩

/-- **The forward simulation** over a whole run of the single-head machine. -/
theorem simulate (w : List Alpha) :
    ∀ {cfgM eM : M.Config} {out : List Gamma} {K : ℕ},
      M.StepsN w cfgM out eM K →
      ∀ (bss : Fin c → List Bool) (T : ℕ → Fin c → Option Bool),
        (∀ j k, T k j = (bss j)[k]?) → (∀ j, bitsVal (bss j) = cfgM.2.2 j) →
      ∃ (T' : ℕ → Fin c → Option Bool) (bss' : Fin c → List Bool) (N : ℕ), K ≤ N ∧
        (toTM M).StepsN w
          ((cfgM.1, TPh.consult (fun j => (cfgM.2.2 j == 0))), cfgM.2.1 0, 0, T) out
          ((eM.1, TPh.consult (fun j => (eM.2.2 j == 0))), eM.2.1 0, 0, T') N ∧
        (∀ j k, T' k j = (bss' j)[k]?) ∧ (∀ j, bitsVal (bss' j) = eM.2.2 j) := by
  intro cfgM eM out K hrun
  induction hrun with
  | refl cfg =>
      intro bss T hrep hval
      exact ⟨T, bss, 0, le_refl 0, LogspaceTM.LogTM.StepsN.refl _, hrep, hval⟩
  | @head q pos cnt q' mv ops u out' e' N' hη rest ih =>
      intro bss T hrep hval
      have hη' : M.η q (fun _ => tapeSym w (pos 0)) (fun _ _ => true)
          (fun j => (cnt j == 0)) = some (q', mv, ops, u) := by
        have h1 : (fun a : Fin 1 => tapeSym w (pos a))
            = fun _ => tapeSym w (pos 0) := funext fun a => by rw [Fin.eq_zero a]
        have h2 : (fun a b : Fin 1 => (pos a == pos b))
            = fun _ _ => true := by
          funext a b
          rw [Fin.eq_zero a, Fin.eq_zero b]
          simp
        rw [← h1, ← h2]
        exact hη
      obtain ⟨T₁, bss₁, N₁, hN₁, hrun₁, hrep₁, hval₁, -⟩ :=
        tm_cycle q cnt bss w (pos 0) T (Finset.univ.sup fun j => (bss j).length)
          hrep hval (fun j => Finset.le_sup (f := fun j => (bss j).length)
            (Finset.mem_univ j)) hη'
      obtain ⟨T', bss', N₂, hle₂, hrun₂, hrep', hval'⟩ := ih bss₁ T₁ hrep₁ hval₁
      exact ⟨T', bss', N₁ + N₂, by omega, hrun₁.1.trans hrun₂, hrep', hval'⟩

/-- **The simulator computes the same partial map.** -/
theorem toTM_computes_iff (M : MHC Alpha Gamma 1 c) (w : List Alpha)
    (out : List Gamma) :
    (toTM M).Computes w out ↔ M.Computes w out := by
  have hinit : ((toTM M).initConfig : (toTM M).Config)
      = ((M.q0, TPh.consult (fun j => (((fun _ : Fin c => 0) j : ℕ) == 0))),
        (0 : ℕ), (0 : ℕ), fun _ => fun _ => none) := rfl
  have hrep0 : ∀ (j : Fin c) k,
      (fun (_ : ℕ) => (fun (_ : Fin c) => (none : Option Bool))) k j
        = ((fun _ : Fin c => ([] : List Bool)) j)[k]? := by
    intro j k
    simp
  have hval0 : ∀ j : Fin c, bitsVal ((fun _ : Fin c => ([] : List Bool)) j)
      = (M.initConfig.2.2 : Fin c → ℕ) j := fun _ => rfl
  constructor
  · -- backward: reconstruct by determinism
    rintro ⟨eN, ⟨N₀, hrunN⟩, hhN, hFN⟩
    obtain ⟨outM, eM, K', hle, hrunM, hcase⟩ :=
      Multihead.MHC.exists_run_upto (M := M) w (N₀ + 1)
    obtain ⟨mq₂, pos₂, cnt₂⟩ := eM
    obtain ⟨T₁, bss₁, N₁, hge, hrunSim, hrep₁, hval₁⟩ :=
      simulate w hrunM (fun _ => []) (fun _ => fun _ => none) hrep0 hval0
    have hrunSim' : (toTM M).StepsN w (toTM M).initConfig outM
        ((mq₂, TPh.consult (fun j => (cnt₂ j == 0))), pos₂ 0, 0, T₁) N₁ := by
      rw [hinit]
      exact hrunSim
    rcases hcase with hKeq | hhaltM
    · exfalso
      have hle₂ := LogspaceTM.LogTM.stepsN_le_of_halted hrunN hhN hrunSim'
      omega
    · have hη' : M.η mq₂ (fun _ => tapeSym w (pos₂ 0)) (fun _ _ => true)
          (fun j => (cnt₂ j == 0)) = none := by
        have h1 : (fun a : Fin 1 => tapeSym w (pos₂ a))
            = fun _ => tapeSym w (pos₂ 0) := funext fun a => by rw [Fin.eq_zero a]
        have h2 : (fun a b : Fin 1 => (pos₂ a == pos₂ b))
            = fun _ _ => true := by
          funext a b
          rw [Fin.eq_zero a, Fin.eq_zero b]
          simp
        rw [← h1, ← h2]
        exact hhaltM
      obtain ⟨hhalt', hFiff⟩ := tm_cycle_halt mq₂ cnt₂ w (pos₂ 0) T₁ hη'
      obtain ⟨ho, he, -⟩ :=
        LogspaceTM.LogTM.stepsN_unique hrunN hhN hrunSim' hhalt'
      have hFM : M.F mq₂ := hFiff.mp (by rw [he] at hFN; exact hFN)
      rw [ho]
      exact ⟨(mq₂, pos₂, cnt₂), ⟨K', hrunM⟩, hhaltM, hFM⟩
  · -- forward: simulate the halting run
    rintro ⟨⟨mq₂, pos₂, cnt₂⟩, ⟨K, hrunM⟩, hhaltM, hFM⟩
    obtain ⟨T₁, bss₁, N₁, hge, hrunSim, hrep₁, hval₁⟩ :=
      simulate w hrunM (fun _ => []) (fun _ => fun _ => none) hrep0 hval0
    have hη' : M.η mq₂ (fun _ => tapeSym w (pos₂ 0)) (fun _ _ => true)
        (fun j => (cnt₂ j == 0)) = none := by
      have h1 : (fun a : Fin 1 => tapeSym w (pos₂ a))
          = fun _ => tapeSym w (pos₂ 0) := funext fun a => by rw [Fin.eq_zero a]
      have h2 : (fun a b : Fin 1 => (pos₂ a == pos₂ b))
          = fun _ _ => true := by
        funext a b
        rw [Fin.eq_zero a, Fin.eq_zero b]
        simp
      rw [← h1, ← h2]
      exact hhaltM
    obtain ⟨hhalt', hFiff⟩ := tm_cycle_halt mq₂ cnt₂ w (pos₂ 0) T₁ hη'
    refine ⟨((mq₂, TPh.consult (fun j => (cnt₂ j == 0))), pos₂ 0, 0, T₁),
      ⟨N₁, ?_⟩, hhalt', hFiff.mpr hFM⟩
    rw [hinit]
    exact hrunSim

end Cycle

section Space

variable {Alpha Gamma : Type} {c : ℕ} {M : MHC Alpha Gamma 1 c}

/-- **The bounded simulation**: when the machine's counters obey the linear
bound `C·(n+1)` along every reachable configuration, the whole simulated run
keeps its work head within `log₂(C·(n+1)) + 1` cells and the track lists
never grow past that length.  (The length re-tightening per cycle uses the
`tm_cycle` dichotomy: a track either kept its length or grew to a length
whose power of two is at most its — reachable, hence bounded — value.) -/
theorem simulate_bounded {C : ℕ} (hC : Multihead.SpaceBound M C) (w : List Alpha) :
    ∀ {cfgM eM : M.Config} {out : List Gamma} {K : ℕ},
      M.StepsN w cfgM out eM K →
      ∀ {o₀ : List Gamma} {K₀ : ℕ}, M.StepsN w M.initConfig o₀ cfgM K₀ →
      ∀ (bss : Fin c → List Bool) (T : ℕ → Fin c → Option Bool),
        (∀ j k, T k j = (bss j)[k]?) → (∀ j, bitsVal (bss j) = cfgM.2.2 j) →
        (∀ j, (bss j).length ≤ Nat.log 2 (C * (w.length + 1)) + 1) →
      ∃ (T' : ℕ → Fin c → Option Bool) (bss' : Fin c → List Bool) (N : ℕ), K ≤ N ∧
        LogspaceTM.LogTM.BStepsN (toTM M) w (Nat.log 2 (C * (w.length + 1)) + 1)
          ((cfgM.1, TPh.consult (fun j => (cfgM.2.2 j == 0))), cfgM.2.1 0, 0, T) out
          ((eM.1, TPh.consult (fun j => (eM.2.2 j == 0))), eM.2.1 0, 0, T') N ∧
        (∀ j k, T' k j = (bss' j)[k]?) ∧ (∀ j, bitsVal (bss' j) = eM.2.2 j) ∧
        (∀ j, (bss' j).length ≤ Nat.log 2 (C * (w.length + 1)) + 1) := by
  intro cfgM eM out K hrun
  induction hrun with
  | refl cfg =>
      intro o₀ K₀ hreach bss T hrep hval hlen
      exact ⟨T, bss, 0, le_refl 0,
        LogspaceTM.LogTM.BStepsN.refl (Nat.zero_le _), hrep, hval, hlen⟩
  | @head q pos cnt q' mv ops u out' e' N' hη rest ih =>
      intro o₀ K₀ hreach bss T hrep hval hlen
      have hη' : M.η q (fun _ => tapeSym w (pos 0)) (fun _ _ => true)
          (fun j => (cnt j == 0)) = some (q', mv, ops, u) := by
        have h1 : (fun a : Fin 1 => tapeSym w (pos a))
            = fun _ => tapeSym w (pos 0) := funext fun a => by rw [Fin.eq_zero a]
        have h2 : (fun a b : Fin 1 => (pos a == pos b))
            = fun _ _ => true := by
          funext a b
          rw [Fin.eq_zero a, Fin.eq_zero b]
          simp
        rw [← h1, ← h2]
        exact hη
      obtain ⟨T₁, bss₁, N₁, hN₁, hrun₁, hrep₁, hval₁, hdich⟩ :=
        tm_cycle q cnt bss w (pos 0) T (Nat.log 2 (C * (w.length + 1)) + 1)
          hrep hval hlen hη'
      have hreach' : M.StepsN w M.initConfig (o₀ ++ (u ++ []))
          (q', (fun a => (mv a).apply (pos a)), fun j => (ops j).apply (cnt j))
          (K₀ + 1) :=
        hreach.trans (Multihead.MHC.StepsN.head hη (Multihead.MHC.StepsN.refl _))
      have hcnt' : ∀ j, (ops j).apply (cnt j) ≤ C * (w.length + 1) := by
        intro j
        exact hC w _ _ _ hreach' j
      have hlen₁ : ∀ j, (bss₁ j).length ≤ Nat.log 2 (C * (w.length + 1)) + 1 := by
        intro j
        rcases hdich j with hd | hd
        · exact le_trans hd (hlen j)
        · have h2 : (2 : ℕ) ^ ((bss₁ j).length - 1) ≤ C * (w.length + 1) := by
            rw [hval₁ j] at hd
            exact le_trans hd (hcnt' j)
          have h1 : (bss₁ j).length - 1 ≤ Nat.log 2 (C * (w.length + 1)) := by
            calc (bss₁ j).length - 1
                = Nat.log 2 (2 ^ ((bss₁ j).length - 1)) :=
                  (Nat.log_pow (by omega) _).symm
              _ ≤ Nat.log 2 (C * (w.length + 1)) := Nat.log_mono_right h2
          omega
      obtain ⟨T', bss', N₂, hle₂, hrun₂, hrep', hval', hlen'⟩ :=
        ih hreach' bss₁ T₁ hrep₁ hval₁ hlen₁
      exact ⟨T', bss', N₁ + N₂, by omega, hrun₁.trans hrun₂, hrep', hval', hlen'⟩

/-- Weakening the space function of a bound. -/
theorem _root_.LogspaceTM.spaceBound_mono {Alpha' Gamma' : Type*}
    {M' : LogspaceTM.LogTM Alpha' Gamma'} {S S' : ℕ → ℕ}
    (h : LogspaceTM.SpaceBound M' S) (hle : ∀ n, S n ≤ S' n) :
    LogspaceTM.SpaceBound M' S' :=
  fun w out e N hrun => le_trans (h w out e N hrun) (hle w.length)

/-- **The simulator runs in `O(log n)` space**: every reachable configuration
of `toTM M` keeps its work head within `log₂(C·(n+1)) + 1` cells.  Proved by
locating the reachable configuration on the (deterministic) simulated run of
`simulate_bounded`, whose every configuration is bounded. -/
theorem toTM_spaceBound {C : ℕ} (hC : Multihead.SpaceBound M C) :
    LogspaceTM.SpaceBound (toTM M) (fun n => Nat.log 2 (C * (n + 1)) + 1) := by
  intro w out e N hrun
  obtain ⟨outM, eM, K', hle, hrunM, hcase⟩ :=
    Multihead.MHC.exists_run_upto (M := M) w (N + 1)
  obtain ⟨mq₂, pos₂, cnt₂⟩ := eM
  have hrep0 : ∀ (j : Fin c) k,
      (fun (_ : ℕ) => (fun (_ : Fin c) => (none : Option Bool))) k j
        = ((fun _ : Fin c => ([] : List Bool)) j)[k]? := by
    intro j k
    simp
  have hval0 : ∀ j : Fin c, bitsVal ((fun _ : Fin c => ([] : List Bool)) j)
      = (M.initConfig.2.2 : Fin c → ℕ) j := fun _ => rfl
  have hlen0 : ∀ j : Fin c, ((fun _ : Fin c => ([] : List Bool)) j).length
      ≤ Nat.log 2 (C * (w.length + 1)) + 1 := fun _ => by simp
  obtain ⟨T₁, bss₁, N₁, hge, hsim, -, -, -⟩ :=
    simulate_bounded hC w hrunM (Multihead.MHC.StepsN.refl _)
      (fun _ => []) (fun _ => fun _ => none) hrep0 hval0 hlen0
  have hinit : ((toTM M).initConfig : (toTM M).Config)
      = ((M.q0, TPh.consult (fun j => (((fun _ : Fin c => 0) j : ℕ) == 0))),
        (0 : ℕ), (0 : ℕ), fun _ => fun _ => none) := rfl
  have hsim' : LogspaceTM.LogTM.BStepsN (toTM M) w
      (Nat.log 2 (C * (w.length + 1)) + 1) (toTM M).initConfig outM
      ((mq₂, TPh.consult (fun j => (cnt₂ j == 0))), pos₂ 0, 0, T₁) N₁ := by
    rw [hinit]
    exact hsim
  rcases hcase with hKeq | hhaltM
  · exact hsim'.2 N out e (by omega) hrun
  · have hη' : M.η mq₂ (fun _ => tapeSym w (pos₂ 0)) (fun _ _ => true)
        (fun j => (cnt₂ j == 0)) = none := by
      have h1 : (fun a : Fin 1 => tapeSym w (pos₂ a))
          = fun _ => tapeSym w (pos₂ 0) := funext fun a => by rw [Fin.eq_zero a]
      have h2 : (fun a b : Fin 1 => (pos₂ a == pos₂ b))
          = fun _ _ => true := by
        funext a b
        rw [Fin.eq_zero a, Fin.eq_zero b]
        simp
      rw [← h1, ← h2]
      exact hhaltM
    obtain ⟨hhalt', -⟩ := tm_cycle_halt mq₂ cnt₂ w (pos₂ 0) T₁ hη'
    have hNle := LogspaceTM.LogTM.stepsN_le_of_halted hsim'.1 hhalt' hrun
    exact hsim'.2 N out e (by omega) hrun

/-- Arithmetic: `log₂(C·(n+1)) + 1 ≤ (C + 2)·(log₂(n+2) + 1)`, so the bound
of `toTM_spaceBound` has the canonical `C'·(⌊log₂(n+2)⌋+1)` shape. -/
theorem log_linear_bound (C n : ℕ) :
    Nat.log 2 (C * (n + 1)) + 1 ≤ (C + 2) * (Nat.log 2 (n + 2) + 1) := by
  have hkey : Nat.log 2 (C * (n + 1)) ≤ C + Nat.log 2 (n + 2) := by
    have h2 : C ≤ 2 ^ C := Nat.le_of_lt (Nat.lt_pow_self (by omega))
    have h1 : C * (n + 1) ≤ (n + 2) * 2 ^ C := by
      calc C * (n + 1) ≤ 2 ^ C * (n + 1) := Nat.mul_le_mul_right _ h2
        _ ≤ 2 ^ C * (n + 2) := Nat.mul_le_mul_left _ (by omega)
        _ = (n + 2) * 2 ^ C := Nat.mul_comm _ _
    have h3 : ∀ k : ℕ, Nat.log 2 ((n + 2) * 2 ^ k) = Nat.log 2 (n + 2) + k := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
          have hsplit : (n + 2) * 2 ^ (k + 1) = ((n + 2) * 2 ^ k) * 2 := by ring
          rw [hsplit, Nat.log_mul_base (by omega) (by positivity), ihk]
          omega
    calc Nat.log 2 (C * (n + 1))
        ≤ Nat.log 2 ((n + 2) * 2 ^ C) := Nat.log_mono_right h1
      _ = Nat.log 2 (n + 2) + C := h3 C
      _ = C + Nat.log 2 (n + 2) := Nat.add_comm _ _
  have hprod : (C + 2) * (Nat.log 2 (n + 2) + 1)
      = C * Nat.log 2 (n + 2) + C + 2 * Nat.log 2 (n + 2) + 2 := by ring
  omega

/-- **Multihead logspace is worktape logspace**: composing the head
elimination (`MHCOneHead.oneHead`) with the binary-counter reduction
(`toTM`) turns a multihead bounded-counter transducer into a worktape
transducer within the canonical `O(log n)`-cell bound. -/
theorem _root_.LogspaceTM.isLogspaceTM_of_isLogspaceMH {Alpha Gamma : Type}
    [Fintype Alpha] [DecidableEq Alpha] {f : List Alpha → Option (List Gamma)}
    (hf : Multihead.IsLogspaceMH f) : LogspaceTM.IsLogspaceTM f := by
  obtain ⟨c', C', N, hSB, hcomp⟩ := MHCOneHead.isLogspaceMH_oneHead hf
  refine ⟨toTM N, C' + 2, ?_, ?_⟩
  · exact LogspaceTM.spaceBound_mono (toTM_spaceBound hSB)
      (fun n => log_linear_bound C' n)
  · intro w out
    rw [hcomp w out, toTM_computes_iff]

end Space

end MHCToTM
