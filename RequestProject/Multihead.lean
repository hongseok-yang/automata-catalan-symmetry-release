/-
# Deterministic multihead bounded-counter transducers

The full logspace machine model for the containment half of
`thm:wrp-strict-below-logspace`: a deterministic transducer with `h` two-way
heads on `⊢w⊣` (reusing `TwoDFT.TapeSym` / `TwoDFT.tapeSym` and the end-marker
discipline of `def:2dft`) and `c` ℕ-valued counters with zero-tests.  Each
transition observes the state, the symbol under every head, the
head-coincidence pattern, and the counter zero-pattern.  Multihead two-way
automata with linearly bounded counters are the classical machine
characterisation of deterministic logspace (Hartmanis, "On non-determinancy
in simple computing devices", Acta Informatica 1, 1972; cited background,
exactly as `Logspace.IsLogspaceMap`): each head and each `O(n)`-bounded
counter is an `O(log n)`-bit register.  This model extends
`Logspace.CounterDFT` by extra heads with coincidence detection, and the
run relation is *step-indexed*, so halting runs carry an explicit length.

**Contents.**

* `HeadMove` / `MHC` / `Config` / `StepsN` / `Steps` / `Halted` /
  `initConfig` / `Computes` — the model; `StepsN … N` is the `N`-step run
  relation with accumulated emission.
* `StepsN.trans`, `stepsN_unique` (determinism, including the run length),
  `computes_unique`, `stepsN_invariant` (generic reachability invariant),
  `head_le_of_stepsN` (every head stays in `[0, n+1]`, from the end-marker
  discipline `rmark_no_right`).
* `SpaceBound` / `IsLogspaceMH` — the linear counter bound and the
  logspace-computable partial maps in the multihead model.
* `stepsN_split`, `halting_length_le`, `computes_halting_length` — **the polynomial halting-time bound**: a halting run of a space-bounded machine
  never repeats a configuration, so its length is less than
  `|Q| · (n+2)^h · (C·(n+1)+1)^c` — polynomial in `n` for fixed machine data.
* `ofCounter` — the single-head embedding of `Logspace.CounterDFT`, with the
  run correspondence, `ofCounter_computes_iff`, `ofCounter_spaceBound`, and
  `isLogspaceMH_of_isLogspaceMap`.
* `Fge0_isLogspaceMH`, `sMap_isLogspaceMH`, `exists_logspaceMH_not_wrp` —
  the separation witnesses transported into the multihead model.

Trust: the model theory and the embedding are axiom-clean;
`exists_logspaceMH_not_wrp` additionally admits `SliceMSO.buchi` (inherited
from `Fge0_not_isWRP`).
-/
import RequestProject.Logspace

namespace Multihead

open TwoDFT
open Logspace (CounterOp)

variable {Alpha Gamma : Type*} {h c : ℕ}

/-! ## Head moves -/

/-- A per-step move of one head: left (monus), stay, or right. -/
inductive HeadMove | left | stay | right
  deriving DecidableEq

/-- Apply a head move to a head position (`left` is truncated). -/
def HeadMove.apply : HeadMove → ℕ → ℕ
  | left, i => i - 1
  | stay, i => i
  | right, i => i + 1

@[simp] theorem HeadMove.apply_left (i : ℕ) : HeadMove.left.apply i = i - 1 := rfl
@[simp] theorem HeadMove.apply_stay (i : ℕ) : HeadMove.stay.apply i = i := rfl
@[simp] theorem HeadMove.apply_right (i : ℕ) : HeadMove.right.apply i = i + 1 := rfl

/-! ## The machine -/

open TwoDFT in
/-- **Deterministic multihead bounded-counter transducer.**  `h` two-way heads
on `⊢w⊣` (same tape alphabet and cell convention as the `def:2dft` run) and `c`
ℕ-valued counters; each transition observes the state, the tape symbol under
every head, the head-coincidence pattern, and the counter zero-pattern, and
outputs a new state, a move per head, a counter operation per counter, and an
emitted word. -/
structure MHC (Alpha Gamma : Type*) (h c : ℕ) where
  Q : Type
  fintypeQ : Fintype Q
  q0 : Q
  F : Q → Prop
  η : Q → (Fin h → TapeSym Alpha) → (Fin h → Fin h → Bool) → (Fin c → Bool) →
        Option (Q × (Fin h → HeadMove) × (Fin c → CounterOp) × List Gamma)
  /-- End-marker discipline: no head may move right while reading `⊣`
  (keeps every head position in `[0, |w| + 1]`). -/
  rmark_no_right : ∀ q syms coin zs r, η q syms coin zs = some r →
    ∀ a, syms a = TapeSym.rmark → r.2.1 a ≠ HeadMove.right

namespace MHC

variable (M : MHC Alpha Gamma h c)

/-- A configuration: state, head positions, counter values. -/
abbrev Config : Type := M.Q × (Fin h → ℕ) × (Fin c → ℕ)

/-- **The step-indexed run relation**, with accumulated emission:
`StepsN w cfg out e N` says the machine goes from `cfg` to `e` in exactly `N`
steps emitting `out`.  The observation fed to `η` at `(q, pos, cnt)` is the
symbol under each head, the coincidence pattern `pos a == pos b`, and the
zero-pattern `cnt j == 0`. -/
inductive StepsN (w : List Alpha) : M.Config → List Gamma → M.Config → ℕ → Prop
  | refl (cfg : M.Config) : StepsN w cfg [] cfg 0
  | head {q : M.Q} {pos : Fin h → ℕ} {cnt : Fin c → ℕ} {q' : M.Q}
      {mv : Fin h → HeadMove} {ops : Fin c → CounterOp} {u out : List Gamma}
      {e : M.Config} {N : ℕ} :
      M.η q (fun a => tapeSym w (pos a)) (fun a b => pos a == pos b)
        (fun j => cnt j == 0) = some (q', mv, ops, u) →
      StepsN w (q', fun a => (mv a).apply (pos a), fun j => (ops j).apply (cnt j))
        out e N →
      StepsN w (q, pos, cnt) (u ++ out) e (N + 1)

/-- The run relation with the length existentially hidden. -/
def Steps (w : List Alpha) (cfg : M.Config) (out : List Gamma) (e : M.Config) : Prop :=
  ∃ N, M.StepsN w cfg out e N

/-- A configuration on which `η` is undefined: the run halts there. -/
def Halted (w : List Alpha) (cfg : M.Config) : Prop :=
  M.η cfg.1 (fun a => tapeSym w (cfg.2.1 a)) (fun a b => cfg.2.1 a == cfg.2.1 b)
    (fun j => cfg.2.2 j == 0) = none

/-- The initial configuration: `q₀`, all heads on `⊢`, all counters `0`. -/
def initConfig : M.Config := (M.q0, fun _ => 0, fun _ => 0)

/-- The computed partial map: the maximal run from `initConfig` is finite,
halts acceptingly, and the emitted words concatenate to `out`. -/
def Computes (w : List Alpha) (out : List Gamma) : Prop :=
  ∃ e, M.Steps w M.initConfig out e ∧ M.Halted w e ∧ M.F e.1

/-- The number of states (the `fintypeQ` field made usable in bounds). -/
def cardQ : ℕ := @Fintype.card M.Q M.fintypeQ

end MHC

/-- **The linear counter bound**: along every run from the initial
configuration, every counter stays `≤ C·(n+1)` — i.e. each counter is an
`O(log n)`-bit register.  (Head positions need no hypothesis: the end-marker
discipline keeps them in `[0, n+1]`, see `head_le_of_stepsN`.) -/
def SpaceBound (M : MHC Alpha Gamma h c) (C : ℕ) : Prop :=
  ∀ w out e N, M.StepsN w M.initConfig out e N → ∀ j, e.2.2 j ≤ C * (w.length + 1)

/-- **Deterministic-logspace word-to-word maps, multihead model**: computed by
some multihead bounded-counter transducer whose counters are linearly bounded
(= logarithmically many bits; Hartmanis 1972 — each two-way head is itself an
`O(log n)`-bit register). -/
def IsLogspaceMH (f : List Alpha → Option (List Gamma)) : Prop :=
  ∃ (h c C : ℕ) (M : MHC Alpha Gamma h c), SpaceBound M C ∧
    ∀ w out, f w = some out ↔ M.Computes w out

/-! ## Determinism and the reachability invariant -/

namespace MHC

variable {M : MHC Alpha Gamma h c}

/-- A configuration with a defined transition has not halted. -/
theorem not_halted_of_step {w : List Alpha} {q : M.Q} {pos : Fin h → ℕ}
    {cnt : Fin c → ℕ}
    {r : M.Q × (Fin h → HeadMove) × (Fin c → CounterOp) × List Gamma}
    (hη : M.η q (fun a => tapeSym w (pos a)) (fun a b => pos a == pos b)
      (fun j => cnt j == 0) = some r) :
    ¬ M.Halted w (q, pos, cnt) := by
  intro hh
  have hnone : M.η q (fun a => tapeSym w (pos a)) (fun a b => pos a == pos b)
      (fun j => cnt j == 0) = none := hh
  rw [hnone] at hη
  simp at hη

/-- Transitivity of the step-indexed run relation: emissions concatenate and
lengths add. -/
theorem StepsN.trans {w : List Alpha} :
    ∀ {c₁ c₂ c₃ : M.Config} {o₁ o₂ : List Gamma} {N₁ N₂ : ℕ},
    M.StepsN w c₁ o₁ c₂ N₁ → M.StepsN w c₂ o₂ c₃ N₂ →
    M.StepsN w c₁ (o₁ ++ o₂) c₃ (N₁ + N₂) := by
  intro c₁ c₂ c₃ o₁ o₂ N₁ N₂ h₁
  induction h₁ with
  | refl cfg => intro h₂; simpa using h₂
  | @head q pos cnt q' mv ops u out e N hη _ ih =>
      intro h₂
      rw [List.append_assoc, show N + 1 + N₂ = (N + N₂) + 1 by omega]
      exact StepsN.head hη (ih h₂)

/-- **Determinism: the maximal run is unique, including its length.**  Two
halting runs from the same configuration have the same emission, the same
halting configuration, and the same number of steps. -/
theorem stepsN_unique {w : List Alpha} :
    ∀ {cfg : M.Config} {out₁ out₂ : List Gamma} {e₁ e₂ : M.Config} {N₁ N₂ : ℕ},
    M.StepsN w cfg out₁ e₁ N₁ → M.Halted w e₁ →
    M.StepsN w cfg out₂ e₂ N₂ → M.Halted w e₂ →
    out₁ = out₂ ∧ e₁ = e₂ ∧ N₁ = N₂ := by
  intro cfg out₁ out₂ e₁ e₂ N₁ N₂ h₁
  induction h₁ generalizing out₂ e₂ N₂ with
  | refl cfg =>
      intro halt₁ h₂ halt₂
      cases h₂ with
      | refl => exact ⟨rfl, rfl, rfl⟩
      | head hη _ => exact absurd halt₁ (not_halted_of_step hη)
  | head hη rest ih =>
      intro halt₁ h₂ halt₂
      cases h₂ with
      | refl => exact absurd halt₂ (not_halted_of_step hη)
      | head hη' rest' =>
          rw [hη] at hη'
          injection hη' with htuple
          injection htuple with hq hrest
          injection hrest with hmv hrest'
          injection hrest' with hops hu
          subst hq; subst hmv; subst hops; subst hu
          obtain ⟨ho, he, hN⟩ := ih halt₁ rest' halt₂
          exact ⟨by rw [ho], he, by rw [hN]⟩

/-- The computed map is a partial function. -/
theorem computes_unique {w : List Alpha} {out₁ out₂ : List Gamma}
    (h₁ : M.Computes w out₁) (h₂ : M.Computes w out₂) : out₁ = out₂ := by
  obtain ⟨e₁, ⟨N₁, hs₁⟩, hh₁, -⟩ := h₁
  obtain ⟨e₂, ⟨N₂, hs₂⟩, hh₂, -⟩ := h₂
  exact (stepsN_unique hs₁ hh₁ hs₂ hh₂).1

/-- **Reachability invariant**: a property of configurations that holds at the
start and is preserved by every single step holds at the end of any `StepsN`
segment. -/
theorem stepsN_invariant {w : List Alpha} {P : M.Config → Prop}
    (hstep : ∀ q pos cnt q' mv ops u, P (q, pos, cnt) →
      M.η q (fun a => tapeSym w (pos a)) (fun a b => pos a == pos b)
        (fun j => cnt j == 0) = some (q', mv, ops, u) →
      P (q', fun a => (mv a).apply (pos a), fun j => (ops j).apply (cnt j))) :
    ∀ {cfg e : M.Config} {out : List Gamma} {N : ℕ},
      M.StepsN w cfg out e N → P cfg → P e := by
  intro cfg e out N hrun
  induction hrun with
  | refl cfg => exact id
  | head hη _ ih =>
      intro hP
      exact ih (hstep _ _ _ _ _ _ _ hP hη)

/-! ## The generic head bound -/

/-- **Every head stays in `[0, |w| + 1]`** along any run from the initial
configuration: a right move needs a non-`⊣` symbol under that head
(`rmark_no_right`), and every cell `≥ |w| + 1` holds `⊣` (`tapeSym_ge`). -/
theorem head_le_of_stepsN {w : List Alpha} {out : List Gamma} {e : M.Config}
    {N : ℕ} (hs : M.StepsN w M.initConfig out e N) :
    ∀ a, e.2.1 a ≤ w.length + 1 := by
  refine stepsN_invariant (P := fun cfg => ∀ a, cfg.2.1 a ≤ w.length + 1)
    ?_ hs (fun a => Nat.zero_le _)
  intro q pos cnt q' mv ops u hP hη a
  show (mv a).apply (pos a) ≤ w.length + 1
  cases hmv : mv a with
  | left =>
      simp only [HeadMove.apply_left]
      have h1 : pos a ≤ w.length + 1 := hP a
      omega
  | stay =>
      simp only [HeadMove.apply_stay]
      exact hP a
  | right =>
      simp only [HeadMove.apply_right]
      by_cases hle : pos a ≤ w.length
      · omega
      · exfalso
        have hrm : (fun a => tapeSym w (pos a)) a = TapeSym.rmark := by
          show tapeSym w (pos a) = TapeSym.rmark
          exact tapeSym_ge w (pos a) (by omega)
        exact M.rmark_no_right q _ _ _ _ hη a hrm hmv

/-! ## The polynomial halting-time bound -/

/-- **Run splitting**: an `N`-step run can be split at any intermediate time
`i ≤ N` into an `i`-step prefix and an `(N - i)`-step suffix through some
intermediate configuration. -/
theorem stepsN_split {w : List Alpha} :
    ∀ {cfg e : M.Config} {out : List Gamma} {N : ℕ},
    M.StepsN w cfg out e N → ∀ i, i ≤ N →
    ∃ mid out₁ out₂, out = out₁ ++ out₂ ∧
      M.StepsN w cfg out₁ mid i ∧ M.StepsN w mid out₂ e (N - i) := by
  intro cfg e out N hrun
  induction hrun with
  | refl cfg =>
      intro i hi
      have h0 : i = 0 := Nat.le_zero.mp hi
      subst h0
      exact ⟨cfg, [], [], rfl, StepsN.refl cfg, StepsN.refl cfg⟩
  | @head q pos cnt q' mv ops u out' e' N' hη rest ih =>
      intro i hi
      cases i with
      | zero =>
          exact ⟨(q, pos, cnt), [], u ++ out', rfl, StepsN.refl _,
            StepsN.head hη rest⟩
      | succ i' =>
          obtain ⟨mid, o₁, o₂, ho, h₁, h₂⟩ := ih i' (by omega)
          refine ⟨mid, u ++ o₁, o₂, ?_, StepsN.head hη h₁, ?_⟩
          · rw [ho, List.append_assoc]
          · rw [show N' + 1 - (i' + 1) = N' - i' by omega]
            exact h₂

/-- **The polynomial halting-time bound.**  A halting run of a machine with
`SpaceBound M C` never repeats a configuration (two visits to the same
configuration would give, by `stepsN_unique`, equal remaining halting times),
and every visited configuration has its state in `Q`, its heads in
`[0, n+1]` (`head_le_of_stepsN`), and its counters `≤ C·(n+1)` (`SpaceBound`);
hence the `N + 1` visited configurations inject into a finite space and
`N < |Q| · (n+2)^h · (C·(n+1)+1)^c` — polynomial in `n = |w|` for fixed
machine data. -/
theorem halting_length_le {C : ℕ} (hSB : SpaceBound M C) {w : List Alpha}
    {out : List Gamma} {e : M.Config} {N : ℕ}
    (hrun : M.StepsN w M.initConfig out e N) (hhalt : M.Halted w e) :
    N < M.cardQ * (w.length + 2) ^ h * (C * (w.length + 1) + 1) ^ c := by
  let _ : Fintype M.Q := M.fintypeQ
  -- the configuration visited at each time `i ≤ N`
  have hspec : ∀ i : Fin (N + 1), ∃ mid : M.Config,
      (∃ out₁, M.StepsN w M.initConfig out₁ mid i.val) ∧
      (∃ out₂, M.StepsN w mid out₂ e (N - i.val)) := by
    intro i
    obtain ⟨mid, o₁, o₂, -, h₁, h₂⟩ :=
      stepsN_split hrun i.val (Nat.lt_succ_iff.mp i.isLt)
    exact ⟨mid, ⟨o₁, h₁⟩, ⟨o₂, h₂⟩⟩
  choose T hT₁ hT₂ using hspec
  -- distinct times visit distinct configurations
  have hinj : Function.Injective T := by
    intro i j hij
    obtain ⟨o₂, h₂i⟩ := hT₂ i
    obtain ⟨o₂', h₂j⟩ := hT₂ j
    rw [hij] at h₂i
    have hlen := (stepsN_unique h₂i hhalt h₂j hhalt).2.2
    have hi := i.isLt
    have hj := j.isLt
    exact Fin.ext (by omega)
  -- every visited configuration is bounded
  have hbound : ∀ i : Fin (N + 1), (∀ a, (T i).2.1 a ≤ w.length + 1) ∧
      ∀ j, (T i).2.2 j ≤ C * (w.length + 1) := by
    intro i
    obtain ⟨o₁, h₁⟩ := hT₁ i
    exact ⟨head_le_of_stepsN h₁, fun j => hSB w o₁ (T i) i.val h₁ j⟩
  -- inject the visit times into the finite configuration space
  have hcard := Fintype.card_le_of_injective
    (β := M.Q × (Fin h → Fin (w.length + 2)) × (Fin c → Fin (C * (w.length + 1) + 1)))
    (fun i => ((T i).1,
      fun a => ⟨(T i).2.1 a, Nat.lt_succ_of_le ((hbound i).1 a)⟩,
      fun j => ⟨(T i).2.2 j, Nat.lt_succ_of_le ((hbound i).2 j)⟩))
    (by
      intro i j hij
      apply hinj
      -- retract the decorated tuple back to the configuration (up to defeq)
      exact congrArg
        (fun p : M.Q × (Fin h → Fin (w.length + 2)) ×
            (Fin c → Fin (C * (w.length + 1) + 1)) =>
          ((p.1, fun a => (p.2.1 a).1, fun j' => (p.2.2 j').1) : M.Config)) hij)
  rw [Fintype.card_fin] at hcard
  have hβ : Fintype.card
      (M.Q × (Fin h → Fin (w.length + 2)) × (Fin c → Fin (C * (w.length + 1) + 1)))
      = Fintype.card M.Q * ((w.length + 2) ^ h * (C * (w.length + 1) + 1) ^ c) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [hβ] at hcard
  show N < Fintype.card M.Q * (w.length + 2) ^ h * (C * (w.length + 1) + 1) ^ c
  rw [mul_assoc]
  exact hcard

/-- The halting-time bound phrased on `Computes`-witnesses: any computed
output is produced by a halting accepting run of polynomially bounded
length. -/
theorem computes_halting_length {C : ℕ} (hSB : SpaceBound M C) {w : List Alpha}
    {out : List Gamma} (hc : M.Computes w out) :
    ∃ e N, M.StepsN w M.initConfig out e N ∧ M.Halted w e ∧ M.F e.1 ∧
      N < M.cardQ * (w.length + 2) ^ h * (C * (w.length + 1) + 1) ^ c := by
  obtain ⟨e, ⟨N, hs⟩, hh, hF⟩ := hc
  exact ⟨e, N, hs, hh, hF, halting_length_le hSB hs hh⟩

end MHC

/-! ## The single-head embedding -/

/-- Translate a 2DFT direction (`true` = right, `false` = left) into a head
move (never `stay`). -/
def dirMove (d : Bool) : HeadMove := if d then HeadMove.right else HeadMove.left

@[simp] theorem dirMove_true : dirMove true = HeadMove.right := rfl
@[simp] theorem dirMove_false : dirMove false = HeadMove.left := rfl

/-- `dirMove` agrees with `TwoDFT.moveDir`. -/
theorem dirMove_apply (d : Bool) (i : ℕ) : (dirMove d).apply i = moveDir i d := by
  cases d <;> rfl

/-- **The single-head embedding**: a bounded-counter 2DFT
(`Logspace.CounterDFT`) is a multihead machine with `h = 1` — same states,
the transition reads the symbol under the single head and the zero-pattern
(the coincidence pattern of one head is trivially reflexive and is ignored),
and the Boolean direction becomes a `HeadMove`.  The `rmark_no_right`
discipline follows from the 2DFT's `rmark_left`. -/
def ofCounter (M : Logspace.CounterDFT Alpha Gamma c) : MHC Alpha Gamma 1 c where
  Q := M.Q
  fintypeQ := M.fintypeQ
  q0 := M.q0
  F := M.F
  η := fun q syms _ zs =>
    (M.η q (syms 0) zs).map fun r => (r.1, fun _ => dirMove r.2.1, r.2.2.1, r.2.2.2)
  rmark_no_right := by
    intro q syms coin zs r hr a hrm
    rw [Option.map_eq_some_iff] at hr
    obtain ⟨⟨q', d, ops, u⟩, hM, rfl⟩ := hr
    rw [Fin.eq_zero a] at hrm
    rw [hrm] at hM
    have hd : d = false := M.rmark_left q zs _ hM
    subst hd
    simp

/-- Runs of the counter 2DFT transfer to the embedded multihead machine
(configurations `(q, i, cnt) ↦ (q, fun _ => i, cnt)`). -/
theorem ofCounter_steps_of {M : Logspace.CounterDFT Alpha Gamma c} {w : List Alpha} :
    ∀ {p e : M.Q × ℕ × (Fin c → ℕ)} {out : List Gamma}, M.Steps w p out e →
      (ofCounter M).Steps w (p.1, fun _ => p.2.1, p.2.2) out
        (e.1, fun _ => e.2.1, e.2.2) := by
  intro p e out hrun
  induction hrun with
  | refl p => exact ⟨0, MHC.StepsN.refl _⟩
  | @head q i cnt q' d ops u out' e' hη hrest ih =>
      obtain ⟨N, ihN⟩ := ih
      have hη' : (ofCounter M).η q (fun _ : Fin 1 => tapeSym w i)
          (fun _ _ : Fin 1 => i == i) (fun j => cnt j == 0)
          = some (q', fun _ => dirMove d, ops, u) := by
        show (M.η q (tapeSym w i) (fun j => cnt j == 0)).map
            (fun r => (r.1, fun _ => dirMove r.2.1, r.2.2.1, r.2.2.2))
          = some (q', fun _ => dirMove d, ops, u)
        simp only [hη, Option.map_some]
      have hrest' : (ofCounter M).StepsN w
          (q', fun _ => (dirMove d).apply i, fun j => (ops j).apply (cnt j))
          out' (e'.1, fun _ => e'.2.1, e'.2.2) N := by
        have hfun : (fun _ : Fin 1 => (dirMove d).apply i)
            = (fun _ : Fin 1 => moveDir i d) := by
          funext a
          exact dirMove_apply d i
        rw [hfun]
        exact ihN
      exact ⟨N + 1, MHC.StepsN.head hη' hrest'⟩

/-- Runs of the embedded machine project back to the counter 2DFT
(configurations `(q, pos, cnt) ↦ (q, pos 0, cnt)`). -/
theorem steps_of_ofCounter {M : Logspace.CounterDFT Alpha Gamma c} {w : List Alpha} :
    ∀ {cfg e : (ofCounter M).Config} {out : List Gamma} {N : ℕ},
      (ofCounter M).StepsN w cfg out e N →
      M.Steps w (cfg.1, cfg.2.1 0, cfg.2.2) out (e.1, e.2.1 0, e.2.2) := by
  intro cfg e out N hrun
  induction hrun with
  | refl cfg => exact Logspace.CounterDFT.Steps.refl _
  | @head q pos cnt q' mv ops u out' e' N' hη hrest ih =>
      have hη' : (M.η q (tapeSym w (pos 0)) (fun j => cnt j == 0)).map
          (fun r => (r.1, fun _ => dirMove r.2.1, r.2.2.1, r.2.2.2))
          = some (q', mv, ops, u) := hη
      obtain ⟨⟨q₁, d₁, ops₁, u₁⟩, hM, heq⟩ := Option.map_eq_some_iff.mp hη'
      injection heq with hq hrest2
      injection hrest2 with hmv hrest3
      injection hrest3 with hops hu
      subst hq; subst hmv; subst hops; subst hu
      have ih' : M.Steps w (q₁, (dirMove d₁).apply (pos 0),
          fun j => (ops₁ j).apply (cnt j)) out' (e'.1, e'.2.1 0, e'.2.2) := ih
      rw [dirMove_apply] at ih'
      exact Logspace.CounterDFT.Steps.head hM ih'

/-- Halting transfers in both directions. -/
theorem ofCounter_halted_iff {M : Logspace.CounterDFT Alpha Gamma c}
    {w : List Alpha} (q : M.Q) (pos : Fin 1 → ℕ) (cnt : Fin c → ℕ) :
    (ofCounter M).Halted w (q, pos, cnt) ↔ M.Halted w (q, pos 0, cnt) := by
  show (M.η q (tapeSym w (pos 0)) (fun j => cnt j == 0)).map
      (fun r => (r.1, fun _ => dirMove r.2.1, r.2.2.1, r.2.2.2)) = none
    ↔ M.η q (tapeSym w (pos 0)) (fun j => cnt j == 0) = none
  exact Option.map_eq_none_iff

/-- The embedded machine computes exactly what the counter 2DFT computes. -/
theorem ofCounter_computes_iff {M : Logspace.CounterDFT Alpha Gamma c}
    {w : List Alpha} {out : List Gamma} :
    (ofCounter M).Computes w out ↔ M.Computes w out := by
  constructor
  · rintro ⟨e, ⟨N, hs⟩, hh, hF⟩
    exact ⟨(e.1, e.2.1 0, e.2.2), steps_of_ofCounter hs,
      (ofCounter_halted_iff e.1 e.2.1 e.2.2).mp hh, hF⟩
  · rintro ⟨e, hs, hh, hF⟩
    exact ⟨(e.1, fun _ => e.2.1, e.2.2), ofCounter_steps_of hs,
      (ofCounter_halted_iff e.1 (fun _ => e.2.1) e.2.2).mpr hh, hF⟩

/-- The linear counter bound transfers along the embedding. -/
theorem ofCounter_spaceBound {M : Logspace.CounterDFT Alpha Gamma c} {C : ℕ}
    (hSB : Logspace.SpaceBound M C) : SpaceBound (ofCounter M) C := by
  intro w out e N hs j
  exact hSB w out (e.1, e.2.1 0, e.2.2) (steps_of_ofCounter hs) j

/-- **Every logspace map of the single-head model is a logspace map of the
multihead model** (`h = 1`, same counters, same space bound). -/
theorem isLogspaceMH_of_isLogspaceMap {f : List Alpha → Option (List Gamma)}
    (hf : Logspace.IsLogspaceMap f) : IsLogspaceMH f := by
  obtain ⟨c', C, M, hSB, hM⟩ := hf
  exact ⟨1, c', C, ofCounter M, ofCounter_spaceBound hSB,
    fun w out => (hM w out).trans ofCounter_computes_iff.symm⟩

/-! ## The separation witnesses in the multihead model -/

/-- `F_{≥0}` (Appendix A.3) is computable in the multihead model. -/
theorem Fge0_isLogspaceMH : IsLogspaceMH WRPComp.Fge0 :=
  isLogspaceMH_of_isLogspaceMap Logspace.Fge0_isLogspace

/-- The map `sMap` of `thm:wrp-not-closed` is computable in the multihead
model. -/
theorem sMap_isLogspaceMH : IsLogspaceMH WRPComp.sMap :=
  isLogspaceMH_of_isLogspaceMap Logspace.sMap_isLogspace

/-- **The separation half of `thm:wrp-strict-below-logspace`, multihead
model**: a deterministic-logspace map (namely `F_{≥0}`) that is not a WRP
map.  Trust: admits `SliceMSO.buchi` through `Fge0_not_isWRP`. -/
theorem exists_logspaceMH_not_wrp :
    ∃ f : List Step → Option (List WRPComp.GBD), IsLogspaceMH f ∧ ¬ WRP.IsWRP f :=
  ⟨WRPComp.Fge0, Fge0_isLogspaceMH, WRPComp.Fge0_not_isWRP⟩

end Multihead
