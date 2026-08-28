/-
# The deterministic logspace worktape transducer (the paper's literal model)

`thm:wrp-logspace` (paper.tex) speaks of an evaluator that
"uses only `O(log n)` bits of working memory beyond a read-only input and a
write-only output", and "Space here and below is measured in bits."  The
repo's `Multihead.MHC` model realises this through the classical multihead /
bounded-counter characterisation (Hartmanis 1972).  This file defines the
**literal machine of the paper's statement** — a deterministic Turing
transducer with a read-only end-marked input tape, a write-only output, and
one two-way read-write worktape over a finite work alphabet, with the space
usage measured by the worktape cells visited — so that the logspace trio can
be stated verbatim (`WRPWorktape.lean`), via the simulation
`MHCOneHead.lean` + `MHCToTM.lean`.

A worktape of `S` cells over a finite alphabet `Δ` holds `S · log₂|Δ|` bits —
`O(log n)` bits exactly when `S = O(log n)`, which is how `IsLogspaceTM`
is phrased (`S(n) = C·(⌊log₂(n+2)⌋+1)`).

**Contents.**

* `LogTM` / `Config` / `StepsN` / `Steps` / `Halted` / `initConfig` /
  `Computes` — the model; a step reads the input symbol under the input head,
  the work symbol under the work head, and a work-head-at-left-end flag,
  then switches state, moves the input head, writes and moves the work head,
  and emits a word.
* `StepsN.trans`, `stepsN_unique`, `computes_unique`, `stepsN_invariant`,
  `stepsN_split`, `head_le_of_stepsN` — determinism and the generic run
  theory, mirroring `Multihead.MHC`.
* `SpaceBound` (every run from the initial configuration keeps the work head
  within the first `S(n)` cells) and `IsLogspaceTM` (the paper's
  logspace-computable partial maps: `S(n) = C·(log₂(n+2)+1)` cells, i.e.
  `O(log n)` bits).
* `wh_le_of_prefix`, `tape_blank_of_stepsN` — a space-bounded run never
  writes beyond cell `S(n)`.
* `halting_length_le` — **the generic polynomial-time bound**: a halting run
  of a space-bounded machine never repeats a configuration, so its length is
  less than `|Q| · (n+2) · (S+1) · |Δ|^(S+1)`; with `S = O(log n)` this is
  polynomial in `n` (`pow_log_poly_bound`, `halting_length_poly`) — the
  "produced in polynomial time" clause of `thm:wrp-logspace` holds in this
  model for *every* space-bounded machine, independently of how it was
  built.

Everything here is axiom-clean.
-/
import RequestProject.Multihead

namespace LogspaceTM

open TwoDFT
open Multihead (HeadMove)

variable {Alpha Gamma : Type*}

/-! ## The machine -/

/-- **Deterministic logspace worktape transducer.**  A read-only two-way input
head on `⊢w⊣` (the end-marker discipline of `def:2dft-run`), one two-way
read-write worktape over the finite work alphabet `Delta` (initially all
`blank`), and a write-only output.  Each transition observes the state, the
input symbol under the input head, the work symbol under the work head, and
whether the work head is at the left end; it yields a new state, an input-head
move, a symbol written at the work head, a work-head move, and an emitted
word. -/
structure LogTM (Alpha Gamma : Type*) where
  Q : Type
  fintypeQ : Fintype Q
  Delta : Type
  fintypeDelta : Fintype Delta
  blank : Delta
  q0 : Q
  F : Q → Prop
  η : Q → TapeSym Alpha → Delta → Bool →
        Option (Q × HeadMove × Delta × HeadMove × List Gamma)
  /-- End-marker discipline: the input head may not move right while
  reading `⊣`. -/
  rmark_no_right : ∀ q d z r, η q TapeSym.rmark d z = some r →
    r.2.1 ≠ HeadMove.right

namespace LogTM

variable (M : LogTM Alpha Gamma)

/-- A configuration: state, input-head position, work-head position, work
tape. -/
abbrev Config : Type := M.Q × ℕ × ℕ × (ℕ → M.Delta)

/-- **The step-indexed run relation** with accumulated emission.  A step at
`(q, i, wh, T)` consults `η` on `(q, ⟨symbol at i⟩, T wh, wh == 0)`; on
`some (q', mvI, d, mvW, u)` it writes `d` at `wh`, applies the two head
moves, and emits `u`. -/
inductive StepsN (w : List Alpha) : M.Config → List Gamma → M.Config → ℕ → Prop
  | refl (cfg : M.Config) : StepsN w cfg [] cfg 0
  | head {q : M.Q} {i wh : ℕ} {T : ℕ → M.Delta} {q' : M.Q}
      {mvI : HeadMove} {d : M.Delta} {mvW : HeadMove} {u out : List Gamma}
      {e : M.Config} {N : ℕ} :
      M.η q (tapeSym w i) (T wh) (wh == 0) = some (q', mvI, d, mvW, u) →
      StepsN w (q', mvI.apply i, mvW.apply wh, Function.update T wh d) out e N →
      StepsN w (q, i, wh, T) (u ++ out) e (N + 1)

/-- The run relation with the length existentially hidden. -/
def Steps (w : List Alpha) (cfg : M.Config) (out : List Gamma) (e : M.Config) : Prop :=
  ∃ N, M.StepsN w cfg out e N

/-- A configuration on which `η` is undefined: the run halts there. -/
def Halted (w : List Alpha) (cfg : M.Config) : Prop :=
  M.η cfg.1 (tapeSym w cfg.2.1) (cfg.2.2.2 cfg.2.2.1) (cfg.2.2.1 == 0) = none

/-- The initial configuration: `q₀`, both heads at `0`, all-blank work tape. -/
def initConfig : M.Config := (M.q0, 0, 0, fun _ => M.blank)

/-- The computed partial map: the maximal run from `initConfig` halts
acceptingly with total emission `out`. -/
def Computes (w : List Alpha) (out : List Gamma) : Prop :=
  ∃ e, M.Steps w M.initConfig out e ∧ M.Halted w e ∧ M.F e.1

/-- The number of states, usable in bounds. -/
def cardQ : ℕ := @Fintype.card M.Q M.fintypeQ

/-- The size of the work alphabet, usable in bounds. -/
def cardDelta : ℕ := @Fintype.card M.Delta M.fintypeDelta

end LogTM

/-- **The space bound**: along every run from the initial configuration, the
work head stays within the first `S(n)` cells (hence, since the tape starts
blank and writes happen at the work head, at most `S(n)+1` cells are ever
non-blank — `tape_blank_of_stepsN`).  With `|Δ|` fixed this is
`O(S(n))` bits of working memory. -/
def SpaceBound (M : LogTM Alpha Gamma) (S : ℕ → ℕ) : Prop :=
  ∀ w out e N, M.StepsN w M.initConfig out e N → e.2.2.1 ≤ S w.length

/-- **Deterministic-logspace word-to-word maps, worktape model** — the
paper's literal reading of "`O(log n)` bits of working memory beyond a
read-only input and a write-only output": computed by a worktape transducer
whose work head stays within `C·(⌊log₂(n+2)⌋+1)` cells. -/
def IsLogspaceTM (f : List Alpha → Option (List Gamma)) : Prop :=
  ∃ (M : LogTM Alpha Gamma) (C : ℕ),
    SpaceBound M (fun n => C * (Nat.log 2 (n + 2) + 1)) ∧
    ∀ w out, f w = some out ↔ M.Computes w out

/-! ## Determinism and the generic run theory -/

namespace LogTM

variable {M : LogTM Alpha Gamma}

theorem not_halted_of_step {w : List Alpha} {q : M.Q} {i wh : ℕ} {T : ℕ → M.Delta}
    {r : M.Q × HeadMove × M.Delta × HeadMove × List Gamma}
    (hη : M.η q (tapeSym w i) (T wh) (wh == 0) = some r) :
    ¬ M.Halted w (q, i, wh, T) := by
  intro hh
  have hnone : M.η q (tapeSym w i) (T wh) (wh == 0) = none := hh
  rw [hnone] at hη
  simp at hη

/-- Transitivity: emissions concatenate and lengths add. -/
theorem StepsN.trans {w : List Alpha} :
    ∀ {c₁ c₂ c₃ : M.Config} {o₁ o₂ : List Gamma} {N₁ N₂ : ℕ},
    M.StepsN w c₁ o₁ c₂ N₁ → M.StepsN w c₂ o₂ c₃ N₂ →
    M.StepsN w c₁ (o₁ ++ o₂) c₃ (N₁ + N₂) := by
  intro c₁ c₂ c₃ o₁ o₂ N₁ N₂ h₁
  induction h₁ with
  | refl cfg => intro h₂; simpa using h₂
  | @head q i wh T q' mvI d mvW u out' e' N' hη _ ih =>
      intro h₂
      rw [List.append_assoc, show N' + 1 + N₂ = (N' + N₂) + 1 by omega]
      exact StepsN.head hη (ih h₂)

/-- **Determinism**: two halting runs from the same configuration agree in
emission, halting configuration, and length. -/
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
          injection hrest with hmvI hrest'
          injection hrest' with hd hrest''
          injection hrest'' with hmvW hu
          subst hq; subst hmvI; subst hd; subst hmvW; subst hu
          obtain ⟨ho, he, hN⟩ := ih halt₁ rest' halt₂
          exact ⟨by rw [ho], he, by rw [hN]⟩

/-- The computed map is a partial function. -/
theorem computes_unique {w : List Alpha} {out₁ out₂ : List Gamma}
    (h₁ : M.Computes w out₁) (h₂ : M.Computes w out₂) : out₁ = out₂ := by
  obtain ⟨e₁, ⟨N₁, hs₁⟩, hh₁, -⟩ := h₁
  obtain ⟨e₂, ⟨N₂, hs₂⟩, hh₂, -⟩ := h₂
  exact (stepsN_unique hs₁ hh₁ hs₂ hh₂).1

/-- Generic reachability invariant. -/
theorem stepsN_invariant {w : List Alpha} {P : M.Config → Prop}
    (hstep : ∀ q i wh T q' mvI d mvW u, P (q, i, wh, T) →
      M.η q (tapeSym w i) (T wh) (wh == 0) = some (q', mvI, d, mvW, u) →
      P (q', HeadMove.apply mvI i, HeadMove.apply mvW wh, Function.update T wh d)) :
    ∀ {cfg e : M.Config} {out : List Gamma} {N : ℕ},
      M.StepsN w cfg out e N → P cfg → P e := by
  intro cfg e out N hrun
  induction hrun with
  | refl cfg => exact id
  | head hη _ ih =>
      intro hP
      exact ih (hstep _ _ _ _ _ _ _ _ _ hP hη)

/-- Run splitting at any intermediate time. -/
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
  | @head q i wh T q' mvI d mvW u out' e' N' hη rest ih =>
      intro j hj
      cases j with
      | zero =>
          exact ⟨(q, i, wh, T), [], u ++ out', rfl, StepsN.refl _,
            StepsN.head hη rest⟩
      | succ j' =>
          obtain ⟨mid, o₁, o₂, ho, h₁, h₂⟩ := ih j' (by omega)
          refine ⟨mid, u ++ o₁, o₂, ?_, StepsN.head hη h₁, ?_⟩
          · rw [ho, List.append_assoc]
          · rw [show N' + 1 - (j' + 1) = N' - j' by omega]
            exact h₂

/-- The input head stays in `[0, |w| + 1]` (end-marker discipline). -/
theorem head_le_of_stepsN {w : List Alpha} {out : List Gamma} {e : M.Config}
    {N : ℕ} (hs : M.StepsN w M.initConfig out e N) :
    e.2.1 ≤ w.length + 1 := by
  refine stepsN_invariant (P := fun cfg => cfg.2.1 ≤ w.length + 1)
    ?_ hs (Nat.zero_le _)
  intro q i wh T q' mvI d mvW u hP hη
  have hP' : i ≤ w.length + 1 := hP
  show mvI.apply i ≤ w.length + 1
  cases hmv : mvI with
  | left =>
      simp only [Multihead.HeadMove.apply_left]
      omega
  | stay =>
      simp only [Multihead.HeadMove.apply_stay]
      exact hP'
  | right =>
      simp only [Multihead.HeadMove.apply_right]
      by_cases hle : i ≤ w.length
      · omega
      · exfalso
        have hrm : tapeSym w i = TapeSym.rmark := tapeSym_ge w i (by omega)
        rw [hrm] at hη
        exact M.rmark_no_right q _ _ _ hη hmv

/-- Every intermediate work-head position of a space-bounded run from the
initial configuration is bounded (every prefix is itself a run). -/
theorem wh_le_of_prefix {S : ℕ → ℕ} (hSB : SpaceBound M S) {w : List Alpha}
    {out : List Gamma} {e : M.Config} {N : ℕ}
    (hrun : M.StepsN w M.initConfig out e N) (i : ℕ) (hi : i ≤ N) :
    ∃ mid out₁ out₂, out = out₁ ++ out₂ ∧
      M.StepsN w M.initConfig out₁ mid i ∧ M.StepsN w mid out₂ e (N - i) ∧
      mid.2.2.1 ≤ S w.length := by
  obtain ⟨mid, o₁, o₂, ho, h₁, h₂⟩ := stepsN_split hrun i hi
  exact ⟨mid, o₁, o₂, ho, h₁, h₂, hSB w o₁ mid i h₁⟩

/-- **A space-bounded run never writes beyond cell `S(n)`**: the tape of every
configuration reached from the initial one is blank at every cell `> S(n)`. -/
theorem tape_blank_of_stepsN {S : ℕ → ℕ} (hSB : SpaceBound M S) {w : List Alpha} :
    ∀ {N : ℕ} {out : List Gamma} {e : M.Config},
      M.StepsN w M.initConfig out e N →
      ∀ k, S w.length < k → e.2.2.2 k = M.blank := by
  intro N
  induction N with
  | zero =>
      intro out e hrun k hk
      cases hrun
      rfl
  | succ N ih =>
      intro out e hrun k hk
      obtain ⟨mid, o₁, o₂, -, h₁, h₂⟩ := stepsN_split hrun N (by omega)
      rw [show N + 1 - N = 1 from by omega] at h₂
      obtain ⟨mq, mi, mwh, mT⟩ := mid
      have hwh : mwh ≤ S w.length := hSB w o₁ (mq, mi, mwh, mT) N h₁
      have hmid : mT k = M.blank := ih h₁ k hk
      -- invert the single step
      cases h₂ with
      | head hη rest =>
          cases rest with
          | refl =>
              show Function.update mT mwh _ k = M.blank
              rw [Function.update_of_ne (by omega)]
              exact hmid

/-! ## The generic polynomial halting bound -/

/-- **A halting space-bounded run never repeats a configuration**, and every
visited configuration lies in a space of size
`|Q| · (n+2) · (S+1) · |Δ|^(S+1)` (state, input head, work head, and the
tape restricted to the first `S+1` cells — beyond them it is blank).  Hence
the run length is below that product. -/
theorem halting_length_le {S : ℕ → ℕ} (hSB : SpaceBound M S) {w : List Alpha}
    {out : List Gamma} {e : M.Config} {N : ℕ}
    (hrun : M.StepsN w M.initConfig out e N) (hhalt : M.Halted w e) :
    N < M.cardQ * (w.length + 2) * (S w.length + 1) *
      M.cardDelta ^ (S w.length + 1) := by
  let _ : Fintype M.Q := M.fintypeQ
  let _ : Fintype M.Delta := M.fintypeDelta
  have hspec : ∀ i : Fin (N + 1), ∃ mid : M.Config,
      (∃ out₁, M.StepsN w M.initConfig out₁ mid i.val) ∧
      (∃ out₂, M.StepsN w mid out₂ e (N - i.val)) := by
    intro i
    obtain ⟨mid, o₁, o₂, -, h₁, h₂⟩ :=
      stepsN_split hrun i.val (Nat.lt_succ_iff.mp i.isLt)
    exact ⟨mid, ⟨o₁, h₁⟩, ⟨o₂, h₂⟩⟩
  choose T hT₁ hT₂ using hspec
  have hinj : Function.Injective T := by
    intro i j hij
    obtain ⟨o₂, h₂i⟩ := hT₂ i
    obtain ⟨o₂', h₂j⟩ := hT₂ j
    rw [hij] at h₂i
    have hlen := (stepsN_unique h₂i hhalt h₂j hhalt).2.2
    have hi := i.isLt
    have hj := j.isLt
    exact Fin.ext (by omega)
  have hbound : ∀ i : Fin (N + 1), (T i).2.1 ≤ w.length + 1 ∧
      (T i).2.2.1 ≤ S w.length ∧
      ∀ k, S w.length < k → (T i).2.2.2 k = M.blank := by
    intro i
    obtain ⟨o₁, h₁⟩ := hT₁ i
    exact ⟨head_le_of_stepsN h₁, hSB w o₁ (T i) i.val h₁,
      tape_blank_of_stepsN hSB h₁⟩
  -- inject the visit times into the finite configuration space
  have hcard := Fintype.card_le_of_injective
    (β := M.Q × Fin (w.length + 2) × Fin (S w.length + 1) ×
      (Fin (S w.length + 1) → M.Delta))
    (fun i => ((T i).1,
      ⟨(T i).2.1, Nat.lt_succ_of_le (hbound i).1⟩,
      ⟨(T i).2.2.1, Nat.lt_succ_of_le (hbound i).2.1⟩,
      fun k => (T i).2.2.2 k.val))
    (by
      intro i j hij
      apply hinj
      have h1 : (T i).1 = (T j).1 := congrArg (fun p => p.1) hij
      have h2 : (T i).2.1 = (T j).2.1 :=
        congrArg (fun p => (p.2.1 : Fin (w.length + 2)).val) hij
      have h3 : (T i).2.2.1 = (T j).2.2.1 :=
        congrArg (fun p => (p.2.2.1 : Fin (S w.length + 1)).val) hij
      have h4 : (T i).2.2.2 = (T j).2.2.2 := by
        funext k
        by_cases hk : k ≤ S w.length
        · exact congrFun (congrArg (fun p => p.2.2.2) hij) ⟨k, by omega⟩
        · rw [(hbound i).2.2 k (by omega), (hbound j).2.2 k (by omega)]
      have hTi : T i = ((T i).1, (T i).2.1, (T i).2.2.1, (T i).2.2.2) := rfl
      have hTj : T j = ((T j).1, (T j).2.1, (T j).2.2.1, (T j).2.2.2) := rfl
      rw [hTi, hTj, h1, h2, h3, h4])
  rw [Fintype.card_fin] at hcard
  have hβ : Fintype.card (M.Q × Fin (w.length + 2) × Fin (S w.length + 1) ×
      (Fin (S w.length + 1) → M.Delta))
      = Fintype.card M.Q * ((w.length + 2) * ((S w.length + 1) *
        Fintype.card M.Delta ^ (S w.length + 1))) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [hβ] at hcard
  show N < Fintype.card M.Q * (w.length + 2) * (S w.length + 1) *
    Fintype.card M.Delta ^ (S w.length + 1)
  calc N < N + 1 := by omega
    _ ≤ _ := by
        rw [mul_assoc, mul_assoc]
        exact hcard

/-! ## The polynomial packaging of the halting bound -/

/-- `A^(C·(⌊log₂(n+2)⌋+1)+1)` is polynomially bounded in `n`:
`≤ (2(n+2))^k` for `k = (⌊log₂(A+1)⌋+1)·(C+1)`. -/
theorem pow_log_poly_bound (A C : ℕ) :
    ∀ n : ℕ, A ^ (C * (Nat.log 2 (n + 2) + 1) + 1) ≤
      (2 * (n + 2)) ^ ((Nat.log 2 (A + 1) + 1) * (C + 1)) := by
  intro n
  set L := Nat.log 2 (n + 2) with hL
  set a := Nat.log 2 (A + 1) with ha
  -- `A < 2^(a+1)`
  have hA : A < 2 ^ (a + 1) := by
    have h := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (A + 1)
    rw [← ha] at h
    omega
  -- `2^L ≤ n + 2`
  have h2L : 2 ^ L ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  calc A ^ (C * (L + 1) + 1)
      ≤ (2 ^ (a + 1)) ^ (C * (L + 1) + 1) :=
        Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ ((a + 1) * (C * (L + 1) + 1)) := by rw [← pow_mul]
    _ ≤ 2 ^ ((L + 1) * ((a + 1) * (C + 1))) := by
        apply Nat.pow_le_pow_right (by omega)
        have h5 : (a + 1) * (C * (L + 1) + 1) = (a + 1) * C * (L + 1) + (a + 1) := by
          ring
        have h6 : (L + 1) * ((a + 1) * (C + 1))
            = (a + 1) * C * (L + 1) + (a + 1) * (L + 1) := by
          ring
        have h7 : (a + 1) ≤ (a + 1) * (L + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        omega
    _ = (2 ^ (L + 1)) ^ ((a + 1) * (C + 1)) := by rw [← pow_mul]
    _ ≤ (2 * (n + 2)) ^ ((a + 1) * (C + 1)) := by
        apply Nat.pow_le_pow_left
        calc 2 ^ (L + 1) = 2 * 2 ^ L := by ring
          _ ≤ 2 * (n + 2) := by omega

/-- **The paper's polynomial-time clause, generically in the worktape
model**: a logspace-bounded machine halts (when it halts) within
`D · (n+2)^k` steps, for constants `D, k` of the machine. -/
theorem halting_length_poly {M : LogTM Alpha Gamma} {C : ℕ}
    (hSB : SpaceBound M (fun n => C * (Nat.log 2 (n + 2) + 1))) :
    ∃ D k : ℕ, ∀ {w : List Alpha} {out : List Gamma} {e : M.Config} {N : ℕ},
      M.StepsN w M.initConfig out e N → M.Halted w e →
      N < D * (w.length + 2) ^ k := by
  refine ⟨M.cardQ * (2 * (C + 1)) *
      2 ^ ((Nat.log 2 (M.cardDelta + 1) + 1) * (C + 1)) + 1,
    2 + (Nat.log 2 (M.cardDelta + 1) + 1) * (C + 1), ?_⟩
  intro w out e N hrun hhalt
  set n := w.length with hn
  have h1 := halting_length_le hSB hrun hhalt
  set S := C * (Nat.log 2 (n + 2) + 1) with hS
  have h2 : M.cardDelta ^ (S + 1) ≤
      (2 * (n + 2)) ^ ((Nat.log 2 (M.cardDelta + 1) + 1) * (C + 1)) :=
    pow_log_poly_bound M.cardDelta C n
  set k1 := (Nat.log 2 (M.cardDelta + 1) + 1) * (C + 1) with hk1
  have h3 : (2 * (n + 2)) ^ k1 = 2 ^ k1 * (n + 2) ^ k1 := by
    rw [mul_pow]
  have h4 : S + 1 ≤ 2 * (C + 1) * (n + 2) := by
    have hlog : Nat.log 2 (n + 2) ≤ n + 2 := Nat.log_le_self 2 (n + 2)
    rw [hS]
    nlinarith
  calc N < M.cardQ * (n + 2) * (S + 1) * M.cardDelta ^ (S + 1) := h1
    _ ≤ M.cardQ * (n + 2) * (2 * (C + 1) * (n + 2)) * (2 ^ k1 * (n + 2) ^ k1) := by
        apply Nat.mul_le_mul
        · apply Nat.mul_le_mul_left
          exact h4
        · rw [← h3]; exact h2
    _ = M.cardQ * (2 * (C + 1)) * 2 ^ k1 * (n + 2) ^ (2 + k1) := by ring
    _ < (M.cardQ * (2 * (C + 1)) * 2 ^ k1 + 1) * (n + 2) ^ (2 + k1) := by
        have hpow : 0 < (n + 2) ^ (2 + k1) := Nat.pow_pos (by omega)
        nlinarith

end LogTM

end LogspaceTM
