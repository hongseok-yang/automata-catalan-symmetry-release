/-
# Deterministic two-way finite-state transducers (`def:2dft`, `def:2dft-run`)

Formalisation of the revision's machine model of word-to-word computation
("A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry", paper-full-new.tex):

* `def:2dft` (line 781): a 2DFT `T = (Q, Σ, Γ, q₀, F, η)` with a **partial
  transition-output function**
  `η : Q × (Σ ∪ {⊢,⊣}) ⇀ Q × {-1,+1} × Γ^*`
  and the **end-marker discipline** — a transition from `⊢`, if defined,
  moves right, and a transition from `⊣`, if defined, moves left.  We encode
  the direction set `{-1,+1}` as `Bool` (`true = +1`, `false = -1`) and the
  tape alphabet `Σ ∪ {⊢,⊣}` as `TapeSym`.

* `def:2dft-run` (line 798): for `w = a₁⋯a_n` put `a₀ = ⊢`, `a_{n+1} = ⊣`
  (`tapeSym`); a configuration is a pair `(q, i)`; the run is the unique
  maximal step sequence from `(q₀, 0)`; a finite run halts where `η` is
  undefined (`Halted`), is accepting if the halting state is in `F`, and then
  outputs the concatenation of the emitted words.  `Steps` is the
  reflexive-transitive step relation with accumulated emission, and
  `Computes w out` says the (unique) maximal run halts acceptingly with
  output `out`.

Determinism ("Because `η` is a function, every configuration has at most one
successor, so the maximal run is unique") is `steps_unique` / `computes_unique`.

`LeftToRight` is the head condition of the revision's `thm:wrp-not-closed`
("a deterministic 2DFT `S` whose input head moves only from left to right",
line 1677); `steps_scan` evaluates such sweeps: a state that self-loops
rightward across a segment of letters emits the concatenation of its
per-letter emissions.
-/
import RequestProject.Transducers

namespace TwoDFT

/-- The tape alphabet `Σ ∪ {⊢, ⊣}` of `def:2dft`. -/
inductive TapeSym (Alpha : Type*)
  | lmark
  | letter (a : Alpha)
  | rmark
  deriving DecidableEq

end TwoDFT

open TwoDFT in
/-- **Definition (`def:2dft`, paper-full-new.tex).**  A deterministic
two-way finite-state transducer: finite states, initial state, accepting
states, and a partial transition-output function subject to the end-marker
discipline.  Direction encoding: `true = +1` (right), `false = -1` (left). -/
structure TwoDFT (Alpha Gamma : Type*) where
  Q : Type
  fintypeQ : Fintype Q
  q0 : Q
  F : Q → Prop
  η : Q → TapeSym Alpha → Option (Q × Bool × List Gamma)
  /-- End-marker discipline: a transition from `⊢`, if defined, moves right. -/
  lmark_right : ∀ q q' d u, η q .lmark = some (q', d, u) → d = true
  /-- End-marker discipline: a transition from `⊣`, if defined, moves left. -/
  rmark_left : ∀ q q' d u, η q .rmark = some (q', d, u) → d = false

namespace TwoDFT

variable {Alpha Gamma : Type*}

/-- Head movement: one step right (`true = +1`) or left (`false = -1`). -/
def moveDir (i : ℕ) (d : Bool) : ℕ := if d then i + 1 else i - 1

@[simp] theorem moveDir_true (i : ℕ) : moveDir i true = i + 1 := rfl
@[simp] theorem moveDir_false (i : ℕ) : moveDir i false = i - 1 := rfl

/-- The tape content of `def:2dft-run`: `a₀ = ⊢`, `a_i = w_i` for
`1 ≤ i ≤ n`, and `a_i = ⊣` for `i > n` (only `i = n + 1` is reachable). -/
def tapeSym (w : List Alpha) (i : ℕ) : TapeSym Alpha :=
  if i = 0 then .lmark
  else if h : i - 1 < w.length then .letter w[i - 1] else .rmark

@[simp] theorem tapeSym_zero (w : List Alpha) : tapeSym w 0 = .lmark := rfl

theorem tapeSym_succ (w : List Alpha) (k : ℕ) (h : k < w.length) :
    tapeSym w (k + 1) = .letter w[k] := by
  unfold tapeSym
  rw [if_neg (Nat.succ_ne_zero k), dif_pos (by simpa using h)]
  simp

theorem tapeSym_ge (w : List Alpha) (i : ℕ) (h : w.length < i) :
    tapeSym w i = .rmark := by
  unfold tapeSym
  rw [if_neg (by omega), dif_neg (by omega)]

variable (T : TwoDFT Alpha Gamma)

/-- **The step relation of `def:2dft-run`**, with accumulated emission:
`Steps w c out c'` says the machine can go from configuration `c` to
configuration `c'` emitting `out` along the way.  (Since `η` is a function
this relation is deterministic; see `steps_unique`.) -/
inductive Steps (w : List Alpha) : T.Q × ℕ → List Gamma → T.Q × ℕ → Prop
  | refl (c : T.Q × ℕ) : Steps w c [] c
  | head {q : T.Q} {i : ℕ} {q' : T.Q} {d : Bool} {u out : List Gamma} {e : T.Q × ℕ} :
      T.η q (tapeSym w i) = some (q', d, u) →
      Steps w (q', moveDir i d) out e →
      Steps w (q, i) (u ++ out) e

/-- A configuration on which `η` is undefined: the run halts there. -/
def Halted (w : List Alpha) (c : T.Q × ℕ) : Prop :=
  T.η c.1 (tapeSym w c.2) = none

/-- **The computed partial map of `def:2dft-run`**: the maximal run from
`(q₀, 0)` is finite, halts acceptingly, and the emitted words concatenate to
`out`. -/
def Computes (w : List Alpha) (out : List Gamma) : Prop :=
  ∃ c : T.Q × ℕ, T.Steps w (T.q0, 0) out c ∧ T.Halted w c ∧ T.F c.1

/-- The head condition of the revision's `thm:wrp-not-closed`: every defined
transition moves right. -/
def LeftToRight : Prop :=
  ∀ q s r, T.η q s = some r → r.2.1 = true

variable {T}

/-- A configuration with a defined transition has not halted. -/
theorem not_halted_of_step {w : List Alpha} {q : T.Q} {i : ℕ}
    {r : T.Q × Bool × List Gamma}
    (hη : T.η q (tapeSym w i) = some r) : ¬ T.Halted w (q, i) := by
  intro hh
  have hnone : T.η q (tapeSym w i) = none := hh
  rw [hnone] at hη
  simp at hη

/-- Transitivity of the step relation, concatenating emissions. -/
theorem Steps.trans {w : List Alpha} : ∀ {c₁ c₂ c₃ : T.Q × ℕ} {o₁ o₂ : List Gamma},
    T.Steps w c₁ o₁ c₂ → T.Steps w c₂ o₂ c₃ → T.Steps w c₁ (o₁ ++ o₂) c₃ := by
  intro c₁ c₂ c₃ o₁ o₂ h₁
  induction h₁ with
  | refl c => intro h₂; simpa using h₂
  | head hη _ ih =>
      intro h₂
      rw [List.append_assoc]
      exact Steps.head hη (ih h₂)

/-- **Determinism (`def:2dft-run`): the maximal run is unique.**  Two halting
runs from the same configuration have the same emission and the same halting
configuration. -/
theorem steps_unique {w : List Alpha} : ∀ {c : T.Q × ℕ} {out₁ out₂ : List Gamma}
    {e₁ e₂ : T.Q × ℕ},
    T.Steps w c out₁ e₁ → T.Halted w e₁ →
    T.Steps w c out₂ e₂ → T.Halted w e₂ →
    out₁ = out₂ ∧ e₁ = e₂ := by
  intro c out₁ out₂ e₁ e₂ h₁
  induction h₁ generalizing out₂ e₂ with
  | refl c =>
      intro halt₁ h₂ halt₂
      cases h₂ with
      | refl => exact ⟨rfl, rfl⟩
      | head hη _ => exact absurd halt₁ (not_halted_of_step hη)
  | head hη rest ih =>
      intro halt₁ h₂ halt₂
      cases h₂ with
      | refl => exact absurd halt₂ (not_halted_of_step hη)
      | head hη' rest' =>
          rw [hη] at hη'
          injection hη' with htriple
          injection htriple with hq hrest
          injection hrest with hd hu
          subst hq; subst hd; subst hu
          obtain ⟨ho, he⟩ := ih halt₁ rest' halt₂
          exact ⟨by rw [ho], he⟩


/-- The computed map is a partial function. -/
theorem computes_unique {w : List Alpha} {out₁ out₂ : List Gamma}
    (h₁ : T.Computes w out₁) (h₂ : T.Computes w out₂) : out₁ = out₂ := by
  obtain ⟨c₁, hs₁, hh₁, -⟩ := h₁
  obtain ⟨c₂, hs₂, hh₂, -⟩ := h₂
  exact (steps_unique hs₁ hh₁ hs₂ hh₂).1

/-- **One-way scanning.**  If state `q` self-loops rightward on every letter
of a segment `l`, emitting `em a` on each `a`, and the tape cells
`i, i+1, …, i+|l|-1` hold the letters of `l`, then the machine sweeps the
segment from `(q, i)` to `(q, i + |l|)` emitting `l.flatMap em`. -/
theorem steps_scan {w : List Alpha} {q : T.Q} {em : Alpha → List Gamma}
    (l : List Alpha) (i : ℕ)
    (hcells : ∀ k, (hk : k < l.length) → tapeSym w (i + k) = TapeSym.letter l[k])
    (hloop : ∀ a ∈ l, T.η q (TapeSym.letter a) = some (q, true, em a)) :
    T.Steps w (q, i) (l.flatMap em) (q, i + l.length) := by
  induction l generalizing i with
  | nil => simpa using Steps.refl (T := T) (w := w) (q, i)
  | cons a t ih =>
      have hcell0 : tapeSym w i = TapeSym.letter a := by
        have h := hcells 0 (by simp)
        rw [List.getElem_cons_zero] at h
        simpa using h
      have hstep : T.η q (tapeSym w i) = some (q, true, em a) := by
        rw [hcell0]
        exact hloop a List.mem_cons_self
      have hrest : T.Steps w (q, i + 1) (t.flatMap em) (q, (i + 1) + t.length) := by
        refine ih (i + 1) (fun k hk => ?_) (fun a' ha' => hloop a' (List.mem_cons_of_mem _ ha'))
        have h := hcells (k + 1) (by simpa using Nat.succ_lt_succ hk)
        rw [show i + (k + 1) = (i + 1) + k by omega] at h
        simpa using h
      have h := Steps.head (T := T) hstep hrest
      rw [show (i + 1) + t.length = i + (a :: t).length by simp; omega] at h
      simpa using h

end TwoDFT
