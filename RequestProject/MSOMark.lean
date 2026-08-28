/-
# Marked-alphabet recogniser for a one-free-variable MSO formula (no new axiom)

The selection-*counting* half of the paper's slice analysis
(`sec:slice-semilinearity`) needs, for a unary MSO predicate
`φ(x)`, a finite automaton that decides `φ(p)` from the word `w` with position `p`
marked.  Crucially this needs **no** new axiom: the existing `SliceMSO.buchi` is
polymorphic in the alphabet, so we instantiate it at `Step × Bool`.

The only ingredient is a syntactic relabeling `markTr : Formula Step nf ns →
Formula (Step × Bool) nf ns` that ignores the mark bit (each `Q_a(x)` becomes
"`x` carries letter `a` with either mark"); its correctness `markTr_sat` is a
clean induction (only `labelEq` changes; positions, sets and lengths are
preserved by `List.map Prod.fst`).  Wrapping `markTr φ` with "the free variable is
the marked position" and closing it gives a **sentence** over `Step × Bool` whose
language, restricted to single-mark words `markAt w p`, is exactly `φ(p)`.

`markedDFA_exists` then feeds that sentence to `buchi`.  `#print axioms` shows only
`[propext, Classical.choice, Quot.sound, SliceMSO.buchi]` — no new axiom.
-/
import RequestProject.MSO
import RequestProject.SliceMSO
import RequestProject.DyckPath

open MSO Step

namespace MSO.Formula

variable {Alpha : Type*}

/-- Relabel a formula over `Alpha` to one over `Alpha × Bool` that ignores the mark
bit: `Q_a(x_i)` becomes "the letter at `x_i` is `(a, true)` or `(a, false)`". -/
def markTr : {nf ns : ℕ} → Formula Alpha nf ns → Formula (Alpha × Bool) nf ns
  | _, _, .lt i j => .lt i j
  | _, _, .labelEq i a => .or (.labelEq i (a, true)) (.labelEq i (a, false))
  | _, _, .mem i j => .mem i j
  | _, _, .tru => .tru
  | _, _, .neg φ => .neg (markTr φ)
  | _, _, .and φ ψ => .and (markTr φ) (markTr ψ)
  | _, _, .or φ ψ => .or (markTr φ) (markTr ψ)
  | _, _, .exFO φ => .exFO (markTr φ)
  | _, _, .exSO φ => .exSO (markTr φ)

/-- **Correctness of `markTr`.**  Over a marked word `u`, `markTr φ` holds exactly
when `φ` holds over the underlying (mark-stripped) word `u.map Prod.fst`. -/
theorem markTr_sat (u : List (Alpha × Bool)) :
    ∀ {nf ns : ℕ} (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ) (φ : Formula Alpha nf ns),
      (markTr φ).Sat u ρ σ ↔ φ.Sat (u.map Prod.fst) ρ σ
  | _, _, ρ, σ, .lt i j => Iff.rfl
  | _, _, ρ, σ, .labelEq i a => by
      simp only [markTr, sat_or, sat_labelEq, List.getElem?_map]
      rcases h : u[ρ i]? with _ | ⟨x, b⟩
      · simp
      · cases b <;> simp [Prod.ext_iff]
  | _, _, ρ, σ, .mem i j => Iff.rfl
  | _, _, ρ, σ, .tru => Iff.rfl
  | _, _, ρ, σ, .neg φ => by simp only [markTr, sat_neg, markTr_sat u ρ σ φ]
  | _, _, ρ, σ, .and φ ψ => by
      simp only [markTr, sat_and, markTr_sat u ρ σ φ, markTr_sat u ρ σ ψ]
  | _, _, ρ, σ, .or φ ψ => by
      simp only [markTr, sat_or, markTr_sat u ρ σ φ, markTr_sat u ρ σ ψ]
  | _, _, ρ, σ, .exFO φ => by
      simp only [markTr, sat_exFO, List.length_map]
      exact exists_congr (fun p => and_congr_right (fun _ => markTr_sat u (Fin.cons p ρ) σ φ))
  | _, _, ρ, σ, .exSO φ => by
      simp only [markTr, sat_exSO, List.length_map]
      exact exists_congr (fun S => and_congr_right (fun _ => markTr_sat u ρ (Fin.cons S σ) φ))

end MSO.Formula

namespace MSOMark

open MSO.Formula

/-- The word `w` with exactly position `p` marked. -/
def markAt (w : List Step) (p : ℕ) : List (Step × Bool) :=
  List.ofFn (fun j : Fin w.length => (w[j], decide (j.val = p)))

@[simp] theorem markAt_length (w : List Step) (p : ℕ) : (markAt w p).length = w.length := by
  simp [markAt]

@[simp] theorem markAt_map_fst (w : List Step) (p : ℕ) : (markAt w p).map Prod.fst = w := by
  simp only [markAt, List.map_ofFn]
  exact List.ofFn_getElem

theorem markAt_getElem? (w : List Step) (p x : ℕ) (hx : x < w.length) :
    (markAt w p)[x]? = some (w[x], decide (x = p)) := by
  rw [markAt, List.getElem?_ofFn]
  simp [hx]

/-- "The letter at `x_0` carries a `true` mark" (`Step` being two-element, an
explicit disjunction). -/
def markedHere : Formula (Step × Bool) 1 0 :=
  .or (.labelEq 0 (U, true)) (.labelEq 0 (D, true))

theorem step_eq_U_or_D (s : Step) : s = U ∨ s = D := by cases s <;> simp

theorem markedHere_sat_markAt (w : List Step) (p x : ℕ) (hx : x < w.length) :
    markedHere.Sat (markAt w p) (Fin.cons x Fin.elim0) Fin.elim0 ↔ x = p := by
  simp only [markedHere, sat_or, sat_labelEq, Fin.cons_zero, markAt_getElem? w p x hx]
  constructor
  · rintro (h | h) <;> (rw [Option.some.injEq, Prod.ext_iff] at h; exact decide_eq_true_iff.mp h.2)
  · intro hxp
    subst hxp
    rcases step_eq_U_or_D w[x] with h | h <;> simp [h]

/-- The sentence over `Step × Bool` whose language, restricted to single-mark words
`markAt w p`, is exactly `φ(p)`. -/
def markedSentence (φ : Formula Step 1 0) : MSO.Sentence (Step × Bool) :=
  .exFO (.and markedHere (markTr φ))

theorem sat_markedSentence (φ : Formula Step 1 0) (w : List Step) (p : ℕ) (hp : p < w.length) :
    (markedSentence φ).Sat (markAt w p) Fin.elim0 Fin.elim0 ↔
      φ.Sat w (fun _ => p) Fin.elim0 := by
  simp only [markedSentence, sat_exFO, sat_and, markAt_length]
  constructor
  · rintro ⟨x, hx, hmark, hsat⟩
    have hxp : x = p := (markedHere_sat_markAt w p x hx).mp hmark
    rw [markTr_sat, markAt_map_fst] at hsat
    have hcons : (Fin.cons x Fin.elim0 : Fin 1 → ℕ) = fun _ => p := by
      funext t; fin_cases t; simpa using hxp
    rwa [hcons] at hsat
  · intro hsat
    refine ⟨p, hp, (markedHere_sat_markAt w p p hp).mpr rfl, ?_⟩
    rw [markTr_sat, markAt_map_fst]
    have hcons : (Fin.cons p Fin.elim0 : Fin 1 → ℕ) = fun _ => p := by
      funext t; fin_cases t; rfl
    rwa [hcons]

/-- **The marked recogniser (no new axiom).**  For a unary MSO formula `φ` over
`Step`, there is a deterministic finite automaton over `Step × Bool` that accepts
the single-mark word `markAt w p` iff `φ` holds of position `p` in `w`. -/
theorem markedDFA_exists (φ : Formula Step 1 0) :
    ∃ M : SliceMSO.DetAuto (Step × Bool), ∀ (w : List Step) (p : ℕ), p < w.length →
      (M.accepts (markAt w p) ↔ φ.Sat w (fun _ => p) Fin.elim0) := by
  obtain ⟨M, hM⟩ := SliceMSO.buchi (markedSentence φ)
  exact ⟨M, fun w p hp => (hM (markAt w p)).trans (sat_markedSentence φ w p hp)⟩

end MSOMark
