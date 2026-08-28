/-
# Existential closure of MSO formulas and finite disjunctions

To feed the textbook Büchi axiom (`SliceMSO.buchi`, stated for *sentences*) the
selection/label conditions of a polyregular presentation — which are MSO formulas
with `arity c` free first-order variables — we need to turn a `Formula Alpha k 0`
into a `Sentence Alpha` whose language is the **existential closure** of the
relation: "there is a valid tuple of positions satisfying the formula".

This is done with plain iterated `exFO` — *no* second-order encoding and *no* new
axiom.  (Crucially, the existential closure answers an EXISTENCE question, e.g.
"does the slice contain a selected `D`-atom"; it does **not** expose a per-position
selection bit, which would require a marked alphabet / forward-backward product.)

We also provide a finite disjunction `bigOr` over a list of sentences, used to
range existence over the finitely many copies of a presentation.

Everything here is proved from the MSO definitions only; `#print axioms` of the
results shows no `sorryAx` and no new axiom.
-/
import RequestProject.MSO

namespace MSO.Formula

variable {Alpha : Type*}

/-- Close all `k` free first-order variables by existential quantification,
yielding a sentence. -/
def closeAllFO : {k : ℕ} → Formula Alpha k 0 → Sentence Alpha
  | 0, φ => φ
  | (_ + 1), φ => closeAllFO (exFO φ)

/-- **Correctness of the existential closure.**  The closed sentence holds on `w`
iff there is a tuple of valid positions satisfying the original formula. -/
theorem sat_closeAllFO : ∀ {k : ℕ} (φ : Formula Alpha k 0) (w : List Alpha),
    (closeAllFO φ).Sat w Fin.elim0 Fin.elim0 ↔
      ∃ ρ : Fin k → ℕ, (∀ t, ρ t < w.length) ∧ φ.Sat w ρ Fin.elim0
  | 0, φ, w => by
      constructor
      · intro h
        exact ⟨Fin.elim0, fun t => t.elim0, h⟩
      · rintro ⟨ρ, _, h⟩
        have hρ0 : ρ = Fin.elim0 := funext (fun t : Fin 0 => t.elim0)
        rwa [hρ0] at h
  | (k + 1), φ, w => by
      refine (sat_closeAllFO (exFO φ) w).trans ?_
      simp only [sat_exFO]
      constructor
      · rintro ⟨ρ, hρ, p, hp, hsat⟩
        refine ⟨Fin.cons p ρ, fun t => ?_, hsat⟩
        refine Fin.cases ?_ ?_ t
        · simpa using hp
        · intro i; simpa using hρ i
      · rintro ⟨ρ', hρ', hsat⟩
        refine ⟨Fin.tail ρ', fun t => hρ' t.succ, ρ' 0, hρ' 0, ?_⟩
        rwa [Fin.cons_self_tail ρ']

/-- Finite disjunction of a list of sentences (`False` on the empty list). -/
def bigOr : List (Sentence Alpha) → Sentence Alpha
  | [] => .neg .tru
  | φ :: φs => .or φ (bigOr φs)

@[simp] theorem sat_bigOr (w : List Alpha) :
    ∀ (φs : List (Sentence Alpha)),
      (bigOr φs).Sat w Fin.elim0 Fin.elim0 ↔ ∃ φ ∈ φs, φ.Sat w Fin.elim0 Fin.elim0
  | [] => by simp [bigOr, Sat]
  | φ :: φs => by
      simp only [bigOr, sat_or, sat_bigOr w φs, List.mem_cons]
      constructor
      · rintro (h | ⟨ψ, hψ, hsat⟩)
        · exact ⟨φ, Or.inl rfl, h⟩
        · exact ⟨ψ, Or.inr hψ, hsat⟩
      · rintro ⟨ψ, (rfl | hψ), hsat⟩
        · exact Or.inl hsat
        · exact Or.inr ⟨ψ, hψ, hsat⟩

/-- Disjunction over a finite index type via `List.finRange`. -/
def bigOrFin {K : ℕ} (f : Fin K → Sentence Alpha) : Sentence Alpha :=
  bigOr ((List.finRange K).map f)

theorem sat_bigOrFin {K : ℕ} (f : Fin K → Sentence Alpha) (w : List Alpha) :
    (bigOrFin f).Sat w Fin.elim0 Fin.elim0 ↔ ∃ c : Fin K, (f c).Sat w Fin.elim0 Fin.elim0 := by
  simp only [bigOrFin, sat_bigOr, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨φ, ⟨c, rfl⟩, hsat⟩; exact ⟨c, hsat⟩
  · rintro ⟨c, hsat⟩; exact ⟨f c, ⟨c, rfl⟩, hsat⟩

end MSO.Formula
