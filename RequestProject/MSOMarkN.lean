/-
# `m`-mark recogniser for an `m`-free-variable MSO formula (no new axiom; route GA-1)

The general-arity §7 discharge (the GA route) decides per-atom MSO
predicates — selection, label, order — for atoms that are `m`-tuples of positions.  This
file generalises `MSOMark` (one mark) and `MSOMark2` (two marks) to `m` marks.

Design: the marked alphabet is the `m`-fold nest `MarkedN m = (((Step × Bool) × Bool)
× ⋯)`, with the `i`-th `Bool` track carrying the mark of variable `i`.  This lets the
unary relabelling `markTr` of `MSOMark` lift by ITERATION (`liftTrN`), so no new
translation is needed; the per-track "this position carries mark `i`" formulas
(`markedHereN`) are finite disjunctions over the (recursively enumerated) letters whose
`i`-th track is set.  Closing with `m` first-order existentials (`closeAllFO`) gives a
sentence over `MarkedN m` whose language, restricted to the `m`-mark words
`markAtN w ī`, is exactly `φ(ī)`; `markedDFAN_exists` feeds it to the
alphabet-polymorphic `SliceMSO.buchi`.

Multiple marks may land on one position (atom coordinates may coincide): the letter at a
position carries the full bit-vector of marks, so nothing special is needed.

`#print axioms` shows only `[propext, Classical.choice, Quot.sound, SliceMSO.buchi]`.
-/
import RequestProject.MSOMark

open MSO Step MSO.Formula MSOMark

namespace MSOMarkN

/-! ## The nested marked alphabet -/

/-- The `m`-track marked alphabet: `Step` with `m` nested `Bool` mark tracks
(track `i` is the `i`-th `Bool` from the inside). -/
@[reducible] def MarkedN : ℕ → Type
  | 0 => Step
  | (m + 1) => MarkedN m × Bool

/-- `MarkedN m` is a finite alphabet (so the finite-alphabet Büchi axiom applies). -/
instance instFintypeMarkedN : ∀ m, Fintype (MarkedN m)
  | 0 => inferInstanceAs (Fintype Step)
  | (m + 1) => @instFintypeProd _ _ (instFintypeMarkedN m) inferInstance

/-- Build a letter from a base step and its `m` mark bits. -/
def mkLetter : (m : ℕ) → Step → (Fin m → Bool) → MarkedN m
  | 0, s, _ => s
  | (m + 1), s, f => (mkLetter m s (f ∘ Fin.castSucc), f (Fin.last m))

/-- Read the `i`-th mark track of a letter. -/
def trackBit : (m : ℕ) → Fin m → MarkedN m → Bool
  | 0, i, _ => i.elim0
  | (m + 1), i, ℓ => Fin.lastCases ℓ.2 (fun i' => trackBit m i' ℓ.1) i

theorem trackBit_mkLetter :
    ∀ (m : ℕ) (i : Fin m) (s : Step) (f : Fin m → Bool),
      trackBit m i (mkLetter m s f) = f i
  | 0, i, _, _ => i.elim0
  | (m + 1), i, s, f => by
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · show trackBit (m + 1) (Fin.last m) (mkLetter m s (f ∘ Fin.castSucc), f (Fin.last m))
          = f (Fin.last m)
        simp [trackBit]
      · show trackBit (m + 1) (Fin.castSucc i')
            (mkLetter m s (f ∘ Fin.castSucc), f (Fin.last m)) = f (Fin.castSucc i')
        simp only [trackBit, Fin.lastCases_castSucc]
        exact trackBit_mkLetter m i' s (f ∘ Fin.castSucc)

/-- The (complete) list of letters of `MarkedN m`. -/
def lettersNM : (m : ℕ) → List (MarkedN m)
  | 0 => [U, D]
  | (m + 1) => (lettersNM m).flatMap (fun ℓ => [(ℓ, true), (ℓ, false)])

theorem mem_lettersNM : ∀ (m : ℕ) (ℓ : MarkedN m), ℓ ∈ lettersNM m
  | 0, ℓ => by
      have h0 : lettersNM 0 = [U, D] := rfl
      rw [h0]
      rcases step_eq_U_or_D ℓ with h | h <;> subst h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  | (m + 1), ℓ => by
      obtain ⟨ℓ', b⟩ := ℓ
      rw [lettersNM]
      refine List.mem_flatMap.mpr ⟨ℓ', mem_lettersNM m ℓ', ?_⟩
      cases b
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_self ..

/-! ## The `m`-mark word -/

/-- The word `w` with mark track `i` set exactly at position `ī i` (tracks may share a
position). -/
def markAtN (m : ℕ) (w : List Step) (ī : Fin m → ℕ) : List (MarkedN m) :=
  List.ofFn (fun j : Fin w.length => mkLetter m w[j] (fun i => decide (j.val = ī i)))

@[simp] theorem markAtN_length (m : ℕ) (w : List Step) (ī : Fin m → ℕ) :
    (markAtN m w ī).length = w.length := by simp [markAtN]

theorem markAtN_zero (w : List Step) (ī : Fin 0 → ℕ) : markAtN 0 w ī = w := by
  simp only [markAtN, mkLetter]
  exact List.ofFn_getElem

theorem markAtN_map_fst (m : ℕ) (w : List Step) (ī : Fin (m + 1) → ℕ) :
    (markAtN (m + 1) w ī).map Prod.fst = markAtN m w (ī ∘ Fin.castSucc) := by
  apply List.ext_getElem?
  intro i
  simp only [markAtN, List.getElem?_map, List.getElem?_ofFn]
  split_ifs with h
  · simp only [Option.map_some]
    rfl
  · simp only [Option.map_none]

theorem markAtN_getElem? (m : ℕ) (w : List Step) (ī : Fin m → ℕ) (x : ℕ)
    (hx : x < w.length) :
    (markAtN m w ī)[x]? = some (mkLetter m w[x] (fun i => decide (x = ī i))) := by
  rw [markAtN, List.getElem?_ofFn]
  simp [hx]

/-- Strip all mark tracks. -/
def stripAllN : (m : ℕ) → List (MarkedN m) → List Step
  | 0, u => u
  | (m + 1), u => stripAllN m (u.map Prod.fst)

theorem stripAllN_markAtN :
    ∀ (m : ℕ) (w : List Step) (ī : Fin m → ℕ), stripAllN m (markAtN m w ī) = w
  | 0, w, ī => markAtN_zero w ī
  | (m + 1), w, ī => by
      show stripAllN m ((markAtN (m + 1) w ī).map Prod.fst) = w
      rw [markAtN_map_fst]
      exact stripAllN_markAtN m w (ī ∘ Fin.castSucc)

/-! ## Lifting a formula to the marked alphabet -/

/-- Iterated `markTr`: lift a formula over `Step` to one over `MarkedN m` that ignores
all mark tracks. -/
def liftTrN : (m : ℕ) → {nf ns : ℕ} → Formula Step nf ns → Formula (MarkedN m) nf ns
  | 0, _, _, φ => φ
  | (m + 1), _, _, φ => markTr (liftTrN m φ)

theorem liftTrN_sat :
    ∀ (m : ℕ) {nf ns : ℕ} (φ : Formula Step nf ns) (u : List (MarkedN m))
      (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ),
      (liftTrN m φ).Sat u ρ σ ↔ φ.Sat (stripAllN m u) ρ σ
  | 0, _, _, φ, u, ρ, σ => Iff.rfl
  | (m + 1), _, _, φ, u, ρ, σ => by
      show (markTr (liftTrN m φ)).Sat u ρ σ ↔ _
      rw [markTr_sat]
      exact liftTrN_sat m φ (u.map Prod.fst) ρ σ

/-! ## Finite disjunction/conjunction and the first-order closure -/

/-- Finite disjunction of a list of formulas. -/
def orList {Alpha : Type*} {nf ns : ℕ} : List (Formula Alpha nf ns) → Formula Alpha nf ns
  | [] => .neg .tru
  | φ :: φs => .or φ (orList φs)

theorem sat_orList {Alpha : Type*} (w : List Alpha) {nf ns : ℕ} (ρ : Fin nf → ℕ)
    (σ : Fin ns → Finset ℕ) :
    ∀ φs : List (Formula Alpha nf ns),
      (orList φs).Sat w ρ σ ↔ ∃ φ ∈ φs, φ.Sat w ρ σ
  | [] => by simp [orList, Formula.Sat]
  | φ :: φs => by
      simp only [orList, Formula.sat_or, sat_orList w ρ σ φs, List.mem_cons]
      constructor
      · rintro (h | ⟨ψ, hψ, hsat⟩)
        · exact ⟨φ, Or.inl rfl, h⟩
        · exact ⟨ψ, Or.inr hψ, hsat⟩
      · rintro ⟨ψ, (rfl | hψ), hsat⟩
        · exact Or.inl hsat
        · exact Or.inr ⟨ψ, hψ, hsat⟩

/-- Finite conjunction of a list of formulas. -/
def andList {Alpha : Type*} {nf ns : ℕ} : List (Formula Alpha nf ns) → Formula Alpha nf ns
  | [] => .tru
  | φ :: φs => .and φ (andList φs)

theorem sat_andList {Alpha : Type*} (w : List Alpha) {nf ns : ℕ} (ρ : Fin nf → ℕ)
    (σ : Fin ns → Finset ℕ) :
    ∀ φs : List (Formula Alpha nf ns),
      (andList φs).Sat w ρ σ ↔ ∀ φ ∈ φs, φ.Sat w ρ σ
  | [] => by simp [andList]
  | φ :: φs => by simp [andList, sat_andList w ρ σ φs]

/-- Close all `k` free first-order variables by existential quantification. -/
def closeAllFO {Alpha : Type*} : {k : ℕ} → Formula Alpha k 0 → Formula Alpha 0 0
  | 0, φ => φ
  | (_ + 1), φ => closeAllFO (.exFO φ)

theorem sat_closeAllFO {Alpha : Type*} :
    ∀ {k : ℕ} (φ : Formula Alpha k 0) (w : List Alpha),
      (closeAllFO φ).Sat w Fin.elim0 Fin.elim0 ↔
        ∃ ρ : Fin k → ℕ, (∀ t, ρ t < w.length) ∧ φ.Sat w ρ Fin.elim0
  | 0, φ, w => by
      constructor
      · intro h
        exact ⟨Fin.elim0, fun t => t.elim0, h⟩
      · rintro ⟨ρ, _, h⟩
        have : ρ = Fin.elim0 := funext (fun t : Fin 0 => t.elim0)
        rwa [this] at h
  | (k + 1), φ, w => by
      refine (sat_closeAllFO (.exFO φ) w).trans ?_
      simp only [Formula.sat_exFO]
      constructor
      · rintro ⟨ρ', hρ', p, hp, hsat⟩
        refine ⟨Fin.cons p ρ', fun t => ?_, hsat⟩
        refine Fin.cases ?_ ?_ t
        · simpa using hp
        · intro i; simpa using hρ' i
      · rintro ⟨ρ, hρ, hsat⟩
        refine ⟨Fin.tail ρ, fun t => hρ t.succ, ρ 0, hρ 0, ?_⟩
        rwa [Fin.cons_self_tail ρ]

/-! ## The mark-pinning formulas and the marked sentence -/

/-- "The letter at `x_i` carries the `i`-th mark track" (a finite disjunction over the
letters whose `i`-th track is set). -/
def markedHereN (m : ℕ) (i : Fin m) : Formula (MarkedN m) m 0 :=
  orList (((lettersNM m).filter (fun ℓ => trackBit m i ℓ)).map (Formula.labelEq i))

theorem markedHereN_sat (m : ℕ) (i : Fin m) (w : List Step) (ī ρ : Fin m → ℕ)
    (hx : ρ i < w.length) :
    (markedHereN m i).Sat (markAtN m w ī) ρ Fin.elim0 ↔ ρ i = ī i := by
  have hget := markAtN_getElem? m w ī (ρ i) hx
  rw [markedHereN, sat_orList]
  constructor
  · rintro ⟨ψ, hψ, hsat⟩
    obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hψ
    rw [List.mem_filter] at hℓ
    rw [Formula.sat_labelEq, hget, Option.some.injEq] at hsat
    have htrack := hℓ.2
    rw [← hsat, trackBit_mkLetter] at htrack
    exact of_decide_eq_true htrack
  · intro heq
    refine ⟨Formula.labelEq i (mkLetter m w[ρ i] (fun t => decide (ρ i = ī t))),
      List.mem_map_of_mem ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨mem_lettersNM m _, ?_⟩
      rw [trackBit_mkLetter]
      exact decide_eq_true heq
    · rw [Formula.sat_labelEq, hget]

/-- The sentence over `MarkedN m` whose language, restricted to `m`-mark words
`markAtN m w ī`, is exactly `φ(ī)`. -/
def markedSentenceN (m : ℕ) (φ : Formula Step m 0) : MSO.Sentence (MarkedN m) :=
  closeAllFO (.and (andList ((List.finRange m).map (markedHereN m))) (liftTrN m φ))

theorem sat_markedSentenceN (m : ℕ) (φ : Formula Step m 0) (w : List Step)
    (ī : Fin m → ℕ) (hī : ∀ i, ī i < w.length) :
    (markedSentenceN m φ).Sat (markAtN m w ī) Fin.elim0 Fin.elim0 ↔
      φ.Sat w ī Fin.elim0 := by
  rw [markedSentenceN, sat_closeAllFO]
  constructor
  · rintro ⟨ρ, hbound, hsat⟩
    rw [Formula.sat_and] at hsat
    obtain ⟨hmarks, hlift⟩ := hsat
    have hρ : ρ = ī := by
      funext i
      have h := (sat_andList _ _ _ _).mp hmarks (markedHereN m i)
        (List.mem_map_of_mem (List.mem_finRange i))
      exact (markedHereN_sat m i w ī ρ (by have := hbound i; rwa [markAtN_length] at this)).mp h
    rw [hρ, liftTrN_sat, stripAllN_markAtN] at hlift
    exact hlift
  · intro hsat
    refine ⟨ī, fun i => by rw [markAtN_length]; exact hī i, ?_⟩
    rw [Formula.sat_and]
    refine ⟨?_, ?_⟩
    · rw [sat_andList]
      intro ψ hψ
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hψ
      exact (markedHereN_sat m i w ī ī (hī i)).mpr rfl
    · rw [liftTrN_sat, stripAllN_markAtN]
      exact hsat

/-- **The `m`-mark recogniser (no new axiom; route GA-1).**  For an `m`-free-variable
MSO formula `φ` over `Step`, there is a deterministic finite automaton over `MarkedN m`
that accepts the `m`-mark word `markAtN m w ī` exactly when `φ` holds of the position
tuple `ī` in `w`. -/
theorem markedDFAN_exists (m : ℕ) (φ : Formula Step m 0) :
    ∃ M : SliceMSO.DetAuto (MarkedN m), ∀ (w : List Step) (ī : Fin m → ℕ),
      (∀ i, ī i < w.length) →
      (M.accepts (markAtN m w ī) ↔ φ.Sat w ī Fin.elim0) := by
  obtain ⟨M, hM⟩ := SliceMSO.buchi (markedSentenceN m φ)
  exact ⟨M, fun w ī hī => (hM _).trans (sat_markedSentenceN m φ w ī hī)⟩

end MSOMarkN
