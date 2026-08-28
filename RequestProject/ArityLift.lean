/-
# Arity-0 elimination: WRP restricted to nonempty inputs is arity-positive

The paper (paper.tex `def:polyregular`,
`def:wrp`) requires every copy to have arity `k_c ≥ 1`; the Lean model allows
arity-`0` copies.  The two conventions can differ only on the empty input,
where an arity-positive presentation has no atoms (`WRPArityPos.lean`).

This file proves the missing bridge in the other direction, by a generic
**arity lift**: every copy of a presentation gains one extra leading
coordinate, constrained by an MSO formula to sit at the minimal position `0`.
On a nonempty input the lifted atoms `(c, 0 ∷ ī)` biject with the original
atoms `(c, ī)`, preserving selection, labels, ranks and the output order, so
the lifted presentation computes the same outputs; on the empty input the
lifted domain fails.  Hence:

* `isWRPPos_restrict_nonempty` — for every WRP map `T`, the restriction of
  `T` to nonempty inputs lies in the paper's arity-positive class
  `WRP.IsWRPPos`;
* `isWRPPos_concat_nonempty` — the paper's `thm:wrp-closures` (iii)
  ("concatenation with fixed separators **on nonempty inputs**",
  paper.tex) inside the arity-positive class: for
  WRP maps `f, g`, the map `w ↦ f(w) ‖ sep ‖ g(w)` restricted to nonempty
  inputs is `IsWRPPos`.

Everything is axiom-clean.
-/
import RequestProject.WRPArityPos
import RequestProject.WRPClosures

open MSO

namespace ArityLift

variable {Alpha Gamma : Type*}

/-! ## The minimal-position formula -/

/-- "`x₀` is the minimal position": no position lies strictly below variable
`0`.  (On a nonempty word, together with validity this pins `x₀ = 0`.) -/
def minFormula (Alpha : Type*) (k : ℕ) : Formula Alpha (k + 1) 0 :=
  Formula.neg (Formula.exFO (Formula.lt 0 1))

theorem sat_minFormula (k : ℕ) (w : List Alpha) (ρ : Fin (k + 1) → ℕ) :
    Formula.Sat w ρ Fin.elim0 (minFormula Alpha k) ↔
      ¬ ∃ q, q < w.length ∧ q < ρ 0 := by
  simp only [minFormula, Formula.sat_neg, Formula.sat_exFO, Formula.sat_lt,
    Fin.cons_zero, ← Fin.succ_zero_eq_one, Fin.cons_succ]

/-! ## Reindexing rank terms along a coordinate map -/

/-- A regular rank term precomposed with a coordinate selection is again a
regular rank term (reassign each summand's coordinate through `g`). -/
theorem isRegularRankTerm_reindexArg {d k m : ℕ} (g : Fin k → Fin m)
    {f : List Alpha → (Fin k → ℕ) → Fin d → ℤ} (hf : IsRegularRankTerm f) :
    IsRegularRankTerm (fun w ī => f w (fun t => ī (g t))) := by
  obtain ⟨κ, hκ⟩ := hf
  refine ⟨⟨κ.c0, κ.summands.map (fun s => ⟨s.A, s.coeff, g s.π, s.β⟩)⟩, fun w ī => ?_⟩
  show f w (fun t => ī (g t)) = _
  rw [hκ]
  funext coord
  show κ.c0 coord + (κ.summands.map (fun s => s.eval w (fun t => ī (g t)) coord)).sum
      = κ.c0 coord + ((κ.summands.map (fun s : Summand Alpha d k =>
          (⟨s.A, s.coeff, g s.π, s.β⟩ : Summand Alpha d m))).map
            (fun s => s.eval w ī coord)).sum
  congr 1
  rw [List.map_map]
  exact congrArg List.sum (List.map_congr_left (fun s _ => rfl))

/-! ## The pairwise coordinate lift for ordering formulas -/

/-- Embed the combined coordinates of an original atom pair into those of the
lifted pair: each block shifts past its new leading coordinate. -/
def liftPair (k k' : ℕ) : Fin (k + k') → Fin ((k + 1) + (k' + 1)) :=
  Fin.addCases (fun t => Fin.castAdd (k' + 1) t.succ)
    (fun t => Fin.natAdd (k + 1) t.succ)

/-! ## The lifted polyregular presentation -/

/-- **The arity lift**: every copy gains one leading coordinate, anchored at
the minimal position by the selection formula; domain restricted to nonempty
words; labels, ordering, and (below) ranks read the original coordinates
through `Fin.tail`. -/
noncomputable def liftPoly (P : Polyreg.Presentation Alpha Gamma) :
    Polyreg.Presentation Alpha Gamma where
  K := P.K
  arity := fun c => P.arity c + 1
  domain := fun w => P.domain w ∧ 0 < w.length
  domainDef := by
    obtain ⟨φ, hφ⟩ := P.domainDef
    refine ⟨Formula.and φ (Formula.exFO Formula.tru), fun w => ?_⟩
    rw [Formula.sat_and, Formula.sat_exFO]
    simp only [Formula.sat_tru]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hφ w).mp h1, 0, h2, trivial⟩
    · rintro ⟨h1, p, hp, -⟩
      exact ⟨(hφ w).mpr h1, by omega⟩
  sel := fun c w ī => Formula.Sat w ī Fin.elim0
    (Formula.and (minFormula Alpha (P.arity c))
      (SliceFasGates.relabelFO Fin.succ (Classical.choose (P.selDef c))))
  selDef := fun c => ⟨_, fun _ _ => Iff.rfl⟩
  label := fun c w ī => P.label c w (Fin.tail ī)
  labelDef := fun c γ => by
    obtain ⟨φ, hφ⟩ := P.labelDef c γ
    exact ⟨SliceFasGates.relabelFO Fin.succ φ, fun w ρ =>
      (hφ w (Fin.tail ρ)).trans
        (SliceFasGates.sat_relabelFO w Fin.succ ρ Fin.elim0 φ).symm⟩
  ord := fun c c' w ii jj => P.ord c c' w (Fin.tail ii) (Fin.tail jj)
  ordDef := fun c c' => by
    obtain ⟨φ, hφ⟩ := P.ordDef c c'
    refine ⟨SliceFasGates.relabelFO (liftPair (P.arity c) (P.arity c')) φ,
      fun w ρ => ?_⟩
    rw [SliceFasGates.sat_relabelFO]
    have h : P.ord c c' w
        (fun t => (ρ ∘ liftPair (P.arity c) (P.arity c')) (Fin.castAdd (P.arity c') t))
        (fun t => (ρ ∘ liftPair (P.arity c) (P.arity c')) (Fin.natAdd (P.arity c) t))
        ↔ Formula.Sat w (ρ ∘ liftPair (P.arity c) (P.arity c')) Fin.elim0 φ :=
      hφ w (ρ ∘ liftPair (P.arity c) (P.arity c'))
    have htup1 : (fun t => (ρ ∘ liftPair (P.arity c) (P.arity c'))
          (Fin.castAdd (P.arity c') t))
        = fun s => ρ (Fin.castAdd (P.arity c' + 1) s.succ) := by
      funext t
      simp only [Function.comp_apply, liftPair, Fin.addCases_left]
    have htup2 : (fun t => (ρ ∘ liftPair (P.arity c) (P.arity c'))
          (Fin.natAdd (P.arity c) t))
        = fun s => ρ (Fin.natAdd (P.arity c + 1) s.succ) := by
      funext t
      simp only [Function.comp_apply, liftPair, Fin.addCases_right]
    rw [htup1, htup2] at h
    exact h

/-- The characterisation of the lifted selection. -/
theorem liftPoly_sel_iff (P : Polyreg.Presentation Alpha Gamma) (c : Fin P.K)
    (w : List Alpha) (ī : Fin (P.arity c + 1) → ℕ) :
    (liftPoly P).sel c w ī ↔
      ((¬ ∃ q, q < w.length ∧ q < ī 0) ∧ P.sel c w (Fin.tail ī)) := by
  show Formula.Sat w ī Fin.elim0
    (Formula.and (minFormula Alpha (P.arity c))
      (SliceFasGates.relabelFO Fin.succ (Classical.choose (P.selDef c)))) ↔ _
  rw [Formula.sat_and, sat_minFormula, SliceFasGates.sat_relabelFO]
  exact and_congr Iff.rfl
    (Classical.choose_spec (P.selDef c) w (Fin.tail ī)).symm

/-- Selectedness of a lifted atom `⟨c, v⟩`: the anchor sits at `0`, the word
is nonempty, and the tail atom is selected. -/
theorem liftPoly_selectedAtom_iff (P : Polyreg.Presentation Alpha Gamma)
    (w : List Alpha) (c : Fin P.K) (v : Fin (P.arity c + 1) → ℕ) :
    (liftPoly P).selectedAtom w ⟨c, v⟩ ↔
      (v 0 = 0 ∧ 0 < w.length ∧ P.selectedAtom w ⟨c, Fin.tail v⟩) := by
  constructor
  · rintro ⟨hval, hsel⟩
    obtain ⟨hmin, hselT⟩ := (liftPoly_sel_iff P c w v).mp hsel
    have hval' : ∀ t : Fin (P.arity c + 1), v t < w.length := fun t => hval t
    have h0lt : v 0 < w.length := hval' 0
    have h0 : v 0 = 0 := by
      by_contra hne
      exact hmin ⟨0, by omega, by omega⟩
    exact ⟨h0, by omega, fun t => hval' t.succ, hselT⟩
  · rintro ⟨h0, hlen, hvalT, hselT⟩
    refine ⟨fun t => ?_, (liftPoly_sel_iff P c w v).mpr ⟨?_, hselT⟩⟩
    · show v t < w.length
      exact Fin.cases (motive := fun t => v t < w.length)
        (by show v 0 < w.length; rw [h0]; exact hlen) (fun s => hvalT s)
        (t : Fin (P.arity c + 1))
    · rintro ⟨q, -, hq⟩
      rw [h0] at hq
      omega

/-- The lifted tuple: anchor `0` prepended (nondependent motive pinned by the
definition, keeping unification deterministic). -/
@[reducible] def cons0 {n : ℕ} (p : Fin n → ℕ) : Fin (n + 1) → ℕ :=
  Fin.cons (α := fun _ => ℕ) 0 p

@[simp] theorem cons0_zero {n : ℕ} (p : Fin n → ℕ) : cons0 p 0 = 0 := by
  show Fin.cons (α := fun _ => ℕ) 0 p 0 = 0
  rw [Fin.cons_zero]

@[simp] theorem tail_cons0 {n : ℕ} (p : Fin n → ℕ) : Fin.tail (cons0 p) = p := by
  show Fin.tail (Fin.cons (α := fun _ => ℕ) 0 p) = p
  rw [Fin.tail_cons]

/-- Prepending the anchor to a selected tail restores the atom. -/
theorem cons0_tail_eq {n : ℕ} (v : Fin (n + 1) → ℕ) (h0 : v 0 = 0) :
    cons0 (Fin.tail v) = v := by
  show Fin.cons (α := fun _ => ℕ) 0 (Fin.tail v) = v
  rw [← h0]
  exact Fin.cons_self_tail v

/-! ## The lifted WRP presentation -/

/-- The arity lift of a WRP presentation: the rank functions read the original
coordinates through `Fin.tail`. -/
noncomputable def liftPres (P : WRP.Presentation Alpha Gamma) :
    WRP.Presentation Alpha Gamma where
  toPoly := liftPoly P.toPoly
  d := P.d
  rank := fun c w ī => P.rank c w (Fin.tail ī)
  rankReg := fun c => isRegularRankTerm_reindexArg Fin.succ (P.rankReg c)

/-- The output order of the lift is the original output order on tail atoms
(definitional). -/
theorem liftPres_wrpOrd (P : WRP.Presentation Alpha Gamma) (w : List Alpha)
    {c c' : Fin P.toPoly.K} (v : Fin (P.toPoly.arity c + 1) → ℕ)
    (v' : Fin (P.toPoly.arity c' + 1) → ℕ) :
    (liftPres P).wrpOrd w ⟨c, v⟩ ⟨c', v'⟩ ↔
      P.wrpOrd w ⟨c, Fin.tail v⟩ ⟨c', Fin.tail v'⟩ := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem liftPres_valid {P : WRP.Presentation Alpha Gamma} (hV : P.Valid) :
    (liftPres P).Valid where
  irrefl := fun w a ha hbad => by
    obtain ⟨c, v⟩ := a
    have haT := ((liftPoly_selectedAtom_iff P.toPoly w c v).mp ha).2.2
    exact hV.irrefl w _ haT ((liftPres_wrpOrd P w v v).mp hbad)
  trans := fun w a b cc ha hb hc hab hbc => by
    obtain ⟨ca, va⟩ := a
    obtain ⟨cb, vb⟩ := b
    obtain ⟨cx, vx⟩ := cc
    have haT := ((liftPoly_selectedAtom_iff P.toPoly w ca va).mp ha).2.2
    have hbT := ((liftPoly_selectedAtom_iff P.toPoly w cb vb).mp hb).2.2
    have hcT := ((liftPoly_selectedAtom_iff P.toPoly w cx vx).mp hc).2.2
    exact (liftPres_wrpOrd P w va vx).mpr
      (hV.trans w _ _ _ haT hbT hcT ((liftPres_wrpOrd P w va vb).mp hab)
        ((liftPres_wrpOrd P w vb vx).mp hbc))
  trichot := fun w a b ha hb => by
    obtain ⟨ca, va⟩ := a
    obtain ⟨cb, vb⟩ := b
    obtain ⟨h0a, -, haT⟩ := (liftPoly_selectedAtom_iff P.toPoly w ca va).mp ha
    obtain ⟨h0b, -, hbT⟩ := (liftPoly_selectedAtom_iff P.toPoly w cb vb).mp hb
    rcases hV.trichot w _ _ haT hbT with h | h | h
    · exact Or.inl ((liftPres_wrpOrd P w va vb).mpr h)
    · refine Or.inr (Or.inl ?_)
      have hc : ca = cb := congrArg Sigma.fst h
      subst hc
      have hts : Fin.tail va = Fin.tail vb := by
        injection h with h1 h2
      have hv : va = vb := by
        rw [← cons0_tail_eq va h0a, ← cons0_tail_eq vb h0b, hts]
      rw [hv]
    · exact Or.inr (Or.inr ((liftPres_wrpOrd P w vb va).mpr h))

/-! ## Output correspondence on nonempty inputs -/

theorem liftPres_isOutput_iff (P : WRP.Presentation Alpha Gamma)
    {w : List Alpha} (hw : 0 < w.length) (out : List Gamma) :
    (liftPres P).IsOutput w out ↔ P.IsOutput w out := by
  constructor
  · rintro ⟨atoms, hnd, hmem, hpw, rfl⟩
    refine ⟨atoms.map (fun a => ⟨a.1, Fin.tail a.2⟩), ?_, ?_, ?_, ?_⟩
    · refine List.Nodup.map_on (fun a ha b hb hab => ?_) hnd
      obtain ⟨ca, va⟩ := a
      obtain ⟨cb, vb⟩ := b
      have h0a := ((liftPoly_selectedAtom_iff P.toPoly w ca va).mp
        ((hmem _).mp ha)).1
      have h0b := ((liftPoly_selectedAtom_iff P.toPoly w cb vb).mp
        ((hmem _).mp hb)).1
      have hc : ca = cb := congrArg Sigma.fst hab
      subst hc
      have hts : Fin.tail va = Fin.tail vb := by
        injection hab with h1 h2
      have hv : va = vb := by
        rw [← cons0_tail_eq va h0a, ← cons0_tail_eq vb h0b, hts]
      rw [hv]
    · intro b
      rw [List.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨ca, va⟩ := a
        exact ((liftPoly_selectedAtom_iff P.toPoly w ca va).mp
          ((hmem _).mp ha)).2.2
      · intro hb
        obtain ⟨cb, vb⟩ := b
        refine ⟨⟨cb, cons0 vb⟩, (hmem _).mpr ?_, ?_⟩
        · refine (liftPoly_selectedAtom_iff P.toPoly w cb (cons0 vb)).mpr
            ⟨cons0_zero vb, hw, ?_⟩
          rw [tail_cons0]
          exact hb
        · show (⟨cb, Fin.tail (cons0 vb)⟩ : P.toPoly.Atom) = ⟨cb, vb⟩
          rw [tail_cons0]
    · refine List.Pairwise.map _ (fun a b hab => ?_) hpw
      obtain ⟨ca, va⟩ := a
      obtain ⟨cb, vb⟩ := b
      exact (liftPres_wrpOrd P w va vb).mp hab
    · rw [List.map_map]
      exact List.map_congr_left (fun a _ => rfl)
  · rintro ⟨atoms, hnd, hmem, hpw, rfl⟩
    refine ⟨atoms.map (fun a => ⟨a.1, cons0 a.2⟩), ?_, ?_, ?_, ?_⟩
    · refine List.Nodup.map_on (fun a _ b _ hab => ?_) hnd
      obtain ⟨ca, va⟩ := a
      obtain ⟨cb, vb⟩ := b
      have hc : ca = cb := congrArg Sigma.fst hab
      subst hc
      have hts : cons0 va = cons0 vb := by
        injection hab with h1 h2
      have hv : va = vb := by
        rw [← tail_cons0 va, hts, tail_cons0]
      rw [hv]
    · intro b
      rw [List.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨ca, va⟩ := a
        refine (liftPoly_selectedAtom_iff P.toPoly w ca (cons0 va)).mpr
          ⟨cons0_zero va, hw, ?_⟩
        rw [tail_cons0]
        exact (hmem _).mp ha
      · intro hb
        obtain ⟨cb, vb⟩ := b
        obtain ⟨h0, -, hbT⟩ := (liftPoly_selectedAtom_iff P.toPoly w cb vb).mp hb
        refine ⟨⟨cb, Fin.tail vb⟩, (hmem _).mpr hbT, ?_⟩
        show (⟨cb, cons0 (Fin.tail vb)⟩ : (liftPoly P.toPoly).Atom)
          = ⟨cb, vb⟩
        rw [cons0_tail_eq vb h0]
    · refine List.Pairwise.map _ (fun a b hab => ?_) hpw
      obtain ⟨ca, va⟩ := a
      obtain ⟨cb, vb⟩ := b
      rw [liftPres_wrpOrd, tail_cons0, tail_cons0]
      exact hab
    · rw [List.map_map]
      refine List.map_congr_left (fun a _ => ?_)
      obtain ⟨ca, va⟩ := a
      show P.toPoly.labelOf w ⟨ca, va⟩
        = P.toPoly.label ca w (Fin.tail (cons0 va))
      rw [tail_cons0]
      rfl

/-! ## The capstone: WRP on nonempty inputs is arity-positive -/

/-- **Arity-0 elimination.**  For every WRP map `T`, the restriction of `T`
to nonempty inputs lies in the paper's arity-positive class
(`def:polyregular`/`def:wrp` with every `k_c ≥ 1`). -/
theorem isWRPPos_restrict_nonempty {T : List Alpha → Option (List Gamma)}
    (h : WRP.IsWRP T) :
    WRP.IsWRPPos (fun w => match w with | [] => none | _ => T w) := by
  obtain ⟨P, hV, hT⟩ := h
  refine ⟨liftPres P, liftPres_valid hV, fun c => Nat.succ_pos _, fun w out => ?_⟩
  cases w with
  | nil =>
      constructor
      · intro h
        exact absurd h (by simp)
      · rintro ⟨⟨-, hlen⟩, -⟩
        simp at hlen
  | cons x rest =>
      show T (x :: rest) = some out ↔ _
      rw [hT (x :: rest) out]
      have hw : 0 < (x :: rest).length := by simp
      constructor
      · rintro ⟨hdom, hout⟩
        exact ⟨⟨hdom, hw⟩, (liftPres_isOutput_iff P hw out).mpr hout⟩
      · rintro ⟨⟨hdom, -⟩, hout⟩
        exact ⟨hdom, (liftPres_isOutput_iff P hw out).mp hout⟩

/-- **`thm:wrp-closures` (iii) in the paper's class**
(paper.tex): concatenation with a fixed separator, on nonempty inputs,
stays in the arity-positive class `IsWRPPos`. -/
theorem isWRPPos_concat_nonempty {Alpha Γ : Type} [Fintype Γ] [DecidableEq Γ] (sep : Γ)
    {f g : List Alpha → Option (List Γ)}
    (hf : WRP.IsWRP f) (hg : WRP.IsWRP g) :
    WRP.IsWRPPos (fun w => match w with
      | [] => none
      | _ => (match f w, g w with
          | some a, some b => some (a ++ [sep] ++ b)
          | _, _ => none)) := by
  have h := WRPClosures.isWRP_concat (sep := sep) hf hg
  have h2 := isWRPPos_restrict_nonempty h
  convert h2 using 1
  funext w
  cases w <;> rfl

end ArityLift
