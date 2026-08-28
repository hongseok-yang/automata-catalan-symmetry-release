/-
# The paper's arity convention: every copy has arity ≥ 1

paper.tex fixes `k_c ≥ 1` for every copy name of a polyregular
presentation (`def:polyregular`), and `def:wrp` inherits
the convention.  The Lean model
(`Polyreg.Presentation.arity : Fin K → ℕ`) also allows arity-`0` copies.

The two conventions differ **only on the empty input**: a selected atom must
place all of its coordinates inside the word (`Polyreg.Presentation.validAtom`),
so with every `k_c ≥ 1` no atom is selected on `ε` and the output there is `ε`
whenever `ε` is in the domain (`Polyreg.Presentation.isOutput_nil_eq_nil`,
`WRP.IsWRPPos.output_nil`); an arity-`0` copy, by contrast, can emit a letter
on `ε`.  This is why the paper's concatenation closure
(`thm:wrp-closures` (iii)) is stated on *nonempty* inputs.

This file defines the paper's classes and the transfer principles:

* `Polyreg.Presentation.ArityPos`, `Polyreg.IsPolyregularPos`, `WRP.IsWRPPos` —
  the paper's `def:polyregular` / `def:wrp` classes;
* inclusions `IsPolyregularPos ⊆ IsPolyregular` and `IsWRPPos ⊆ IsWRP`
  (`IsPolyregularPos.isPolyregular`, `IsWRPPos.isWRP`): every **negative**
  theorem proved over the Lean classes (`thm:zeta-not-polyregular`,
  `thm:wrp-no-swap`, `cor:inverse-zeta-not-wrp`, …) therefore yields the
  paper's statement a fortiori;
* `Polyreg.IsRegular.isPolyregularPos`, `WRP.IsRR.isWRPPos`,
  `WRP.IsSRR1.isWRPPos`: arity-**1** presentations are arity-positive, so the
  paper's **positive** memberships land in its own class — the zeta sweep
  (`thm:zeta-wrp`), the Narayana height sweep, and every additive level sort
  (`prop:alw-sweep-swr`) are `sRR₁` and hence `IsWRPPos`
  (`zetaSweep_isWRPPos`, `heightSweep_isWRPPos`, `additiveSweep_isWRPPos`);
* `WRP.isWRPPos_of_isPolyregularPos` — the conservativity inclusion
  `prop:conservative` within the paper's convention (rank dimension `0`,
  same arity-positive polyregular presentation).
-/
import RequestProject.AdditiveSweepWRP

open MSO Step

/-! ## The arity-positive convention on presentations -/

namespace Polyreg

variable {Alpha Gamma : Type*}

/-- **`def:polyregular` (paper.tex), arity convention.**
Every copy name carries a fixed arity `k_c ≥ 1`. -/
def Presentation.ArityPos (P : Presentation Alpha Gamma) : Prop :=
  ∀ c, 0 < P.arity c

/-- On the empty input, an arity-positive presentation selects no atom: a
selected atom is valid, and a valid atom needs a position `< 0`. -/
theorem Presentation.not_selectedAtom_nil {P : Presentation Alpha Gamma}
    (hpos : P.ArityPos) (a : P.Atom) : ¬ P.selectedAtom [] a := by
  rintro ⟨hval, -⟩
  simpa using hval ⟨0, hpos a.1⟩

/-- On the empty input, the declarative output of an arity-positive
presentation is `ε` ("if there are no selected atoms, this concatenation is
`ε`", `def:mso-transduction`). -/
theorem Presentation.isOutput_nil_eq_nil {P : Presentation Alpha Gamma}
    (hpos : P.ArityPos) {out : List Gamma} (h : P.IsOutput [] out) : out = [] := by
  obtain ⟨atoms, -, hmem, -, rfl⟩ := h
  have hnil : atoms = [] :=
    List.eq_nil_iff_forall_not_mem.mpr
      (fun a ha => P.not_selectedAtom_nil hpos a ((hmem a).mp ha))
  rw [hnil, List.map_nil]

/-- **The paper's polyregular class** (`def:polyregular`,
paper.tex): realised by a valid presentation all of whose copies have arity
`≥ 1`. -/
def IsPolyregularPos (f : List Alpha → Option (List Gamma)) : Prop :=
  ∃ P : Presentation Alpha Gamma, P.Valid ∧ P.ArityPos ∧
    ∀ w out, f w = some out ↔ (P.domain w ∧ P.IsOutput w out)

/-- The paper's class is contained in the Lean class (which also admits
arity-`0` copies); negative theorems over `IsPolyregular` transfer. -/
theorem IsPolyregularPos.isPolyregular {f : List Alpha → Option (List Gamma)}
    (h : IsPolyregularPos f) : IsPolyregular f := by
  obtain ⟨P, hV, -, hf⟩ := h
  exact ⟨P, hV, hf⟩

/-- Arity-**1** presentations (the regular / 2DFT model `IsRegular`) are in
particular arity-positive. -/
theorem IsRegular.isPolyregularPos {f : List Alpha → Option (List Gamma)}
    (h : IsRegular f) : IsPolyregularPos f := by
  obtain ⟨P, hV, h1, hf⟩ := h
  exact ⟨P, hV, fun c => (h1 c) ▸ Nat.one_pos, hf⟩

/-- The value of a paper-convention polyregular map at `ε` is `ε` (or
undefined). -/
theorem IsPolyregularPos.output_nil {f : List Alpha → Option (List Gamma)}
    (h : IsPolyregularPos f) {out : List Gamma} (hf : f [] = some out) : out = [] := by
  obtain ⟨P, -, hpos, hrel⟩ := h
  exact P.isOutput_nil_eq_nil hpos ((hrel [] out).mp hf).2

end Polyreg

/-! ## The paper's WRP class -/

namespace WRP

variable {Alpha Gamma : Type*}

/-- **The paper's WRP class** (`def:wrp`, paper.tex):
realised by a valid WRP presentation whose underlying polyregular presentation
is arity-positive. -/
def IsWRPPos (T : List Alpha → Option (List Gamma)) : Prop :=
  ∃ P : Presentation Alpha Gamma, P.Valid ∧ P.toPoly.ArityPos ∧
    ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out)

/-- The paper's class is contained in the Lean class; every negative
theorem over `IsWRP` yields the paper's statement a fortiori. -/
theorem IsWRPPos.isWRP {T : List Alpha → Option (List Gamma)}
    (h : IsWRPPos T) : IsWRP T := by
  obtain ⟨P, hV, -, hT⟩ := h
  exact ⟨P, hV, hT⟩

/-- Arity-1 (`RR`) membership is arity-positive membership. -/
theorem IsRR.isWRPPos {T : List Alpha → Option (List Gamma)}
    (h : IsRR T) : IsWRPPos T := by
  obtain ⟨P, hV, h1, hT⟩ := h
  exact ⟨P, hV, fun c => (h1 c) ▸ Nat.one_pos, hT⟩

/-- `sRR₁ = SWR` membership is arity-positive membership. -/
theorem IsSRR1.isWRPPos {T : List Alpha → Option (List Gamma)}
    (h : IsSRR1 T) : IsWRPPos T :=
  h.isRR.isWRPPos

/-- The value of a paper-convention WRP map at `ε` is `ε` (or undefined). -/
theorem IsWRPPos.output_nil {T : List Alpha → Option (List Gamma)}
    (h : IsWRPPos T) {out : List Gamma} (hT : T [] = some out) : out = [] := by
  obtain ⟨P, -, hpos, hrel⟩ := h
  obtain ⟨atoms, -, hmem, -, rfl⟩ := ((hrel [] out).mp hT).2
  have hnil : atoms = [] :=
    List.eq_nil_iff_forall_not_mem.mpr
      (fun a ha => P.toPoly.not_selectedAtom_nil hpos a ((hmem a).mp ha))
  rw [hnil, List.map_nil]

/-- **`prop:conservative` within the paper's convention**: an arity-positive
polyregular map is an arity-positive WRP map, with rank dimension `0` on the
same presentation.  (Mirrors `isWRP_of_isPolyregular`, which proves the
inclusion for the Lean classes.) -/
theorem isWRPPos_of_isPolyregularPos {T : List Alpha → Option (List Gamma)}
    (h : Polyreg.IsPolyregularPos T) : IsWRPPos T := by
  obtain ⟨P, hValid, hpos, hT⟩ := h
  set Q : Presentation Alpha Gamma :=
    ⟨P, 0, fun _ _ _ => Fin.elim0, fun _ => isRegularRankTerm_zero _⟩ with hQ
  have hwrp : ∀ w (a b : Q.toPoly.Atom), Q.wrpOrd w a b ↔ P.atomOrd w a b := by
    intro w a b
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact (lexLt_zero _ _ h).elim
      · exact h
    · intro h; exact Or.inr ⟨funext (fun c => c.elim0), h⟩
  refine ⟨Q, ?_, hpos, ?_⟩
  · constructor
    · intro w a ha hbad; exact hValid.irrefl w a ha ((hwrp w a a).mp hbad)
    · intro w a b c ha hb hc hab hbc
      exact (hwrp w a c).mpr
        (hValid.trans w a b c ha hb hc ((hwrp w a b).mp hab) ((hwrp w b c).mp hbc))
    · intro w a b ha hb
      rcases hValid.trichot w a b ha hb with h | h | h
      · exact Or.inl ((hwrp w a b).mpr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ((hwrp w b a).mpr h))
  · intro w out
    rw [hT w out]
    constructor
    · rintro ⟨hdom, atoms, hnd, hmem, hpair, hout⟩
      exact ⟨hdom, atoms, hnd, hmem, hpair.imp (fun hh => (hwrp w _ _).mpr hh), hout⟩
    · rintro ⟨hdom, atoms, hnd, hmem, hpair, hout⟩
      exact ⟨hdom, atoms, hnd, hmem, hpair.imp (fun hh => (hwrp w _ _).mp hh), hout⟩

end WRP

/-! ## The paper's positive memberships land in its own class

The zeta sweep (`thm:zeta-wrp`), the Narayana height sweep (`sec:narayana-sweep`), and
every additive level sort (`prop:alw-sweep-swr`) are `sRR₁`, hence arity-1,
hence in the paper's `IsWRPPos` class. -/

/-- **`thm:zeta-wrp` under the paper's convention**: the zeta sweep is an
arity-positive WRP map. -/
theorem zetaSweep_isWRPPos :
    WRP.IsWRPPos (fun w : List Step => some (zetaSweep w)) :=
  zetaSweep_isSRR1.isWRPPos

/-- **Height-sweep membership (`sec:narayana-sweep`) under the paper's
convention**: the Narayana height sweep is an arity-positive WRP map. -/
theorem heightSweep_isWRPPos :
    WRP.IsWRPPos (fun w : List Step => some (heightSweep w)) :=
  heightSweep_isSRR1.isWRPPos

/-- **`prop:alw-sweep-swr` under the paper's convention**: every additive
level sort `Φ_ν` (arbitrary step weights `ν` and either tie-order direction)
is an arity-positive WRP map. -/
theorem additiveSweep_isWRPPos (nu : Step → ℤ) (dir : Bool) :
    WRP.IsWRPPos (fun w : List Step => some (additiveSweep nu dir w)) :=
  (additiveSweep_isSRR1 nu dir).isWRPPos
