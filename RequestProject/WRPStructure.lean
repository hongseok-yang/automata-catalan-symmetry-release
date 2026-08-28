/-
# Section 4 — WRP as a natural class (structural results)

Formalisations of the structural results of §4 of paper-full-new.tex ("WRP as a
natural class: closure, complexity, and sharp boundaries").

What is genuine here:

* §4.3 `thm:wrp-strict-over-poly` — `PolyReg ⊊ WRP` on the Dyck domain, witnessed
  by the zeta map (assembled from the §6 theorems `zetaMap_realisedByWRP` and
  `ZetaNotPolyreg.zetaMap_not_polyregular`).

The §4 complexity results (`thm:wrp-logspace`, `cor:srr-quadratic`,
`thm:wrp-strict-below-logspace`) are NOT here: they require a deterministic
logspace / time-complexity model of string transductions that the repository does
not provide, so they remain documented milestones in `Transducers.lean`.
-/
import RequestProject.ZetaWRP
import RequestProject.ZetaNotPolyreg

open Step

namespace WRPStructure

/-! ## §4.3 Strictness over polyregular (`thm:wrp-strict-over-poly`) -/

/-- **Theorem `thm:wrp-strict-over-poly` (`thm:wrp-strict-over-poly`, paper-full-new.tex), genuine.**
`PolyReg ⊊ WRP` on the Dyck domain.  The inclusion `PolyReg ⊆ WRP` is
`WRP.isWRP_of_isPolyregular` (Prop 3.15); strictness is witnessed by the Haglund
zeta map, which is realised by a WRP transduction on the Dyck domain
(`thm:zeta-wrp`, `zetaMap_realisedByWRP`) but by no ordinary polyregular
transduction (`cor:zeta-not-polyregular`, `ZetaNotPolyreg.zetaMap_not_polyregular`).
This is the paper's central concrete witness: a Catalan map drives the strictness
of an inclusion in the transducer hierarchy.  Trust base: `+ polyreg_regular_preimage`
(inherited from the not-polyregular half). -/
theorem polyreg_strict_subset_wrp :
    (∃ T : List Step → Option (List Step),
        WRP.IsWRP T ∧ Realises T {P | IsDyckPath P} zetaMap) ∧
    ¬ (∃ T : List Step → Option (List Step),
        Polyreg.IsPolyregular T ∧ Realises T {P | IsDyckPath P} zetaMap) :=
  ⟨zetaMap_realisedByWRP, ZetaNotPolyreg.zetaMap_not_polyregular⟩

end WRPStructure
