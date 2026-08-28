/-
# Section 4 — Weighted-rank polyregular maps (structural results)

Formalisations of the structural results of §4 of paper.tex (`sec:wrp`,
"Weighted-rank polyregular maps").

What is genuine here:

* `thm:wrp-strict-over-poly` — `PolyReg ⊊ WRP` on the Dyck domain, witnessed
  by the zeta map (assembled from the `sec:zeta` theorems `zetaMap_realisedByWRP` and
  `ZetaNotPolyreg.zetaMap_not_polyregular`).

The §4 complexity results are NOT here: `thm:wrp-logspace` and
`thm:wrp-strict-below-logspace` are proved over the machine models of
`WRPLogspace.lean` / `Logspace.lean` / `WRPWorktape.lean`, and
`cor:srr-quadratic` in `SRRQuadratic.lean`.
-/
import RequestProject.ZetaWRP
import RequestProject.ZetaNotPolyreg

open Step

namespace WRPStructure

/-! ## Strictness over polyregular (`thm:wrp-strict-over-poly`) -/

/-- **Theorem `thm:wrp-strict-over-poly` (paper.tex), genuine.**
`PolyReg ⊊ WRP` on the Dyck domain.  The inclusion `PolyReg ⊆ WRP` is
`WRP.isWRP_of_isPolyregular` (`prop:conservative`); strictness is witnessed by the Haglund
zeta map, which is realised by a WRP transduction on the Dyck domain
(`thm:zeta-wrp`, `zetaMap_realisedByWRP`) but by no ordinary polyregular
transduction (`thm:zeta-not-polyregular`, `ZetaNotPolyreg.zetaMap_not_polyregular`).
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
