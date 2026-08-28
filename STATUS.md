# Status: paper ↔ Lean correspondence

This file records, section by section, how `paper.tex` is rendered in the
Lean development, and the modelling conventions the rendering uses.  The
build is complete: **0 `sorry`, 0 warnings, four project axioms** (listed in
[`README.md`](README.md), which also tables the headline results with their
trust bases).

## Section-by-section map

**§2 (Dyck paths).**  All definitions and identities are formalised in
`DyckPath.lean`/`AreaSeq.lean` (`height`, `areaSeq`, `area`, `dinv`,
`coarea`, `zetaMap`, `wrappedFlat`, `twoPyramid`, `firstAscent`, `tailU`).
The worked examples are checked by `decide`/`native_decide` in
`Examples.lean`.

**§3 (models).**  `def:relative`, `def:dfa`, `def:regular-language`
(`Transducers.lean`); `sec:mso` (`MSO.lean` with marked-word encodings in
`MSOMark.lean`/`MSOMarkN.lean`); `def:mso-transduction`/`def:polyregular`
(`Polyregular.lean`); `def:2dft` with its configuration/run/output definition
(`TwoDFT.lean`).

**§4 (WRP and its structural picture).**
* `def:rank-source`, `def:prefix-rank`, `def:prefix-additive-rank`
  (`WRP.lean`, `PrefixAdditiveRank.lean`); `def:wrp` (`WRP.IsWRP` and the
  verbatim `WRP.IsWRPPaper`, see Conventions); the sRR₁ fragment
  (`WRP.IsSRR1`, `SRR1.lean`); `prop:conservative`
  (`WRP.isWRP_of_isPolyregular`).
* `thm:wrp-closures` — `WRPClosures.isWRP_relabel`/`_restrict`/`_reverse`/
  `_disjointUnion`/`_concat`, axiom-clean.
* `thm:wrp-strict-over-poly` — `WRPStructure.polyreg_strict_subset_wrp`
  (`polyreg_regular_preimage` only).
* `lem:wrp-nonempty-regular` — `WRPNonemptyRegular.lean`.
* `thm:wrp-logspace` — multihead model: `wrp_isLogspaceMH` +
  `wrp_logspace_polytime` (`WRPLogspace.lean`, a fully verified evaluator
  with the ≺-successor round structure and the `O(n^{2k+1})` generic bound);
  worktape model: `wrp_isLogspaceTM` + `wrp_logspaceTM_polytime`
  (`WRPWorktape.lean`, through the simulation
  `MHCOneHead.lean` + `MHCToTM.lean` → `LogspaceTM.lean`).  All four use the
  Büchi axiom only.
* `cor:srr-quadratic` — `srr_quadratic` (`SRRQuadratic.lean`), with a
  verified `N ≤ D·(n+1)²` bound on every halting run.
* `thm:wrp-strict-below-logspace` — `wrp_strict_below_logspace`
  (multihead) and `wrp_strict_below_logspaceTM` (worktape), both
  unconditional; the separating witness is `F_{≥0}`.
* `thm:wrp-not-closed` — `wrp_not_closed_preimage_comp` (regular preimage
  fails; `WRPCompWitness.lean`, axiom-clean) and
  `wrp_not_closed_composition` (with the genuine 2DFT `S`;
  `WRPNotClosedComp.lean`, `SMapWRP.lean`, Büchi only).
* `thm:bounded-rank-collapse` — `WRPBoundedRank.bounded_rank_collapse`,
  axiom-clean; `cor:rank-necessary` — `WRPBoundedRank.rank_necessary`.

**§5 (zeta classification).**  `thm:zeta-wrp` — `zetaMap_realisedByWRP`
(`ZetaWRP.lean`) and `zetaSweep_isSRR1` (`SRR1.lean`);
`prop:alw-sweep-swr` — `additiveSweep_isSRR1` (`AdditiveSweepWRP.lean`);
`prop:two-pyramid-criterion` — `ZetaNotPolyreg.two_pyramid_criterion`
(see Conventions on its hypotheses);
`lem:zeta-two-pyramid` and `lem:zeta-probe` — `ZetaClassification.lean`
(with a concrete DFA witness for the probe language);
`thm:zeta-not-polyregular` / `cor:zeta-not-regular` —
`ZetaNotPolyreg.lean` (see Conventions on the 2DFT reading).

**§6 (Narayana sweep).**  `thm:narayana-sweep` —
`valleys_heightSweep_eq_doubleRises` / `doubleRises_heightSweep_eq_valleys`
(`NarayanaSweep.lean`), the bijection `heightSweep_bijOn`
(`NarayanaBijection.lean`), the WRP presentation (`NarayanaWRP.lean`), and
`heightSweep_isSRR1` (`SRR1.lean`); `lem:H-two-pyramid` —
`heightSweep_twoPyramid` (`HeightSweepTwoPyramid.lean`); `lem:H-probe` —
`inRegularProbe_heightSweep_twoPyramid` and `thm:H-not-polyregular` —
`heightSweep_not_polyregular` / `heightSweep_not_regular`
(`HeightSweepNotPolyreg.lean`, `polyreg_regular_preimage` only).

**§7 (regular-slice semilinearity).**  The one-loop lemmas are formalised
twice: instantiated at the wrapped-flat slice as the growth-collapse tower
that discharges `wrp_slice_profile_affine_general`
(`SliceFasAssemblyGA.lean` and the `Slice*` files, Büchi only), and verbatim
over an arbitrary slice `u·vⁿ·z` in `OneLoopSlice.lean`
(`one_loop_finite_state`, `one_loop_rank_graph`,
`one_loop_presburger_sel`/`_label`/`_rankLt`/`_rankEq`/`_tie`/`_wrpOrd`,
from the two general semilinearity axioms).
`lem:presburger-counting` is the single counting input, transcribed
in Mathlib vocabulary as `PresburgerCounting.count_graph_semilinear` and proved
in `CountGeneral.lean` (see Conventions).  Both forms the towers consume are
derived from it: the joint
count-graph form (`TwoParamSemilinearity.twoParamCountGraph_proved`) by
instantiating it at two parameters, and the row-uniform form
(`SliceSemilinearN.isSliceFamilySemilinear2_count_global`) from that together
with the axiom-clean `semilinearGraph3_affineOnResiduesAt_uniform`
(`SemilinearGraphAffine.lean`), which turns a semilinear count graph in `ℕ³`
into rows that are eventually affine on the residues of one row-uniform
period.
`lem:semilinear-envelope` — `semilinear_envelope_dichotomy`
(`Semilinearity.lean`) and `EnvelopeMin.semilinear_envelope_min`.
`thm:wrp-slice-semilinearity` — `wrp_slice_profile_semilinear`
(`NoSwapWRP.lean`).

**§8 (no-swap).**  `lem:wrapped-flat-stats` (`WrappedFlat.lean`),
`lem:dinv-coarea`, `lem:deficit-zero-targets` (`TightTargets.lean`),
`cor:forced-triangular-pairs`, `lem:triangular-not-semilinear`
(`S_tri_not_semilinear`, `Semilinearity.lean`),
`cor:model-free-obstruction` (`model_free_obstruction`, `NoSwapWRP.lean`,
axiom-clean), and the headline `thm:wrp-no-swap` —
`wrp_no_area_dinv_swap` (`NoSwapWRP.lean`, Büchi only).

**§9 (inverse zeta).**  `lem:inverse-zeta-fas` — `inverse_zeta_fas`
(`InverseZetaFas.lean`, with the explicit pyramid-row preimages);
`lem:inverse-zeta-not-semilinear` —
`inverse_zeta_graph_band_not_semilinear`;
`thm:two-parameter-semilinearity` —
`two_param_profile_semilinear_unconditional`
(`TwoParamSemilinearity.lean`); `cor:inverse-zeta-not-wrp` —
`CopiedD4.inverse_zeta_not_wrp_arity1` (arity 1, Büchi-only) and
`CopiedTieSemilinear2.inverse_zeta_not_wrp` (general arity), built on the
`Copied*` tower.

## Modelling conventions

1. **Two renderings of `def:wrp`.**  The working class `WRP.IsWRP` asks the
   induced output order `≺` (atom rank refined by the tie-order χ) to totally
   order the *selected* atoms of each word.  It is a superset of the paper's
   class, so negative theorems over it are formally stronger.  The verbatim
   class `WRP.IsWRPPaper` (χ itself a strict total order, and every arity
   positive) is also formalised (`WRPTieTotal.lean`), the inclusion is
   proved, and every headline theorem is restated over it
   (`WRPPaperTheorems.lean`, `WRPPaperNotClosed.lean`) with unchanged trust
   bases; the positive memberships (ζ, `H`, the additive level sorts) are
   proved in the verbatim class directly.

2. **Transductions are `Option`-valued.**  A transduction is a
   `List Alpha → Option (List Beta)`; `none` is "undefined".  Realising a
   function on a domain constrains the transduction only on that domain
   (`Realises`).

3. **The no-swap statement is the paper's map form.**
   `wrp_no_area_dinv_swap` refutes any WRP transduction realising a map
   `F : D → D` with `area(F P) = dinv P` and `dinv(F P) = area P`;
   bijectivity of `F` is nowhere assumed, matching the paper's statement.
   The combinatorial half is factored out as `model_free_obstruction`
   (`cor:model-free-obstruction`), which mentions no computational model.

4. **The 2DFT reading of `cor:zeta-not-regular` and
   `thm:H-not-polyregular`.**  "Deterministic two-way transducer" is rendered
   as `Polyreg.IsRegular`, the arity-1 (dimension-1) MSO string transductions
   — by Engelfriet–Hoogeboom exactly the deterministic 2DFT class, which is
   the equivalence the paper itself invokes.  No literal two-way machine is
   re-proved equivalent; the lower bounds use the single admitted closure
   `polyreg_regular_preimage` applied to the hypothetical realiser and to a
   block-counting encoder.

5. **`prop:two-pyramid-criterion` without the growth hypothesis.**  The Lean
   criterion (`two_pyramid_criterion`) omits the paper's hypothesis
   `|f(P_{m,n})| = O(|P_{m,n}|)`: the formal proof applies
   `polyreg_regular_preimage` directly to the polyregular realiser, without
   passing through the linear-growth collapse, so the growth bound is never
   used.  The non-regularity hypothesis is phrased as: no regular language
   agrees with the probe condition on the index family
   (`not_regular_le_family` and `not_regular_ge_family` discharge it for the
   two index sets used).

6. **`lem:one-loop-rank-affine` in graph form.**  `OneLoopSlice.lean` states
   the rank lemma as semilinearity of the rank value graph — the exact form
   the paper's application (the rank comparisons of
   `lem:one-loop-presburger`(c,d)) consumes.  The rational piecewise-affine
   normal form `b₀ + b_n·n + Σ b_ℓ j_ℓ` is proof-internal in the paper and is
   not separately formalised.

7. **`lem:semilinear-envelope` constants are rational.**  The
   eventually-affine minimum is stated in integer-cleared form
   (`M · min S_b = p·b + γ` on residue classes); the all-integer reading is
   false (the `⌊b/2⌋` section is a counterexample), so the rational form is
   the correct one.

8. **`cor:srr-quadratic` lives in the multihead model.**  Its quadratic step
   count uses the paper's unit-cost word comparisons, realised by
   `O(log n)`-bit head registers in `Multihead.MHC`.  A worktape machine pays
   a logarithmic factor per comparison, so the quadratic bound is stated for
   the multihead model only; the worktape restatement covers
   `thm:wrp-logspace` and `thm:wrp-strict-below-logspace`.

9. **Where the axioms are used.**  `SliceMSO.buchi` enters wherever a
   presentation's MSO data is turned into automata (the slice tower, the
   machine evaluators, the separating witnesses); the automaton-to-MSO
   direction is the proved theorem `detAuto_state_mso`.  The two general
   semilinearity axioms enter the general-arity §9 assembly,
   `thm:two-parameter-semilinearity`, and `OneLoopSlice.lean`.  The counting
   input `count_graph_semilinear` enters the same two places, through the
   derived row-uniform and joint-graph forms, but it is a theorem and so adds
   nothing to the trust base.  The arity-1 inverse-zeta capstone
   `CopiedD4.inverse_zeta_not_wrp_arity1` needs no counting input at all
   (`buchi` only), and neither does the one-parameter slice analysis behind
   `thm:wrp-slice-semilinearity`: counting is used only for the
   general-arity tie count of §9.
   `polyreg_regular_preimage` enters only the §5 and §6 lower bounds (and
   hence `thm:wrp-strict-over-poly` and `cor:rank-necessary`, which invoke
   them).  The combinatorial core (§2, §6's exchange and bijection theorems,
   §8's lemmas) and the machine simulations are axiom-clean, as are
   `thm:wrp-closures`, `thm:bounded-rank-collapse`, and the regular-preimage
   clause of `thm:wrp-not-closed`.

10. **The counting theorem against `lem:presburger-counting`.**
    `PresburgerCounting.count_graph_semilinear` is stated with Mathlib's
    `IsSemilinearSet` and `Nat.card` only, so it can be compared with the
    literature (Woods; Ginsburg–Spanier) without reference to this
    development.  It is **proved**, not admitted: `CountGeneral.lean` derives
    it from `ProperLinearRep.lean`, `SemilinearMinMax.lean`,
    `KernelDichotomy.lean`, `SemilinearGraphArith.lean`,
    `ProperPieceCount.lean` and `CountBaseCase.lean` by proper linear
    decomposition (linearly independent periods, hence unique coefficient
    tuples), a kernel dichotomy in which the linear fibre bound rules out two
    independent integer kernel directions — so every fibre is an arithmetic
    progression with a parameter-independent step — and inclusion–exclusion
    over those progressions, residue class by residue class.  No Ehrhart or
    quasi-polynomial input is needed.  Two differences from the paper's text,
    both deliberate: the paper's `p, q ≥ 1` is dropped, so the statement also
    covers `p = 0` and `q = 0` — harmless, since both degenerate cases are
    elementary (for `p = 0` the graph is a singleton; for `q = 0` the count is
    the indicator of a semilinear condition, and semilinear sets are closed
    under complement) — and the paper's joint `r`-tuple form is not
    transcribed, the development needing only the single-count case.  The
    linear bound is load-bearing rather than cosmetic: without it the
    statement is false, as the family `A_x = {y | y 0 < x 0 ∧ y 1 < x 0}`
    with `|A_x| = (x 0)²` shows.

11. **Decidable examples.**  The paper's worked examples are verified by
    `decide`/`native_decide` rather than by hand (`Examples.lean`,
    plus spot checks in `NarayanaSweep.lean`, `ZetaClassification.lean`, and
    `HeightSweepTwoPyramid.lean`).
