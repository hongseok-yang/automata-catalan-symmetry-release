# Status: paper ↔ Lean correspondence

This file records, section by section, how `paper.tex` is rendered in the
Lean development, and the modelling conventions the rendering uses.  The
build is complete: **0 `sorry`, 0 warnings, three project axioms** (listed in
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
  with the ≺-successor round structure and an explicit step bound
  `cardQ · (n+2)^h · (C·(n+1)+1)^c`, where the head count `h` depends on the
  presentation's arity and `c = 2`; the paper's clause asks only for
  polynomial time, which this delivers).  The output-length clause
  `|T(w)| = O(n^k)` of `thm:wrp-logspace` is not formalised;
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

**§6 (Narayana sweep).**  `thm:narayana-sweep` — `valleys_heightSweep` /
`doubleRises_heightSweep` (`NarayanaBijection.lean`; the forms in
`NarayanaSweep.lean` carry an extra `semilength P ≥ 1`), the bijection
`heightSweep_bijOn`
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
from `msoDefinableRel2_semilinear_general`).
`lem:presburger-counting` is `PresburgerCounting.count_graph_semilinear`,
transcribed in Mathlib vocabulary and proved in `CountGeneral.lean` (see
Conventions).  The two forms the towers consume follow from it: the two-parameter
count-graph form (`TwoParamSemilinearity.twoParamCountGraph_proved`, a single
count at two parameters — not the paper's simultaneous `r`-tuple form, which
is not transcribed) by
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
`lem:dinv-coarea` (`dinv_le_coarea`, `WrappedFlat.lean`),
`lem:deficit-zero-targets` (`TightTargets.lean`),
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
   proved, and every **negative** headline theorem is restated over it
   (`WRPPaperTheorems.lean`, `WRPPaperNotClosed.lean`) with unchanged trust
   bases; the positive memberships (ζ, `H`, the additive level sorts) are
   proved in the verbatim class directly.  Closure statements are positive, so
   proving them over the larger class does *not* give the paper's statement:
   paper-class closure forms exist only for relabelling and concatenation.
   No map is exhibited in the working class but outside the paper's, so the
   inclusion is a superset, not a known strict one.

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

7. **`lem:semilinear-envelope` constants are rational, and three forms
   exist.**  The eventually-affine minimum is stated in integer-cleared form,
   `q · min S_b = p·b + γ` on residue classes with an independently
   existentially quantified `q > 0` (not the period); the all-integer reading
   is false — the `⌊b/2⌋` section is a counterexample — so the rational form
   is the correct one.  Of the three envelope theorems, the one on the
   critical path of both non-semilinearity results is the weakest,
   `semilinear_envelope` (`Semilinearity.lean`), which replaces `min S_b` by
   *some* element of `S_b`; the full minimum form
   (`EnvelopeMin.semilinear_envelope_min`) and the dichotomy
   (`semilinear_envelope_dichotomy`) are proved but unused.

8. **`cor:srr-quadratic` lives in the multihead model.**  Its quadratic step
   count uses the paper's unit-cost word comparisons, realised by
   `O(log n)`-bit head registers in `Multihead.MHC`.  A worktape machine pays
   a logarithmic factor per comparison, so the quadratic bound is stated for
   the multihead model only; the worktape restatement covers
   `thm:wrp-logspace` and `thm:wrp-strict-below-logspace`.

9. **Where the axioms are used.**  `SliceMSO.buchi` enters wherever a
   presentation's MSO data is turned into automata (the slice tower, the
   machine evaluators, the separating witnesses); the automaton-to-MSO
   direction is the proved theorem `detAuto_state_mso`.  The general
   semilinearity axiom `msoDefinableRel2_semilinear_general` enters the
   general-arity §9 assembly, `thm:two-parameter-semilinearity`, and
   `OneLoopSlice.lean`, both directly and through the rank-term value graph
   `regularRankTerm_value2_graph_semilinear`, which is a theorem
   (`RankTermGraph.lean`) whose proof applies the axiom twice.  The counting
   theorem `count_graph_semilinear` is reached through that value graph, and
   so underlies `thm:two-parameter-semilinearity`, every one-loop lemma, and
   the general-arity §9 tie count; being a theorem it adds nothing to the
   trust base.  Two places are conclusively counting-free, their modules not
   importing the counting file at all: the arity-1 inverse-zeta capstone
   `CopiedD4.inverse_zeta_not_wrp_arity1` (`buchi` only) and the
   one-parameter slice analysis behind `thm:wrp-slice-semilinearity`.
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
    development, and it is a theorem: `CountGeneral.lean` derives it from
    `ProperLinearRep.lean`, `SemilinearMinMax.lean`, `KernelDichotomy.lean`,
    `SemilinearGraphArith.lean`, `ProperPieceCount.lean` and
    `CountBaseCase.lean` by proper linear decomposition (linearly independent
    periods, hence unique coefficient tuples), a kernel dichotomy in which the
    linear fibre bound rules out two independent integer kernel directions —
    so every fibre is an arithmetic progression with a parameter-independent
    step — and inclusion–exclusion over those progressions, residue class by
    residue class.  Neither Ehrhart theory nor quasi-polynomiality enters, so
    the formal proof does not follow the route by which
    §7 of the paper derives the lemma from Woods' theorem.
    The Lean statement differs from the paper's in two respects.  It omits the
    paper's `p, q ≥ 1`, covering `p = 0` and `q = 0` as well; both degenerate
    cases are elementary, since for `p = 0` the graph is a singleton and for
    `q = 0` the count is the indicator of a semilinear condition, and
    semilinear sets are closed under complement.  It covers only the
    single-count case, the paper's joint `r`-tuple form being unused here.
    The linear bound is load-bearing rather than cosmetic: without it the
    statement is false, as the family `A_x = {y | y 0 < x 0 ∧ y 1 < x 0}` with
    `|A_x| = (x 0)²` shows.

11. **Decidable examples.**  The paper's worked examples are verified by
    `decide`/`native_decide` rather than by hand (`Examples.lean`,
    plus spot checks in `NarayanaSweep.lean`, `ZetaClassification.lean`, and
    `HeightSweepTwoPyramid.lean`).

## Further deviations from the paper

The conventions above cover the deviations that shape how the main theorems
are read.  This section records the remainder, so that the correspondence can
be audited without reading the sources.  Direction key: *stronger* = the Lean
statement implies the paper's and more; *weaker* = the paper's statement is not
fully delivered; *rendering* = same content in different formal vocabulary;
*route* = same conclusion by a different proof.

### Definitions

* Lean permits copies of arity 0 and presentations with no copies, where the
  paper requires at least one copy of arity ≥ 1.  The conventions are proved to
  differ only on the empty input, and the arity-0 freedom is used by the
  concatenation witness, which emits its separator from an arity-0 copy.
  (*superset*)
* A presentation must be well-formed on every input word; the paper's MSO
  string-transduction definition asks this only on the domain.  The paper's
  polyregular definition is itself global, so only the arity-1 class is
  affected.  The standard repair — folding the domain condition into the
  selection formulas — is routine but not carried out.  (*weaker, in a small
  and un-formalised way*)
* MSO definability is required at position tuples outside the word as well.
  This is semantically inert, since out-of-range atoms are never selected, and
  the in-range guard is itself definable and proved so.  (*rendering*)
* Rank sources and prefix ranks are 0-indexed and defined past the end of the
  word; both are inert because atoms must lie inside the word.  (*rendering*)
* The paper's prefix-additive rank functions and Lean's regular rank terms are
  proved to define the same class, in both directions and at the level of the
  class.  (*equivalent*)
* ζ and `H` have memberships of different shapes.  `H` is total, and its
  membership is asserted on all step words.  For ζ the analogous total claim is
  **false** — the level scan truncates below level 0, and the repository
  records the checked counterexample — so membership is asserted for a
  level-symmetric totalisation and transferred to ζ on Dyck paths.
  (*rendering*)
* The output of a presentation is defined declaratively, as a duplicate-free
  list containing exactly the selected atoms and pairwise ordered by `≺`, with
  uniqueness proved.  The paper's equivalent description — list in χ-order,
  then stably sort by rank — is not formalised.  (*rendering*)
* Automata and regular languages are defined without requiring a finite
  alphabet.  Every use site is at a finite alphabet, and both MSO axioms do
  require finiteness; only `polyreg_regular_preimage` is stated over arbitrary
  types, which is more general than the literature statement it cites.
  (*rendering; the generality of that axiom is an open fidelity question*)
* The paper's numeric worked examples are machine-checked.  Its structural
  examples — the reverse-complement in both presentations, the quadratic map
  `w ↦ w^{#U(w)}`, and the two-dimensional atom-rank example — are not
  formalised.  (*weaker than a blanket claim that the examples are certified*)

### Statements

* `prop:conservative` is half formalised: that every polyregular map is WRP is
  proved, in four class variants; the converse for rank dimension 0 is not
  stated.  (*weaker*)
* `thm:wrp-closures` is the least complete result.  The paper states it for
  arity-bounded subclasses; the Lean theorems track no arity.  Definition by
  cases over disjoint regular languages and letter-deleting relabellings are
  missing; source-tagging and concatenation are done for two maps rather than
  `r`, with a single-letter separator; restriction is stated with an
  MSO-definable language rather than a regular one, and no automaton-to-formula
  bridge exists.  (*weaker, on several counts*)
* The complexity layer fixes the input alphabet to `{U, D}`, where the paper
  allows any finite alphabet; the strict-below-logspace statements also fix a
  five-letter output alphabet.  The generalisation is mechanical.  (*weaker as
  stated*)
* `lem:inverse-zeta-not-semilinear` is formalised only in two dimensions; the
  paper's three-dimensional first-ascent graph, and the reduction between them,
  are not.  The capstone does not need the three-dimensional form.  (*weaker*)
* `lem:two-parameter-presburger` has no single statement: its clauses appear
  only in raw input-position coordinates, the (region, offset, repetition-index)
  encoding being carried out only for the one-parameter family.  (*partial*)
* The statistics of the wrapped-flat family are proved for every `n`, including
  `n = 0` where the paper assumes `n ≥ 1`.  (*stronger*)
* The Narayana symmetry is rendered coefficient by coefficient; the polynomial
  `Nar_n(q,t)` is never defined.  (*rendering*)
* The four introduction-level theorems have no separate Lean declarations; each
  is covered by its body version.  (*no counterpart*)

### Proofs

* The Narayana sweep is proved by sorted-adjacency and level-counting arguments
  on step words, not by the paper's contour-forest normal form.  (*route*)
* The quadratic scan-order evaluator is a different algorithm: it loops over
  the `O(n)` rank levels rather than over output letters, keeps per-copy ranks
  as signed differences so that a comparison is a single head coincidence, and
  uses no counters at all.  The bound `D·(n+1)²` comes with an explicit
  constant.  (*route*)
* The non-regularity of the two index languages is proved by direct pigeonhole
  on the recognising automaton; the pumping lemma is never formalised.
  (*route*)
* The composition-failure argument replaces a citation with a construction: the
  word map computed by the two-way machine `S` is identified against its actual
  runs and given an explicit arity-1 presentation.  This is stronger locally
  and weaker globally — it is about that machine, not about two-way machines in
  general.  (*route*)
* The bounded-rank collapse follows the paper's argument, and the
  automaton-to-logic step it needs is the direction of Büchi's theorem that the
  development proves, so it is axiom-free.  (*equivalent*)
* Several formalised results sit on no critical path:
  `thm:two-parameter-semilinearity`, all six one-loop lemmas, the full and
  dichotomy forms of the semilinear-envelope lemma, the two-dimensional
  inverse-zeta band, and three of the five closure clauses (restriction,
  reversal, disjoint union).  They are certified statements that nothing else
  consumes.
