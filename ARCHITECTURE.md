# Architecture

The Lean library `RequestProject` formalises `paper.tex`.  This file
maps the sources to the paper, section by section.  Result-level
correspondences and trust bases are in [`STATUS.md`](STATUS.md);
[`RequestProject/Main.lean`](RequestProject/Main.lean) imports everything and
summarises the axioms.

## §2 — Dyck paths and statistics

* `DyckPath.lean` — the `Step` alphabet `{U, D}`, Dyck paths (`IsDyckPath`,
  `DyckPath n`), `height`, `areaSeq`/`area`/`dinv`/`coarea`, the zeta map
  (`zetaMap`), wrapped-flat paths (`wrappedFlat`), first ascent and `tailU`,
  valleys/peaks/double rises, and the height sweep (`heightSweep`).
* `AreaSeq.lean` — the area-sequence ↔ Dyck-path round trip
  (`pathOfAreaSeq`, `areaSeq_pathOfAreaSeq`, `dyck_eq_of_areaSeq_eq`).
* `WrappedFlat.lean` — statistics of the slice `W_n`
  (`area_wrappedFlat`, `dinv_wrappedFlat`, `dinv_le_coarea`).
* `TriangularDecomp.lean`, `TightTargets.lean` — the deficit-zero analysis
  (`lem:deficit-zero-targets`, `cor:forced-triangular-pairs`).
* `Examples.lean` — decidable spot checks of the paper's worked examples.

## §3 — Transducer models

* `Transducers.lean` — shared vocabulary: `Realises`, `DFA'`,
  `IsRegularLang`.
* `MSO.lean` (+ `MSOClose.lean`, `MSOMark.lean`, `MSOMarkN.lean`) — MSO on
  words with intrinsic satisfaction, closure operations, and the marked-word
  encodings of free variables used throughout.
* `Polyregular.lean` — polyregular presentations (`Polyreg.Presentation`,
  `Polyreg.IsPolyregular`, `def:polyregular`) and the arity-1 fragment
  `Polyreg.IsRegular` (the deterministic MSO string transductions, i.e. by
  Engelfriet–Hoogeboom the 2DFT class).
* `WRP.lean` — rank sources and regular rank terms, the weighted-rank class
  `WRP.IsWRP` (`def:wrp`), the output order `wrpOrd`, conservativity
  (`isWRP_of_isPolyregular`).
* `PrefixAdditiveRank.lean` — the paper's `def:prefix-additive-rank`
  packaging and its equivalence with regular rank terms.
* `WRPArityPos.lean`, `ArityLift.lean` — the arity-positive convention and
  the generic arity-0 elimination (every copy gains an anchored coordinate).
* `WRPTieTotal.lean` — the verbatim paper classes: `WRP.IsWRPTieTotal`
  (χ itself a strict total order) and `WRP.IsWRPPaper` (χ-total + positive
  arity), with the inclusions into `WRP.IsWRP`.
* `SRR1.lean` — the scan-order fragment `WRP.IsSRR1` (`sRR₁ = SWR`) and the
  memberships `heightSweep_isSRR1`, `zetaSweep_isSRR1`.
* `TwoDFT.lean` — deterministic two-way transducers (`def:2dft`), used by the
  composition clause of `thm:wrp-not-closed`.

## §4 — Closure, complexity, and boundaries

* `WRPClosures.lean` — `thm:wrp-closures`: restriction, relabelling,
  reversal, disjoint union, and separator concatenation, plus the rank-term
  (R1) algebra.
* `WRPStructure.lean` — `thm:wrp-strict-over-poly` (PolyReg ⊊ WRP, witnessed
  by ζ).
* `WRPNonemptyRegular.lean` — `lem:wrp-nonempty-regular`.
* `WRPNotClosed.lean`, `WRPCompWitness.lean`, `WRPNotClosedComp.lean`,
  `SMapWRP.lean` — `thm:wrp-not-closed`: the witness `D`, the 2DFT `S`, the
  non-regular preimage, and the failure of composition closure.
* `WRPBoundedRank.lean` — `thm:bounded-rank-collapse` and
  `cor:rank-necessary` (bounded ranks collapse to polyregular; ζ needs
  unbounded rank).
* Machine models and `thm:wrp-logspace` / `cor:srr-quadratic` /
  `thm:wrp-strict-below-logspace`:
  * `Logspace.lean` — single-head bounded-counter transducers (`CounterDFT`)
    and the logspace witness `F_{≥0}` outside WRP;
  * `Multihead.lean` — the multihead bounded-counter model (`MHC`,
    `IsLogspaceMH`) with the pigeonhole halting bound;
  * `WRPLogspace.lean` — the verified WRP evaluator (marked-DFA sweeps,
    signed-counter rank comparisons, ≺-successor rounds):
    `wrp_isLogspaceMH`, `wrp_logspace_polytime`,
    `wrp_strict_below_logspace`;
  * `SRRQuadratic.lean` — the quadratic-time machine for scan-order `d = 1`
    presentations (`srr_quadratic`, `N ≤ D·(n+1)²`);
  * `LogspaceTM.lean` — the literal worktape model (`LogTM`,
    `IsLogspaceTM`);
  * `MHCOneHead.lean`, `MHCToTM.lean` — the proved two-stage simulation
    (head elimination, then binary counters on worktape tracks);
  * `WRPWorktape.lean` — the logspace theorems restated over the worktape
    model.

## §5 — Classifying the zeta map

* `ZetaClassification.lean` — ζ on two-pyramid paths, `area ∘ ζ = dinv`, the
  regular probe `lem:zeta-probe` with its DFA witness.
* `ZetaWRP.lean` — `thm:zeta-wrp`: the explicit WRP presentation realising ζ.
* `AdditiveSweep.lean`, `AdditiveSweepWRP.lean` — additive sweep
  transductions and `prop:alw-sweep-swr` (every additive sweep is in SWR).
* `ZetaNotPolyreg.lean` — `thm:zeta-not-polyregular` and
  `cor:zeta-not-regular`, via a counting encoder and the polyregular
  regular-preimage axiom.

## §7 — Regular-slice semilinearity

The slice analysis that powers both §8 and §9.

* `Semilinearity.lean`, `SliceSemilinear.lean`, `SliceSemilinearN.lean`,
  `SliceSemilinear2.lean` — linear and semilinear sets in `ℕ^d`, the bridge
  to Mathlib's `IsSemilinearSet` (Ginsburg–Spanier closures), the
  two-parameter slice-family notion, and the general admitted facts.
* `SliceAutomata.lean`, `SliceRank.lean`, `SliceMSO.lean`, `SliceOrder.lean`
  — the finite-state core: eventual periodicity of DFA states along
  `pre·loopⁿ·suf`, affine-on-residues rank accumulation, the Büchi axiom and
  the proved converse (`detAuto_state_mso`), eventually-periodic predicates.
* `SliceAffine*.lean`, `SliceThreshold.lean`, `SliceProfile*.lean`,
  `SliceFas*.lean`, `SliceDstar*.lean`, `SliceCell*.lean`,
  `SliceGrowthCollapse.lean`, `SliceFamilyCell.lean`, `SliceFamilyRank.lean`,
  and the remaining `Slice*` files — the general-arity discharge of the slice
  first-ascent analysis (`wrp_slice_profile_affine_general`), organised as a
  growth-collapse tower over the wrapped-flat slice.
* `EnvelopeMin.lean` — `lem:semilinear-envelope` (dichotomy and
  eventually-affine minimum).
* `OneLoopSlice.lean` — the paper's one-loop lemmas verbatim over an
  arbitrary slice `u·vⁿ·z` (`lem:one-loop-finite-state`,
  `lem:one-loop-presburger` (a)–(d), and the rank value graph), from the two
  general semilinearity axioms via a position-encoding engine.

## §8 — The no-swap theorem

* `NoSwapWRP.lean` — `thm:wrp-slice-semilinearity`
  (`wrp_slice_profile_semilinear`) and the headline `thm:wrp-no-swap`
  (`wrp_no_area_dinv_swap`): a WRP swap of area and dinv would make the
  non-semilinear triangular set `S_tri` semilinear.

## §9 — The inverse zeta map is not WRP

* `InverseZeta.lean`, `InverseZetaFas.lean`, `InverseZetaNotWRP.lean` — the
  copied slice `C_{m,n}`, its ζ-preimage pyramid rows, the first-ascent
  formula `⌈(m+n)/(m+1)⌉`, and the non-semilinear band.
* The `Copied*` tower (from `CopiedMark.lean` and `CopiedSetup.lean` through
  `CopiedTieSlice.lean`, `CopiedTieCounting.lean`, `CopiedTieSemilinear2.lean`
  and `CopiedD4.lean`) — the copied-slice analysis: marked automata over the
  two-parameter slice, region descriptors and cells, the `d*`-rank and its
  lex-minimum characterisation, gated argmin machinery, tie counting, and the
  final assemblies `CopiedD4.inverse_zeta_not_wrp_arity1` (arity 1,
  Büchi-only) and `CopiedTieSemilinear2.inverse_zeta_not_wrp` (general
  arity).
* `TwoParamSemilinearity.lean` — `thm:two-parameter-semilinearity`: the ℕ⁴
  first-ascent/tail profile of a linear-growth WRP transduction on the
  two-parameter family is semilinear.

## §6 — The Narayana sweep

* `NarayanaSweep.lean` — the height sweep swaps valleys and double rises
  (`thm:narayana-sweep`), with the non-involutivity counterexample.
* `NarayanaBijection.lean` — `heightSweep_bijOn`: the sweep restricts to a
  bijection of `D_n`.
* `NarayanaWRP.lean` — the explicit WRP presentation of the height sweep.

## Paper-exact statement layer

* `WRPPaperTheorems.lean` — every headline theorem restated verbatim over the
  paper class `WRP.IsWRPPaper` (a fortiori corollaries; identical trust
  bases).
* `WRPPaperNotClosed.lean` — `thm:wrp-not-closed` with paper-exact witnesses
  (the block-refined concatenation tie-order and the arity lift).
