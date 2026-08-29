# A Computational Obstruction to Swapping Area and Dinv — Lean formalisation

This repository contains the paper

> **A Computational Obstruction to Swapping Area and Dinv:
> An Automata-Theoretic View of the q,t-Catalan Symmetry**
> Jineon Baek, Byung-Hak Hwang, Joonhyun La, Hongseok Yang

as [`paper.tex`](paper.tex), together with a Lean 4 formalisation of its
results in [`RequestProject/`](RequestProject/).

The paper introduces *weighted-rank polyregular transductions* (WRP) — a
transducer model sitting between the polyregular functions and deterministic
logspace — and proves that no WRP transduction swaps the `area` and `dinv`
statistics on Dyck paths, an automata-theoretic obstruction to a long-sought
combinatorial proof of the q,t-Catalan symmetry.  Along the way it classifies
Haglund's zeta map and the Narayana height sweep within the model hierarchy
(both lie in the fragment `sRR₁` of WRP and outside the polyregular class)
and shows that the *inverse* zeta map is not WRP.

## Layout

| Path | Contents |
|---|---|
| `paper.tex`, `paper.bib` | the paper |
| `RequestProject/` | the Lean sources (one library) |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | the pinned build configuration |
| [`ARCHITECTURE.md`](ARCHITECTURE.md) | module map: which file proves what, organised by paper section |
| [`STATUS.md`](STATUS.md) | theorem-by-theorem paper ↔ Lean correspondence, trust bases, and modelling conventions |

## Building

The project pins **Lean 4 v4.33.1** and the matching **Mathlib** release via
`lean-toolchain` and `lake-manifest.json`.  With
[elan](https://github.com/leanprover/elan) installed:

```bash
lake exe cache get   # fetch the prebuilt Mathlib cache; building Mathlib from scratch is infeasible
lake build
```

A green build **is** the verification: the development compiles with **zero
`sorry` and zero warnings**.  `RequestProject/Main.lean` imports every module,
so `lake build RequestProject.Main` elaborates the whole development.

## Trust base

Every result is proved from Lean's kernel primitives plus exactly **three**
axioms.  Each names a standard external result about MSO, finite automata,
semilinear sets, and polyregular maps:

| Axiom | Statement | Standard reference |
|---|---|---|
| `SliceMSO.buchi` | an MSO-definable language is recognised by a DFA | Büchi–Elgot–Trakhtenbrot |
| `msoDefinableRel2_semilinear_general` | an MSO-definable relation over a block-linear word family is semilinear | Büchi + Ginsburg–Spanier |
| `polyreg_regular_preimage` | polyregular preimages of regular languages are regular | Bojańczyk |

The automaton-to-MSO direction of Büchi–Elgot–Trakhtenbrot is a proved
theorem of the development (`detAuto_state_mso`); only the MSO-to-automaton
direction is admitted.

The ℤ-valued companion of the second axiom — the value graph of a regular rank
term along a block-linear family — is a theorem rather than an assumption.
`RankTermGraph.lean` proves
`SliceSemilinearN.regularRankTerm_value2_graph_semilinear` by unfolding a rank
term into a fixed signed combination of prefix ranks and bounded local
corrections; a prefix rank is the `ω`-weighted sum, over the finitely many
`(state, letter)` pairs, of the number of positions below the queried one
carrying that pair (`SlicePrefixRankGraph.lean`), those position sets are
MSO-definable by the proved `detAuto_state_mso`, and their counts are semilinear
by `count_graph_semilinear` (`SliceMSOCount.lean`), the fibres being positions of
a slice word whose length is affine in the two parameters.

The counting layer rests on no axiom.
`PresburgerCounting.count_graph_semilinear` is `lem:presburger-counting`,
stated in Mathlib vocabulary alone (`IsSemilinearSet`, `Nat.card`) so that it
can be compared with the literature without reference to this development.
`CountGeneral.lean` proves it from `ProperLinearRep.lean`,
`SemilinearMinMax.lean`, `KernelDichotomy.lean`, `SemilinearGraphArith.lean`,
`ProperPieceCount.lean` and `CountBaseCase.lean`.  The argument is elementary:
a semilinear set decomposes into proper linear pieces, whose linearly
independent periods make coefficient tuples unique; the linear fibre bound
forbids two independent integer vectors in the kernel of the parameter map, so
that kernel is cyclic and every fibre is an arithmetic progression with a
parameter-independent direction; the pieces then combine by inclusion–exclusion
over those progressions, each residue class counting as an interval with
definable endpoints.  The only external ingredient is Mathlib's
Ginsburg–Spanier bridge `presburger.definable_iff_isSemilinearSet`, used for
first-order closure; no Ehrhart theory or quasi-polynomiality enters.

Two consequences of it are what the towers consume: the joint count graph of a
two-parameter family (`twoParamCountGraph_proved`), obtained by instantiating
it at two parameters, and the row-uniform form
(`isSliceFamilySemilinear2_count_global`), obtained from that together with
`semilinearGraph3_affineOnResiduesAt_uniform`, which turns a semilinear count
graph in ℕ³ into rows that are eventually affine on the residues of one
row-uniform period.  Counting enters only the general-arity tie count of §9;
the arity-1 inverse-zeta capstone and the whole one-parameter slice analysis
behind `thm:wrp-slice-semilinearity` are independent of it.

To check what any theorem depends on:

```bash
echo 'import RequestProject.Main
#print axioms wrp_no_area_dinv_swap' | lake env lean --stdin
```

## Headline results

| Paper | Lean | File | Axioms beyond the kernel |
|---|---|---|---|
| `thm:wrp-no-swap` (no WRP area–dinv swap) | `wrp_no_area_dinv_swap` | `NoSwapWRP.lean` | `buchi` |
| `cor:model-free-obstruction` (model-free form) | `model_free_obstruction` | `NoSwapWRP.lean` | none |
| `cor:inverse-zeta-not-wrp` (arity 1) | `CopiedD4.inverse_zeta_not_wrp_arity1` | `CopiedD4.lean` | `buchi` |
| `cor:inverse-zeta-not-wrp` (general arity) | `CopiedTieSemilinear2.inverse_zeta_not_wrp` | `CopiedTieSemilinear2.lean` | `buchi`, `msoDefinableRel2_semilinear_general` |
| `thm:zeta-wrp` (ζ ∈ sRR₁ ⊆ WRP) | `zetaMap_realisedByWRP`, `zetaSweep_isSRR1` | `ZetaWRP.lean`, `SRR1.lean` | none |
| `prop:two-pyramid-criterion` (shared lower-bound criterion) | `two_pyramid_criterion` | `ZetaNotPolyreg.lean` | `polyreg_regular_preimage` |
| `thm:zeta-not-polyregular`, `cor:zeta-not-regular` | `zetaMap_not_polyregular`, `zetaMap_not_regular` | `ZetaNotPolyreg.lean` | `polyreg_regular_preimage` |
| `lem:H-two-pyramid` (height sweep on two-pyramids) | `heightSweep_twoPyramid` | `HeightSweepTwoPyramid.lean` | none |
| `lem:H-probe`, `thm:H-not-polyregular` (H beyond PolyReg) | `inRegularProbe_heightSweep_twoPyramid`, `heightSweep_not_polyregular`, `heightSweep_not_regular` | `HeightSweepNotPolyreg.lean` | `polyreg_regular_preimage` |
| `thm:wrp-closures` (all five clauses) | `WRPClosures.isWRP_*` | `WRPClosures.lean` | none |
| `thm:wrp-strict-over-poly` | `WRPStructure.polyreg_strict_subset_wrp` | `WRPStructure.lean` | `polyreg_regular_preimage` |
| `thm:wrp-logspace` (multihead model) | `wrp_isLogspaceMH`, `wrp_logspace_polytime` | `WRPLogspace.lean` | `buchi` |
| `thm:wrp-logspace` (worktape model) | `wrp_isLogspaceTM`, `wrp_logspaceTM_polytime` | `WRPWorktape.lean` | `buchi` |
| `cor:srr-quadratic` | `srr_quadratic` | `SRRQuadratic.lean` | `buchi` |
| `thm:wrp-strict-below-logspace` | `wrp_strict_below_logspace`, `wrp_strict_below_logspaceTM` | `WRPLogspace.lean`, `WRPWorktape.lean` | `buchi` |
| `thm:wrp-not-closed` (regular preimage) | `wrp_not_closed_preimage_comp` | `WRPCompWitness.lean` | none |
| `thm:wrp-not-closed` (composition) | `wrp_not_closed_composition` | `WRPNotClosedComp.lean` | `buchi` |
| `thm:bounded-rank-collapse`, `cor:rank-necessary` | `WRPBoundedRank.bounded_rank_collapse`, `.rank_necessary` | `WRPBoundedRank.lean` | none / `polyreg_regular_preimage` |
| `thm:wrp-slice-semilinearity` | `wrp_slice_profile_semilinear` | `NoSwapWRP.lean` | `buchi` |
| `thm:two-parameter-semilinearity` | `two_param_profile_semilinear_unconditional` | `TwoParamSemilinearity.lean` | `msoDefinableRel2_semilinear_general` |
| `lem:one-loop-finite-state`, `lem:one-loop-presburger` | `OneLoopSlice.one_loop_*` | `OneLoopSlice.lean` | `msoDefinableRel2_semilinear_general` |
| `thm:narayana-sweep` | `valleys_heightSweep_eq_doubleRises`, `heightSweep_bijOn`, `heightSweep_isSRR1` | `NarayanaSweep.lean`, `NarayanaBijection.lean`, `SRR1.lean` | none |

The paper's `def:wrp` is formalised twice, deliberately: the working class
`WRP.IsWRP` (the induced output order `≺` is required to totally order the
*selected* atoms — a superset of the paper's class, so every negative theorem
over it is stronger) and the verbatim paper class `WRP.IsWRPPaper`
(`WRPTieTotal.lean`).  Every headline theorem is restated over the verbatim
class in `WRPPaperTheorems.lean` / `WRPPaperNotClosed.lean` with the same
trust bases.  See [`STATUS.md`](STATUS.md) for the full correspondence and
the modelling conventions.
