# A Computational Obstruction to Swapping Area and Dinv — Lean formalisation

This repository contains the paper

> **A Computational Obstruction to Swapping Area and Dinv:
> An Automata-Theoretic View of the q,t-Catalan Symmetry**
> Jineon Baek, Byung-Hak Hwang, Joonhyun La, Hongseok Yang

as [`paper.tex`](paper.tex), together with a Lean 4
formalisation of its results in [`RequestProject/`](RequestProject/).

The paper introduces *weighted-rank polyregular transductions* (WRP) — a
transducer model sitting between the polyregular functions and deterministic
logspace — and proves that no WRP transduction swaps the `area` and `dinv`
statistics on Dyck paths, an automata-theoretic obstruction to a long-sought
combinatorial proof of the q,t-Catalan symmetry.  Along the way it classifies
Haglund's zeta map within the model hierarchy and shows that the *inverse*
zeta map is not WRP.

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

Every result is proved from Lean's kernel primitives plus exactly **six**
axioms, all standard textbook facts and all *project-agnostic* (none mentions
any notion defined in this project):

| Axiom | Statement | Standard reference |
|---|---|---|
| `SliceMSO.buchi` | an MSO-definable language is recognised by a DFA | Büchi–Elgot–Trakhtenbrot |
| `msoDefinableRel2_semilinear_general` | an MSO-definable relation over a block-linear word family is semilinear | Büchi + Ginsburg–Spanier |
| `regularRankTerm_value2_graph_semilinear` | the ℤ-valued sibling for regular rank terms | ibid. |
| `isSliceFamilySemilinear2_count` | bounded Presburger counting (`lem:presburger-counting`) | Ginsburg–Spanier |
| `twoParamCountGraph_admitted` | its joint-graph form for two-parameter families | ibid. |
| `polyreg_regular_preimage` | polyregular preimages of regular languages are regular | Bojańczyk |

To check what any theorem depends on:

```bash
echo 'import RequestProject.Main
#print axioms wrp_no_area_dinv_swap' | lake env lean --stdin
```

## Headline results

| Paper | Lean | File | Axioms beyond the kernel |
|---|---|---|---|
| `thm:wrp-no-swap` (no WRP area–dinv swap) | `wrp_no_area_dinv_swap` | `NoSwapWRP.lean` | `buchi` |
| `cor:inverse-zeta-not-wrp` (arity 1) | `CopiedD4.inverse_zeta_not_wrp_arity1` | `CopiedD4.lean` | `buchi` |
| `cor:inverse-zeta-not-wrp` (general arity) | `CopiedTieSemilinear2.inverse_zeta_not_wrp` | `CopiedTieSemilinear2.lean` | `buchi` + the three semilinearity axioms |
| `thm:zeta-wrp` (ζ ∈ SWR ⊆ WRP) | `zetaMap_realisedByWRP`, `zetaSweep_isSRR1` | `ZetaWRP.lean`, `SRR1.lean` | none |
| `thm:zeta-not-polyregular`, `cor:zeta-not-regular` | `ZetaNotPolyreg.zetaMap_not_polyregular`, `.zetaMap_not_regular` | `ZetaNotPolyreg.lean` | `polyreg_regular_preimage` |
| `thm:wrp-closures` (all five clauses) | `WRPClosures.isWRP_*` | `WRPClosures.lean` | none |
| `thm:wrp-strict-over-poly` | `WRPStructure.polyreg_strict_subset_wrp` | `WRPStructure.lean` | `buchi`, `polyreg_regular_preimage` |
| `thm:wrp-logspace` (multihead model) | `wrp_isLogspaceMH`, `wrp_logspace_polytime` | `WRPLogspace.lean` | `buchi` |
| `thm:wrp-logspace` (worktape model) | `wrp_isLogspaceTM`, `wrp_logspaceTM_polytime` | `WRPWorktape.lean` | `buchi` |
| `cor:srr-quadratic` | `srr_quadratic` | `SRRQuadratic.lean` | `buchi` |
| `thm:wrp-strict-below-logspace` | `wrp_strict_below_logspace`, `wrp_strict_below_logspaceTM` | `WRPLogspace.lean`, `WRPWorktape.lean` | `buchi` |
| `thm:wrp-not-closed` | `wrp_not_closed_preimage_comp`, `wrp_not_closed_composition` | `WRPCompWitness.lean`, `WRPNotClosedComp.lean` | `buchi` |
| `thm:bounded-rank-collapse`, `cor:rank-necessary` | `WRPBoundedRank.bounded_rank_collapse`, `.rank_necessary` | `WRPBoundedRank.lean` | none / `polyreg_regular_preimage` |
| `thm:wrp-slice-semilinearity` | `wrp_slice_profile_semilinear` | `NoSwapWRP.lean` | `buchi` |
| `thm:two-parameter-semilinearity` | `two_param_profile_semilinear_unconditional` | `TwoParamSemilinearity.lean` | the three semilinearity axioms |
| `lem:one-loop-finite-state`, `lem:one-loop-presburger` | `OneLoopSlice.one_loop_*` | `OneLoopSlice.lean` | the two general semilinearity axioms |
| `thm:narayana-sweep` | `valleys_heightSweep_eq_doubleRises`, `heightSweep_bijOn`, `heightSweep_isSRR1` | `NarayanaSweep.lean`, `NarayanaBijection.lean`, `SRR1.lean` | none |

The paper's `def:wrp` is formalised twice, deliberately: the working class
`WRP.IsWRP` (tie-order only required to totally order the *selected* atoms —
a superset, so every negative theorem over it is stronger) and the verbatim
paper class `WRP.IsWRPPaper` (`WRPTieTotal.lean`).  Every headline theorem is
restated over the verbatim class in `WRPPaperTheorems.lean` /
`WRPPaperNotClosed.lean` with the same trust bases.  See
[`STATUS.md`](STATUS.md) for the full correspondence and the modelling
conventions.
