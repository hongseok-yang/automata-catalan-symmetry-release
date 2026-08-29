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

## What the formalisation assumes

The paper proves its results from scratch apart from a handful of standard
results it takes from the literature.  This table lists those results and what
becomes of each in Lean.  Three are assumed, three are not needed at all, and
the rest are proved — either here or in Mathlib.

| Result the paper uses | Where the paper uses it | In the formalisation |
|---|---|---|
| Büchi–Elgot–Trakhtenbrot, logic to automata: an MSO-definable language is recognised by a finite automaton | §3, and throughout the slice analysis of §7 | **assumed** (`SliceMSO.buchi`) |
| Büchi–Elgot–Trakhtenbrot, automata to logic | §4's restriction clause, and the prefix-rank argument | proved (`SliceMSO.detAuto_state_mso`) |
| Semilinear sets are exactly the Presburger-definable ones (Ginsburg–Spanier) | §7 | proved in Mathlib (`presburger.definable_iff_isSemilinearSet`) |
| The two above, combined over a slice: MSO-definable position tuples along a block-linear family form a semilinear family | §7 and §9 | **assumed** (`msoDefinableRel2_semilinear_general`) |
| Polyregular maps have regular preimages of regular languages (Bojańczyk) | §5 and §6 lower bounds | **assumed** (`polyreg_regular_preimage`) |
| Polyregular maps are closed under composition (Bojańczyk) | §5's two-pyramid criterion | not needed |
| Linear-growth collapse for polyregular maps (Bojańczyk) | §5's two-pyramid criterion | not needed |
| Woods' parametric Presburger counting, and Ehrhart theory behind it | §7's proof of the counting lemma | not needed |
| Engelfriet–Hoogeboom: MSO transductions are exactly the two-way transducers | §3, and to read the "not two-way-realisable" corollaries | not used as a proof step — see the note below |

So the trust base is **three axioms**, each a standard external result:

| Axiom | Statement |
|---|---|
| `SliceMSO.buchi` | an MSO-definable language over a finite alphabet is recognised by a DFA |
| `msoDefinableRel2_semilinear_general` | MSO-definable position tuples over a block-linear word family form a semilinear family |
| `polyreg_regular_preimage` | the preimage of a regular language under a polyregular map is regular |

Three of the paper's external inputs disappear, at two places where the
formalisation proves things differently.  The counting lemma
`lem:presburger-counting`, which the paper derives from Woods' theorem, is
proved outright by an elementary argument, so neither Woods' theorem nor the
Ehrhart theory behind it is needed.  And the lower bounds on ζ and on the
height sweep, which the paper obtains by composing with an encoder and
collapsing the composite to a two-way machine, are obtained in Lean by applying
the polyregular preimage closure twice — so neither the collapse nor
composition closure is needed.

Engelfriet–Hoogeboom is a third case, and a different one: it is not an
assumption the formalisation discharges, but the bridge that lets the reader
interpret two of the results.  The Lean statements about ζ and `H` are about
arity-1 MSO transductions; reading them as statements about two-way machines
is exactly what that theorem licenses, and it is quoted rather than proved.
The two-way machine model itself *is* formalised and is used, as the witness
for the composition failure in `thm:wrp-not-closed`.

To check what any theorem depends on:

```bash
echo 'import RequestProject.Main
#print axioms wrp_no_area_dinv_swap' | lake env lean --stdin
```

One caveat on "three axioms": it holds for every mathematical result in the
development.  The paper's numeric worked examples are discharged by compiled
evaluation, so each such example additionally trusts the Lean compiler; no
headline theorem depends on one.

## Headline results

| Paper | Lean | File | Axioms beyond the kernel |
|---|---|---|---|
| `thm:wrp-no-swap` (no WRP area–dinv swap) | `wrp_no_area_dinv_swap` | `NoSwapWRP.lean` | `buchi` |
| `cor:model-free-obstruction` (model-free form) | `model_free_obstruction` | `NoSwapWRP.lean` | none |
| `cor:inverse-zeta-not-wrp` (arity 1) | `CopiedD4.inverse_zeta_not_wrp_arity1` | `CopiedD4.lean` | `buchi` |
| `cor:inverse-zeta-not-wrp` (general arity) | `CopiedTieSemilinear2.inverse_zeta_not_wrp` | `CopiedTieSemilinear2.lean` | `buchi`, `msoDefinableRel2_semilinear_general` |
| `thm:zeta-wrp` (ζ ∈ sRR₁ ⊆ WRP) | `zetaMap_realisedByWRP`, `zetaSweep_isSRR1` | `ZetaWRP.lean`, `SRR1.lean` | none |
| `prop:two-pyramid-criterion` (shared lower-bound criterion) | `ZetaNotPolyreg.two_pyramid_criterion` | `ZetaNotPolyreg.lean` | `polyreg_regular_preimage` |
| `thm:zeta-not-polyregular`, `cor:zeta-not-regular` | `ZetaNotPolyreg.zetaMap_not_polyregular`, `ZetaNotPolyreg.zetaMap_not_regular` | `ZetaNotPolyreg.lean` | `polyreg_regular_preimage` |
| `lem:H-two-pyramid` (height sweep on two-pyramids) | `heightSweep_twoPyramid` | `HeightSweepTwoPyramid.lean` | none |
| `lem:H-probe`, `thm:H-not-polyregular` (H beyond PolyReg) | `HeightSweepNotPolyreg.inRegularProbe_heightSweep_twoPyramid`, `HeightSweepNotPolyreg.heightSweep_not_polyregular`, `HeightSweepNotPolyreg.heightSweep_not_regular` | `HeightSweepNotPolyreg.lean` | `polyreg_regular_preimage` |
| `thm:wrp-closures` (all five clauses) | `WRPClosures.isWRP_*` | `WRPClosures.lean` | none |
| `thm:wrp-strict-over-poly` | `WRPStructure.polyreg_strict_subset_wrp` | `WRPStructure.lean` | `polyreg_regular_preimage` |
| `thm:wrp-logspace` (multihead model) | `wrp_isLogspaceMH`, `wrp_logspace_polytime` | `WRPLogspace.lean` | `buchi` |
| `thm:wrp-logspace` (worktape model) | `wrp_isLogspaceTM`, `wrp_logspaceTM_polytime` | `WRPWorktape.lean` | `buchi` |
| `cor:srr-quadratic` | `srr_quadratic` | `SRRQuadratic.lean` | `buchi` |
| `thm:wrp-strict-below-logspace` | `wrp_strict_below_logspace`, `wrp_strict_below_logspaceTM` | `WRPLogspace.lean`, `WRPWorktape.lean` | `buchi` |
| `thm:wrp-not-closed` (regular preimage) | `WRPComp.wrp_not_closed_preimage_comp` | `WRPCompWitness.lean` | none |
| `thm:wrp-not-closed` (composition) | `WRPComp.wrp_not_closed_composition` | `WRPNotClosedComp.lean` | `buchi` |
| `thm:bounded-rank-collapse`, `cor:rank-necessary` | `WRPBoundedRank.bounded_rank_collapse`, `.rank_necessary` | `WRPBoundedRank.lean` | none / `polyreg_regular_preimage` |
| `thm:wrp-slice-semilinearity` | `wrp_slice_profile_semilinear` | `NoSwapWRP.lean` | `buchi` |
| `thm:two-parameter-semilinearity` | `TwoParamSemilinearity.two_param_profile_semilinear_unconditional` | `TwoParamSemilinearity.lean` | `msoDefinableRel2_semilinear_general` |
| `lem:one-loop-finite-state`, `lem:one-loop-presburger` | `OneLoopSlice.one_loop_*` | `OneLoopSlice.lean` | `msoDefinableRel2_semilinear_general` |
| `thm:narayana-sweep` | `valleys_heightSweep`, `doubleRises_heightSweep`, `heightSweep_bijOn`, `heightSweep_isSRR1` | `NarayanaBijection.lean`, `SRR1.lean` | none |

Lean names are given fully qualified, so they can be pasted into
`#print axioms` directly.  `NarayanaSweep.lean` also carries versions of the two statistic
identities with an explicit `semilength P ≥ 1`, which the paper's statement
does not have; the row cites the hypothesis-free forms.
The logspace rows prove the paper's "polynomial time" clause with an explicit
bound of the shape `cardQ · (n+2)^h · (C·(n+1)+1)^c`, where the head count `h`
depends on the presentation's arity; the output-length clause `|T(w)| = O(n^k)`
of `thm:wrp-logspace` is not formalised.

## How the formalisation differs from the paper

A machine-checked proof certifies exactly its formal statement, so the
differences matter.  They fall into three kinds.  The full list, with Lean
names and file references, is in [`STATUS.md`](STATUS.md); the entries below
are the ones worth knowing before reading either document.

### Definitions

* Transductions are modelled as total functions into "output word or
  undefined", and *realising* a map on a set of inputs constrains the
  transduction only there.
* `def:wrp` is formalised twice: a verbatim class asking exactly what
  the paper asks, and a working class asking only that the combined output
  order be total on selected atoms.  The working class is a *superset*, which
  makes negative theorems over it stronger.  No map is exhibited that
  separates the two, so the inclusion is not known to be strict.
* Lean permits copies of arity 0 where the paper requires arity ≥ 1.
  The two conventions are proved to differ only on the empty input, and the
  extra freedom is genuinely used by one witness.
* "Deterministic two-way transducer" is rendered as the arity-1 MSO
  transduction class, with the machine equivalence quoted rather than proved.
* The paper's prefix-additive rank functions and Lean's regular rank
  terms are proved to define the same class, in both directions.
* The inverse zeta map is never defined; its corollary is rendered as
  left inversion, which is a weaker hypothesis to refute and avoids depending
  on ζ's classical bijectivity.
* That ζ is a bijection is not formalised, and `bounce` does not occur
  in the development.  Nothing depends on either.

### Statements

* The two-pyramid criterion drops the paper's growth hypothesis
  entirely, because the formal proof never enters the two-way class.
* The no-swap theorem assumes no bijectivity, matching the paper.
* The inverse-zeta corollary comes in a general-arity form and an
  arity-1 form; the latter is stated about arity-1 presentations rather than
  about a class, and rests on a smaller trust base.
* The slice-semilinearity theorem is proved in a stronger form —
  "defined on at least one member of the family" rather than on all — with the
  paper's literal form exported separately.  The weaker hypothesis cannot be
  dropped, and the repository gives the refuting example.
* Every negative theorem is stated over the larger working class, with
  verbatim-class restatements at identical trust bases.
* `thm:wrp-closures` is the least complete: the arity bound that the
  paper's statement carries is not tracked, definition by cases and
  letter-deleting relabellings are missing, and because closure statements are
  positive, proving them for the larger class does not yield the paper's
  statement — paper-class versions exist only for relabelling and
  concatenation.
* The output-length clause of `thm:wrp-logspace` is not formalised,
  and the complexity layer fixes the input alphabet to `{U, D}` where the paper
  allows any finite alphabet.
* Engelfriet–Hoogeboom and the linear-growth collapse have no Lean
  counterpart; neither is needed.
* Of `prop:conservative`, only the direction actually used is proved.

### Proofs

* The counting lemma is proved from scratch rather than quoted from
  Woods: decompose a semilinear set into pieces with linearly independent
  periods, use the linear bound once to force the kernel to be at most
  one-dimensional, then count arithmetic progressions by inclusion–exclusion.
* The two-pyramid criterion trades three of the paper's external
  theorems for one, applying the polyregular preimage closure twice instead of
  composing and collapsing.
* The slice-semilinearity theorem does not follow the paper's proof at
  all.  Instead of Presburger definability plus counting, it uses the
  linear-growth bound structurally and reduces to finitely many cells — which
  is why it needs only the Büchi axiom.
* The paper's own §7 one-loop lemmas *are* stated verbatim, but they are
  short consequences of the semilinearity axiom rather than independent proofs,
  and nothing else depends on them.
* The inverse-zeta capstone bypasses the machinery the paper builds for
  it, finishing with an arithmetic contradiction; both of the paper's
  ingredients are formalised but unused.
* The Narayana sweep is proved without the paper's contour-forest normal
  form.
* The quadratic scan-order evaluator is a different algorithm from the
  paper's, with no counters and an explicit constant.
* The integer-valued companion of the semilinearity axiom is a theorem,
  but its proof applies that axiom twice — it removes an assumption, it does not
  make the layer assumption-free.
* Counting is used by the rank-term value graph, and so by
  `thm:two-parameter-semilinearity` and the one-loop lemmas as well as the
  general-arity §9 tie count.  It does not enter the one-parameter slice
  analysis behind the no-swap theorem, nor the arity-1 inverse-zeta capstone.

Some formalised results sit on no critical path: `thm:two-parameter-semilinearity`,
the one-loop lemmas, the full semilinear-envelope lemma, and three of the five
closure clauses are certified statements that nothing else consumes.
