/-
# Root module: imports the entire formalisation

Lean formalisation of
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang (`paper.tex`).

Importing this module elaborates every file of the development.  `lake build`
succeeds with 0 `sorry` and 0 warnings.  The entire development admits exactly
six axioms beyond Lean's kernel primitives; each packages a standard external
result, or a direct consequence of one, some stated through the development's
own abstractions so that they apply directly where they are needed:

* `SliceMSO.buchi` — the MSO ⇒ automaton half of Büchi–Elgot–Trakhtenbrot
  (the converse direction is the theorem `detAuto_state_mso`);
* `SliceSemilinearN.msoDefinableRel2_semilinear_general` — an MSO-definable
  relation over a block-linear word family is semilinear (Ginsburg–Spanier);
* `SliceSemilinearN.regularRankTerm_value2_graph_semilinear` — its ℤ-valued
  sibling for regular rank terms;
* `SliceSemilinearN.isSliceFamilySemilinear2_count` — bounded Presburger
  counting (`lem:presburger-counting`), per-row form;
* `TwoParamSemilinearity.twoParamCountGraph_admitted` — its joint-graph form
  for the two-parameter family;
* `polyreg_regular_preimage` — polyregular preimages of regular languages are
  regular (Bojańczyk).

The headline results and where they live:

* `wrp_no_area_dinv_swap` (`NoSwapWRP.lean`) — `thm:wrp-no-swap`, the no-swap
  theorem, kernel + `buchi` only — with its model-free combinatorial half
  `model_free_obstruction` (`cor:model-free-obstruction`, axiom-clean);
* `CopiedTieSemilinear2.inverse_zeta_not_wrp` (general arity) and
  `CopiedD4.inverse_zeta_not_wrp_arity1` — `cor:inverse-zeta-not-wrp`;
* `zetaMap_realisedByWRP` / `zetaSweep_isSRR1` (`ZetaWRP.lean`, `SRR1.lean`)
  and `ZetaNotPolyreg.zetaMap_not_polyregular` — the §5 zeta classification,
  the lower bound via the shared criterion
  `ZetaNotPolyreg.two_pyramid_criterion` (`prop:two-pyramid-criterion`);
* `heightSweep_twoPyramid` (`HeightSweepTwoPyramid.lean`) and
  `HeightSweepNotPolyreg.heightSweep_not_polyregular`
  (`HeightSweepNotPolyreg.lean`) — `lem:H-two-pyramid`, `lem:H-probe`, and
  `thm:H-not-polyregular`: the height sweep is beyond PolyReg;
* `wrp_isLogspaceMH` / `wrp_strict_below_logspace` (`WRPLogspace.lean`),
  `srr_quadratic` (`SRRQuadratic.lean`), and the worktape-model versions
  `wrp_isLogspaceTM` / `wrp_strict_below_logspaceTM` (`WRPWorktape.lean`);
* the §4 closures and boundaries (`WRPClosures.lean`, `WRPStructure.lean`,
  `WRPNotClosed*.lean`, `WRPBoundedRank.lean`) and the paper-exact statement
  layer (`WRPTieTotal.lean`, `WRPPaperTheorems.lean`);
* `two_param_profile_semilinear_unconditional`
  (`TwoParamSemilinearity.lean`) — `thm:two-parameter-semilinearity`;
* the general one-loop lemmas over `u·vⁿ·z` (`OneLoopSlice.lean`) —
  `lem:one-loop-finite-state`, `lem:one-loop-presburger`;
* `valleys_heightSweep_eq_doubleRises` / `doubleRises_heightSweep_eq_valleys`
  (`NarayanaSweep.lean`), `heightSweep_bijOn` (`NarayanaBijection.lean`), and
  `heightSweep_isSRR1` (`SRR1.lean`) — `thm:narayana-sweep`.

See `README.md` for building and verifying, and `ARCHITECTURE.md` for the
module map.
-/
import RequestProject.AdditiveSweep
import RequestProject.AdditiveSweepWRP
import RequestProject.AreaSeq
import RequestProject.ArityLift
import RequestProject.CopiedAchSetFold
import RequestProject.CopiedAchSetFold2
import RequestProject.CopiedAchieverLocus
import RequestProject.CopiedAffineAt
import RequestProject.CopiedBandRunGate
import RequestProject.CopiedBoundedGate
import RequestProject.CopiedBoundedGateBand
import RequestProject.CopiedCells
import RequestProject.CopiedCluster
import RequestProject.CopiedCountStrict
import RequestProject.CopiedCountTie
import RequestProject.CopiedCounts
import RequestProject.CopiedD4
import RequestProject.CopiedDeepRunGate
import RequestProject.CopiedDischarge
import RequestProject.CopiedDstar
import RequestProject.CopiedDstarC
import RequestProject.CopiedDstarCMS
import RequestProject.CopiedFullGate
import RequestProject.CopiedGateEP
import RequestProject.CopiedGates
import RequestProject.CopiedKernels
import RequestProject.CopiedKernelsBounded
import RequestProject.CopiedLandmark
import RequestProject.CopiedLandmarkF
import RequestProject.CopiedMark
import RequestProject.CopiedRank
import RequestProject.CopiedRecount
import RequestProject.CopiedRegionF
import RequestProject.CopiedSelConst
import RequestProject.CopiedSelUniform
import RequestProject.CopiedSelector
import RequestProject.CopiedSelectorMS
import RequestProject.CopiedSetup
import RequestProject.CopiedSetupBound
import RequestProject.CopiedSetupMS
import RequestProject.CopiedSlopeBound
import RequestProject.CopiedSufRunGate
import RequestProject.CopiedTie2b
import RequestProject.CopiedTieBridge
import RequestProject.CopiedTieCounting
import RequestProject.CopiedTieGate
import RequestProject.CopiedTieGateF
import RequestProject.CopiedTieSemilinear2
import RequestProject.CopiedTieSlice
import RequestProject.DyckPath
import RequestProject.EnvelopeMin
import RequestProject.Examples
import RequestProject.HeightSweepNotPolyreg
import RequestProject.HeightSweepTwoPyramid
import RequestProject.InverseZeta
import RequestProject.InverseZetaFas
import RequestProject.InverseZetaNotWRP
import RequestProject.Logspace
import RequestProject.LogspaceTM
import RequestProject.MHCOneHead
import RequestProject.MHCToTM
import RequestProject.MSO
import RequestProject.MSOClose
import RequestProject.MSOMark
import RequestProject.MSOMarkN
import RequestProject.Multihead
import RequestProject.NarayanaBijection
import RequestProject.NarayanaSweep
import RequestProject.NarayanaWRP
import RequestProject.NoSwapWRP
import RequestProject.OneLoopSlice
import RequestProject.Polyregular
import RequestProject.PrefixAdditiveRank
import RequestProject.SMapWRP
import RequestProject.SRR1
import RequestProject.SRRQuadratic
import RequestProject.Semilinearity
import RequestProject.SliceAffine
import RequestProject.SliceAffineSelect
import RequestProject.SliceAutomata
import RequestProject.SliceBoundaryMinCore
import RequestProject.SliceBridge
import RequestProject.SliceCellClassifyGA
import RequestProject.SliceCellConvGA
import RequestProject.SliceConv
import RequestProject.SliceCount
import RequestProject.SliceCountSlice
import RequestProject.SliceDstar
import RequestProject.SliceDstarBridge
import RequestProject.SliceDstarBridgeGA
import RequestProject.SliceDstarCore
import RequestProject.SliceDstarGA
import RequestProject.SliceDstarGateGA
import RequestProject.SliceFamilyCell
import RequestProject.SliceFamilyRank
import RequestProject.SliceFasAssembly
import RequestProject.SliceFasAssemblyGA
import RequestProject.SliceFasBridges
import RequestProject.SliceFasCount
import RequestProject.SliceFasCountGA
import RequestProject.SliceFasGates
import RequestProject.SliceFasGatesGA
import RequestProject.SliceFasSelector
import RequestProject.SliceFasSelectorGA
import RequestProject.SliceFasTie
import RequestProject.SliceGatedConv
import RequestProject.SliceGrowthCollapse
import RequestProject.SliceLexCount
import RequestProject.SliceLexOrder
import RequestProject.SliceMSO
import RequestProject.SliceMarkN
import RequestProject.SliceOrder
import RequestProject.SliceOutput
import RequestProject.SlicePeriodStar
import RequestProject.SliceProfile
import RequestProject.SliceProfileDischarge
import RequestProject.SliceProfileDischargeGA
import RequestProject.SliceRank
import RequestProject.SliceRankAffine
import RequestProject.SliceRankAtom
import RequestProject.SliceRankBlock
import RequestProject.SliceRankRegions
import RequestProject.SliceRankThreshold
import RequestProject.SliceReRoot
import RequestProject.SliceSelCount
import RequestProject.SliceSelect
import RequestProject.SliceSemilinear
import RequestProject.SliceSemilinear2
import RequestProject.SliceSemilinearN
import RequestProject.SliceThreshold
import RequestProject.SliceVectorLexMin
import RequestProject.SliceWords
import RequestProject.TightTargets
import RequestProject.Transducers
import RequestProject.TriangularDecomp
import RequestProject.TwoDFT
import RequestProject.TwoParamSemilinearity
import RequestProject.WRP
import RequestProject.WRPArityPos
import RequestProject.WRPBoundedRank
import RequestProject.WRPClosures
import RequestProject.WRPCompWitness
import RequestProject.WRPLogspace
import RequestProject.WRPNonemptyRegular
import RequestProject.WRPNotClosed
import RequestProject.WRPNotClosedComp
import RequestProject.WRPPaperNotClosed
import RequestProject.WRPPaperTheorems
import RequestProject.WRPStructure
import RequestProject.WRPTieTotal
import RequestProject.WRPWorktape
import RequestProject.WrappedFlat
import RequestProject.ZetaClassification
import RequestProject.ZetaNotPolyreg
import RequestProject.ZetaWRP
