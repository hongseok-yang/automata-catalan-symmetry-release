/-
# `d*` for general arity — the affine bridge, stage 1 (GA-5.11: the setup fold)

The adjudicated GA-5 bridge starts with the STAGE-1 common-period setup: a single
`(m, p)` at which

* every cell's rank families `Rcell`/`Bcell` (from
  `SliceFamilyRank.rank_cell_decomp`, chosen per copy and per descriptor tuple) have
  GLOBAL slopes — aligned over the flattened cell list by
  `rankAffine_align_common_period` and rescaled to `p` by `RankAffine.iterate`;
* every copy's selected-`D` DFA (`exists_selDDFA`) has its `bFN` function-iterate
  periodic — folded in by the product of the per-copy periods.

Gate-sentence periods are deliberately NOT folded here: per the adjudicated two-stage
design (GA-5.10), the anchor gates are built AT `p` and their `mso_slice_eventually-
Periodic` periods enter only at stage 2 (`p* := p · ∏ p_sent`), breaking the
gate-period circularity.

Axiom-clean except the DFA layer (+`SliceMSO.buchi`).
-/
import RequestProject.SliceDstarGateGA
import RequestProject.SliceFamilyRank
import RequestProject.SliceFasBridges
import RequestProject.SliceDstarBridge

namespace SliceDstarBridgeGA

open WRP Step SliceFamilyCell SliceDstarGA SliceDstarGateGA SliceRankAtom
  SliceMarkN MSOMarkN SliceThreshold SliceAffine SliceOrder SliceLexOrder SliceDstarCore SliceBoundaryMinCore SliceDstar
open scoped Classical

/-- **The stage-1 common-period setup, general arity**: one `(m, p)` with global
rank slopes for every cell family and `bFN` function-iterate periodicity for every
copy's selected-`D` DFA. -/
theorem dstar_setup_GA (P : WRP.Presentation Step Step) (B : ℕ) :
    ∃ (m p : ℕ)
      (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
      (Rcell Bcell : (c : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c) → RegionSpec B) → ℕ → Fin P.d → ℤ)
      (PR PBn : (c : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c) → RegionSpec B) → Fin P.d → ℤ),
      1 ≤ p ∧ B + 1 ≤ m ∧
      (∀ (c : Fin P.toPoly.K) (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ),
        (∀ i, ī i < w.length) →
        ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D))) ∧
      (∀ (c : Fin P.toPoly.K) (g : ℕ), m ≤ g →
        (bFN (Mc c))^[g + p] = (bFN (Mc c))^[g]) ∧
      (∀ (c : Fin P.toPoly.K) (rs : Fin (P.toPoly.arity c) → RegionSpec B) (t n : ℕ),
        B + 1 ≤ t → t + B + 1 ≤ n →
        P.rank c (wrappedFlat n) (cellTuple rs t n)
          = fun i => Rcell c rs t i + Bcell c rs n i) ∧
      (∀ (c : Fin P.toPoly.K) (rs : Fin (P.toPoly.arity c) → RegionSpec B) (t : ℕ),
        m ≤ t → Rcell c rs (t + p) = Rcell c rs t + PR c rs) ∧
      (∀ (c : Fin P.toPoly.K) (rs : Fin (P.toPoly.arity c) → RegionSpec B) (n : ℕ),
        m ≤ n → Bcell c rs (n + p) = Bcell c rs n + PBn c rs) := by
  classical
  -- the per-cell rank decompositions
  have hdec := fun (c : Fin P.toPoly.K) (rs : Fin (P.toPoly.arity c) → RegionSpec B) =>
    SliceFamilyRank.rank_cell_decomp P c rs
  choose Rcell Bcell hRA hBA heq using hdec
  -- align all cell families at one period
  obtain ⟨mR, pR, hpR, halign⟩ := SliceFasBridges.rankAffine_align_common_period
    ((List.finRange P.toPoly.K).flatMap (fun c =>
      (regionTuples B (P.toPoly.arity c)).flatMap (fun rs =>
        [Rcell c rs, Bcell c rs])))
    (by
      intro F hF
      rw [List.mem_flatMap] at hF
      obtain ⟨c, _, hF⟩ := hF
      rw [List.mem_flatMap] at hF
      obtain ⟨rs, _, hF⟩ := hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact hRA c rs
      · rw [List.mem_cons] at hF
        rcases hF with rfl | hF
        · exact hBA c rs
        · exact absurd hF (by simp))
  have hslopes : ∀ (c : Fin P.toPoly.K) (rs : Fin (P.toPoly.arity c) → RegionSpec B),
      ∃ PRv PBv : Fin P.d → ℤ,
        (∀ t, mR ≤ t → Rcell c rs (t + pR) = Rcell c rs t + PRv) ∧
        (∀ n, mR ≤ n → Bcell c rs (n + pR) = Bcell c rs n + PBv) := by
    intro c rs
    obtain ⟨PRv, hPRv⟩ := halign (Rcell c rs)
      (by rw [List.mem_flatMap]
          refine ⟨c, List.mem_finRange c, ?_⟩
          rw [List.mem_flatMap]
          exact ⟨rs, mem_regionTuples B _ rs, by simp⟩)
    obtain ⟨PBv, hPBv⟩ := halign (Bcell c rs)
      (by rw [List.mem_flatMap]
          refine ⟨c, List.mem_finRange c, ?_⟩
          rw [List.mem_flatMap]
          exact ⟨rs, mem_regionTuples B _ rs, by simp⟩)
    exact ⟨PRv, PBv, hPRv, hPBv⟩
  choose PR PBn hPRc hPBc using hslopes
  -- the per-copy selected-D DFAs and their periodicities
  have hdata : ∀ c : Fin P.toPoly.K,
      ∃ (M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c))) (mv pv : ℕ), 1 ≤ pv ∧
        (∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ),
          (∀ i, ī i < w.length) →
          (M.accepts (markAtN (P.toPoly.arity c) w ī) ↔
            (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D))) ∧
        (∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g]) := by
    intro c
    obtain ⟨M, hM⟩ := SliceDstarGA.exists_selDDFA P c
    obtain ⟨mv, pv, hpv, hEP⟩ := SliceMarkN.bFN_func_iterate_eventuallyPeriodic M
    exact ⟨M, mv, pv, hpv, hM, hEP⟩
  choose Mc mvc pvc hpvc hMc hEPc using hdata
  -- the common period and threshold
  set p : ℕ := pR * (∏ c : Fin P.toPoly.K, pvc c) with hpdef
  have hprodpos : 0 < ∏ c : Fin P.toPoly.K, pvc c :=
    Finset.prod_pos (fun c _ => hpvc c)
  have hp : 1 ≤ p := by
    rw [hpdef]
    exact Nat.mul_pos hpR hprodpos
  have hpRdvd : pR ∣ p := by
    rw [hpdef]
    exact dvd_mul_right pR _
  have hpvcdvd : ∀ c, pvc c ∣ p := by
    intro c
    have h1 : pvc c ∣ ∏ c : Fin P.toPoly.K, pvc c :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
    rw [hpdef]
    exact Dvd.dvd.mul_left h1 pR
  set m : ℕ := (mR ⊔ Finset.univ.sup (fun c => mvc c)) ⊔ (B + 1) with hmdef
  have hmB : B + 1 ≤ m := by
    rw [hmdef]
    exact le_max_right _ _
  have hmmR : mR ≤ m := by
    rw [hmdef]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hmmvc : ∀ c, mvc c ≤ m := by
    intro c
    rw [hmdef]
    exact le_trans (le_trans (Finset.le_sup (f := fun c => mvc c) (Finset.mem_univ c))
      (le_max_right mR _)) (le_max_left _ _)
  refine ⟨m, p, Mc, Rcell, Bcell,
    (fun c rs => (p / pR) • PR c rs), (fun c rs => (p / pR) • PBn c rs),
    hp, hmB, hMc, ?_, ?_, ?_, ?_⟩
  · -- bFN function-iterate periodicity at (m, p)
    intro c g hg
    obtain ⟨t, ht⟩ := hpvcdvd c
    rw [ht, Nat.mul_comm]
    exact SliceGrowthCollapse.bFN_iterate_period_mul (Mc c) (mvc c) (pvc c) (hEPc c) t g
      (le_trans (hmmvc c) hg)
  · -- the window equality
    intro c rs t n htw hnw
    exact heq c rs t n htw hnw
  · -- Rcell global slope at p
    intro c rs t ht
    obtain ⟨q, hq⟩ := hpRdvd
    rw [hq, Nat.mul_div_cancel_left q hpR]
    exact RankAffine.iterate (hPRc c rs) t q (le_trans hmmR ht)
  · -- Bcell global slope at p
    intro c rs n hn
    obtain ⟨q, hq⟩ := hpRdvd
    rw [hq, Nat.mul_div_cancel_left q hpR]
    exact RankAffine.iterate (hPBc c rs) n q (le_trans hmmR hn)

/-! ## Stage-2 prerequisites: the EP fold and base-freedom of frozen cells -/

/-- Cluster-free cell tuples ignore the base entirely. -/
theorem cellTuple_clusterFree_base {B k : ℕ} (rs : Fin k → RegionSpec B)
    (hcf : ∀ i, clusterFree (rs i)) (t t' n : ℕ) :
    cellTuple rs t n = cellTuple rs t' n :=
  funext fun i => clusterFree_posAt_base (rs i) (hcf i) t t' n

/-- **The gate-period fold** (stage 2): finitely many eventually-periodic gates align
at the product of their periods — `p*` divides through `EP_of_dvd`. -/
theorem eventuallyPeriodic_align (l : List (ℕ → Prop))
    (h : ∀ Pr ∈ l, ∃ p, 1 ≤ p ∧ SliceOrder.EventuallyPeriodic Pr p) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ Pr ∈ l, SliceOrder.EventuallyPeriodic Pr p := by
  induction l with
  | nil => exact ⟨1, le_refl 1, fun Pr hPr => absurd hPr (by simp)⟩
  | cons Pr0 rest ih =>
      obtain ⟨p0, hp0, hEP0⟩ := h Pr0 (by simp)
      obtain ⟨p', hp', hrest⟩ := ih (fun Pr hPr => h Pr (by simp [hPr]))
      refine ⟨p0 * p', Nat.one_le_iff_ne_zero.mpr (by positivity), fun Pr hPr => ?_⟩
      rcases List.mem_cons.mp hPr with rfl | hPr
      · exact SliceDstar.EP_of_dvd hEP0 (dvd_mul_right p0 p')
      · exact SliceDstar.EP_of_dvd (hrest Pr hPr) (dvd_mul_left p' p0)


/-! ## The constructive `d*`-rank, general arity (GA-5.12–5.15) -/

set_option maxHeartbeats 1000000 in
/-- **The constructive `d*`-rank exists, general arity** (GA-5.12–5.15).  Under the
pinned per-copy budget (the exact conclusion shape of
`SliceProfileDischargeGA.hbud_of_hgrow`), there is an `AffineOnResiduesZ`-per-coordinate
sequence `dstarC` equal to `dstarRankGA` on every in-domain `D`-present slice past a
threshold.  Build script: `GA5_PORTMAP.json`, sections S0–S12. -/
theorem dstarC_exists_GA (P : WRP.Presentation Step Step) (hV : P.Valid) (C : ℕ)
    (hbud : ∀ n, P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
      (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
      l.length ≤ C * (n + 1)) :
    ∃ (dstarC : ℕ → Fin P.d → ℤ) (N0 : ℕ),
      (∀ i, AffineOnResiduesZ (fun n => dstarC n i)) ∧
      (∀ n, N0 ≤ n → P.toPoly.domain (wrappedFlat n) →
        (∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧
          P.toPoly.labelOf (wrappedFlat n) a = D) →
        SliceDstarGA.dstarRankGA P hV n = dstarC n) := by
  classical
  rcases Nat.eq_zero_or_pos P.d with hd0 | hd
  · exact ⟨fun _ _ => 0, 0, fun i => (hd0 ▸ i).elim0,
      fun n _ _ _ => funext (fun i => (hd0 ▸ i).elim0)⟩
  -- S2: constants and the two setups
  obtain ⟨B, Ncc, hB1, hcells⟩ := SliceFamilyCell.cells_cover P C
  obtain ⟨m, p, Mc, Rcell, Bcell, PR, PBn, hp, hmB, hMc, hbwd, hwineq, hRrec, hBrec⟩ :=
    dstar_setup_GA P B
  set B' : ℕ := 3 * B + m with hB'def
  have hBB' : B ≤ B' := by omega
  have hB'1 : 1 ≤ B' := by omega
  obtain ⟨m₂, p₂, _Mc₂, Rcell₂, Bcell₂, _PR₂, PBn₂, hp₂, _hmB₂, _hMc₂, _hbwd₂, hwineq₂,
    _hRrec₂, hBrec₂⟩ := dstar_setup_GA P B'
  set A0 : ℕ := B + m with hA0def
  set tl : (c : Fin P.toPoly.K) → (Fin (P.toPoly.arity c) → RegionSpec B) → Bool :=
    fun c rs => decide (WRP.lexLt (PR c rs) (fun _ => 0)) with htldef
  -- S3: the candidate list and the dominator
  set cands : List ((ℕ → Prop) × (ℕ → Fin P.d → ℤ)) :=
    ((List.finRange P.toPoly.K).flatMap (fun c =>
      (regionTuples B' (P.toPoly.arity c)).map (fun rs' =>
        (fun n => (anchorGate P c rs' (B' + 1)).Sat (wrappedFlat n) Fin.elim0 Fin.elim0,
         fun n => fun i => Rcell₂ c rs' (B' + 1) i + Bcell₂ c rs' n i))))
    ++ ((List.finRange P.toPoly.K).flatMap (fun c =>
      (regionTuples B (P.toPoly.arity c)).flatMap (fun rs =>
        (List.range p).map (fun r =>
          (fun n => (anchorGate P c rs (A0 + r)).Sat (wrappedFlat n) Fin.elim0 Fin.elim0,
           fun n => fun i => Bcell c rs n i +
             SliceDstar.selBvecVal (Rcell c rs) A0 r (PR c rs) (tl c rs) 0
               ((n - (4 * B + 2 * m + r)) / p) i))))) with hcandsdef
  set BIG : ℕ → Fin P.d → ℤ := fun n coord =>
    if coord = ⟨0, hd⟩
    then (cands.map (fun gf => gf.2 n ⟨0, hd⟩)).foldr max 0 + 1 else 0 with hBIGdef
  -- S4: the gate-period fold and p*
  have halignArg : ∀ Pr ∈ cands.map Prod.fst,
      ∃ q, 1 ≤ q ∧ SliceOrder.EventuallyPeriodic Pr q := by
    intro Pr hPr
    rw [List.mem_map] at hPr
    obtain ⟨gf, hgf, rfl⟩ := hPr
    rw [hcandsdef, List.mem_append] at hgf
    rcases hgf with hgf | hgf
    · rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨rs', _, rfl⟩ := hgf
      obtain ⟨mg, pg', hpg', hper⟩ := anchorGate_EP P c rs' (B' + 1)
      exact ⟨pg', hpg', mg, hper⟩
    · rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_flatMap] at hgf
      obtain ⟨rs, _, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨r, hr, rfl⟩ := hgf
      obtain ⟨mg, pg', hpg', hper⟩ := anchorGate_EP P c rs (A0 + r)
      exact ⟨pg', hpg', mg, hper⟩
  obtain ⟨pg, hpg, halign⟩ := eventuallyPeriodic_align (cands.map Prod.fst) halignArg
  set pstar : ℕ := p * p₂ * pg with hpstardef
  have hpstar : 1 ≤ pstar := by
    rw [hpstardef]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hps1 : pstar = p * (p₂ * pg) := by rw [hpstardef]; ring
  have hps2 : pstar = p₂ * (p * pg) := by rw [hpstardef]; ring
  have hps3 : pstar = pg * (p * p₂) := by rw [hpstardef]; ring
  have hgate : ∀ gf ∈ cands, SliceOrder.EventuallyPeriodic gf.1 pstar := fun gf hgf =>
    SliceDstar.EP_of_dvd (halign gf.1 (List.mem_map_of_mem hgf)) ⟨p * p₂, hps3⟩
  -- S5: per-coordinate affineness of the candidate values
  have hcaff : ∀ gf ∈ cands, ∀ i, AffineOnResiduesZ (fun n => gf.2 n i) := by
    intro gf hgf i
    rw [hcandsdef, List.mem_append] at hgf
    rcases hgf with hgf | hgf
    · rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨rs', _, rfl⟩ := hgf
      exact (AffineOnResiduesZ.const (Rcell₂ c rs' (B' + 1) i)).add
        (SliceFasBridges.rankAffine_coord_affineOnResiduesZ
          ⟨m₂, p₂, PBn₂ c rs', hp₂, hBrec₂ c rs'⟩ i)
    · rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_flatMap] at hgf
      obtain ⟨rs, _, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨r, hr, rfl⟩ := hgf
      exact (SliceFasBridges.rankAffine_coord_affineOnResiduesZ
          ⟨m, p, PBn c rs, hp, hBrec c rs⟩ i).add
        (SliceDstar.selBvecCoord_affineOnResiduesZ (Rcell c rs) A0 r (PR c rs) (tl c rs)
          (fun _ => 0) (fun n => (n - (4 * B + 2 * m + r)) / p)
          (affineOnResidues_of_eventuallyPeriodic (m := 0) (p := 1) (le_refl 1)
            (fun n _ => rfl))
          (affineOnResidues_natSubDiv (4 * B + 2 * m + r) p hp) i)
  -- S6: per-candidate global slopes and pairwise lexLt EP at pstar
  set M0 : ℕ := 4 * B + 2 * m + p + m₂ with hM0def
  have hcandrec : ∀ gf ∈ cands, ∃ Pf : Fin P.d → ℤ,
      ∀ i n, M0 ≤ n → gf.2 (n + pstar) i = gf.2 n i + Pf i := by
    intro gf hgf
    rw [hcandsdef, List.mem_append] at hgf
    rcases hgf with hgf | hgf
    · rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨rs', _, rfl⟩ := hgf
      refine ⟨fun i => ((p * pg : ℕ) : ℤ) * PBn₂ c rs' i, fun i n hn => ?_⟩
      simp only []
      rw [hps2]
      have hit := congrFun (RankAffine.iterate (hBrec₂ c rs') n (p * pg) (by omega)) i
      rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at hit
      rw [hit]
      ring
    · rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_flatMap] at hgf
      obtain ⟨rs, _, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨r, hr, rfl⟩ := hgf
      rw [List.mem_range] at hr
      refine ⟨fun i => ((p₂ * pg : ℕ) : ℤ) * PBn c rs i +
        (if tl c rs then ((p₂ * pg : ℕ) : ℤ) * PR c rs i else 0), fun i n hn => ?_⟩
      simp only []
      rw [hps1]
      have hit := congrFun (RankAffine.iterate (hBrec c rs) n (p₂ * pg) (by omega)) i
      rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at hit
      have hdiv : (n + p * (p₂ * pg) - (4 * B + 2 * m + r)) / p
          = (n - (4 * B + 2 * m + r)) / p + p₂ * pg := by
        rw [show n + p * (p₂ * pg) - (4 * B + 2 * m + r)
            = (n - (4 * B + 2 * m + r)) + p * (p₂ * pg) from by omega,
          Nat.add_mul_div_left _ _ hp]
      simp only [SliceDstar.selBvecVal]
      cases htl : tl c rs with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          rw [hit]
          ring
      | true =>
          simp only [if_true]
          rw [hit, hdiv]
          push_cast
          ring
  have hpair : ∀ gf ∈ cands, ∀ gf' ∈ cands,
      EventuallyPeriodic (fun n => WRP.lexLt (gf.2 n) (gf'.2 n)) pstar := by
    intro gf hgf gf' hgf'
    obtain ⟨Pf, hPf⟩ := hcandrec gf hgf
    obtain ⟨Pg, hPg⟩ := hcandrec gf' hgf'
    exact lexLt_eventuallyPeriodic (gf.2) (gf'.2) M0 pstar hpstar Pf Pg hPf hPg
  -- S7: the dominator (verbatim arity-1 ports)
  have hBIGaff : ∀ i, AffineOnResiduesZ (fun n => BIG n i) := by
    intro i
    by_cases hi : i = ⟨0, hd⟩
    · have heq : (fun n => BIG n i)
          = (fun n => ((cands.map (fun gf => fun n => gf.2 n ⟨0, hd⟩)).map
              (fun f => f n)).foldr max 0 + 1) := by
        funext n
        simp only [hBIGdef, hi, ↓reduceIte, List.map_map, Function.comp_def]
      rw [heq]
      exact (affineOnResiduesZ_listMax (cands.map (fun gf => fun n => gf.2 n ⟨0, hd⟩))
        (fun f hf => by
          rw [List.mem_map] at hf
          obtain ⟨gf, hgf, rfl⟩ := hf
          exact hcaff gf hgf ⟨0, hd⟩)).add (AffineOnResiduesZ.const 1)
    · have heq : (fun n => BIG n i) = (fun _ => (0 : ℤ)) := by
        funext n
        rw [hBIGdef]
        simp only [if_neg hi]
      rw [heq]
      exact AffineOnResiduesZ.const 0
  have hdom : ∀ gf ∈ cands, ∀ n, WRP.lexLt (gf.2 n) (BIG n) := by
    intro gf hgf n
    refine ⟨⟨0, hd⟩, fun j hj => absurd (Fin.lt_def.mp hj) (Nat.not_lt_zero _), ?_⟩
    simp only [hBIGdef, ↓reduceIte]
    have hmem : gf.2 n ⟨0, hd⟩ ∈ cands.map (fun gf' => gf'.2 n ⟨0, hd⟩) :=
      List.mem_map.mpr ⟨gf, hgf, rfl⟩
    have := SliceDstarBridge.le_foldr_max hmem
    omega
  -- S8: the witness and its affine leg
  refine ⟨fun n => lexMinList (BIG :: cands.map
    (fun gf => fun n => if gf.1 n then gf.2 n else BIG n)) n,
    Ncc + 6 * B + 2 * m + 2 * p + 2, ?_, ?_⟩
  · exact fun i => SliceDstar.gated_lexMin_affine cands hpstar hgate hcaff hpair
      BIG hBIGaff hdom i
  -- S9: the bridge opening
  intro n hn hdomain hD
  show SliceDstarGA.dstarRankGA P hV n
    = lexMinList (BIG :: cands.map (fun gf => fun n => if gf.1 n then gf.2 n else BIG n)) n
  set L := BIG :: cands.map (fun gf => fun n => if gf.1 n then gf.2 n else BIG n) with hLdef
  have hLne : L ≠ [] := by rw [hLdef]; simp
  obtain ⟨hmin, hattn⟩ := lexMinList_le L hLne n
  obtain ⟨dstar, hdsel, hdD, hdmin, hdrank⟩ := SliceDstarGA.dstarRankGA_spec P hV n hD
  have hDRle : ∀ b, P.toPoly.selectedAtom (wrappedFlat n) b →
      P.toPoly.labelOf (wrappedFlat n) b = D →
      ¬ WRP.lexLt (P.rankOf (wrappedFlat n) b) (SliceDstarGA.dstarRankGA P hV n) := by
    intro b hbsel hbD
    rw [hdrank]
    rcases hdmin b hbsel hbD with rfl | hord
    · exact lexLt_irrefl _
    · simp only [WRP.Presentation.wrpOrd] at hord
      rcases hord with hlt | ⟨heqr, _⟩
      · exact fun hcon => lexLt_irrefl _ (lexLt_trans _ _ _ hlt hcon)
      · rw [heqr]
        exact lexLt_irrefl _
  have hmn : m ≤ n := by omega
  -- S10: every on-candidate value is rankOf a selected D-atom
  have hOnIsRank : ∀ gf ∈ cands, gf.1 n → ∃ b, P.toPoly.selectedAtom (wrappedFlat n) b ∧
      P.toPoly.labelOf (wrappedFlat n) b = D ∧ gf.2 n = P.rankOf (wrappedFlat n) b := by
    intro gf hgf hon
    rw [hcandsdef, List.mem_append] at hgf
    rcases hgf with hgf | hgf
    · -- frozen: the gate IS the atom's own selected-D, value at the dummy base
      rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨rs', _, rfl⟩ := hgf
      have hwin : (B' + 1) + B' ≤ n := by omega
      have hsl := (sat_anchorGate P c rs' (B' + 1) n hwin).mp hon
      refine ⟨⟨c, cellTuple rs' (B' + 1) n⟩,
        ⟨cellTuple_valid rs' (B' + 1) n hwin, hsl.1⟩, hsl.2, ?_⟩
      exact (hwineq₂ c rs' (B' + 1) n (le_refl _) (by omega)).symm
    · -- bulk: transport RIGHT from the anchor to the boundary base
      rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_flatMap] at hgf
      obtain ⟨rs, _, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨r, hr, rfl⟩ := hgf
      rw [List.mem_range] at hr
      obtain ⟨kend, hkenddef⟩ : ∃ k : ℕ, k = (n - (4 * B + 2 * m + r)) / p := ⟨_, rfl⟩
      obtain ⟨kbd, hkbddef⟩ : ∃ k : ℕ, k = (if tl c rs then kend else 0 : ℕ) := ⟨_, rfl⟩
      have hkbd_le : kbd ≤ kend := by
        rw [hkbddef]
        split
        · exact le_refl _
        · exact Nat.zero_le _
      have hkk : p * kbd ≤ p * kend := Nat.mul_le_mul_left p hkbd_le
      have hpke : p * kend ≤ n - (4 * B + 2 * m + r) := by
        rw [hkenddef, Nat.mul_comm]
        exact Nat.div_mul_le_self _ _
      have hcrn : 4 * B + 2 * m + r ≤ n := by omega
      have hmc : kbd * p = p * kbd := Nat.mul_comm kbd p
      have hacc0 : (Mc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
          (cellTuple rs (A0 + r) n)) :=
        (anchorGate_iff_accepts P c rs (A0 + r) n (by omega) (Mc c) (hMc c)).mp hon
      have htr := cell_base_transport_right (Mc c) m p (hbwd c) rs (A0 + r) n kbd
        (by omega) (by omega) (by omega)
      have hacc := htr.mpr hacc0
      have hbd : A0 + r + kbd * p = A0 + r + p * kbd := by omega
      rw [hbd] at hacc
      have hval := cellTuple_valid rs (A0 + r + p * kbd) n (by omega)
      have hsl := (hMc c (wrappedFlat n) _ hval).mp hacc
      refine ⟨⟨c, cellTuple rs (A0 + r + p * kbd) n⟩, ⟨hval, hsl.1⟩, hsl.2, ?_⟩
      have hsel_eq : (fun i => Bcell c rs n i + SliceDstar.selBvecVal (Rcell c rs) A0 r
          (PR c rs) (tl c rs) 0 kend i)
          = fun i => Rcell c rs (A0 + r + p * kbd) i + Bcell c rs n i := by
        funext i
        have hit := congrFun (RankAffine.iterate (hRrec c rs) (A0 + r) kbd (by omega)) i
        rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at hit
        rw [SliceDstar.selBvecVal, hit, hkbddef]
        by_cases htl : tl c rs
        · simp only [if_pos htl]
          ring
        · simp only [if_neg htl]
          ring
      show (fun i => Bcell c rs n i + SliceDstar.selBvecVal (Rcell c rs) A0 r (PR c rs)
          (tl c rs) 0 ((n - (4 * B + 2 * m + r)) / p) i) = P.rankOf (wrappedFlat n) _
      rw [← hkenddef, hsel_eq]
      exact (hwineq c rs (A0 + r + p * kbd) n (by omega) (by omega)).symm
  have hII : ∀ gf ∈ cands, gf.1 n →
      ¬ WRP.lexLt (gf.2 n) (SliceDstarGA.dstarRankGA P hV n) := by
    intro gf hgf hon
    obtain ⟨b, hbsel, hbD, hbeq⟩ := hOnIsRank gf hgf hon
    rw [hbeq]
    exact hDRle b hbsel hbD
  -- S11: dstar's own candidate is on and not lex-above it (three zones)
  have hI : ∃ gf ∈ cands, gf.1 n ∧
      ¬ WRP.lexLt (SliceDstarGA.dstarRankGA P hV n) (gf.2 n) := by
    clear hII hDRle hOnIsRank
    obtain ⟨c0, ī⟩ := dstar
    obtain ⟨t, htB, htn, hreg⟩ := hcells n (by omega) c0 ī hdsel
      (fun l hnd hl => hbud n hdomain c0 l hnd hl)
    choose rs hrs using hreg
    have hīeq : ī = cellTuple rs t n := funext hrs
    by_cases hfront : t < A0
    · -- FRONT zone: re-freeze and use the frozen candidate at the dummy base
      have hfz : t + B ≤ B' := by omega
      set rs' := fun i => refreezeFront hBB' t hfz (rs i) with hrs'def
      have htup : cellTuple rs' (B' + 1) n = ī := by
        funext i
        show (refreezeFront hBB' t hfz (rs i)).posAt (B' + 1) n = ī i
        rw [refreezeFront_posAt, ← hrs i]
      refine ⟨(fun n => (anchorGate P c0 rs' (B' + 1)).Sat (wrappedFlat n)
          Fin.elim0 Fin.elim0,
        fun n => fun i => Rcell₂ c0 rs' (B' + 1) i + Bcell₂ c0 rs' n i), ?_, ?_, ?_⟩
      · rw [hcandsdef]
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨c0, List.mem_finRange c0,
          List.mem_map_of_mem (mem_regionTuples B' _ rs')⟩)
      · refine (sat_anchorGate P c0 rs' (B' + 1) n (by omega)).mpr ?_
        rw [htup]
        exact ⟨hdsel.2, hdD⟩
      · have heq : SliceDstarGA.dstarRankGA P hV n
            = fun i => Rcell₂ c0 rs' (B' + 1) i + Bcell₂ c0 rs' n i := by
          rw [hdrank]
          show P.rank c0 _ ī = _
          rw [← htup]
          exact hwineq₂ c0 rs' (B' + 1) n (le_refl _) (by omega)
        rw [heq]
        exact lexLt_irrefl _
    · by_cases hbulk : t + 3 * B + m ≤ n
      · -- BULK zone: transport LEFT to the anchor; boundary value dominates
        obtain ⟨r, hrdef⟩ : ∃ rr : ℕ, rr = (t - A0) % p := ⟨_, rfl⟩
        obtain ⟨kd, hkddef⟩ : ∃ kk : ℕ, kk = (t - A0) / p := ⟨_, rfl⟩
        obtain ⟨kend, hkenddef⟩ : ∃ kk : ℕ, kk = (n - (4 * B + 2 * m + r)) / p := ⟨_, rfl⟩
        have hrlt : r < p := by
          rw [hrdef]
          exact Nat.mod_lt _ hp
        have hjeq : A0 + r + p * kd = t := by
          rw [hrdef, hkddef]
          have := Nat.mod_add_div (t - A0) p
          omega
        have hmc : kd * p = p * kd := Nat.mul_comm kd p
        have hpkd : p * kd ≤ n - (4 * B + 2 * m + r) := by omega
        have hkd_le : kd ≤ kend := by
          rw [hkenddef, Nat.le_div_iff_mul_le hp, Nat.mul_comm]
          exact hpkd
        have hN : numReps A0 p r (n + 1 - (3 * B + m)) = kend + 1 := by
          unfold numReps
          rw [if_pos (by omega), hkenddef,
            show n + 1 - (3 * B + m) - (A0 + r) - 1 = n - (4 * B + 2 * m + r) from by omega]
        refine ⟨(fun n => (anchorGate P c0 rs (A0 + r)).Sat (wrappedFlat n)
            Fin.elim0 Fin.elim0,
          fun n => fun i => Bcell c0 rs n i +
            SliceDstar.selBvecVal (Rcell c0 rs) A0 r (PR c0 rs) (tl c0 rs) 0
              ((n - (4 * B + 2 * m + r)) / p) i), ?_, ?_, ?_⟩
        · rw [hcandsdef]
          exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨c0, List.mem_finRange c0,
            List.mem_flatMap.mpr ⟨rs, mem_regionTuples B _ rs,
              List.mem_map_of_mem (List.mem_range.mpr hrlt)⟩⟩)
        · -- the gate turns on by leftward transport from t to the anchor
          have hval_t := cellTuple_valid rs t n htn
          have hacc_t : (Mc c0).accepts (markAtN (P.toPoly.arity c0) (wrappedFlat n)
              (cellTuple rs t n)) := by
            refine (hMc c0 (wrappedFlat n) _ hval_t).mpr ?_
            rw [← hīeq]
            exact ⟨hdsel.2, hdD⟩
          have htr := cell_base_transport_left (Mc c0) m p (hbwd c0) rs t n kd
            (by omega) (by omega) (by omega)
          have hsub : t - kd * p = A0 + r := by omega
          rw [hsub] at htr
          exact (anchorGate_iff_accepts P c0 rs (A0 + r) n (by omega) (Mc c0)
            (hMc c0)).mpr (htr.mpr hacc_t)
        · -- the boundary value lex-dominates dstar's own member value
          set F : ℕ → Fin P.d → ℤ := fun j i => Rcell c0 rs j i + Bcell c0 rs n i
            with hFdef
          have hrecF : ∀ (i : Fin P.d) (r' k : ℕ),
              F (A0 + r' + p * k) i = F (A0 + r') i + k * PR c0 rs i := by
            intro i r' k
            have hit := congrFun (RankAffine.iterate (hRrec c0 rs) (A0 + r') k
              (by omega)) i
            rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at hit
            simp only [hFdef]
            rw [hit]
            ring
          have hflag : tl c0 rs = true ↔ WRP.lexLt (PR c0 rs) (fun _ => 0) := by
            rw [htldef]
            exact decide_eq_true_iff
          have hDeq : SliceDstarGA.dstarRankGA P hV n = F t := by
            rw [hdrank]
            show P.rank c0 _ ī = _
            rw [hīeq, hFdef]
            exact hwineq c0 rs t n (by omega) (by omega)
          have hbnd_eq : (fun i => Bcell c0 rs n i +
              SliceDstar.selBvecVal (Rcell c0 rs) A0 r (PR c0 rs) (tl c0 rs) 0
                ((n - (4 * B + 2 * m + r)) / p) i)
              = SliceDstar.selBvecVal F A0 r (PR c0 rs) (tl c0 rs) 0
                  ((n - (4 * B + 2 * m + r)) / p) := by
            funext i
            simp only [SliceDstar.selBvecVal, hFdef]
            by_cases htl : tl c0 rs
            · simp only [if_pos htl]
              ring
            · simp only [if_neg htl]
              ring
          show ¬ WRP.lexLt (SliceDstarGA.dstarRankGA P hV n)
            (fun i => Bcell c0 rs n i +
              SliceDstar.selBvecVal (Rcell c0 rs) A0 r (PR c0 rs) (tl c0 rs) 0
                ((n - (4 * B + 2 * m + r)) / p) i)
          rw [hbnd_eq,
            show (n - (4 * B + 2 * m + r)) / p
              = numReps A0 p r (n + 1 - (3 * B + m)) - 1 from by rw [hN]; omega,
            hDeq, ← hjeq]
          exact SliceDstarBridge.selBvec_le_member F (PR c0 rs) (tl c0 rs) hrecF hflag
            r (n + 1 - (3 * B + m)) kd (by rw [hN]; omega)
      · -- BACK zone: re-freeze and use the frozen candidate at the dummy base
        have hbz : n ≤ t + B' := by omega
        set rs' := fun i => refreezeBack hBB' hB'1 t n hbz (rs i) with hrs'def
        have htup : cellTuple rs' (B' + 1) n = ī := by
          funext i
          show (refreezeBack hBB' hB'1 t n hbz (rs i)).posAt (B' + 1) n = ī i
          rw [refreezeBack_posAt hBB' hB'1 t n hbz htn, ← hrs i]
        refine ⟨(fun n => (anchorGate P c0 rs' (B' + 1)).Sat (wrappedFlat n)
            Fin.elim0 Fin.elim0,
          fun n => fun i => Rcell₂ c0 rs' (B' + 1) i + Bcell₂ c0 rs' n i), ?_, ?_, ?_⟩
        · rw [hcandsdef]
          exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨c0, List.mem_finRange c0,
            List.mem_map_of_mem (mem_regionTuples B' _ rs')⟩)
        · refine (sat_anchorGate P c0 rs' (B' + 1) n (by omega)).mpr ?_
          rw [htup]
          exact ⟨hdsel.2, hdD⟩
        · have heq : SliceDstarGA.dstarRankGA P hV n
              = fun i => Rcell₂ c0 rs' (B' + 1) i + Bcell₂ c0 rs' n i := by
            rw [hdrank]
            show P.rank c0 _ ī = _
            rw [← htup]
            exact hwineq₂ c0 rs' (B' + 1) n (le_refl _) (by omega)
          rw [heq]
          exact lexLt_irrefl _
  -- S12: the endgame (verbatim arity-1 port)
  obtain ⟨gfd, hgfd, hond, hled⟩ := hI
  set gatedd : ℕ → Fin P.d → ℤ := fun n => if gfd.1 n then gfd.2 n else BIG n with hgddef
  have hgddmem : gatedd ∈ L := by
    rw [hLdef]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨gfd, hgfd, rfl⟩)
  have hgddval : gatedd n = gfd.2 n := by
    rw [hgddef]
    simp only [if_pos hond]
  have hDCle : ¬ WRP.lexLt (gatedd n) (lexMinList L n) := hmin gatedd hgddmem
  have hIfinal : ¬ WRP.lexLt (SliceDstarGA.dstarRankGA P hV n) (lexMinList L n) := by
    rw [← hgddval] at hled
    exact lexLt_negtrans _ _ _ hled hDCle
  have hDClt : WRP.lexLt (lexMinList L n) (BIG n) := by
    have hgdlt : WRP.lexLt (gatedd n) (BIG n) := by
      rw [hgddval]
      exact hdom gfd hgfd n
    rcases lexLt_trichot (lexMinList L n) (gatedd n) with h | h | h
    · exact lexLt_trans _ _ _ h hgdlt
    · rw [h]
      exact hgdlt
    · exact absurd h hDCle
  obtain ⟨F, hFmem, hFeq⟩ := hattn
  have hIIfinal : ¬ WRP.lexLt (lexMinList L n) (SliceDstarGA.dstarRankGA P hV n) := by
    rw [hLdef, List.mem_cons] at hFmem
    rcases hFmem with rfl | hFmem
    · rw [hFeq] at hDClt
      exact absurd hDClt (lexLt_irrefl _)
    · rw [List.mem_map] at hFmem
      obtain ⟨gf, hgf, rfl⟩ := hFmem
      by_cases hon : gf.1 n
      · have hval : lexMinList L n = gf.2 n := by
          rw [hFeq]
          simp only [if_pos hon]
        rw [hval]
        exact hII gf hgf hon
      · have hval : lexMinList L n = BIG n := by
          rw [hFeq]
          simp only [if_neg hon]
        rw [hval] at hDClt
        exact absurd hDClt (lexLt_irrefl _)
  rcases lexLt_trichot (SliceDstarGA.dstarRankGA P hV n) (lexMinList L n) with h | h | h
  · exact absurd h hIfinal
  · exact h
  · exact absurd h hIIfinal


end SliceDstarBridgeGA
