/-
# GA-7.3–7.6 — the three counts and the pinned deliverables
# (`SliceFasCountGA` namespace, part 3/3)

The counting layer proper: frozen
cells are EP indicators, bulk cells feed the `SliceGatedConv`/`SliceFasCount`
convolution kernels through the cell-tuple convolution data (window via
saturating-counter flags where kernels lack interval parameters), with the
boundary base `t = Z` re-frozen to the `2Z`-layer.

* `totalSelectedU_count_GA` (the pipeline shakedown),
* `strict_count_GA` (rank lex-below the `d*`-rank, via `dstarC`),
* `tie_count_GA` (the per-class `Gdfa` of `tie_point_bridge_GA`, stitched by
  `AffineOnResidues.select`),
* `fas_pred_split_GA` (the keystone trichotomy) and THE PINNED DELIVERABLES
  `fas_count_affineOnResidues_GA` / `tailU_count_affineOnResidues_GA` —
  what the capstone `SliceFasAssemblyGA` consumes.
-/
import RequestProject.SliceCellClassifyGA
import RequestProject.SliceFasCount
import RequestProject.SliceAffineSelect
import RequestProject.SliceFasTie
import RequestProject.SliceFasAssembly
import RequestProject.SliceProfileDischargeGA

namespace SliceFasCountGA

open WRP Step SliceFamilyCell SliceDstarGA SliceDstarGateGA SliceFasGatesGA
  SliceThreshold SliceAffine SliceOrder MSOMarkN SliceMarkN SliceFasSelectorGA
open scoped Classical

/-! ## GA-7.3: the total selected-`U` count -/

/-- **The total selected-`U` count is affine-on-residues** (GA-7.3): the kernel
pipeline shakedown — frozen cells are EP indicators, bulk cells feed the gated
convolution through the cell-tuple convolution form. -/
theorem totalSelectedU_count_GA (P : WRP.Presentation Step Step) (C : ℕ)
    (hbud : ∀ n, P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) :
    ∃ (tot' : ℕ → ℕ) (N : ℕ), AffineOnResidues tot' ∧
      ∀ n, N ≤ n → P.toPoly.domain (wrappedFlat n) →
        tot' n = ∑ c : Fin P.toPoly.K,
          ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
            Finset.range (wrappedFlat n).length),
          if (P.toPoly.sel c (wrappedFlat n) ī
              ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U) then 1 else 0 := by
  classical
  obtain ⟨Z, Ncan, hZ, hrecount⟩ := canonical_recount P C hbud
  choose Uc hUc using fun c => selectedU_gate_GA P c
  choose mv pv hpv hEPc using fun c => bFN_func_iterate_eventuallyPeriodic (Uc c)
  set tot' : ℕ → ℕ := fun n =>
    ∑ c : Fin P.toPoly.K,
      ((∑ rs' ∈ frozenCells Z (P.toPoly.arity c),
        if (Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
            (cellTuple rs' (Z + 1) n)) then 1 else 0)
      + ∑ rs ∈ bulkCells Z hZ (P.toPoly.arity c),
          ((Finset.range n).filter (fun t : ℕ =>
            (Z : ℤ) ≤ (t : ℤ) ∧ (t : ℤ) < (n : ℤ) - Z - clusterWidth rs + 1
              ∧ cellAcc (Uc c) rs
                  ((bFN (Uc c))^[n - 1 - t + 1 - (Z + clusterWidth rs)]
                    (cellGclW (Uc c) rs
                      ((bFN (Uc c))^[t - Z] (cellQ0 (Uc c) rs)))))).card)
    with htotdef
  refine ⟨tot', Ncan + 2 * Z + 2, ?_, ?_⟩
  · -- affineness: per copy, frozen indicators + bulk kernel counts
    rw [htotdef]
    refine AffineOnResidues.finsetSum _ _ (fun c _ => ?_)
    refine AffineOnResidues.add ?_ ?_
    · refine AffineOnResidues.finsetSum _ _ (fun rs' hrs' => ?_)
      have hcf : ∀ i, clusterFree (rs' i) := by
        rw [frozenCells, Finset.mem_filter] at hrs'
        exact hrs'.2
      obtain ⟨p', hp', hEP'⟩ := acceptsN_clusterFree_EP (Uc c) rs' hcf (Z + 1)
      exact SliceFasCount.affineOnResidues_indicator_of_EP hp' hEP'
    · refine AffineOnResidues.finsetSum _ _ (fun rs hrs => ?_)
      refine SliceGatedConv.affineOnResidues_gatedConvolution
        (u := fun t => (bFN (Uc c))^[t - Z] (cellQ0 (Uc c) rs))
        (v := fun m => (bFN (Uc c))^[m + 1 - (Z + clusterWidth rs)])
        (b := fun q g => cellAcc (Uc c) rs (g (cellGclW (Uc c) rs q)))
        (mu := mv c + Z) (hpu := hpv c) ?_
        (mv := mv c + Z + clusterWidth rs) (hpv := hpv c) ?_
        (hlo := AffineOnResiduesZ.const (Z : ℤ))
        (hhi := ((AffineOnResiduesZ.id_cast.sub
          (AffineOnResiduesZ.const (Z : ℤ))).sub
          (AffineOnResiduesZ.const (clusterWidth rs : ℤ))).add
          (AffineOnResiduesZ.const 1))
      · intro i hi
        rw [show i + pv c - Z = (i - Z) + pv c from by omega]
        exact congrFun (hEPc c (i - Z) (by omega)) _
      · intro j hj
        rw [show j + pv c + 1 - (Z + clusterWidth rs)
          = (j + 1 - (Z + clusterWidth rs)) + pv c from by omega]
        exact hEPc c (j + 1 - (Z + clusterWidth rs)) (by omega)
  · -- agreement on in-domain slices past the threshold
    intro n hn hdom
    rw [htotdef]
    beta_reduce
    refine Finset.sum_congr rfl (fun c _ => ?_)
    set QQ : (Fin (P.toPoly.arity c) → ℕ) → Prop := fun ī =>
      P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩
        ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U with hQQdef
    have hQsel : ∀ ī, QQ ī → P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩ := by
      intro ī h
      rw [hQQdef] at h
      exact h.1
    have hQiff : ∀ ī, (∀ i, ī i < (wrappedFlat n).length) →
        (QQ ī ↔ (P.toPoly.sel c (wrappedFlat n) ī
          ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U)) := by
      intro ī hval
      rw [hQQdef]
      beta_reduce
      constructor
      · rintro ⟨hs, hl⟩
        exact ⟨hs.2, hl⟩
      · rintro ⟨hs, hl⟩
        exact ⟨⟨hval, hs⟩, hl⟩
    have hrec := hrecount n (by omega) hdom c QQ hQsel
    refine Eq.trans (Eq.trans ?_ hrec.symm) ?_
    case refine_2 =>
      refine Finset.sum_congr rfl (fun ī hī => ?_)
      have hval : ∀ i, ī i < (wrappedFlat n).length := by
        rw [Fintype.mem_piFinset] at hī
        intro i
        have := hī i
        rwa [Finset.mem_range] at this
      by_cases h : QQ ī
      · rw [if_pos h, if_pos ((hQiff ī hval).mp h)]
      · rw [if_neg h, if_neg (fun hc => h ((hQiff ī hval).mpr hc))]
    have h2 : (∑ rs' ∈ frozenCells Z (P.toPoly.arity c),
          if (Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
              (cellTuple rs' (Z + 1) n)) then 1 else 0)
        + (∑ rs ∈ bulkCells Z hZ (P.toPoly.arity c),
            ((Finset.range n).filter (fun t : ℕ =>
              (Z : ℤ) ≤ (t : ℤ) ∧ (t : ℤ) < (n : ℤ) - Z - clusterWidth rs + 1
                ∧ cellAcc (Uc c) rs
                    ((bFN (Uc c))^[n - 1 - t + 1 - (Z + clusterWidth rs)]
                      (cellGclW (Uc c) rs
                        ((bFN (Uc c))^[t - Z] (cellQ0 (Uc c) rs)))))).card)
        = (∑ rs' ∈ frozenCells Z (P.toPoly.arity c),
            if QQ (cellTuple rs' (Z + 1) n) then 1 else 0)
          + ∑ rs ∈ bulkCells Z hZ (P.toPoly.arity c),
              ((Finset.Icc Z (n - Z - clusterWidth rs)).filter
                (fun t => QQ (cellTuple rs t n))).card := by
      congr 1
      · -- the frozen arm: acceptance ⟺ the predicate
        refine Finset.sum_congr rfl (fun rs' hrs' => ?_)
        have hval := SliceDstarGateGA.cellTuple_valid rs' (Z + 1) n
          (show Z + 1 + Z ≤ n from by omega)
        have hiff : ((Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
              (cellTuple rs' (Z + 1) n)) ↔ QQ (cellTuple rs' (Z + 1) n)) := by
          rw [hUc c (wrappedFlat n) _ hval]
          exact ((hQiff _ hval).trans Iff.rfl).symm
        by_cases h : (Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
            (cellTuple rs' (Z + 1) n))
        · rw [if_pos h, if_pos (hiff.mp h)]
        · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
      · -- the bulk arm: the filter sets coincide
        refine Finset.sum_congr rfl (fun rs hrs => ?_)
        congr 1
        refine Finset.ext (fun t => ?_)
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
        have hWpos : 1 ≤ clusterWidth rs := by
          rw [bulkCells, Finset.mem_filter] at hrs
          exact bulk_width_pos (hZ := hZ) hrs.2
        constructor
        · rintro ⟨htn', htZ, htub, hbit⟩
          have htZ' : Z ≤ t := by exact_mod_cast htZ
          have hwin : t + clusterWidth rs + Z ≤ n := by omega
          have hacc : (Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
              (cellTuple rs t n)) := by
            rw [acceptsN_cellTuple_convW (Uc c) rs t n htZ' hwin,
              show n - Z - clusterWidth rs - t = n - 1 - t + 1 - (Z + clusterWidth rs)
                from by omega]
            exact hbit
          have hval := SliceDstarGateGA.cellTuple_valid rs t n (by omega)
          rw [hUc c (wrappedFlat n) _ hval] at hacc
          exact ⟨⟨htZ', by omega⟩, (hQiff _ hval).mpr hacc⟩
        · rintro ⟨⟨htZ, htn⟩, hQ⟩
          have hwin : t + clusterWidth rs + Z ≤ n := by omega
          refine ⟨by omega, by exact_mod_cast htZ, by omega, ?_⟩
          have hval := SliceDstarGateGA.cellTuple_valid rs t n (by omega)
          have hacc : (Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
              (cellTuple rs t n)) := by
            rw [hUc c (wrappedFlat n) _ hval]
            exact (hQiff _ hval).mp hQ
          rw [acceptsN_cellTuple_convW (Uc c) rs t n htZ hwin] at hacc
          rwa [show n - 1 - t + 1 - (Z + clusterWidth rs) = n - Z - clusterWidth rs - t
            from by omega]
    refine h2.trans ?_
    congr 1
    · refine Finset.sum_congr rfl (fun rs' _ => ?_)
      by_cases h : QQ (cellTuple rs' (Z + 1) n)
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
    · refine Finset.sum_congr rfl (fun rs _ => ?_)
      refine congrArg Finset.card ?_
      convert rfl

/-! ## GA-7.4: the strict count -/

/-- Lex translation: adding a vector on the left is subtracting it on the right. -/
theorem lexLt_sub_right {d : ℕ} (x y z : Fin d → ℤ) :
    WRP.lexLt (fun i => x i + z i) y ↔ WRP.lexLt x (fun i => y i - z i) := by
  constructor <;> rintro ⟨i, hpre, hlt⟩ <;>
    exact ⟨i, fun j hj => by have := hpre j hj; simp only [] at *; omega,
      by simp only [] at *; omega⟩

/-- **The strict count is affine-on-residues** (GA-7.4): selected `U`-atoms whose rank
lex-precedes the `d*`-rank. -/
theorem strict_count_GA (P : WRP.Presentation Step Step) (hV : P.Valid) (C : ℕ)
    (hbud : ∀ n, P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) :
    ∃ (strict' : ℕ → ℕ) (N : ℕ), AffineOnResidues strict' ∧
      ∀ n, N ≤ n → P.toPoly.domain (wrappedFlat n) →
        (∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧
          P.toPoly.labelOf (wrappedFlat n) a = D) →
        strict' n = ∑ c : Fin P.toPoly.K,
          ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
            Finset.range (wrappedFlat n).length),
          if (P.toPoly.sel c (wrappedFlat n) ī
              ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
              ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, ī⟩)
                  (SliceDstarGA.dstarRankGA P hV n)) then 1 else 0 := by
  classical
  obtain ⟨dstarC, N0, hCaff, hCagree⟩ := SliceDstarBridgeGA.dstarC_exists_GA P hV C hbud
  obtain ⟨Z, Ncan, hZ, hrecount⟩ := canonical_recount P C hbud
  obtain ⟨m, p, _Mc, Rcell, Bcell, PR, PBn, hp, hmB, _hMc, _hbwd, hwineq, hRrec, hBrec⟩ :=
    SliceDstarBridgeGA.dstar_setup_GA P Z
  choose RcellH BcellH hRAH hBAH heqH using
    fun (c : Fin P.toPoly.K) (rs'' : Fin (P.toPoly.arity c) → RegionSpec (2 * Z)) =>
      SliceFamilyRank.rank_cell_decomp (B := 2 * Z) P c rs''
  choose Uc hUc using fun c => selectedU_gate_GA P c
  choose mv pv hpv hEPc using fun c => bFN_func_iterate_eventuallyPeriodic (Uc c)
  -- the boundary re-freeze (n-uniform)
  have hZ2 : Z ≤ 2 * Z := by omega
  have hZZ : Z + Z ≤ 2 * Z := by omega
  set fr2 : (c : Fin P.toPoly.K) → (Fin (P.toPoly.arity c) → RegionSpec Z) →
      (Fin (P.toPoly.arity c) → RegionSpec (2 * Z)) :=
    fun c rs i => refreezeFront hZ2 Z hZZ (rs i) with hfr2def
  have hfr2cf : ∀ c rs i, clusterFree (fr2 c rs i) := by
    intro c rs i
    rw [hfr2def]
    beta_reduce
    exact clusterFree_refreezeFront hZ2 Z hZZ (rs i)
  have hfr2tup : ∀ (c : Fin P.toPoly.K) (rs : Fin (P.toPoly.arity c) → RegionSpec Z)
      (n : ℕ), cellTuple rs Z n = cellTuple (fr2 c rs) (2 * Z + 1) n := by
    intro c rs n
    funext i
    rw [hfr2def]
    beta_reduce
    exact (refreezeFront_posAt hZ2 Z hZZ (rs i) (2 * Z + 1) n).symm
  -- the per-cell EP packages (frozen and boundary)
  have hfzEP : ∀ (c : Fin P.toPoly.K) (rs' : Fin (P.toPoly.arity c) → RegionSpec Z),
      (∀ i, clusterFree (rs' i)) →
      ∃ q, 1 ≤ q ∧ EventuallyPeriodic (fun n =>
        (Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
          (cellTuple rs' (Z + 1) n))
        ∧ WRP.lexLt (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) (dstarC n)) q := by
    intro c rs' hcf
    obtain ⟨q1, hq1, hE1⟩ := acceptsN_clusterFree_EP (Uc c) rs' hcf (Z + 1)
    obtain ⟨q2, hq2, hE2⟩ := SliceFasSelector.affineOnResiduesZ_lexLt_EP
      (F := fun n => fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) (G := dstarC)
      (fun i => (AffineOnResiduesZ.const (Rcell c rs' (Z + 1) i)).add
        (SliceFasBridges.rankAffine_coord_affineOnResiduesZ
          ⟨m, p, PBn c rs', hp, hBrec c rs'⟩ i)) hCaff
    exact ⟨q1 * q2, Nat.mul_pos hq1 hq2,
      (SliceDstar.EP_of_dvd hE1 (dvd_mul_right q1 q2)).and
        (SliceDstar.EP_of_dvd hE2 (dvd_mul_left q2 q1))⟩
  have hbdEP : ∀ (c : Fin P.toPoly.K) (rs : Fin (P.toPoly.arity c) → RegionSpec Z),
      ∃ q, 1 ≤ q ∧ EventuallyPeriodic (fun n =>
        (Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n) (cellTuple rs Z n))
        ∧ WRP.lexLt (fun i => RcellH c (fr2 c rs) (2 * Z + 1) i
            + BcellH c (fr2 c rs) n i) (dstarC n)) q := by
    intro c rs
    obtain ⟨q1, hq1, hE1⟩ := acceptsN_cellTuple_baseZ_EP (Uc c) rs
    obtain ⟨q2, hq2, hE2⟩ := SliceFasSelector.affineOnResiduesZ_lexLt_EP
      (F := fun n => fun i => RcellH c (fr2 c rs) (2 * Z + 1) i
        + BcellH c (fr2 c rs) n i) (G := dstarC)
      (fun i => (AffineOnResiduesZ.const (RcellH c (fr2 c rs) (2 * Z + 1) i)).add
        (SliceFasBridges.rankAffine_coord_affineOnResiduesZ (hBAH c (fr2 c rs)) i))
      hCaff
    exact ⟨q1 * q2, Nat.mul_pos hq1 hq2,
      (SliceDstar.EP_of_dvd hE1 (dvd_mul_right q1 q2)).and
        (SliceDstar.EP_of_dvd hE2 (dvd_mul_left q2 q1))⟩
  set strict' : ℕ → ℕ := fun n =>
    ∑ c : Fin P.toPoly.K,
      ((∑ rs' ∈ frozenCells Z (P.toPoly.arity c),
        if ((Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
              (cellTuple rs' (Z + 1) n))
            ∧ WRP.lexLt (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) (dstarC n))
        then 1 else 0)
      + ∑ rs ∈ bulkCells Z hZ (P.toPoly.arity c),
          ((((Finset.range n).filter (fun t : ℕ =>
            WRP.lexLt (Rcell c rs t) (fun i => dstarC n i - Bcell c rs n i)
              ∧ (min t (Z + 1) = Z + 1
                ∧ min (n - 1 - t) (Z + clusterWidth rs - 1) = Z + clusterWidth rs - 1
                ∧ cellAcc (Uc c) rs
                    ((bFN (Uc c))^[n - 1 - t + 1 - (Z + clusterWidth rs)]
                      (cellGclW (Uc c) rs
                        ((bFN (Uc c))^[t - Z] (cellQ0 (Uc c) rs))))))).card)
          + (if ((Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
                  (cellTuple rs Z n))
                ∧ WRP.lexLt (fun i => RcellH c (fr2 c rs) (2 * Z + 1) i
                    + BcellH c (fr2 c rs) n i) (dstarC n))
            then 1 else 0)))
    with hstrictdef
  refine ⟨strict', Ncan + N0 + 4 * Z + 3, ?_, ?_⟩
  · -- affineness
    rw [hstrictdef]
    refine AffineOnResidues.finsetSum _ _ (fun c _ => ?_)
    refine AffineOnResidues.add ?_ ?_
    · refine AffineOnResidues.finsetSum _ _ (fun rs' hrs' => ?_)
      have hcf : ∀ i, clusterFree (rs' i) := by
        rw [frozenCells, Finset.mem_filter] at hrs'
        exact hrs'.2
      obtain ⟨q, hq, hE⟩ := hfzEP c rs' hcf
      refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_)
        (SliceFasCount.affineOnResidues_indicator_of_EP hq hE)
      by_cases h : ((Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
            (cellTuple rs' (Z + 1) n))
          ∧ WRP.lexLt (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) (dstarC n))
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
    · refine AffineOnResidues.finsetSum _ _ (fun rs hrs => ?_)
      refine AffineOnResidues.add ?_ ?_
      · have hker := SliceGatedConv.affineOnResidues_gatedLexConvolution
          (u := fun t => ((bFN (Uc c))^[t - Z] (cellQ0 (Uc c) rs), min t (Z + 1)))
          (v := fun mm => ((bFN (Uc c))^[mm + 1 - (Z + clusterWidth rs)],
            min mm (Z + clusterWidth rs - 1)))
          (b := fun qf gf => qf.2 = Z + 1 ∧ gf.2 = Z + clusterWidth rs - 1
            ∧ cellAcc (Uc c) rs (gf.1 (cellGclW (Uc c) rs qf.1)))
          (mu := mv c + Z + Z + 1) (hpu := hpv c)
          (by
            intro i hi
            rw [show i + pv c - Z = (i - Z) + pv c from by omega,
              congrFun (hEPc c (i - Z) (by omega)) (cellQ0 (Uc c) rs),
              show min (i + pv c) (Z + 1) = Z + 1 from by omega,
              show min i (Z + 1) = Z + 1 from by omega])
          (mv := mv c + 2 * Z + clusterWidth rs) (hpv := hpv c)
          (by
            intro j hj
            rw [show j + pv c + 1 - (Z + clusterWidth rs)
                = (j + 1 - (Z + clusterWidth rs)) + pv c from by omega,
              hEPc c (j + 1 - (Z + clusterWidth rs)) (by omega),
              show min (j + pv c) (Z + clusterWidth rs - 1)
                = Z + clusterWidth rs - 1 from by omega,
              show min j (Z + clusterWidth rs - 1) = Z + clusterWidth rs - 1
                from by omega])
          (R := Rcell c rs) (PR := PR c rs) (hpR := hp)
          (hR := fun j hj => hRrec c rs j hj)
          (T := fun n => fun i => dstarC n i - Bcell c rs n i)
          (hT := fun i => (hCaff i).sub
            (SliceFasBridges.rankAffine_coord_affineOnResiduesZ
              ⟨m, p, PBn c rs, hp, hBrec c rs⟩ i))
        refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_) hker
        refine congrArg Finset.card ?_
        convert rfl
      · obtain ⟨q, hq, hE⟩ := hbdEP c rs
        refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_)
          (SliceFasCount.affineOnResidues_indicator_of_EP hq hE)
        by_cases h : ((Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
              (cellTuple rs Z n))
            ∧ WRP.lexLt (fun i => RcellH c (fr2 c rs) (2 * Z + 1) i
                + BcellH c (fr2 c rs) n i) (dstarC n))
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h]
  · -- agreement
    intro n hn hdom hD
    have hagree : SliceDstarGA.dstarRankGA P hV n = dstarC n :=
      hCagree n (by omega) hdom hD
    rw [hstrictdef]
    beta_reduce
    refine Finset.sum_congr rfl (fun c _ => ?_)
    obtain ⟨QQ, hQQ⟩ : ∃ Q : (Fin (P.toPoly.arity c) → ℕ) → Prop,
        ∀ ī, Q ī ↔ (P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩
          ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
          ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, ī⟩) (dstarC n)) :=
      ⟨_, fun ī => Iff.rfl⟩
    have hQsel : ∀ ī, QQ ī → P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩ := by
      intro ī h
      rw [hQQ ī] at h
      exact h.1
    have hQiff : ∀ ī, (∀ i, ī i < (wrappedFlat n).length) →
        (QQ ī ↔ (P.toPoly.sel c (wrappedFlat n) ī
          ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
          ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, ī⟩)
              (SliceDstarGA.dstarRankGA P hV n))) := by
      intro ī hval
      rw [hQQ ī, hagree]
      constructor
      · rintro ⟨hs, hl, hr⟩
        exact ⟨hs.2, hl, hr⟩
      · rintro ⟨hs, hl, hr⟩
        exact ⟨⟨hval, hs⟩, hl, hr⟩
    have hrec := hrecount n (by omega) hdom c QQ hQsel
    refine Eq.trans (Eq.trans ?_ hrec.symm) ?_
    case refine_2 =>
      refine Finset.sum_congr rfl (fun ī hī => ?_)
      have hval : ∀ i, ī i < (wrappedFlat n).length := by
        rw [Fintype.mem_piFinset] at hī
        intro i
        have := hī i
        rwa [Finset.mem_range] at this
      by_cases h : QQ ī
      · rw [if_pos h, if_pos ((hQiff ī hval).mp h)]
      · rw [if_neg h, if_neg (fun hc => h ((hQiff ī hval).mpr hc))]
    congr 1
    · -- frozen arm
      refine Finset.sum_congr rfl (fun rs' hrs' => ?_)
      have hval := SliceDstarGateGA.cellTuple_valid rs' (Z + 1) n
        (show Z + 1 + Z ≤ n from by omega)
      have hrank : P.rankOf (wrappedFlat n) ⟨c, cellTuple rs' (Z + 1) n⟩
          = fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i :=
        hwineq c rs' (Z + 1) n le_rfl (by omega)
      have hiff : (((Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
            (cellTuple rs' (Z + 1) n))
          ∧ WRP.lexLt (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) (dstarC n))
          ↔ QQ (cellTuple rs' (Z + 1) n)) := by
        rw [hQQ _]
        rw [hUc c (wrappedFlat n) _ hval, hrank]
        constructor
        · rintro ⟨⟨hs, hl⟩, hr⟩
          exact ⟨⟨hval, hs⟩, hl, hr⟩
        · rintro ⟨hs, hl, hr⟩
          exact ⟨⟨hs.2, hl⟩, hr⟩
      by_cases h : ((Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
          (cellTuple rs' (Z + 1) n))
        ∧ WRP.lexLt (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) (dstarC n))
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
    · -- bulk arm: split the boundary base and match the kernel window
      refine Finset.sum_congr rfl (fun rs hrs => ?_)
      have hWpos : 1 ≤ clusterWidth rs := by
        rw [bulkCells, Finset.mem_filter] at hrs
        exact bulk_width_pos (hZ := hZ) hrs.2
      have hWZ := clusterWidth_le rs
      -- the prop-level window/kernel identification (instance-free)
      have hiffT : ∀ t : ℕ, (t < n
            ∧ (WRP.lexLt (Rcell c rs t) (fun i => dstarC n i - Bcell c rs n i)
              ∧ (min t (Z + 1) = Z + 1
                ∧ min (n - 1 - t) (Z + clusterWidth rs - 1)
                    = Z + clusterWidth rs - 1
                ∧ cellAcc (Uc c) rs
                    ((bFN (Uc c))^[n - 1 - t + 1 - (Z + clusterWidth rs)]
                      (cellGclW (Uc c) rs
                        ((bFN (Uc c))^[t - Z] (cellQ0 (Uc c) rs)))))))
          ↔ ((Z + 1 ≤ t ∧ t ≤ n - Z - clusterWidth rs)
              ∧ QQ (cellTuple rs t n)) := by
        intro t
        constructor
        · rintro ⟨htn', hlex, hfl, hfr, hbit⟩
          have htlo : Z + 1 ≤ t := by omega
          have hthi : t ≤ n - Z - clusterWidth rs := by
            have : Z + clusterWidth rs - 1 ≤ n - 1 - t := by omega
            omega
          have hwin : t + clusterWidth rs + Z ≤ n := by omega
          have hval := SliceDstarGateGA.cellTuple_valid rs t n (by omega)
          have hacc : (Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
              (cellTuple rs t n)) := by
            rw [acceptsN_cellTuple_convW (Uc c) rs t n (by omega) hwin,
              show n - Z - clusterWidth rs - t
                = n - 1 - t + 1 - (Z + clusterWidth rs) from by omega]
            exact hbit
          rw [hUc c (wrappedFlat n) _ hval] at hacc
          have hrank : P.rankOf (wrappedFlat n) ⟨c, cellTuple rs t n⟩
              = fun i => Rcell c rs t i + Bcell c rs n i :=
            hwineq c rs t n (by omega) (by omega)
          refine ⟨⟨htlo, hthi⟩, ?_⟩
          rw [hQQ _, hrank]
          exact ⟨⟨hval, hacc.1⟩, hacc.2, (lexLt_sub_right _ _ _).mpr hlex⟩
        · rintro ⟨⟨htlo, hthi⟩, hQ⟩
          have hwin : t + clusterWidth rs + Z ≤ n := by omega
          have hval := SliceDstarGateGA.cellTuple_valid rs t n (by omega)
          have hrank : P.rankOf (wrappedFlat n) ⟨c, cellTuple rs t n⟩
              = fun i => Rcell c rs t i + Bcell c rs n i :=
            hwineq c rs t n (by omega) (by omega)
          rw [hQQ _] at hQ
          rw [hrank] at hQ
          obtain ⟨hsel, hlab, hlex⟩ := hQ
          refine ⟨by omega, (lexLt_sub_right _ _ _).mp hlex,
            by omega, by omega, ?_⟩
          have hacc : (Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
              (cellTuple rs t n)) := by
            rw [hUc c (wrappedFlat n) _ hval]
            exact ⟨hsel.2, hlab⟩
          rw [acceptsN_cellTuple_convW (Uc c) rs t n (by omega) hwin] at hacc
          rwa [show n - 1 - t + 1 - (Z + clusterWidth rs)
            = n - Z - clusterWidth rs - t from by omega]
      -- the boundary indicator ⟺ the predicate at the boundary base
      have hbdiff : (((Uc c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
            (cellTuple rs Z n))
          ∧ WRP.lexLt (fun i => RcellH c (fr2 c rs) (2 * Z + 1) i
              + BcellH c (fr2 c rs) n i) (dstarC n))
          ↔ QQ (cellTuple rs Z n)) := by
        have hvalZ := SliceDstarGateGA.cellTuple_valid rs Z n (by omega)
        have hrk : P.rankOf (wrappedFlat n) ⟨c, cellTuple rs Z n⟩
            = fun i => RcellH c (fr2 c rs) (2 * Z + 1) i
              + BcellH c (fr2 c rs) n i := by
          show P.rank c (wrappedFlat n) (cellTuple rs Z n) = _
          rw [hfr2tup c rs n]
          exact heqH c (fr2 c rs) (2 * Z + 1) n le_rfl (by omega)
        rw [hQQ _]
        rw [hUc c (wrappedFlat n) _ hvalZ, hrk]
        constructor
        · rintro ⟨⟨hs, hl⟩, hr⟩
          exact ⟨⟨hvalZ, hs⟩, hl, hr⟩
        · rintro ⟨hs, hl, hr⟩
          exact ⟨⟨hs.2, hl⟩, hr⟩
      conv_rhs => rw [← Finset.card_filter_add_card_filter_not
        (p := fun t => t = Z)]
      conv_rhs => rw [Nat.add_comm]
      congr 1
      · -- the kernel matches the non-boundary part
        symm
        refine congrArg Finset.card ?_
        refine Finset.ext (fun t => ?_)
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter,
          Finset.mem_range, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨⟨htlo, hthi⟩, hQ⟩, htne⟩
          exact (hiffT t).mpr ⟨⟨by omega, hthi⟩, hQ⟩
        · intro h
          have := (hiffT t).mp h
          exact ⟨⟨⟨by omega, this.1.2⟩, this.2⟩, by omega⟩
      · -- the boundary part is the boundary indicator
        by_cases hQZ : QQ (cellTuple rs Z n)
        · rw [if_pos (hbdiff.mpr hQZ)]
          symm
          refine Finset.card_eq_one.mpr ⟨Z, ?_⟩
          refine Finset.ext (fun t => ?_)
          rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc,
            Finset.mem_singleton]
          constructor
          · rintro ⟨-, ht⟩
            exact ht
          · rintro rfl
            exact ⟨⟨⟨by omega, by omega⟩, hQZ⟩, rfl⟩
        · rw [if_neg (fun hc => hQZ (hbdiff.mp hc))]
          symm
          rw [Finset.card_eq_zero]
          refine Finset.eq_empty_of_forall_notMem (fun t ht => ?_)
          rw [Finset.mem_filter, Finset.mem_filter] at ht
          obtain ⟨⟨-, hQ⟩, ht⟩ := ht
          subst ht
          exact hQZ hQ

/-! ## GA-7.5: the tie count -/

/-- Vector translation: adding on the left is subtracting on the right. -/
theorem vec_eq_sub_right {d : ℕ} (x y z : Fin d → ℤ) :
    ((fun i => x i + z i) = y) ↔ (x = fun i => y i - z i) := by
  constructor <;> intro h <;> funext i <;> have := congrFun h i <;>
    omega

/-- **The TIE count is affine-on-residues** (GA-7.5): selected `U`-atoms of `d*`-rank
that `atomOrd`-precede every equal-rank selected `D`-atom. -/
theorem tie_count_GA (P : WRP.Presentation Step Step) (hV : P.Valid) (C : ℕ)
    (hbud : ∀ n, P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) :
    ∃ (tie' : ℕ → ℕ) (N : ℕ), AffineOnResidues tie' ∧
      ∀ n, N ≤ n → P.toPoly.domain (wrappedFlat n) →
        (∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧
          P.toPoly.labelOf (wrappedFlat n) a = D) →
        tie' n = ∑ c : Fin P.toPoly.K,
          ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
            Finset.range (wrappedFlat n).length),
          if (P.toPoly.sel c (wrappedFlat n) ī
              ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
              ∧ P.rankOf (wrappedFlat n) ⟨c, ī⟩ = SliceDstarGA.dstarRankGA P hV n
              ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
                  P.toPoly.labelOf (wrappedFlat n) b = D →
                  P.rankOf (wrappedFlat n) b = SliceDstarGA.dstarRankGA P hV n →
                  P.toPoly.atomOrd (wrappedFlat n) ⟨c, ī⟩ b) then 1 else 0 := by
  classical
  obtain ⟨p0, N1, Gdfa, hp0, hbridge⟩ := tie_point_bridge_GA P hV C hbud
  obtain ⟨dstarC, N0, hCaff, hCagree⟩ := SliceDstarBridgeGA.dstarC_exists_GA P hV C hbud
  obtain ⟨Z, Ncan, hZ, hrecount⟩ := canonical_recount P C hbud
  obtain ⟨m, p, _Mc, Rcell, Bcell, PR, PBn, hp, hmB, _hMc, _hbwd, hwineq, hRrec, hBrec⟩ :=
    SliceDstarBridgeGA.dstar_setup_GA P Z
  choose RcellH BcellH hRAH hBAH heqH using
    fun (c : Fin P.toPoly.K) (rs'' : Fin (P.toPoly.arity c) → RegionSpec (2 * Z)) =>
      SliceFamilyRank.rank_cell_decomp (B := 2 * Z) P c rs''
  choose mvG pvG hpvG hEPG using
    fun (κ : ℕ) (c : Fin P.toPoly.K) => bFN_func_iterate_eventuallyPeriodic (Gdfa κ c)
  have hZ2 : Z ≤ 2 * Z := by omega
  have hZZ : Z + Z ≤ 2 * Z := by omega
  set fr2 : (c : Fin P.toPoly.K) → (Fin (P.toPoly.arity c) → RegionSpec Z) →
      (Fin (P.toPoly.arity c) → RegionSpec (2 * Z)) :=
    fun c rs i => refreezeFront hZ2 Z hZZ (rs i) with hfr2def
  have hfr2tup : ∀ (c : Fin P.toPoly.K) (rs : Fin (P.toPoly.arity c) → RegionSpec Z)
      (n : ℕ), cellTuple rs Z n = cellTuple (fr2 c rs) (2 * Z + 1) n := by
    intro c rs n
    funext i
    rw [hfr2def]
    beta_reduce
    exact (refreezeFront_posAt hZ2 Z hZZ (rs i) (2 * Z + 1) n).symm
  -- per-class EP packages
  have hfzEP : ∀ (κ : ℕ) (c : Fin P.toPoly.K)
      (rs' : Fin (P.toPoly.arity c) → RegionSpec Z), (∀ i, clusterFree (rs' i)) →
      ∃ q, 1 ≤ q ∧ EventuallyPeriodic (fun n =>
        (Gdfa κ c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
          (cellTuple rs' (Z + 1) n))
        ∧ (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) = dstarC n) q := by
    intro κ c rs' hcf
    obtain ⟨q1, hq1, hE1⟩ := acceptsN_clusterFree_EP (Gdfa κ c) rs' hcf (Z + 1)
    obtain ⟨q2, hq2, hE2⟩ := SliceFasSelector.affineOnResiduesZ_vec_eq_EP
      (F := fun n => fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) (G := dstarC)
      (fun i => (AffineOnResiduesZ.const (Rcell c rs' (Z + 1) i)).add
        (SliceFasBridges.rankAffine_coord_affineOnResiduesZ
          ⟨m, p, PBn c rs', hp, hBrec c rs'⟩ i)) hCaff
    exact ⟨q1 * q2, Nat.mul_pos hq1 hq2,
      (SliceDstar.EP_of_dvd hE1 (dvd_mul_right q1 q2)).and
        (SliceDstar.EP_of_dvd hE2 (dvd_mul_left q2 q1))⟩
  have hbdEP : ∀ (κ : ℕ) (c : Fin P.toPoly.K)
      (rs : Fin (P.toPoly.arity c) → RegionSpec Z),
      ∃ q, 1 ≤ q ∧ EventuallyPeriodic (fun n =>
        (Gdfa κ c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
          (cellTuple rs Z n))
        ∧ (fun i => RcellH c (fr2 c rs) (2 * Z + 1) i
            + BcellH c (fr2 c rs) n i) = dstarC n) q := by
    intro κ c rs
    obtain ⟨q1, hq1, hE1⟩ := acceptsN_cellTuple_baseZ_EP (Gdfa κ c) rs
    obtain ⟨q2, hq2, hE2⟩ := SliceFasSelector.affineOnResiduesZ_vec_eq_EP
      (F := fun n => fun i => RcellH c (fr2 c rs) (2 * Z + 1) i
        + BcellH c (fr2 c rs) n i) (G := dstarC)
      (fun i => (AffineOnResiduesZ.const (RcellH c (fr2 c rs) (2 * Z + 1) i)).add
        (SliceFasBridges.rankAffine_coord_affineOnResiduesZ (hBAH c (fr2 c rs)) i))
      hCaff
    exact ⟨q1 * q2, Nat.mul_pos hq1 hq2,
      (SliceDstar.EP_of_dvd hE1 (dvd_mul_right q1 q2)).and
        (SliceDstar.EP_of_dvd hE2 (dvd_mul_left q2 q1))⟩
  set tieKer : ℕ → ℕ → ℕ := fun κ n =>
    ∑ c : Fin P.toPoly.K,
      ((∑ rs' ∈ frozenCells Z (P.toPoly.arity c),
        if ((Gdfa κ c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
              (cellTuple rs' (Z + 1) n))
            ∧ (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) = dstarC n)
        then 1 else 0)
      + ∑ rs ∈ bulkCells Z hZ (P.toPoly.arity c),
          ((((Finset.range n).filter (fun t : ℕ =>
            Rcell c rs t = (fun i => dstarC n i - Bcell c rs n i)
              ∧ (min t (Z + 1) = Z + 1
                ∧ min (n - 1 - t) (Z + clusterWidth rs - 1)
                    = Z + clusterWidth rs - 1
                ∧ cellAcc (Gdfa κ c) rs
                    ((bFN (Gdfa κ c))^[n - 1 - t + 1 - (Z + clusterWidth rs)]
                      (cellGclW (Gdfa κ c) rs
                        ((bFN (Gdfa κ c))^[t - Z] (cellQ0 (Gdfa κ c) rs))))))).card)
          + (if ((Gdfa κ c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
                  (cellTuple rs Z n))
                ∧ (fun i => RcellH c (fr2 c rs) (2 * Z + 1) i
                    + BcellH c (fr2 c rs) n i) = dstarC n)
            then 1 else 0)))
    with htiedef
  have htieAff : ∀ κ, AffineOnResidues (tieKer κ) := by
    intro κ
    rw [htiedef]
    beta_reduce
    refine AffineOnResidues.finsetSum _ _ (fun c _ => ?_)
    refine AffineOnResidues.add ?_ ?_
    · refine AffineOnResidues.finsetSum _ _ (fun rs' hrs' => ?_)
      have hcf : ∀ i, clusterFree (rs' i) := by
        rw [frozenCells, Finset.mem_filter] at hrs'
        exact hrs'.2
      obtain ⟨q, hq, hE⟩ := hfzEP κ c rs' hcf
      refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_)
        (SliceFasCount.affineOnResidues_indicator_of_EP hq hE)
      by_cases h : ((Gdfa κ c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
            (cellTuple rs' (Z + 1) n))
          ∧ (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) = dstarC n)
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
    · refine AffineOnResidues.finsetSum _ _ (fun rs hrs => ?_)
      refine AffineOnResidues.add ?_ ?_
      · have hker := SliceFasCount.affineOnResidues_gatedEqConvolution
          (u := fun t => ((bFN (Gdfa κ c))^[t - Z] (cellQ0 (Gdfa κ c) rs),
            min t (Z + 1)))
          (v := fun mm => ((bFN (Gdfa κ c))^[mm + 1 - (Z + clusterWidth rs)],
            min mm (Z + clusterWidth rs - 1)))
          (b := fun qf gf => qf.2 = Z + 1 ∧ gf.2 = Z + clusterWidth rs - 1
            ∧ cellAcc (Gdfa κ c) rs (gf.1 (cellGclW (Gdfa κ c) rs qf.1)))
          (mu := mvG κ c + Z + Z + 1) (hpu := hpvG κ c)
          (by
            intro i hi
            rw [show i + pvG κ c - Z = (i - Z) + pvG κ c from by omega,
              congrFun (hEPG κ c (i - Z) (by omega)) (cellQ0 (Gdfa κ c) rs),
              show min (i + pvG κ c) (Z + 1) = Z + 1 from by omega,
              show min i (Z + 1) = Z + 1 from by omega])
          (mv := mvG κ c + 2 * Z + clusterWidth rs) (hpv := hpvG κ c)
          (by
            intro j hj
            rw [show j + pvG κ c + 1 - (Z + clusterWidth rs)
                = (j + 1 - (Z + clusterWidth rs)) + pvG κ c from by omega,
              hEPG κ c (j + 1 - (Z + clusterWidth rs)) (by omega),
              show min (j + pvG κ c) (Z + clusterWidth rs - 1)
                = Z + clusterWidth rs - 1 from by omega,
              show min j (Z + clusterWidth rs - 1) = Z + clusterWidth rs - 1
                from by omega])
          (R := Rcell c rs) (PR := PR c rs) (hpR := hp)
          (hR := fun j hj => hRrec c rs j hj)
          (T := fun n => fun i => dstarC n i - Bcell c rs n i)
          (hT := fun i => (hCaff i).sub
            (SliceFasBridges.rankAffine_coord_affineOnResiduesZ
              ⟨m, p, PBn c rs, hp, hBrec c rs⟩ i))
        refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_) hker
        refine congrArg Finset.card ?_
        convert rfl
      · obtain ⟨q, hq, hE⟩ := hbdEP κ c rs
        refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_)
          (SliceFasCount.affineOnResidues_indicator_of_EP hq hE)
        by_cases h : ((Gdfa κ c).accepts (markAtN (P.toPoly.arity c) (wrappedFlat n)
              (cellTuple rs Z n))
            ∧ (fun i => RcellH c (fr2 c rs) (2 * Z + 1) i
                + BcellH c (fr2 c rs) n i) = dstarC n)
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h]
  refine ⟨fun n => tieKer (n % p0) n, N1 + N0 + Ncan + 4 * Z + 3, ?_, ?_⟩
  · exact AffineOnResidues.select (Finset.range p0) tieKer (fun n => n % p0) p0 hp0
      (fun κ _ => htieAff κ) (fun n => Finset.mem_range.mpr (Nat.mod_lt _ hp0))
      (fun κ _ => ⟨0, fun n _ => by simp only []; rw [Nat.add_mod_right]⟩)
  · -- agreement
    intro n hn hdom hD
    have hagree : SliceDstarGA.dstarRankGA P hV n = dstarC n :=
      hCagree n (by omega) hdom hD
    rw [htiedef]
    beta_reduce
    refine Finset.sum_congr rfl (fun c _ => ?_)
    obtain ⟨QQ, hQQ⟩ : ∃ Q : (Fin (P.toPoly.arity c) → ℕ) → Prop,
        ∀ ī, Q ī ↔ (P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩
          ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
          ∧ P.rankOf (wrappedFlat n) ⟨c, ī⟩ = SliceDstarGA.dstarRankGA P hV n
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
              P.toPoly.labelOf (wrappedFlat n) b = D →
              P.rankOf (wrappedFlat n) b = SliceDstarGA.dstarRankGA P hV n →
              P.toPoly.atomOrd (wrappedFlat n) ⟨c, ī⟩ b) :=
      ⟨_, fun ī => Iff.rfl⟩
    have hQsel : ∀ ī, QQ ī → P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩ := by
      intro ī h
      rw [hQQ ī] at h
      exact h.1
    have hQiff : ∀ ī, (∀ i, ī i < (wrappedFlat n).length) →
        (QQ ī ↔ (P.toPoly.sel c (wrappedFlat n) ī
          ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
          ∧ P.rankOf (wrappedFlat n) ⟨c, ī⟩ = SliceDstarGA.dstarRankGA P hV n
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
              P.toPoly.labelOf (wrappedFlat n) b = D →
              P.rankOf (wrappedFlat n) b = SliceDstarGA.dstarRankGA P hV n →
              P.toPoly.atomOrd (wrappedFlat n) ⟨c, ī⟩ b)) := by
      intro ī hval
      rw [hQQ ī]
      constructor
      · rintro ⟨hs, hrest⟩
        exact ⟨hs.2, hrest⟩
      · rintro ⟨hs, hrest⟩
        exact ⟨⟨hval, hs⟩, hrest⟩
    -- the per-tuple bridge form: QQ ⟺ accepts ∧ rank-eq (against dstarC)
    have hQacc : ∀ (ī : Fin (P.toPoly.arity c) → ℕ),
        (∀ i, ī i < (wrappedFlat n).length) →
        (QQ ī ↔ ((Gdfa (n % p0) c).accepts (markAtN (P.toPoly.arity c)
            (wrappedFlat n) ī)
          ∧ P.rank c (wrappedFlat n) ī = dstarC n)) := by
      intro ī hval
      rw [← hagree, hQQ ī]
      have hb := hbridge n (by omega) hdom hD c ī hval
      constructor
      · rintro ⟨hs, hrest⟩
        exact hb.mp ⟨hs.2, hrest⟩
      · intro h
        obtain ⟨hs, hrest⟩ := hb.mpr h
        exact ⟨⟨hval, hs⟩, hrest⟩
    have hrec := hrecount n (by omega) hdom c QQ hQsel
    refine Eq.trans (Eq.trans ?_ hrec.symm) ?_
    case refine_2 =>
      refine Finset.sum_congr rfl (fun ī hī => ?_)
      have hval : ∀ i, ī i < (wrappedFlat n).length := by
        rw [Fintype.mem_piFinset] at hī
        intro i
        have := hī i
        rwa [Finset.mem_range] at this
      by_cases h : QQ ī
      · rw [if_pos h, if_pos ((hQiff ī hval).mp h)]
      · rw [if_neg h, if_neg (fun hc => h ((hQiff ī hval).mpr hc))]
    congr 1
    · -- frozen arm
      refine Finset.sum_congr rfl (fun rs' hrs' => ?_)
      have hval := SliceDstarGateGA.cellTuple_valid rs' (Z + 1) n
        (show Z + 1 + Z ≤ n from by omega)
      have hrank : P.rank c (wrappedFlat n) (cellTuple rs' (Z + 1) n)
          = fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i :=
        hwineq c rs' (Z + 1) n le_rfl (by omega)
      have hiff : (((Gdfa (n % p0) c).accepts (markAtN (P.toPoly.arity c)
            (wrappedFlat n) (cellTuple rs' (Z + 1) n))
          ∧ (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) = dstarC n)
          ↔ QQ (cellTuple rs' (Z + 1) n)) := by
        rw [hQacc _ hval, hrank]
      by_cases h : ((Gdfa (n % p0) c).accepts (markAtN (P.toPoly.arity c)
            (wrappedFlat n) (cellTuple rs' (Z + 1) n))
          ∧ (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) = dstarC n)
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
    · -- bulk arm
      refine Finset.sum_congr rfl (fun rs hrs => ?_)
      have hWpos : 1 ≤ clusterWidth rs := by
        rw [bulkCells, Finset.mem_filter] at hrs
        exact bulk_width_pos (hZ := hZ) hrs.2
      have hWZ := clusterWidth_le rs
      have hiffT : ∀ t : ℕ, (t < n
            ∧ (Rcell c rs t = (fun i => dstarC n i - Bcell c rs n i)
              ∧ (min t (Z + 1) = Z + 1
                ∧ min (n - 1 - t) (Z + clusterWidth rs - 1)
                    = Z + clusterWidth rs - 1
                ∧ cellAcc (Gdfa (n % p0) c) rs
                    ((bFN (Gdfa (n % p0) c))^[n - 1 - t + 1 - (Z + clusterWidth rs)]
                      (cellGclW (Gdfa (n % p0) c) rs
                        ((bFN (Gdfa (n % p0) c))^[t - Z]
                          (cellQ0 (Gdfa (n % p0) c) rs)))))))
          ↔ ((Z + 1 ≤ t ∧ t ≤ n - Z - clusterWidth rs)
              ∧ QQ (cellTuple rs t n)) := by
        intro t
        constructor
        · rintro ⟨htn', heq, hfl, hfr, hbit⟩
          have htlo : Z + 1 ≤ t := by omega
          have hthi : t ≤ n - Z - clusterWidth rs := by
            have : Z + clusterWidth rs - 1 ≤ n - 1 - t := by omega
            omega
          have hwin : t + clusterWidth rs + Z ≤ n := by omega
          have hval := SliceDstarGateGA.cellTuple_valid rs t n (by omega)
          have hacc : (Gdfa (n % p0) c).accepts (markAtN (P.toPoly.arity c)
              (wrappedFlat n) (cellTuple rs t n)) := by
            rw [acceptsN_cellTuple_convW (Gdfa (n % p0) c) rs t n (by omega) hwin,
              show n - Z - clusterWidth rs - t
                = n - 1 - t + 1 - (Z + clusterWidth rs) from by omega]
            exact hbit
          have hrank : P.rank c (wrappedFlat n) (cellTuple rs t n)
              = fun i => Rcell c rs t i + Bcell c rs n i :=
            hwineq c rs t n (by omega) (by omega)
          refine ⟨⟨htlo, hthi⟩, ?_⟩
          rw [hQacc _ hval]
          refine ⟨hacc, ?_⟩
          rw [hrank]
          exact (vec_eq_sub_right _ _ _).mpr heq
        · rintro ⟨⟨htlo, hthi⟩, hQ⟩
          have hwin : t + clusterWidth rs + Z ≤ n := by omega
          have hval := SliceDstarGateGA.cellTuple_valid rs t n (by omega)
          rw [hQacc _ hval] at hQ
          obtain ⟨hacc, hrkeq⟩ := hQ
          have hrank : P.rank c (wrappedFlat n) (cellTuple rs t n)
              = fun i => Rcell c rs t i + Bcell c rs n i :=
            hwineq c rs t n (by omega) (by omega)
          rw [hrank] at hrkeq
          refine ⟨by omega, (vec_eq_sub_right _ _ _).mp hrkeq,
            by omega, by omega, ?_⟩
          rw [acceptsN_cellTuple_convW (Gdfa (n % p0) c) rs t n (by omega) hwin]
            at hacc
          rwa [show n - 1 - t + 1 - (Z + clusterWidth rs)
            = n - Z - clusterWidth rs - t from by omega]
      have hbdiff : (((Gdfa (n % p0) c).accepts (markAtN (P.toPoly.arity c)
            (wrappedFlat n) (cellTuple rs Z n))
          ∧ (fun i => RcellH c (fr2 c rs) (2 * Z + 1) i
              + BcellH c (fr2 c rs) n i) = dstarC n)
          ↔ QQ (cellTuple rs Z n)) := by
        have hvalZ := SliceDstarGateGA.cellTuple_valid rs Z n (by omega)
        have hrk : P.rank c (wrappedFlat n) (cellTuple rs Z n)
            = fun i => RcellH c (fr2 c rs) (2 * Z + 1) i
              + BcellH c (fr2 c rs) n i := by
          rw [hfr2tup c rs n]
          exact heqH c (fr2 c rs) (2 * Z + 1) n le_rfl (by omega)
        rw [hQacc _ hvalZ, hrk]
      conv_rhs => rw [← Finset.card_filter_add_card_filter_not
        (p := fun t => t = Z)]
      conv_rhs => rw [Nat.add_comm]
      congr 1
      · symm
        refine congrArg Finset.card ?_
        refine Finset.ext (fun t => ?_)
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter,
          Finset.mem_range, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨⟨htlo, hthi⟩, hQ⟩, htne⟩
          exact (hiffT t).mpr ⟨⟨by omega, hthi⟩, hQ⟩
        · intro h
          have := (hiffT t).mp h
          exact ⟨⟨⟨by omega, this.1.2⟩, this.2⟩, by omega⟩
      · by_cases hQZ : QQ (cellTuple rs Z n)
        · rw [if_pos (hbdiff.mpr hQZ)]
          symm
          refine Finset.card_eq_one.mpr ⟨Z, ?_⟩
          refine Finset.ext (fun t => ?_)
          rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc,
            Finset.mem_singleton]
          constructor
          · rintro ⟨-, ht⟩
            exact ht
          · rintro rfl
            exact ⟨⟨⟨by omega, by omega⟩, hQZ⟩, rfl⟩
        · rw [if_neg (fun hc => hQZ (hbdiff.mp hc))]
          symm
          rw [Finset.card_eq_zero]
          refine Finset.eq_empty_of_forall_notMem (fun t ht => ?_)
          rw [Finset.mem_filter, Finset.mem_filter] at ht
          obtain ⟨⟨-, hQ⟩, ht⟩ := ht
          subst ht
          exact hQZ hQ

/-! ## GA-7.6: the pinned deliverables -/

/-- **The fas-predicate trichotomy** (the keystone split): on `D`-present slices the
pinned first-ascent membership splits exactly into the STRICT and TIE memberships. -/
theorem fas_pred_split_GA (P : WRP.Presentation Step Step) (hV : P.Valid) (n : ℕ)
    (hDp : ∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧
      P.toPoly.labelOf (wrappedFlat n) a = D)
    (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ)
    (hval : ∀ i, ī i < (wrappedFlat n).length) :
    ((if (P.toPoly.sel c (wrappedFlat n) ī
        ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
        ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
            (P.toPoly.labelOf (wrappedFlat n) b = U
              ∨ P.wrpOrd (wrappedFlat n) ⟨c, ī⟩ b)) then 1 else 0) : ℕ)
      = (if (P.toPoly.sel c (wrappedFlat n) ī
            ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
            ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, ī⟩)
                (SliceDstarGA.dstarRankGA P hV n)) then 1 else 0)
        + (if (P.toPoly.sel c (wrappedFlat n) ī
            ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
            ∧ P.rankOf (wrappedFlat n) ⟨c, ī⟩ = SliceDstarGA.dstarRankGA P hV n
            ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
                P.toPoly.labelOf (wrappedFlat n) b = D →
                P.rankOf (wrappedFlat n) b = SliceDstarGA.dstarRankGA P hV n →
                P.toPoly.atomOrd (wrappedFlat n) ⟨c, ī⟩ b) then 1 else 0) := by
  classical
  by_cases hsU : P.toPoly.sel c (wrappedFlat n) ī
      ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
  · obtain ⟨dstar, hdsel, hdD, hdmin, hdrank⟩ := SliceDstarGA.dstarRankGA_spec P hV n hDp
    have hasel : P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩ := ⟨hval, hsU.1⟩
    have hcoll := SliceOutput.fas_inner_collapse P hV (wrappedFlat n) dstar hdsel hdD
      hdmin ⟨c, ī⟩ hasel
    rcases SliceLexOrder.lexLt_trichot (P.rankOf (wrappedFlat n) ⟨c, ī⟩)
        (SliceDstarGA.dstarRankGA P hV n) with hlt | heq | hgt
    · -- strictly below
      rw [if_pos ⟨hsU.1, hsU.2, hcoll.mpr (Or.inl (by rw [← hdrank]; exact hlt))⟩,
        if_pos ⟨hsU.1, hsU.2, hlt⟩,
        if_neg (fun hc => SliceFasCount.lexLt_ne hlt hc.2.2.1)]
    · -- equal rank: the keystone
      have hrankeq : P.rankOf (wrappedFlat n) (⟨c, ī⟩ : P.toPoly.Atom)
          = P.rankOf (wrappedFlat n) dstar := by
        rw [heq, hdrank]
      have hkey := SliceFasTie.fas_member_eqRank P hV (wrappedFlat n) dstar hdsel hdD
        hdmin ⟨c, ī⟩ hasel hrankeq
      have hnB : ¬ (P.toPoly.sel c (wrappedFlat n) ī
          ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
          ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, ī⟩)
              (SliceDstarGA.dstarRankGA P hV n)) := by
        rintro ⟨-, -, hl⟩
        rw [heq] at hl
        exact SliceLexOrder.lexLt_irrefl _ hl
      by_cases hall : ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
          (P.toPoly.labelOf (wrappedFlat n) b = U
            ∨ P.wrpOrd (wrappedFlat n) ⟨c, ī⟩ b)
      · rw [if_pos ⟨hsU.1, hsU.2, hall⟩, if_neg hnB,
          if_pos ⟨hsU.1, hsU.2, heq, fun b hb hbD hbr =>
            (hkey.mp hall) b hb hbD (by rw [← hdrank]; exact hbr)⟩]
      · have hnA : ¬ (P.toPoly.sel c (wrappedFlat n) ī
            ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
            ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
                (P.toPoly.labelOf (wrappedFlat n) b = U
                  ∨ P.wrpOrd (wrappedFlat n) ⟨c, ī⟩ b)) :=
          fun hc => hall hc.2.2
        have hnC : ¬ (P.toPoly.sel c (wrappedFlat n) ī
            ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
            ∧ P.rankOf (wrappedFlat n) ⟨c, ī⟩ = SliceDstarGA.dstarRankGA P hV n
            ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
                P.toPoly.labelOf (wrappedFlat n) b = D →
                P.rankOf (wrappedFlat n) b = SliceDstarGA.dstarRankGA P hV n →
                P.toPoly.atomOrd (wrappedFlat n) ⟨c, ī⟩ b) :=
          fun hc => hall (hkey.mpr (fun b hb hbD hbr =>
            hc.2.2.2 b hb hbD (by rw [← hdrank] at hbr; exact hbr)))
        rw [if_neg hnA, if_neg hnB, if_neg hnC]
    · -- strictly above
      have hnA : ¬ (P.toPoly.sel c (wrappedFlat n) ī
          ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
              (P.toPoly.labelOf (wrappedFlat n) b = U
                ∨ P.wrpOrd (wrappedFlat n) ⟨c, ī⟩ b)) := by
        rintro ⟨-, -, hall⟩
        rcases hcoll.mp hall with hl | ⟨he, -⟩
        · refine SliceDstar.lexLt_asymm _ _ hgt ?_
          rw [hdrank]
          exact hl
        · refine SliceLexOrder.lexLt_irrefl (SliceDstarGA.dstarRankGA P hV n) ?_
          have he' : P.rankOf (wrappedFlat n) (⟨c, ī⟩ : P.toPoly.Atom)
              = SliceDstarGA.dstarRankGA P hV n := by
            rw [he, ← hdrank]
          rw [he'] at hgt
          exact hgt
      have hnB' : ¬ (P.toPoly.sel c (wrappedFlat n) ī
          ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
          ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, ī⟩)
              (SliceDstarGA.dstarRankGA P hV n)) := by
        rintro ⟨-, -, hl⟩
        exact SliceDstar.lexLt_asymm _ _ hgt hl
      have hnC : ¬ (P.toPoly.sel c (wrappedFlat n) ī
          ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
          ∧ P.rankOf (wrappedFlat n) ⟨c, ī⟩ = SliceDstarGA.dstarRankGA P hV n
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
              P.toPoly.labelOf (wrappedFlat n) b = D →
              P.rankOf (wrappedFlat n) b = SliceDstarGA.dstarRankGA P hV n →
              P.toPoly.atomOrd (wrappedFlat n) ⟨c, ī⟩ b) := by
        rintro ⟨-, -, he, -⟩
        rw [he] at hgt
        exact SliceLexOrder.lexLt_irrefl _ hgt
      rw [if_neg hnA, if_neg hnB', if_neg hnC]
  · rw [if_neg (fun hc => hsU ⟨hc.1, hc.2.1⟩), if_neg (fun hc => hsU ⟨hc.1, hc.2.1⟩),
      if_neg (fun hc => hsU ⟨hc.1, hc.2.1⟩)]

/-- **The first-ascent count is affine-on-residues** (GA-7.6, THE pinned deliverable):
agrees with `gatedFasCountGA` past a threshold, with NO domain or `D`-presence
hypothesis — the three-way Boolean select absorbs both. -/
theorem fas_count_affineOnResidues_GA (P : WRP.Presentation Step Step) (hV : P.Valid)
    (C : ℕ)
    (hbud : ∀ n, P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) :
    ∃ (fas' : ℕ → ℕ) (N : ℕ), AffineOnResidues fas' ∧
      ∀ n, N ≤ n → fas' n = SliceProfileDischargeGA.gatedFasCountGA P n := by
  classical
  obtain ⟨tot', Nt, htotA, htotE⟩ := totalSelectedU_count_GA P C hbud
  obtain ⟨strict', Ns, hstA, hstE⟩ := strict_count_GA P hV C hbud
  obtain ⟨tie', Nti, htiA, htiE⟩ := tie_count_GA P hV C hbud
  obtain ⟨md, pd, hpd, hdomEP⟩ := SliceFasAssembly.domain_slice_EP P.toPoly
  obtain ⟨pD, hpD, hDpEP⟩ := SliceDstar.Dpresent_eventuallyPeriodic P
  have hdomEP' : EventuallyPeriodic
      (fun n => P.toPoly.domain (wrappedFlat n)) pd := ⟨md, hdomEP⟩
  set sel3 : ℕ → Bool × Bool := fun n =>
    (decide (P.toPoly.domain (wrappedFlat n)),
     decide (∃ a, P.toPoly.selectedAtom (wrappedFlat n) a
       ∧ P.toPoly.labelOf (wrappedFlat n) a = D)) with hsel3def
  set f3 : Bool × Bool → ℕ → ℕ := fun bb n =>
    if bb.1 then (if bb.2 then strict' n + tie' n else tot' n) else 0 with hf3def
  refine ⟨fun n => f3 (sel3 n) n, Nt + Ns + Nti, ?_, ?_⟩
  · refine AffineOnResidues.select Finset.univ f3 sel3 (pd * pD)
      (Nat.mul_pos hpd hpD) (fun bb _ => ?_)
      (fun n => Finset.mem_univ _) (fun bb _ => ?_)
    · rw [hf3def]
      rcases bb with ⟨b1, b2⟩
      rcases b1 with _ | _
      · exact ⟨0, 1, fun _ => 0, le_refl 1, fun r k => by simp⟩
      · rcases b2 with _ | _
        · exact htotA
        · exact hstA.add htiA
    · -- the fibre `sel3 n = bb` is eventually periodic
      have hdom2 := SliceDstar.EP_of_dvd hdomEP' (dvd_mul_right pd pD)
      have hDp2 := SliceDstar.EP_of_dvd hDpEP (dvd_mul_left pD pd)
      rcases bb with ⟨b1, b2⟩
      have h1 : EventuallyPeriodic (fun n =>
          decide (P.toPoly.domain (wrappedFlat n)) = b1) (pd * pD) := by
        rcases b1 with _ | _
        · refine (SliceDstarCore.EP_not hdom2).congr (fun n => ?_)
          rw [decide_eq_false_iff_not]
        · refine hdom2.congr (fun n => ?_)
          rw [decide_eq_true_eq]
      have h2 : EventuallyPeriodic (fun n =>
          decide (∃ a, P.toPoly.selectedAtom (wrappedFlat n) a
            ∧ P.toPoly.labelOf (wrappedFlat n) a = D) = b2) (pd * pD) := by
        rcases b2 with _ | _
        · refine (SliceDstarCore.EP_not hDp2).congr (fun n => ?_)
          rw [decide_eq_false_iff_not]
        · refine hDp2.congr (fun n => ?_)
          rw [decide_eq_true_eq]
      refine (h1.and h2).congr (fun n => ?_)
      rw [hsel3def]
      beta_reduce
      constructor
      · rintro ⟨ha, hb⟩
        exact Prod.ext ha hb
      · intro h
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · -- agreement
    intro n hn
    by_cases hdom : P.toPoly.domain (wrappedFlat n)
    · by_cases hDp : ∃ a, P.toPoly.selectedAtom (wrappedFlat n) a
          ∧ P.toPoly.labelOf (wrappedFlat n) a = D
      · have hsel3n : sel3 n = (true, true) := by
          rw [hsel3def]
          beta_reduce
          rw [decide_eq_true hdom, decide_eq_true hDp]
        beta_reduce
        rw [hsel3n, hf3def]
        simp only [if_true]
        rw [SliceProfileDischargeGA.gatedFasCountGA, if_pos hdom,
          SliceProfileDischargeGA.fasCountGA,
          hstE n (by omega) hdom hDp, htiE n (by omega) hdom hDp,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun ī hī => ?_)
        have hval : ∀ i, ī i < (wrappedFlat n).length := by
          rw [Fintype.mem_piFinset] at hī
          intro i
          have := hī i
          rwa [Finset.mem_range] at this
        exact (fas_pred_split_GA P hV n hDp c ī hval).symm
      · have hsel3n : sel3 n = (true, false) := by
          rw [hsel3def]
          beta_reduce
          rw [decide_eq_true hdom, decide_eq_false hDp]
        beta_reduce
        rw [hsel3n, hf3def]
        simp only [if_true]
        rw [if_neg (Bool.false_ne_true),
          SliceProfileDischargeGA.gatedFasCountGA, if_pos hdom,
          SliceProfileDischargeGA.fasCountGA, htotE n (by omega) hdom]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        refine Finset.sum_congr rfl (fun ī hī => ?_)
        by_cases hsU : P.toPoly.sel c (wrappedFlat n) ī
            ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
        · have hall : ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
              (P.toPoly.labelOf (wrappedFlat n) b = U
                ∨ P.wrpOrd (wrappedFlat n) ⟨c, ī⟩ b) := by
            intro b hb
            rcases hlb : P.toPoly.labelOf (wrappedFlat n) b with _ | _
            · exact Or.inl rfl
            · exact absurd ⟨b, hb, hlb⟩ hDp
          rw [if_pos hsU, if_pos ⟨hsU.1, hsU.2, hall⟩]
        · rw [if_neg hsU, if_neg (fun hc => hsU ⟨hc.1, hc.2.1⟩)]
    · have hsel3n : (sel3 n).1 = false := by
        rw [hsel3def]
        beta_reduce
        rw [decide_eq_false hdom]
      rw [hf3def]
      beta_reduce
      rw [hsel3n]
      rw [if_neg (Bool.false_ne_true),
        SliceProfileDischargeGA.gatedFasCountGA, if_neg hdom]

/-- **The tail count is affine-on-residues** (GA-7.6): in fact `gatedTailUCountGA`
itself is affine, by the patched-witness subtraction against the landed partition. -/
theorem tailU_count_affineOnResidues_GA (P : WRP.Presentation Step Step) (hV : P.Valid)
    (C : ℕ)
    (hbud : ∀ n, P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) :
    AffineOnResidues (fun n => SliceProfileDischargeGA.gatedTailUCountGA P n) := by
  classical
  obtain ⟨fas', Nf, hfA, hfE⟩ := fas_count_affineOnResidues_GA P hV C hbud
  obtain ⟨tot', Nt, htA, htE⟩ := totalSelectedU_count_GA P C hbud
  obtain ⟨md, pd, hpd, hdomEP⟩ := SliceFasAssembly.domain_slice_EP P.toPoly
  have hdomEP' : EventuallyPeriodic
      (fun n => P.toPoly.domain (wrappedFlat n)) pd := ⟨md, hdomEP⟩
  -- the gated total
  set gTotSem : ℕ → ℕ := fun n =>
    if P.toPoly.domain (wrappedFlat n)
    then (∑ c : Fin P.toPoly.K,
      ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
        Finset.range (wrappedFlat n).length),
      if (P.toPoly.sel c (wrappedFlat n) ī
          ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U) then 1 else 0)
    else 0 with hgTotdef
  set N := Nf + Nt with hNdef
  -- the patched witnesses agree with the gated semantics EVERYWHERE
  set fas'' : ℕ → ℕ := fun n =>
    if n < N then SliceProfileDischargeGA.gatedFasCountGA P n else fas' n with hf2def
  set gtot'' : ℕ → ℕ := fun n =>
    if n < N then gTotSem n
    else (if P.toPoly.domain (wrappedFlat n) then tot' n else 0) with hg2def
  have hfas2 : ∀ n, fas'' n = SliceProfileDischargeGA.gatedFasCountGA P n := by
    intro n
    rw [hf2def]
    beta_reduce
    by_cases h : n < N
    · rw [if_pos h]
    · rw [if_neg h]
      exact hfE n (by omega)
  have hgtot2 : ∀ n, gtot'' n = gTotSem n := by
    intro n
    rw [hg2def, hgTotdef]
    beta_reduce
    by_cases h : n < N
    · rw [if_pos h]
    · rw [if_neg h]
      by_cases hdom : P.toPoly.domain (wrappedFlat n)
      · rw [if_pos hdom, if_pos hdom]
        exact htE n (by omega) hdom
      · rw [if_neg hdom, if_neg hdom]
  -- the pointwise partition
  have hpart : ∀ n, gtot'' n = fas'' n + SliceProfileDischargeGA.gatedTailUCountGA P n := by
    intro n
    rw [hfas2 n, hgtot2 n, hgTotdef, SliceProfileDischargeGA.gatedFasCountGA,
      SliceProfileDischargeGA.gatedTailUCountGA]
    beta_reduce
    by_cases hdom : P.toPoly.domain (wrappedFlat n)
    · rw [if_pos hdom, if_pos hdom, if_pos hdom]
      exact SliceProfileDischargeGA.totalSelectedU_eq_fas_add_tail_GA P n
    · rw [if_neg hdom, if_neg hdom, if_neg hdom]
  -- affineness of the patched witnesses
  have hf2A : AffineOnResidues fas'' := by
    refine AffineOnResidues.congr_eventually (N := N) (fun n hn => ?_) hfA
    rw [hf2def]
    beta_reduce
    rw [if_neg (by omega)]
  have hg2A : AffineOnResidues gtot'' := by
    have hgsel : AffineOnResidues (fun n =>
        if P.toPoly.domain (wrappedFlat n) then tot' n else 0) := by
      have := AffineOnResidues.select (Finset.univ : Finset Bool)
        (fun b n => if b then tot' n else 0)
        (fun n => decide (P.toPoly.domain (wrappedFlat n))) pd hpd
        (fun b _ => by
          rcases b with _ | _
          · exact ⟨0, 1, fun _ => 0, le_refl 1, fun r k => by simp⟩
          · exact htA)
        (fun n => Finset.mem_univ _)
        (fun b _ => by
          rcases b with _ | _
          · refine (SliceDstarCore.EP_not hdomEP').congr (fun n => ?_)
            rw [decide_eq_false_iff_not]
          · refine hdomEP'.congr (fun n => ?_)
            rw [decide_eq_true_eq])
      refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_) this
      by_cases hdom : P.toPoly.domain (wrappedFlat n)
      · rw [if_pos hdom, if_pos (show (decide (P.toPoly.domain (wrappedFlat n))
          = true) from decide_eq_true hdom)]
      · rw [if_neg hdom, if_neg (show ¬(decide (P.toPoly.domain (wrappedFlat n))
          = true) from by rw [decide_eq_false hdom]; exact Bool.false_ne_true)]
    refine AffineOnResidues.congr_eventually (N := N) (fun n hn => ?_) hgsel
    rw [hg2def]
    beta_reduce
    rw [if_neg (by omega)]
  exact SliceFasCount.AffineOnResidues.sub_of_partition hg2A hf2A hpart

end SliceFasCountGA
