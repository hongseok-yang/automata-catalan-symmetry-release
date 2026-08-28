/-
# The three fibred counts (§9 tower, Stage F3.9)

The copied-slice (fibred) twins of `SliceFasCountGA.{totalSelectedU,strict,tie}_count_GA`.
Frozen cells are eventually-periodic indicators (`gateF_EP'`); bulk cells feed the
PINNED fibred convolution kernels (`CopiedKernels.gated{,Lex,Eq}Convolution_at`)
through the fibred cell-tuple convolution form (`CopiedGateEP.acceptsF_cellTuple_convW`).
The recount backbone is `CopiedRecount.canonical_recount_fibred` (F3.8).  Each count
concludes `SlicePeriodStar.AffineOnResiduesAt p0` with `p0` HOISTED before `mS`
(machine-level), so the F3.10 assembly's `(domain, D-present)` select and final
partition stay at one shared pinned period.

This file currently lands `totalSelectedU_count_fibred` (the pipeline shakedown,
no rank / no `D`-presence).
-/
import RequestProject.CopiedRecount
import RequestProject.CopiedGateEP
import RequestProject.CopiedKernels
import RequestProject.CopiedTieBridge

namespace CopiedCounts

open WRP Step SliceFamilyCell CopiedCells CopiedDstar CopiedRegionF CopiedRecount
  CopiedGateEP CopiedKernels MSOMarkN SliceMarkN SliceFasGatesGA SliceFasCountGA
open scoped Classical

set_option maxHeartbeats 1600000 in
/-- **The total selected-`U` count is affine-on-residues** (fibred, F3.9 shakedown):
the kernel pipeline on the copied slice — frozen cells are EP indicators, bulk cells
feed the pinned gated convolution through the fibred cell-tuple convolution form.  The
pinned period `p0 = ∏_c (pv c)^4` is machine-level (the `selectedU` gates' `bFN`
periods), hoisted before `mS`. -/
theorem totalSelectedU_count_fibred (P : WRP.Presentation Step Step) :
    ∃ p0 : ℕ, 1 ≤ p0 ∧ ∀ (C mS : ℕ), 1 ≤ mS →
      (∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ C * (mS + n + 1)) →
      ∃ (tot' : ℕ → ℕ) (N : ℕ), SlicePeriodStar.AffineOnResiduesAt p0 tot' ∧
        ∀ n, N ≤ n → P.toPoly.domain (copiedSlice mS n) →
          tot' n = ∑ c : Fin P.toPoly.K,
            ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
              Finset.range (copiedSlice mS n).length),
            if (P.toPoly.sel c (copiedSlice mS n) ī
                ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U) then 1 else 0 := by
  classical
  obtain ⟨Z, hZ, hrecount⟩ := canonical_recount_fibred P
  choose Uc hUc using fun c => selectedU_gate_GA P c
  choose mv pv hpv hEPc using fun c => bFN_func_iterate_eventuallyPeriodic (Uc c)
  have hpvpos : ∀ c, 0 < pv c := fun c => hpv c
  set p0 : ℕ := ∏ c : Fin P.toPoly.K, (pv c) ^ 4 with hp0def
  have hp0 : 1 ≤ p0 := by
    rw [hp0def]; exact Finset.prod_pos (fun c _ => pow_pos (hpvpos c) 4)
  have hdvdc : ∀ c, (pv c) ^ 4 ∣ p0 := by
    intro c; rw [hp0def]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
  refine ⟨p0, hp0, fun C mS hm hbud => ?_⟩
  obtain ⟨Ncan, hrec⟩ := hrecount C mS hm hbud
  set tot' : ℕ → ℕ := fun n =>
    ∑ c : Fin P.toPoly.K,
      ((∑ rs' ∈ frozenCellsF Z (P.toPoly.arity c) mS,
        if gateF (Uc c) rs' mS (Z + 1) n then 1 else 0)
      + ∑ rs ∈ bulkCellsF Z hZ (P.toPoly.arity c) mS,
          ((Finset.range n).filter (fun t : ℕ =>
            (Z : ℤ) ≤ (t : ℤ)
              ∧ (t : ℤ) < (n : ℤ) - Z - clusterWidth (coreSpec rs) + 1
              ∧ cellAcc (redM (Uc c) mS rs Z) (coreSpec rs)
                  ((bFN (Uc c))^[n - 1 - t + 1 - (Z + clusterWidth (coreSpec rs))]
                    (cellGclW (redM (Uc c) mS rs Z) (coreSpec rs)
                      ((bFN (Uc c))^[t - Z]
                        (cellQ0 (redM (Uc c) mS rs Z) (coreSpec rs))))))).card)
    with htotdef
  refine ⟨tot', Ncan + 2 * Z + 2, ?_, ?_⟩
  · -- affineness at p0
    rw [htotdef]
    refine SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hp0 (fun c _ => ?_)
    have hpvc4 : (1 : ℕ) ≤ (pv c) ^ 4 := pow_pos (hpvpos c) 4
    refine (SlicePeriodStar.AffineOnResiduesAt.add hpvc4 ?_ ?_).of_dvd hpvc4 (hdvdc c) hp0
    · -- frozen arm
      refine SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hpvc4 (fun rs' hrs' => ?_)
      have hvalid := ((mem_frozenCellsF rs').mp hrs').1
      have hEP : SliceOrder.EventuallyPeriodic (fun n => gateF (Uc c) rs' mS (Z + 1) n)
          (pv c) := gateF_EP' (Uc c) (mv c) (pv c) (hpv c) (hEPc c) mS hm rs' hvalid
          (Z + 1) (by omega)
      exact (CopiedAffineAt.affineOnResiduesAt_indicator_of_EP (hpv c) hEP).of_dvd
        (hpv c) (dvd_pow_self (pv c) (by norm_num)) hpvc4
    · -- bulk arm
      refine SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hpvc4 (fun rs hrs => ?_)
      have hker := CopiedKernels.gatedConvolution_at
        (u := fun t => (bFN (Uc c))^[t - Z]
          (cellQ0 (redM (Uc c) mS rs Z) (coreSpec rs)))
        (v := fun m => (bFN (Uc c))^[m + 1 - (Z + clusterWidth (coreSpec rs))])
        (b := fun q g => cellAcc (redM (Uc c) mS rs Z) (coreSpec rs)
          (g (cellGclW (redM (Uc c) mS rs Z) (coreSpec rs) q)))
        (mu := mv c + Z) (pu := pv c) (hpu := hpv c)
        (mv := mv c + Z + clusterWidth (coreSpec rs)) (pv := pv c) (hpv := hpv c)
        (P := (pv c) ^ 2) (hP := pow_pos (hpvpos c) 2)
        (hdvd := dvd_of_eq (pow_two (pv c)).symm)
        (lo := fun _ => (Z : ℤ))
        (hi := fun n => (n : ℤ) - Z - clusterWidth (coreSpec rs) + 1)
        (hlo := CopiedAffineAt.AffineOnResiduesAtZ.const _ (Z : ℤ))
        (hhi := ?hhi) ?hu ?hv
      · have heq : (pv c) ^ 2 * (pv c * pv c) = (pv c) ^ 4 := by ring
        rw [heq] at hker; exact hker
      case hhi =>
        have hid : CopiedAffineAt.AffineOnResiduesAtZ ((pv c) ^ 2) (fun n => (n : ℤ)) :=
          ⟨0, fun j _ => ⟨(j : ℤ), ((pv c) ^ 2 : ℤ), fun k => by push_cast; ring⟩⟩
        exact ((hid.sub (pow_pos (hpvpos c) 2)
            (CopiedAffineAt.AffineOnResiduesAtZ.const _ _)).sub (pow_pos (hpvpos c) 2)
          (CopiedAffineAt.AffineOnResiduesAtZ.const _ _)).add (pow_pos (hpvpos c) 2)
          (CopiedAffineAt.AffineOnResiduesAtZ.const _ (1 : ℤ))
      case hu =>
        intro i hi
        rw [show i + pv c - Z = (i - Z) + pv c from by omega]
        exact congrFun (hEPc c (i - Z) (by omega)) _
      case hv =>
        intro j hj
        rw [show j + pv c + 1 - (Z + clusterWidth (coreSpec rs))
          = (j + 1 - (Z + clusterWidth (coreSpec rs))) + pv c from by omega]
        exact hEPc c (j + 1 - (Z + clusterWidth (coreSpec rs))) (by omega)
  · -- agreement
    intro n hn hdom
    rw [htotdef]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    set QQ : (Fin (P.toPoly.arity c) → ℕ) → Prop := fun ī =>
      P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩
        ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U with hQQdef
    have hQsel : ∀ ī, QQ ī → P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ :=
      fun ī h => h.1
    have hQiff : ∀ ī, (∀ i, ī i < (copiedSlice mS n).length) →
        (QQ ī ↔ (P.toPoly.sel c (copiedSlice mS n) ī
          ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U)) := by
      intro ī hval
      constructor
      · rintro ⟨hs, hl⟩; exact ⟨hs.2, hl⟩
      · rintro ⟨hs, hl⟩; exact ⟨⟨hval, hs⟩, hl⟩
    have hrecc := hrec n (by omega) hdom c QQ hQsel
    refine Eq.trans (Eq.trans ?_ hrecc.symm) ?_
    case refine_2 =>
      refine Finset.sum_congr rfl (fun ī hī => ?_)
      have hval : ∀ i, ī i < (copiedSlice mS n).length := by
        rw [Fintype.mem_piFinset] at hī
        intro i; have := hī i; rwa [Finset.mem_range] at this
      by_cases h : QQ ī
      · rw [if_pos h, if_pos ((hQiff ī hval).mp h)]
      · rw [if_neg h, if_neg (fun hc => h ((hQiff ī hval).mpr hc))]
    -- kernel-form arm equals the QQ-form recount arm
    have h2 : (∑ rs' ∈ frozenCellsF Z (P.toPoly.arity c) mS,
          if gateF (Uc c) rs' mS (Z + 1) n then 1 else 0)
        + (∑ rs ∈ bulkCellsF Z hZ (P.toPoly.arity c) mS,
            ((Finset.range n).filter (fun t : ℕ =>
              (Z : ℤ) ≤ (t : ℤ)
                ∧ (t : ℤ) < (n : ℤ) - Z - clusterWidth (coreSpec rs) + 1
                ∧ cellAcc (redM (Uc c) mS rs Z) (coreSpec rs)
                    ((bFN (Uc c))^[n - 1 - t + 1 - (Z + clusterWidth (coreSpec rs))]
                      (cellGclW (redM (Uc c) mS rs Z) (coreSpec rs)
                        ((bFN (Uc c))^[t - Z]
                          (cellQ0 (redM (Uc c) mS rs Z) (coreSpec rs))))))).card)
        = (∑ rs' ∈ frozenCellsF Z (P.toPoly.arity c) mS,
            if QQ (cellTupleF rs' mS (Z + 1) n) then 1 else 0)
          + ∑ rs ∈ bulkCellsF Z hZ (P.toPoly.arity c) mS,
              ((Finset.Icc Z (n - Z - clusterWidthF rs)).filter
                (fun t => QQ (cellTupleF rs mS t n))).card := by
      congr 1
      · -- frozen arm
        refine Finset.sum_congr rfl (fun rs' hrs' => ?_)
        have hvalid := ((mem_frozenCellsF rs').mp hrs').1
        have hval := cellTupleF_valid rs' mS (Z + 1) n hm hvalid (by omega)
        have hiff : (gateF (Uc c) rs' mS (Z + 1) n ↔ QQ (cellTupleF rs' mS (Z + 1) n)) := by
          rw [gateF, hUc c (copiedSlice mS n) _ hval]
          exact ((hQiff _ hval).trans Iff.rfl).symm
        by_cases h : gateF (Uc c) rs' mS (Z + 1) n
        · rw [if_pos h, if_pos (hiff.mp h)]
        · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
      · -- bulk arm: the filter sets coincide
        refine Finset.sum_congr rfl (fun rs hrs => ?_)
        congr 1
        refine Finset.ext (fun t => ?_)
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
        have hvalid := ((mem_bulkCellsF hZ rs).mp hrs).1
        have hwit := ((mem_bulkCellsF hZ rs).mp hrs).2
        have hWFpos : 1 ≤ clusterWidthF rs := by
          obtain ⟨i, e, hi⟩ := hwit
          have := cluster_lt_widthF rs i ⟨0, hZ⟩ e hi
          omega
        have hWeq : clusterWidthF rs = clusterWidth (coreSpec rs) :=
          clusterWidthF_eq_coreSpec rs
        have hWpos : 1 ≤ clusterWidth (coreSpec rs) := by rw [← hWeq]; exact hWFpos
        constructor
        · rintro ⟨htn', htZ, htub, hbit⟩
          have htZ' : Z ≤ t := by exact_mod_cast htZ
          have hwin : t + clusterWidth (coreSpec rs) + Z ≤ n := by omega
          have hval := cellTupleF_valid rs mS t n hm hvalid (by omega)
          have hacc : (Uc c).accepts (markAtN _ (copiedSlice mS n)
              (cellTupleF rs mS t n)) := by
            rw [acceptsF_cellTuple_convW (Uc c) mS hm rs hvalid t n htZ' (by omega),
              show n - Z - clusterWidth (coreSpec rs) - t
                = n - 1 - t + 1 - (Z + clusterWidth (coreSpec rs)) from by omega]
            exact hbit
          rw [hUc c (copiedSlice mS n) _ hval] at hacc
          exact ⟨⟨htZ', by omega⟩, (hQiff _ hval).mpr hacc⟩
        · rintro ⟨⟨htZ, htn⟩, hQ⟩
          have hwin : t + clusterWidth (coreSpec rs) + Z ≤ n := by rw [hWeq] at htn; omega
          have hval := cellTupleF_valid rs mS t n hm hvalid (by omega)
          refine ⟨by omega, by exact_mod_cast htZ, by omega, ?_⟩
          have hacc : (Uc c).accepts (markAtN _ (copiedSlice mS n)
              (cellTupleF rs mS t n)) := by
            rw [hUc c (copiedSlice mS n) _ hval]
            exact (hQiff _ hval).mp hQ
          rw [acceptsF_cellTuple_convW (Uc c) mS hm rs hvalid t n htZ (by omega)] at hacc
          rwa [show n - 1 - t + 1 - (Z + clusterWidth (coreSpec rs))
            = n - Z - clusterWidth (coreSpec rs) - t from by omega]
    refine h2.trans ?_
    congr 1
    · refine Finset.sum_congr rfl (fun rs' _ => ?_)
      by_cases h : QQ (cellTupleF rs' mS (Z + 1) n)
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
    · refine Finset.sum_congr rfl (fun rs _ => ?_)
      refine congrArg Finset.card ?_
      convert rfl

end CopiedCounts
