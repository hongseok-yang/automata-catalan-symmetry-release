/-
# The fibred strict count (§9 tower, Stage F3.9)

The copied-slice twin of `SliceFasCountGA.strict_count_GA`: selected `U`-atoms whose
rank lex-precedes the fibred `d*`-rank.  Frozen + boundary cells are EP indicators
(`lexLt_EP_at` + `gateF_EP'`); bulk cells feed the PINNED bounded lex kernel
(`CopiedKernels.gatedLexConvolution_bounded`, with the slope-product divisibility
discharged from `dstar_setup_fibred_bounded`'s `mS`-free slope bound).  The pinned
period `p0 = p3 · ∏_c Qc` is machine-level, hoisted before `mS`.
-/
import RequestProject.CopiedRecount
import RequestProject.CopiedGateEP
import RequestProject.CopiedKernelsBounded
import RequestProject.CopiedDstarC
import RequestProject.CopiedSetupBound
import RequestProject.CopiedRegionF
import RequestProject.SliceFasCountGA

namespace CopiedCounts

open WRP Step SliceFamilyCell CopiedCells CopiedDstar CopiedRegionF CopiedRecount
  CopiedGateEP CopiedKernels CopiedSetup CopiedAffineAt MSOMarkN SliceMarkN
  SliceFasGatesGA SliceFasCountGA SliceDstarGA
open scoped Classical

set_option maxHeartbeats 1600000 in
/-- **The fibred strict count is affine-on-residues** (F3.9): selected `U`-atoms whose
rank lex-precedes the fibred `d*`-rank, on the copied slice. -/
theorem strict_count_fibred (P : WRP.Presentation Step Step) (hV : P.Valid) :
    ∃ p0 : ℕ, 1 ≤ p0 ∧ ∀ (C mS : ℕ), 1 ≤ mS →
      (∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ C * (mS + n + 1)) →
      ∃ (strict' : ℕ → ℕ) (N : ℕ), SlicePeriodStar.AffineOnResiduesAt p0 strict' ∧
        ∀ n, N ≤ n → P.toPoly.domain (copiedSlice mS n) →
          (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
            P.toPoly.labelOf (copiedSlice mS n) a = D) →
          strict' n = ∑ c : Fin P.toPoly.K,
            ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
              Finset.range (copiedSlice mS n).length),
            if (P.toPoly.sel c (copiedSlice mS n) ī
                ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
                ∧ WRP.lexLt (P.rankOf (copiedSlice mS n) ⟨c, ī⟩)
                    (CopiedDstar.dstarRankGA_m P hV mS n)) then 1 else 0 := by
  classical
  obtain ⟨pstar, hpstar, hdstarC⟩ := CopiedDstarC.dstarC_exists_fibred P hV
  obtain ⟨Z, hZ, hrecount⟩ := canonical_recount_fibred P
  obtain ⟨m, p, Mc, SPb, hp, hmB, hMc, hbwd, hsetupB⟩ :=
    CopiedSetup.dstar_setup_fibred_bounded P Z
  obtain ⟨m3, p3, Mc3, SP3, hp3, hm3B, hMc3, hbwd3, hsetupBh⟩ :=
    CopiedSetup.dstar_setup_fibred_bounded P (2 * Z)
  choose Uc hUc using fun c => selectedU_gate_GA P c
  choose mv pv hpv hEPc using fun c => bFN_func_iterate_eventuallyPeriodic (Uc c)
  have hpvpos : ∀ c, 0 < pv c := fun c => hpv c
  have hZ2 : Z ≤ 2 * Z := by omega
  have hZZ : Z + Z ≤ 2 * Z := by omega
  -- the per-class bulk-kernel period and the global hoisted period
  set Qc : Fin P.toPoly.K → ℕ := fun c =>
    (pstar * p) * (pv c * pv c * p)
      * Nat.factorial (∏ i : Fin P.d, max (pv c * pv c * SPb c i) 1) with hQcdef
  have hQcpos : ∀ c, 1 ≤ Qc c := by
    intro c
    rw [hQcdef]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hpstar hp)
      (Nat.mul_pos (Nat.mul_pos (hpvpos c) (hpvpos c)) hp)) (Nat.factorial_pos _)
  set p0 : ℕ := p3 * ∏ c : Fin P.toPoly.K, Qc c with hp0def
  have hp0 : 1 ≤ p0 := by
    rw [hp0def]
    exact Nat.mul_pos hp3 (Finset.prod_pos (fun c _ => hQcpos c))
  have hQcdvd : ∀ c, Qc c ∣ p0 := by
    intro c
    rw [hp0def]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ c)) _
  refine ⟨p0, hp0, fun C mS hm hbud => ?_⟩
  obtain ⟨dstarC, N0, hCaff, hCagree⟩ := hdstarC C mS hm hbud
  obtain ⟨Ncan, hrec⟩ := hrecount C mS hm hbud
  obtain ⟨Rcell, Bcell, PR, PBn, hwineq, hRrec, hBrec, hPRb, hPBnb⟩ := hsetupB mS hm
  obtain ⟨RcellH, BcellH, PRH, PBnH, hwineqH, hRrecH, hBrecH, hPRHb, hPBnHb⟩ :=
    hsetupBh mS hm
  -- the boundary re-freeze (front-zone) of a bulk descriptor
  set rfZ : (c : Fin P.toPoly.K) → (Fin (P.toPoly.arity c) → RegionSpecF Z) →
      (Fin (P.toPoly.arity c) → RegionSpecF (2 * Z)) :=
    fun c rs i => refreezeFrontF hZ2 Z hZZ (rs i) with hrfZdef
  set strict' : ℕ → ℕ := fun n =>
    ∑ c : Fin P.toPoly.K,
      ((∑ rs' ∈ frozenCellsF Z (P.toPoly.arity c) mS,
        if (gateF (Uc c) rs' mS (Z + 1) n
            ∧ WRP.lexLt (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) (dstarC n))
        then 1 else 0)
      + ∑ rs ∈ bulkCellsF Z hZ (P.toPoly.arity c) mS,
          (((Finset.range n).filter (fun t : ℕ =>
              WRP.lexLt (Rcell c rs t) (fun i => dstarC n i - Bcell c rs n i)
                ∧ min t (Z + 1) = Z + 1
                ∧ min (n - 1 - t) (Z + clusterWidth (coreSpec rs) - 1)
                    = Z + clusterWidth (coreSpec rs) - 1
                ∧ cellAcc (redM (Uc c) mS rs Z) (coreSpec rs)
                    ((bFN (Uc c))^[n - 1 - t + 1 - (Z + clusterWidth (coreSpec rs))]
                      (cellGclW (redM (Uc c) mS rs Z) (coreSpec rs)
                        ((bFN (Uc c))^[t - Z]
                          (cellQ0 (redM (Uc c) mS rs Z) (coreSpec rs))))))).card
            + (if (gateF (Uc c) rs mS Z n
                  ∧ WRP.lexLt (fun i => RcellH c (rfZ c rs) (2 * Z + 1) i
                      + BcellH c (rfZ c rs) n i) (dstarC n))
              then 1 else 0)))
    with hstrictdef
  have hpp : 1 ≤ pstar * p := Nat.mul_pos hpstar hp
  have hpstar_pp : pstar ∣ pstar * p := dvd_mul_right pstar p
  have hp_pp : p ∣ pstar * p := dvd_mul_left p pstar
  refine ⟨strict', Ncan + N0 + 4 * Z + 3, ?_, ?_⟩
  · -- affineness at p0
    rw [hstrictdef]
    refine SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hp0 (fun c _ => ?_)
    -- per-class divisibilities into p0
    have hpvc_p0 : pv c ∣ p0 :=
      dvd_trans (⟨pstar * p * pv c * p
            * Nat.factorial (∏ i : Fin P.d, max (pv c * pv c * SPb c i) 1),
          by rw [hQcdef]; ring⟩ : pv c ∣ Qc c) (hQcdvd c)
    have hp_p0 : p ∣ p0 :=
      dvd_trans (⟨pstar * (pv c * pv c * p)
            * Nat.factorial (∏ i : Fin P.d, max (pv c * pv c * SPb c i) 1),
          by rw [hQcdef]; ring⟩ : p ∣ Qc c) (hQcdvd c)
    have hpstar_p0 : pstar ∣ p0 :=
      dvd_trans (⟨p * (pv c * pv c * p)
            * Nat.factorial (∏ i : Fin P.d, max (pv c * pv c * SPb c i) 1),
          by rw [hQcdef]; ring⟩ : pstar ∣ Qc c) (hQcdvd c)
    have hp3_p0 : p3 ∣ p0 := ⟨∏ c : Fin P.toPoly.K, Qc c, hp0def⟩
    refine SlicePeriodStar.AffineOnResiduesAt.add hp0 ?_ ?_
    · -- frozen arm
      refine SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hp0 (fun rs' hrs' => ?_)
      have hvalid := ((mem_frozenCellsF rs').mp hrs').1
      have hgateEP : SliceOrder.EventuallyPeriodic
          (fun n => gateF (Uc c) rs' mS (Z + 1) n) p0 :=
        SliceDstar.EP_of_dvd (gateF_EP' (Uc c) (mv c) (pv c) (hpv c) (hEPc c)
          mS hm rs' hvalid (Z + 1) (by omega)) hpvc_p0
      have hlexEP : SliceOrder.EventuallyPeriodic
          (fun n => WRP.lexLt (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i)
            (dstarC n)) p0 := by
        refine lexLt_EP_at hp0 (fun i => ?_)
          (fun i => AffineOnResiduesAtZ.of_dvd hpstar hpstar_p0 hp0 (hCaff i))
        exact AffineOnResiduesAtZ.add hp0
          (AffineOnResiduesAtZ.const p0 (Rcell c rs' (Z + 1) i))
          (AffineOnResiduesAtZ.of_dvd hp hp_p0 hp0
            (AffineOnResiduesAtZ.of_recurrence (m := m) hp (fun nn hnn => by
              have hb := congrFun (hBrec c rs' nn hnn) i
              rw [Pi.add_apply] at hb
              exact hb)))
      exact affineOnResiduesAt_indicator_of_EP hp0 (hgateEP.and hlexEP)
    · -- bulk arm
      refine SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hp0 (fun rs hrs => ?_)
      have hvalid := ((mem_bulkCellsF hZ rs).mp hrs).1
      refine SlicePeriodStar.AffineOnResiduesAt.add hp0 ?_ ?_
      · -- the bounded lex kernel, lifted to p0
        have hker := CopiedKernels.gatedLexConvolution_bounded
          (u := fun t => ((bFN (Uc c))^[t - Z]
            (cellQ0 (redM (Uc c) mS rs Z) (coreSpec rs)), min t (Z + 1)))
          (v := fun mm => ((bFN (Uc c))^[mm + 1 - (Z + clusterWidth (coreSpec rs))],
            min mm (Z + clusterWidth (coreSpec rs) - 1)))
          (b := fun qf gf => qf.2 = Z + 1
            ∧ gf.2 = Z + clusterWidth (coreSpec rs) - 1
            ∧ cellAcc (redM (Uc c) mS rs Z) (coreSpec rs)
                (gf.1 (cellGclW (redM (Uc c) mS rs Z) (coreSpec rs) qf.1)))
          (mu := mv c + Z + Z + 1) (hpu := hpv c)
          (hu := by
            intro i hi
            rw [show i + pv c - Z = (i - Z) + pv c from by omega,
              congrFun (hEPc c (i - Z) (by omega))
                (cellQ0 (redM (Uc c) mS rs Z) (coreSpec rs)),
              show min (i + pv c) (Z + 1) = Z + 1 from by omega,
              show min i (Z + 1) = Z + 1 from by omega])
          (mv := mv c + 2 * Z + clusterWidth (coreSpec rs)) (hpv := hpv c)
          (hv := by
            intro j hj
            rw [show j + pv c + 1 - (Z + clusterWidth (coreSpec rs))
                = (j + 1 - (Z + clusterWidth (coreSpec rs))) + pv c from by omega,
              hEPc c (j + 1 - (Z + clusterWidth (coreSpec rs))) (by omega),
              show min (j + pv c) (Z + clusterWidth (coreSpec rs) - 1)
                = Z + clusterWidth (coreSpec rs) - 1 from by omega,
              show min j (Z + clusterWidth (coreSpec rs) - 1)
                = Z + clusterWidth (coreSpec rs) - 1 from by omega])
          (R := Rcell c rs) (PR := PR c rs) (hpR := hp)
          (hR := fun j hj => hRrec c rs j hj)
          (T := fun n => fun i => dstarC n i - Bcell c rs n i) (hP := hpp)
          (hT := fun i => (AffineOnResiduesAtZ.of_dvd hpstar hpstar_pp hpp (hCaff i)).sub
            hpp (AffineOnResiduesAtZ.of_dvd hp hp_pp hpp
              (AffineOnResiduesAtZ.of_recurrence (m := m) hp (fun nn hnn => by
                have hb := congrFun (hBrec c rs nn hnn) i
                rw [Pi.add_apply] at hb
                exact hb))))
          (SP := SPb c) (hPRb := hPRb c rs)
        refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => ?_)
          (hker.of_dvd (hQcpos c) (hQcdvd c) hp0)
        refine congrArg Finset.card ?_
        convert rfl
      · -- the boundary indicator at p0
        have hgateEP : SliceOrder.EventuallyPeriodic
            (fun n => gateF (Uc c) rs mS Z n) p0 :=
          SliceDstar.EP_of_dvd (gateF_EP' (Uc c) (mv c) (pv c) (hpv c) (hEPc c)
            mS hm rs hvalid Z (by omega)) hpvc_p0
        have hlexEP : SliceOrder.EventuallyPeriodic
            (fun n => WRP.lexLt (fun i => RcellH c (rfZ c rs) (2 * Z + 1) i
              + BcellH c (rfZ c rs) n i) (dstarC n)) p0 := by
          refine lexLt_EP_at hp0 (fun i => ?_)
            (fun i => AffineOnResiduesAtZ.of_dvd hpstar hpstar_p0 hp0 (hCaff i))
          exact AffineOnResiduesAtZ.add hp0
            (AffineOnResiduesAtZ.const p0 (RcellH c (rfZ c rs) (2 * Z + 1) i))
            (AffineOnResiduesAtZ.of_dvd hp3 hp3_p0 hp0
              (AffineOnResiduesAtZ.of_recurrence (m := m3) hp3 (fun nn hnn => by
                have hb := congrFun (hBrecH c (rfZ c rs) nn hnn) i
                rw [Pi.add_apply] at hb
                exact hb)))
        exact affineOnResiduesAt_indicator_of_EP hp0 (hgateEP.and hlexEP)
  · -- agreement
    intro n hn hdom hD
    have hagree : CopiedDstar.dstarRankGA_m P hV mS n = dstarC n :=
      hCagree n (by omega) hdom hD
    rw [hstrictdef]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    obtain ⟨QQ, hQQ⟩ : ∃ Q : (Fin (P.toPoly.arity c) → ℕ) → Prop,
        ∀ ī, Q ī ↔ (P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩
          ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
          ∧ WRP.lexLt (P.rankOf (copiedSlice mS n) ⟨c, ī⟩) (dstarC n)) :=
      ⟨_, fun ī => Iff.rfl⟩
    have hQsel : ∀ ī, QQ ī → P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ := by
      intro ī h; rw [hQQ ī] at h; exact h.1
    have hQiff : ∀ ī, (∀ i, ī i < (copiedSlice mS n).length) →
        (QQ ī ↔ (P.toPoly.sel c (copiedSlice mS n) ī
          ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
          ∧ WRP.lexLt (P.rankOf (copiedSlice mS n) ⟨c, ī⟩)
              (CopiedDstar.dstarRankGA_m P hV mS n))) := by
      intro ī hval
      rw [hQQ ī, hagree]
      exact ⟨fun ⟨hs, hl, hr⟩ => ⟨hs.2, hl, hr⟩, fun ⟨hs, hl, hr⟩ => ⟨⟨hval, hs⟩, hl, hr⟩⟩
    have hrec' := hrec n (by omega) hdom c QQ hQsel
    refine Eq.trans (Eq.trans ?_ hrec'.symm) ?_
    · -- strict' c-arm = recount RHS (frozen at Z+1 + bulk Icc)
      congr 1
      · -- frozen arm
        refine Finset.sum_congr rfl (fun rs' hrs' => ?_)
        have hvalid := ((mem_frozenCellsF rs').mp hrs').1
        have hval := cellTupleF_valid rs' mS (Z + 1) n hm hvalid (by omega)
        have hrank : P.rankOf (copiedSlice mS n) ⟨c, cellTupleF rs' mS (Z + 1) n⟩
            = fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i :=
          hwineq c rs' hvalid (Z + 1) n (by omega) (by omega)
        have hiff : ((gateF (Uc c) rs' mS (Z + 1) n
              ∧ WRP.lexLt (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) (dstarC n))
            ↔ QQ (cellTupleF rs' mS (Z + 1) n)) := by
          rw [hQQ _, gateF, hUc c (copiedSlice mS n) _ hval, hrank]
          exact ⟨fun ⟨⟨hs, hl⟩, hr⟩ => ⟨⟨hval, hs⟩, hl, hr⟩,
            fun ⟨hs, hl, hr⟩ => ⟨⟨hs.2, hl⟩, hr⟩⟩
        by_cases h : (gateF (Uc c) rs' mS (Z + 1) n
            ∧ WRP.lexLt (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) (dstarC n))
        · rw [if_pos h, if_pos (hiff.mp h)]
        · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
      · -- bulk arm
        refine Finset.sum_congr rfl (fun rs hrs => ?_)
        have hvalid := ((mem_bulkCellsF hZ rs).mp hrs).1
        have hwit := ((mem_bulkCellsF hZ rs).mp hrs).2
        have hWFpos : 1 ≤ clusterWidthF rs := by
          obtain ⟨i, e, hi⟩ := hwit
          have := cluster_lt_widthF rs i ⟨0, hZ⟩ e hi
          omega
        have hWeq : clusterWidthF rs = clusterWidth (coreSpec rs) :=
          clusterWidthF_eq_coreSpec rs
        have hWpos : 1 ≤ clusterWidth (coreSpec rs) := by rw [← hWeq]; exact hWFpos
        have hWZ : clusterWidth (coreSpec rs) ≤ Z := clusterWidth_le (coreSpec rs)
        have hiffT : ∀ t : ℕ, (t < n
              ∧ (WRP.lexLt (Rcell c rs t) (fun i => dstarC n i - Bcell c rs n i)
                ∧ min t (Z + 1) = Z + 1
                ∧ min (n - 1 - t) (Z + clusterWidth (coreSpec rs) - 1)
                    = Z + clusterWidth (coreSpec rs) - 1
                ∧ cellAcc (redM (Uc c) mS rs Z) (coreSpec rs)
                    ((bFN (Uc c))^[n - 1 - t + 1 - (Z + clusterWidth (coreSpec rs))]
                      (cellGclW (redM (Uc c) mS rs Z) (coreSpec rs)
                        ((bFN (Uc c))^[t - Z]
                          (cellQ0 (redM (Uc c) mS rs Z) (coreSpec rs)))))))
            ↔ ((Z + 1 ≤ t ∧ t ≤ n - Z - clusterWidth (coreSpec rs))
                ∧ QQ (cellTupleF rs mS t n)) := by
          intro t
          constructor
          · rintro ⟨htn', hlex, hfl, hfr, hbit⟩
            have htlo : Z + 1 ≤ t := by omega
            have hthi : t ≤ n - Z - clusterWidth (coreSpec rs) := by omega
            have hval := cellTupleF_valid rs mS t n hm hvalid (by omega)
            have hacc : (Uc c).accepts
                (markAtN _ (copiedSlice mS n) (cellTupleF rs mS t n)) := by
              rw [acceptsF_cellTuple_convW (Uc c) mS hm rs hvalid t n (by omega) (by omega),
                show n - Z - clusterWidth (coreSpec rs) - t
                  = n - 1 - t + 1 - (Z + clusterWidth (coreSpec rs)) from by omega]
              exact hbit
            rw [hUc c (copiedSlice mS n) _ hval] at hacc
            have hrank : P.rankOf (copiedSlice mS n) ⟨c, cellTupleF rs mS t n⟩
                = fun i => Rcell c rs t i + Bcell c rs n i :=
              hwineq c rs hvalid t n (by omega) (by omega)
            refine ⟨⟨htlo, hthi⟩, ?_⟩
            rw [hQQ _, hrank]
            exact ⟨⟨hval, hacc.1⟩, hacc.2, (lexLt_sub_right _ _ _).mpr hlex⟩
          · rintro ⟨⟨htlo, hthi⟩, hQ⟩
            have hval := cellTupleF_valid rs mS t n hm hvalid (by omega)
            have hrank : P.rankOf (copiedSlice mS n) ⟨c, cellTupleF rs mS t n⟩
                = fun i => Rcell c rs t i + Bcell c rs n i :=
              hwineq c rs hvalid t n (by omega) (by omega)
            rw [hQQ _, hrank] at hQ
            obtain ⟨hsel, hlab, hlex⟩ := hQ
            refine ⟨by omega, (lexLt_sub_right _ _ _).mp hlex, by omega, by omega, ?_⟩
            have hacc : (Uc c).accepts
                (markAtN _ (copiedSlice mS n) (cellTupleF rs mS t n)) := by
              rw [hUc c (copiedSlice mS n) _ hval]; exact ⟨hsel.2, hlab⟩
            rw [acceptsF_cellTuple_convW (Uc c) mS hm rs hvalid t n (by omega) (by omega)] at hacc
            rwa [show n - 1 - t + 1 - (Z + clusterWidth (coreSpec rs))
              = n - Z - clusterWidth (coreSpec rs) - t from by omega]
        have hbdiff : ((gateF (Uc c) rs mS Z n
              ∧ WRP.lexLt (fun i => RcellH c (rfZ c rs) (2 * Z + 1) i
                  + BcellH c (rfZ c rs) n i) (dstarC n))
            ↔ QQ (cellTupleF rs mS Z n)) := by
          have hvalZ := cellTupleF_valid rs mS Z n hm hvalid (by omega)
          have hrfv : ∀ i, (rfZ c rs i).valid mS := fun i =>
            refreezeFrontF_valid hZ2 Z hZZ (rs i) mS (hvalid i)
          have hcell : cellTupleF rs mS Z n = cellTupleF (rfZ c rs) mS (2 * Z + 1) n := by
            funext i
            rw [hrfZdef]
            exact (refreezeFrontF_posAt hZ2 Z hZZ (rs i) mS (2 * Z + 1) n).symm
          have hrk : P.rankOf (copiedSlice mS n) ⟨c, cellTupleF rs mS Z n⟩
              = fun i => RcellH c (rfZ c rs) (2 * Z + 1) i
                + BcellH c (rfZ c rs) n i := by
            show P.rank c (copiedSlice mS n) (cellTupleF rs mS Z n) = _
            rw [hcell]
            exact hwineqH c (rfZ c rs) hrfv (2 * Z + 1) n (by omega) (by omega)
          rw [hQQ _, gateF, hUc c (copiedSlice mS n) _ hvalZ, hrk]
          exact ⟨fun ⟨⟨hs, hl⟩, hr⟩ => ⟨⟨hvalZ, hs⟩, hl, hr⟩,
            fun ⟨hs, hl, hr⟩ => ⟨⟨hs.2, hl⟩, hr⟩⟩
        rw [hWeq]
        conv_rhs => rw [← Finset.card_filter_add_card_filter_not
          (s := (Finset.Icc Z (n - Z - clusterWidth (coreSpec rs))).filter
            (fun t => QQ (cellTupleF rs mS t n))) (p := fun t => t = Z)]
        conv_rhs => rw [Nat.add_comm]
        congr 1
        · -- kernel = the non-boundary part
          symm
          refine congrArg Finset.card ?_
          refine Finset.ext (fun t => ?_)
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
          constructor
          · rintro ⟨⟨⟨htlo, hthi⟩, hQ⟩, htne⟩
            exact (hiffT t).mpr ⟨⟨by omega, hthi⟩, hQ⟩
          · intro h
            have hh := (hiffT t).mp h
            have hlo := hh.1.1
            exact ⟨⟨⟨by omega, hh.1.2⟩, hh.2⟩, by omega⟩
        · -- boundary indicator = the boundary part
          by_cases hQZ : QQ (cellTupleF rs mS Z n)
          · rw [if_pos (hbdiff.mpr hQZ)]
            symm
            refine Finset.card_eq_one.mpr ⟨Z, ?_⟩
            refine Finset.ext (fun t => ?_)
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc,
              Finset.mem_singleton]
            constructor
            · rintro ⟨-, ht⟩; exact ht
            · rintro rfl; exact ⟨⟨⟨by omega, by omega⟩, hQZ⟩, rfl⟩
          · rw [if_neg (fun hc => hQZ (hbdiff.mp hc))]
            symm
            rw [Finset.card_eq_zero]
            refine Finset.eq_empty_of_forall_notMem (fun t ht => ?_)
            rw [Finset.mem_filter, Finset.mem_filter] at ht
            obtain ⟨⟨-, hQ⟩, ht⟩ := ht
            subst ht
            exact hQZ hQ
    · -- ∑ if QQ = the target sel/label/lex sum
      refine Finset.sum_congr rfl (fun ī hī => ?_)
      have hval : ∀ i, ī i < (copiedSlice mS n).length := by
        rw [Fintype.mem_piFinset] at hī
        intro i; have := hī i; rwa [Finset.mem_range] at this
      by_cases h : QQ ī
      · rw [if_pos h, if_pos ((hQiff ī hval).mp h)]
      · rw [if_neg h, if_neg (fun hc => h ((hQiff ī hval).mpr hc))]

end CopiedCounts
