/-
# The fibred tie count, parameterized by a folded per-class gate (§9 tower, F3.9)

The copied-slice twin of `SliceFasCountGA.tie_count_GA`: selected `U`-atoms of `d*`-rank
that `atomOrd`-precede every equal-rank selected `D`-atom.  This file lands the MECHANICAL
80% — `tie_count_fibred_of_gate` and its budgeted finite-index variant — which take a folded
gate hypothesis and produce the affine tie count.  Structure = `strict_count_fibred` with
`lexLt → (= )` (`gatedEqConvolution_bounded`, `vec_eq_EP_at`, `vec_eq_sub_right`) PLUS the
per-class `AffineOnResiduesAt.select` fold over `n % p0` (mirroring `tie_count_GA`).  The
budgeted capstone consumes `CopiedTieSlice.tie_point_bridge_fibred_clause_budgeted_indexed`,
whose finite row index is chosen after the row and budget proof are known.
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
/-- **The fibred tie count, from a folded per-class gate** (F3.9, the mechanical 80%):
given a gate family `GdfaF` (indexed by `(mS % qM, n % pG)`) whose acceptance characterizes the
TIE membership, the tie count is affine-on-residues at an `mS`-FREE pinned period.  Mirrors
`strict_count_fibred` (frozen/bulk/boundary skeleton) with `lexLt → (=)` and a per-class
`select` fold over `n % p0`. -/
theorem tie_count_fibred_of_gate (P : WRP.Presentation Step Step) (hV : P.Valid)
    (qM pG : ℕ) (hqM : 1 ≤ qM) (hpG : 1 ≤ pG)
    (GdfaF : ℕ → ℕ → (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (Mbr : ℕ) (hMbr1 : 1 ≤ Mbr)
    (hbr : ∀ (mS : ℕ), Mbr ≤ mS → ∃ Nbr, ∀ n, Nbr ≤ n → P.toPoly.domain (copiedSlice mS n) →
      (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
        P.toPoly.labelOf (copiedSlice mS n) a = D) →
      ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
        (∀ i, ī i < (copiedSlice mS n).length) →
        ((P.toPoly.sel c (copiedSlice mS n) ī
            ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
            ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ = CopiedDstar.dstarRankGA_m P hV mS n
            ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
                P.toPoly.labelOf (copiedSlice mS n) b = D →
                P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
                P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
         ↔ ((GdfaF (mS % qM) (n % pG) c).accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)
            ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩
                = CopiedDstar.dstarRankGA_m P hV mS n))) :
    ∃ p0 : ℕ, 1 ≤ p0 ∧ ∀ (C mS : ℕ), Mbr ≤ mS →
      (∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ C * (mS + n + 1)) →
      ∃ (tie' : ℕ → ℕ) (N : ℕ), SlicePeriodStar.AffineOnResiduesAt p0 tie' ∧
        ∀ n, N ≤ n → P.toPoly.domain (copiedSlice mS n) →
          (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
            P.toPoly.labelOf (copiedSlice mS n) a = D) →
          tie' n = ∑ c : Fin P.toPoly.K,
            ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
              Finset.range (copiedSlice mS n).length),
            if (P.toPoly.sel c (copiedSlice mS n) ī
                ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
                ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩
                    = CopiedDstar.dstarRankGA_m P hV mS n
                ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
                    P.toPoly.labelOf (copiedSlice mS n) b = D →
                    P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
                    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b) then 1 else 0 := by
  classical
  obtain ⟨pstar, hpstar, hdstarC⟩ := CopiedDstarC.dstarC_exists_fibred P hV
  obtain ⟨Z, hZ, hrecount⟩ := canonical_recount_fibred P
  obtain ⟨m, p, Mc, SPb, hp, hmB, hMc, hbwd, hsetupB⟩ :=
    CopiedSetup.dstar_setup_fibred_bounded P Z
  obtain ⟨m3, p3, Mc3, SP3, hp3, hm3B, hMc3, hbwd3, hsetupBh⟩ :=
    CopiedSetup.dstar_setup_fibred_bounded P (2 * Z)
  choose mvG pvG hpvG hEPG using
    fun (r : ℕ) (j : ℕ) (c : Fin P.toPoly.K) => bFN_func_iterate_eventuallyPeriodic (GdfaF r j c)
  have hpvGpos : ∀ r j c, 0 < pvG r j c := fun r j c => hpvG r j c
  have hZ2 : Z ≤ 2 * Z := by omega
  have hZZ : Z + Z ≤ 2 * Z := by omega
  -- per-(r,j,c) bulk-kernel period and the global hoisted period (r = mS % qM)
  set Qc : ℕ → ℕ → Fin P.toPoly.K → ℕ := fun r j c =>
    (pstar * p) * (pvG r j c * pvG r j c * p)
      * Nat.factorial (∏ i : Fin P.d, max (pvG r j c * pvG r j c * SPb c i) 1) with hQcdef
  have hQcpos : ∀ r j c, 1 ≤ Qc r j c := by
    intro r j c
    rw [hQcdef]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hpstar hp)
      (Nat.mul_pos (Nat.mul_pos (hpvGpos r j c) (hpvGpos r j c)) hp)) (Nat.factorial_pos _)
  set p0 : ℕ := p3 * pG
      * (∏ r ∈ Finset.range qM, ∏ j ∈ Finset.range pG, ∏ c : Fin P.toPoly.K, Qc r j c)
    with hp0def
  have hp0 : 1 ≤ p0 := by
    rw [hp0def]
    exact Nat.mul_pos (Nat.mul_pos hp3 hpG)
      (Finset.prod_pos (fun r _ => Finset.prod_pos (fun j _ =>
        Finset.prod_pos (fun c _ => hQcpos r j c))))
  have hQQdvd : (∏ r ∈ Finset.range qM, ∏ j ∈ Finset.range pG,
      ∏ c : Fin P.toPoly.K, Qc r j c) ∣ p0 := by
    rw [hp0def]; exact dvd_mul_left _ (p3 * pG)
  have hp3_p0 : p3 ∣ p0 := ⟨pG * ∏ r ∈ Finset.range qM, ∏ j ∈ Finset.range pG,
      ∏ c : Fin P.toPoly.K, Qc r j c, by rw [hp0def]; ring⟩
  have hpG_p0 : pG ∣ p0 := ⟨p3 * ∏ r ∈ Finset.range qM, ∏ j ∈ Finset.range pG,
      ∏ c : Fin P.toPoly.K, Qc r j c, by rw [hp0def]; ring⟩
  have hpp : 1 ≤ pstar * p := Nat.mul_pos hpstar hp
  have hpstar_pp : pstar ∣ pstar * p := dvd_mul_right pstar p
  have hp_pp : p ∣ pstar * p := dvd_mul_left p pstar
  refine ⟨p0, hp0, fun C mS hmS hbud => ?_⟩
  have hm : 1 ≤ mS := le_trans hMbr1 hmS
  -- per-mS tie-bridge threshold `Nbr` (the n-leg threshold grows linearly in mS; harmless,
  -- absorbed into the per-mS output `N` below)
  obtain ⟨Nbr, hbrn⟩ := hbr mS hmS
  obtain ⟨dstarC, N0, hCaff, hCagree⟩ := hdstarC C mS hm hbud
  obtain ⟨Ncan, hrec⟩ := hrecount C mS hm hbud
  obtain ⟨Rcell, Bcell, PR, PBn, hwineq, hRrec, hBrec, hPRb, hPBnb⟩ := hsetupB mS hm
  obtain ⟨RcellH, BcellH, PRH, PBnH, hwineqH, hRrecH, hBrecH, hPRHb, hPBnHb⟩ :=
    hsetupBh mS hm
  set rfZ : (c : Fin P.toPoly.K) → (Fin (P.toPoly.arity c) → RegionSpecF Z) →
      (Fin (P.toPoly.arity c) → RegionSpecF (2 * Z)) :=
    fun c rs i => refreezeFrontF hZ2 Z hZZ (rs i) with hrfZdef
  -- the per-class tie kernel
  set tieKer : ℕ → ℕ → ℕ := fun κ n =>
    ∑ c : Fin P.toPoly.K,
      ((∑ rs' ∈ frozenCellsF Z (P.toPoly.arity c) mS,
        if (gateF (GdfaF (mS % qM) (κ % pG) c) rs' mS (Z + 1) n
            ∧ (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) = dstarC n)
        then 1 else 0)
      + ∑ rs ∈ bulkCellsF Z hZ (P.toPoly.arity c) mS,
          (((Finset.range n).filter (fun t : ℕ =>
              Rcell c rs t = (fun i => dstarC n i - Bcell c rs n i)
                ∧ min t (Z + 1) = Z + 1
                ∧ min (n - 1 - t) (Z + clusterWidth (coreSpec rs) - 1)
                    = Z + clusterWidth (coreSpec rs) - 1
                ∧ cellAcc (redM (GdfaF (mS % qM) (κ % pG) c) mS rs Z) (coreSpec rs)
                    ((bFN (GdfaF (mS % qM) (κ % pG) c))^[n - 1 - t + 1
                        - (Z + clusterWidth (coreSpec rs))]
                      (cellGclW (redM (GdfaF (mS % qM) (κ % pG) c) mS rs Z) (coreSpec rs)
                        ((bFN (GdfaF (mS % qM) (κ % pG) c))^[t - Z]
                          (cellQ0 (redM (GdfaF (mS % qM) (κ % pG) c) mS rs Z)
                            (coreSpec rs))))))).card
            + (if (gateF (GdfaF (mS % qM) (κ % pG) c) rs mS Z n
                  ∧ (fun i => RcellH c (rfZ c rs) (2 * Z + 1) i
                      + BcellH c (rfZ c rs) n i) = dstarC n)
              then 1 else 0)))
    with htieKdef
  -- the per-class affineness at p0 (gate fixed at j = κ % pG)
  have htieAff : ∀ κ, SlicePeriodStar.AffineOnResiduesAt p0 (tieKer κ) := by
    intro κ
    have hjlt : κ % pG < pG := Nat.mod_lt κ hpG
    simp only [htieKdef]
    refine SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hp0 (fun c _ => ?_)
    have hrlt : mS % qM < qM := Nat.mod_lt mS hqM
    have hQcjdvd : Qc (mS % qM) (κ % pG) c ∣ p0 :=
      dvd_trans (dvd_trans (dvd_trans
        (Finset.dvd_prod_of_mem (fun c' => Qc (mS % qM) (κ % pG) c') (Finset.mem_univ c))
        (Finset.dvd_prod_of_mem (fun j => ∏ c' : Fin P.toPoly.K, Qc (mS % qM) j c')
          (Finset.mem_range.mpr hjlt)))
        (Finset.dvd_prod_of_mem
          (fun r => ∏ j ∈ Finset.range pG, ∏ c' : Fin P.toPoly.K, Qc r j c')
          (Finset.mem_range.mpr hrlt))) hQQdvd
    have hpvGj_p0 : pvG (mS % qM) (κ % pG) c ∣ p0 :=
      dvd_trans (⟨pstar * p * pvG (mS % qM) (κ % pG) c * p
            * Nat.factorial (∏ i : Fin P.d,
                max (pvG (mS % qM) (κ % pG) c * pvG (mS % qM) (κ % pG) c * SPb c i) 1),
          by rw [hQcdef]; ring⟩ : pvG (mS % qM) (κ % pG) c ∣ Qc (mS % qM) (κ % pG) c) hQcjdvd
    have hpstar_p0 : pstar ∣ p0 :=
      dvd_trans (⟨p * (pvG (mS % qM) (κ % pG) c * pvG (mS % qM) (κ % pG) c * p)
            * Nat.factorial (∏ i : Fin P.d,
                max (pvG (mS % qM) (κ % pG) c * pvG (mS % qM) (κ % pG) c * SPb c i) 1),
          by rw [hQcdef]; ring⟩ : pstar ∣ Qc (mS % qM) (κ % pG) c) hQcjdvd
    have hp_p0 : p ∣ p0 :=
      dvd_trans (⟨pstar * (pvG (mS % qM) (κ % pG) c * pvG (mS % qM) (κ % pG) c * p)
            * Nat.factorial (∏ i : Fin P.d,
                max (pvG (mS % qM) (κ % pG) c * pvG (mS % qM) (κ % pG) c * SPb c i) 1),
          by rw [hQcdef]; ring⟩ : p ∣ Qc (mS % qM) (κ % pG) c) hQcjdvd
    refine SlicePeriodStar.AffineOnResiduesAt.add hp0 ?_ ?_
    · -- frozen arm
      refine SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hp0 (fun rs' hrs' => ?_)
      have hvalid := ((mem_frozenCellsF rs').mp hrs').1
      have hgateEP : SliceOrder.EventuallyPeriodic
          (fun n => gateF (GdfaF (mS % qM) (κ % pG) c) rs' mS (Z + 1) n) p0 :=
        SliceDstar.EP_of_dvd (gateF_EP' (GdfaF (mS % qM) (κ % pG) c) (mvG (mS % qM) (κ % pG) c) (pvG (mS % qM) (κ % pG) c)
          (hpvG (mS % qM) (κ % pG) c) (hEPG (mS % qM) (κ % pG) c) mS hm rs' hvalid (Z + 1) (by omega)) hpvGj_p0
      have hvecEP : SliceOrder.EventuallyPeriodic
          (fun n => (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) = dstarC n) p0 := by
        refine vec_eq_EP_at hp0 (fun i => ?_)
          (fun i => AffineOnResiduesAtZ.of_dvd hpstar hpstar_p0 hp0 (hCaff i))
        exact AffineOnResiduesAtZ.add hp0
          (AffineOnResiduesAtZ.const p0 (Rcell c rs' (Z + 1) i))
          (AffineOnResiduesAtZ.of_dvd hp hp_p0 hp0
            (AffineOnResiduesAtZ.of_recurrence (m := m) hp (fun nn hnn => by
              have hb := congrFun (hBrec c rs' nn hnn) i
              rw [Pi.add_apply] at hb
              exact hb)))
      exact affineOnResiduesAt_indicator_of_EP hp0 (hgateEP.and hvecEP)
    · -- bulk arm
      refine SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hp0 (fun rs hrs => ?_)
      have hvalid := ((mem_bulkCellsF hZ rs).mp hrs).1
      refine SlicePeriodStar.AffineOnResiduesAt.add hp0 ?_ ?_
      · -- the bounded eq kernel, lifted to p0
        have hker := CopiedKernels.gatedEqConvolution_bounded
          (u := fun t => ((bFN (GdfaF (mS % qM) (κ % pG) c))^[t - Z]
            (cellQ0 (redM (GdfaF (mS % qM) (κ % pG) c) mS rs Z) (coreSpec rs)), min t (Z + 1)))
          (v := fun mm => ((bFN (GdfaF (mS % qM) (κ % pG) c))^[mm + 1
              - (Z + clusterWidth (coreSpec rs))],
            min mm (Z + clusterWidth (coreSpec rs) - 1)))
          (b := fun qf gf => qf.2 = Z + 1
            ∧ gf.2 = Z + clusterWidth (coreSpec rs) - 1
            ∧ cellAcc (redM (GdfaF (mS % qM) (κ % pG) c) mS rs Z) (coreSpec rs)
                (gf.1 (cellGclW (redM (GdfaF (mS % qM) (κ % pG) c) mS rs Z) (coreSpec rs) qf.1)))
          (mu := mvG (mS % qM) (κ % pG) c + Z + Z + 1) (hpu := hpvG (mS % qM) (κ % pG) c)
          (hu := by
            intro i hi
            rw [show i + pvG (mS % qM) (κ % pG) c - Z = (i - Z) + pvG (mS % qM) (κ % pG) c from by omega,
              congrFun (hEPG (mS % qM) (κ % pG) c (i - Z) (by omega))
                (cellQ0 (redM (GdfaF (mS % qM) (κ % pG) c) mS rs Z) (coreSpec rs)),
              show min (i + pvG (mS % qM) (κ % pG) c) (Z + 1) = Z + 1 from by omega,
              show min i (Z + 1) = Z + 1 from by omega])
          (mv := mvG (mS % qM) (κ % pG) c + 2 * Z + clusterWidth (coreSpec rs))
          (hpv := hpvG (mS % qM) (κ % pG) c)
          (hv := by
            intro jj hj
            rw [show jj + pvG (mS % qM) (κ % pG) c + 1 - (Z + clusterWidth (coreSpec rs))
                = (jj + 1 - (Z + clusterWidth (coreSpec rs))) + pvG (mS % qM) (κ % pG) c from by omega,
              hEPG (mS % qM) (κ % pG) c (jj + 1 - (Z + clusterWidth (coreSpec rs))) (by omega),
              show min (jj + pvG (mS % qM) (κ % pG) c) (Z + clusterWidth (coreSpec rs) - 1)
                = Z + clusterWidth (coreSpec rs) - 1 from by omega,
              show min jj (Z + clusterWidth (coreSpec rs) - 1)
                = Z + clusterWidth (coreSpec rs) - 1 from by omega])
          (R := Rcell c rs) (PR := PR c rs) (hpR := hp)
          (hR := fun jj hj => hRrec c rs jj hj)
          (T := fun n => fun i => dstarC n i - Bcell c rs n i) (hP := hpp)
          (hT := fun i => (AffineOnResiduesAtZ.of_dvd hpstar hpstar_pp hpp (hCaff i)).sub
            hpp (AffineOnResiduesAtZ.of_dvd hp hp_pp hpp
              (AffineOnResiduesAtZ.of_recurrence (m := m) hp (fun nn hnn => by
                have hb := congrFun (hBrec c rs nn hnn) i
                rw [Pi.add_apply] at hb
                exact hb))))
          (SP := SPb c) (hPRb := hPRb c rs)
        refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => ?_)
          (hker.of_dvd (hQcpos (mS % qM) (κ % pG) c) hQcjdvd hp0)
        refine congrArg Finset.card ?_
        convert rfl
      · -- the boundary indicator at p0
        have hgateEP : SliceOrder.EventuallyPeriodic
            (fun n => gateF (GdfaF (mS % qM) (κ % pG) c) rs mS Z n) p0 :=
          SliceDstar.EP_of_dvd (gateF_EP' (GdfaF (mS % qM) (κ % pG) c) (mvG (mS % qM) (κ % pG) c) (pvG (mS % qM) (κ % pG) c)
            (hpvG (mS % qM) (κ % pG) c) (hEPG (mS % qM) (κ % pG) c) mS hm rs hvalid Z (by omega)) hpvGj_p0
        have hvecEP : SliceOrder.EventuallyPeriodic
            (fun n => (fun i => RcellH c (rfZ c rs) (2 * Z + 1) i
              + BcellH c (rfZ c rs) n i) = dstarC n) p0 := by
          refine vec_eq_EP_at hp0 (fun i => ?_)
            (fun i => AffineOnResiduesAtZ.of_dvd hpstar hpstar_p0 hp0 (hCaff i))
          exact AffineOnResiduesAtZ.add hp0
            (AffineOnResiduesAtZ.const p0 (RcellH c (rfZ c rs) (2 * Z + 1) i))
            (AffineOnResiduesAtZ.of_dvd hp3 hp3_p0 hp0
              (AffineOnResiduesAtZ.of_recurrence (m := m3) hp3 (fun nn hnn => by
                have hb := congrFun (hBrecH c (rfZ c rs) nn hnn) i
                rw [Pi.add_apply] at hb
                exact hb)))
        exact affineOnResiduesAt_indicator_of_EP hp0 (hgateEP.and hvecEP)
  refine ⟨fun n => tieKer (n % p0) n, Ncan + N0 + Nbr + 4 * Z + 3, ?_, ?_⟩
  · exact SlicePeriodStar.AffineOnResiduesAt.select (Finset.range p0) tieKer
      (fun n => n % p0) p0 hp0 (fun κ _ => htieAff κ)
      (fun n => Finset.mem_range.mpr (Nat.mod_lt _ hp0))
      (fun κ _ => ⟨0, fun n _ => by simp only []; rw [Nat.add_mod_right]⟩)
  · -- agreement
    intro n hn hdom hD
    have hagree : CopiedDstar.dstarRankGA_m P hV mS n = dstarC n :=
      hCagree n (by omega) hdom hD
    show tieKer (n % p0) n = _
    simp only [htieKdef]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hmod : (n % p0) % pG = n % pG := Nat.mod_mod_of_dvd n hpG_p0
    obtain ⟨QQ, hQQ⟩ : ∃ Q : (Fin (P.toPoly.arity c) → ℕ) → Prop,
        ∀ ī, Q ī ↔ (P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩
          ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
          ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ = CopiedDstar.dstarRankGA_m P hV mS n
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
              P.toPoly.labelOf (copiedSlice mS n) b = D →
              P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
              P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b) :=
      ⟨_, fun ī => Iff.rfl⟩
    have hQsel : ∀ ī, QQ ī → P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ := by
      intro ī h; rw [hQQ ī] at h; exact h.1
    have hQiff : ∀ ī, (∀ i, ī i < (copiedSlice mS n).length) →
        (QQ ī ↔ (P.toPoly.sel c (copiedSlice mS n) ī
          ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
          ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ = CopiedDstar.dstarRankGA_m P hV mS n
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
              P.toPoly.labelOf (copiedSlice mS n) b = D →
              P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
              P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)) := by
      intro ī hval
      rw [hQQ ī]
      exact ⟨fun ⟨hs, hrest⟩ => ⟨hs.2, hrest⟩, fun ⟨hs, hrest⟩ => ⟨⟨hval, hs⟩, hrest⟩⟩
    have hQacc : ∀ ī, (∀ i, ī i < (copiedSlice mS n).length) →
        (QQ ī ↔ ((GdfaF (mS % qM) (n % p0 % pG) c).accepts (markAtN _ (copiedSlice mS n) ī)
          ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ = dstarC n)) := by
      intro ī hval
      rw [hQQ ī, ← hagree, hmod]
      have hb := hbrn n (by omega) hdom hD c ī hval
      constructor
      · rintro ⟨hs, hrest⟩
        exact hb.mp ⟨hs.2, hrest⟩
      · intro h
        obtain ⟨hs, hrest⟩ := hb.mpr h
        exact ⟨⟨hval, hs⟩, hrest⟩
    have hrec' := hrec n (by omega) hdom c QQ hQsel
    refine Eq.trans (Eq.trans ?_ hrec'.symm) ?_
    · -- tieKer c-arm = recount RHS (frozen at Z+1 + bulk Icc)
      congr 1
      · -- frozen arm
        refine Finset.sum_congr rfl (fun rs' hrs' => ?_)
        have hvalid := ((mem_frozenCellsF rs').mp hrs').1
        have hval := cellTupleF_valid rs' mS (Z + 1) n hm hvalid (by omega)
        have hrank : P.rankOf (copiedSlice mS n) ⟨c, cellTupleF rs' mS (Z + 1) n⟩
            = fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i :=
          hwineq c rs' hvalid (Z + 1) n (by omega) (by omega)
        have hiff : ((gateF (GdfaF (mS % qM) (n % p0 % pG) c) rs' mS (Z + 1) n
              ∧ (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) = dstarC n)
            ↔ QQ (cellTupleF rs' mS (Z + 1) n)) := by
          rw [hQacc _ hval, gateF, hrank]
        by_cases h : (gateF (GdfaF (mS % qM) (n % p0 % pG) c) rs' mS (Z + 1) n
            ∧ (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) = dstarC n)
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
              ∧ (Rcell c rs t = (fun i => dstarC n i - Bcell c rs n i)
                ∧ min t (Z + 1) = Z + 1
                ∧ min (n - 1 - t) (Z + clusterWidth (coreSpec rs) - 1)
                    = Z + clusterWidth (coreSpec rs) - 1
                ∧ cellAcc (redM (GdfaF (mS % qM) (n % p0 % pG) c) mS rs Z) (coreSpec rs)
                    ((bFN (GdfaF (mS % qM) (n % p0 % pG) c))^[n - 1 - t + 1
                        - (Z + clusterWidth (coreSpec rs))]
                      (cellGclW (redM (GdfaF (mS % qM) (n % p0 % pG) c) mS rs Z) (coreSpec rs)
                        ((bFN (GdfaF (mS % qM) (n % p0 % pG) c))^[t - Z]
                          (cellQ0 (redM (GdfaF (mS % qM) (n % p0 % pG) c) mS rs Z)
                            (coreSpec rs)))))))
            ↔ ((Z + 1 ≤ t ∧ t ≤ n - Z - clusterWidth (coreSpec rs))
                ∧ QQ (cellTupleF rs mS t n)) := by
          intro t
          constructor
          · rintro ⟨htn', heq, hfl, hfr, hbit⟩
            have htlo : Z + 1 ≤ t := by omega
            have hthi : t ≤ n - Z - clusterWidth (coreSpec rs) := by omega
            have hval := cellTupleF_valid rs mS t n hm hvalid (by omega)
            have hacc : (GdfaF (mS % qM) (n % p0 % pG) c).accepts
                (markAtN _ (copiedSlice mS n) (cellTupleF rs mS t n)) := by
              rw [acceptsF_cellTuple_convW (GdfaF (mS % qM) (n % p0 % pG) c) mS hm rs hvalid t n
                  (by omega) (by omega),
                show n - Z - clusterWidth (coreSpec rs) - t
                  = n - 1 - t + 1 - (Z + clusterWidth (coreSpec rs)) from by omega]
              exact hbit
            have hrank : P.rankOf (copiedSlice mS n) ⟨c, cellTupleF rs mS t n⟩
                = fun i => Rcell c rs t i + Bcell c rs n i :=
              hwineq c rs hvalid t n (by omega) (by omega)
            refine ⟨⟨htlo, hthi⟩, ?_⟩
            rw [hQacc _ hval]
            refine ⟨hacc, ?_⟩
            rw [hrank]
            exact (vec_eq_sub_right _ _ _).mpr heq
          · rintro ⟨⟨htlo, hthi⟩, hQ⟩
            have hval := cellTupleF_valid rs mS t n hm hvalid (by omega)
            rw [hQacc _ hval] at hQ
            obtain ⟨hacc, hrkeq⟩ := hQ
            have hrank : P.rankOf (copiedSlice mS n) ⟨c, cellTupleF rs mS t n⟩
                = fun i => Rcell c rs t i + Bcell c rs n i :=
              hwineq c rs hvalid t n (by omega) (by omega)
            rw [hrank] at hrkeq
            refine ⟨by omega, (vec_eq_sub_right _ _ _).mp hrkeq, by omega, by omega, ?_⟩
            rw [acceptsF_cellTuple_convW (GdfaF (mS % qM) (n % p0 % pG) c) mS hm rs hvalid t n
              (by omega) (by omega)] at hacc
            rwa [show n - 1 - t + 1 - (Z + clusterWidth (coreSpec rs))
              = n - Z - clusterWidth (coreSpec rs) - t from by omega]
        have hbdiff : ((gateF (GdfaF (mS % qM) (n % p0 % pG) c) rs mS Z n
              ∧ (fun i => RcellH c (rfZ c rs) (2 * Z + 1) i
                  + BcellH c (rfZ c rs) n i) = dstarC n)
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
          rw [hQacc _ hvalZ, gateF, hrk]
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
    · -- ∑ if QQ = the target tie sum
      refine Finset.sum_congr rfl (fun ī hī => ?_)
      have hval : ∀ i, ī i < (copiedSlice mS n).length := by
        rw [Fintype.mem_piFinset] at hī
        intro i; have := hī i; rwa [Finset.mem_range] at this
      by_cases h : QQ ī
      · rw [if_pos h, if_pos ((hQiff ī hval).mp h)]
      · rw [if_neg h, if_neg (fun hc => h ((hQiff ī hval).mpr hc))]


/-- **Budgeted finite-index fibred tie count.**  This is the row-indexed variant of
`tie_count_fibred_of_gate`: for a fixed budget `C`, the bridge may choose a finite
row index `idx : ι` after seeing the row `mS` and its budget proof.  The output
period is still chosen before `mS`, by multiplying the machine periods over all
`idx : ι` and all `n % pG` classes. -/
theorem tie_count_fibred_of_gate_budgeted_indexed (P : WRP.Presentation Step Step) (hV : P.Valid)
    (C : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (pG : ℕ) (hpG : 1 ≤ pG)
    (GdfaF : ι → ℕ → (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (Mbr : ℕ) (hMbr1 : 1 ≤ Mbr)
    (hbr : ∀ (mS : ℕ), Mbr ≤ mS →
      (∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ C * (mS + n + 1)) →
      ∃ idx : ι, ∃ Nbr, ∀ n, Nbr ≤ n → P.toPoly.domain (copiedSlice mS n) →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
          P.toPoly.labelOf (copiedSlice mS n) a = D) →
        ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
          (∀ i, ī i < (copiedSlice mS n).length) →
          ((P.toPoly.sel c (copiedSlice mS n) ī
              ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
              ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ = CopiedDstar.dstarRankGA_m P hV mS n
              ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
                  P.toPoly.labelOf (copiedSlice mS n) b = D →
                  P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
                  P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
           ↔ ((GdfaF idx (n % pG) c).accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)
              ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩
                  = CopiedDstar.dstarRankGA_m P hV mS n))) :
    ∃ p0 : ℕ, 1 ≤ p0 ∧ ∀ (mS : ℕ), Mbr ≤ mS →
      (∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ C * (mS + n + 1)) →
      ∃ (tie' : ℕ → ℕ) (N : ℕ), SlicePeriodStar.AffineOnResiduesAt p0 tie' ∧
        ∀ n, N ≤ n → P.toPoly.domain (copiedSlice mS n) →
          (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
            P.toPoly.labelOf (copiedSlice mS n) a = D) →
          tie' n = ∑ c : Fin P.toPoly.K,
            ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
              Finset.range (copiedSlice mS n).length),
            if (P.toPoly.sel c (copiedSlice mS n) ī
                ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
                ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩
                    = CopiedDstar.dstarRankGA_m P hV mS n
                ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
                    P.toPoly.labelOf (copiedSlice mS n) b = D →
                    P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
                    P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b) then 1 else 0 := by
  classical
  obtain ⟨pstar, hpstar, hdstarC⟩ := CopiedDstarC.dstarC_exists_fibred P hV
  obtain ⟨Z, hZ, hrecount⟩ := canonical_recount_fibred P
  obtain ⟨m, p, Mc, SPb, hp, hmB, hMc, hbwd, hsetupB⟩ :=
    CopiedSetup.dstar_setup_fibred_bounded P Z
  obtain ⟨m3, p3, Mc3, SP3, hp3, hm3B, hMc3, hbwd3, hsetupBh⟩ :=
    CopiedSetup.dstar_setup_fibred_bounded P (2 * Z)
  choose mvG pvG hpvG hEPG using
    fun (idx : ι) (j : ℕ) (c : Fin P.toPoly.K) => bFN_func_iterate_eventuallyPeriodic (GdfaF idx j c)
  have hpvGpos : ∀ idx j c, 0 < pvG idx j c := fun idx j c => hpvG idx j c
  have hZ2 : Z ≤ 2 * Z := by omega
  have hZZ : Z + Z ≤ 2 * Z := by omega
  -- per-(r,j,c) bulk-kernel period and the global hoisted period (r = idx)
  set Qc : ι → ℕ → Fin P.toPoly.K → ℕ := fun idx j c =>
    (pstar * p) * (pvG idx j c * pvG idx j c * p)
      * Nat.factorial (∏ i : Fin P.d, max (pvG idx j c * pvG idx j c * SPb c i) 1) with hQcdef
  have hQcpos : ∀ idx j c, 1 ≤ Qc idx j c := by
    intro idx j c
    rw [hQcdef]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hpstar hp)
      (Nat.mul_pos (Nat.mul_pos (hpvGpos idx j c) (hpvGpos idx j c)) hp)) (Nat.factorial_pos _)
  set p0 : ℕ := p3 * pG
      * (∏ idx : ι, ∏ j ∈ Finset.range pG, ∏ c : Fin P.toPoly.K, Qc idx j c)
    with hp0def
  have hp0 : 1 ≤ p0 := by
    rw [hp0def]
    exact Nat.mul_pos (Nat.mul_pos hp3 hpG)
        (Finset.prod_pos (fun idx _ => Finset.prod_pos (fun j _ =>
          Finset.prod_pos (fun c _ => hQcpos idx j c))))
  have hQQdvd : (∏ idx : ι, ∏ j ∈ Finset.range pG,
      ∏ c : Fin P.toPoly.K, Qc idx j c) ∣ p0 := by
    rw [hp0def]; exact dvd_mul_left _ (p3 * pG)
  have hp3_p0 : p3 ∣ p0 := ⟨pG * ∏ idx : ι, ∏ j ∈ Finset.range pG,
      ∏ c : Fin P.toPoly.K, Qc idx j c, by rw [hp0def]; ring⟩
  have hpG_p0 : pG ∣ p0 := ⟨p3 * ∏ idx : ι, ∏ j ∈ Finset.range pG,
      ∏ c : Fin P.toPoly.K, Qc idx j c, by rw [hp0def]; ring⟩
  have hpp : 1 ≤ pstar * p := Nat.mul_pos hpstar hp
  have hpstar_pp : pstar ∣ pstar * p := dvd_mul_right pstar p
  have hp_pp : p ∣ pstar * p := dvd_mul_left p pstar
  refine ⟨p0, hp0, fun mS hmS hbud => ?_⟩
  have hm : 1 ≤ mS := le_trans hMbr1 hmS
  -- per-mS tie-bridge threshold `Nbr` (the n-leg threshold grows linearly in mS; harmless,
  -- absorbed into the per-mS output `N` below)
  obtain ⟨idx, Nbr, hbrn⟩ := hbr mS hmS hbud
  obtain ⟨dstarC, N0, hCaff, hCagree⟩ := hdstarC C mS hm hbud
  obtain ⟨Ncan, hrec⟩ := hrecount C mS hm hbud
  obtain ⟨Rcell, Bcell, PR, PBn, hwineq, hRrec, hBrec, hPRb, hPBnb⟩ := hsetupB mS hm
  obtain ⟨RcellH, BcellH, PRH, PBnH, hwineqH, hRrecH, hBrecH, hPRHb, hPBnHb⟩ :=
    hsetupBh mS hm
  set rfZ : (c : Fin P.toPoly.K) → (Fin (P.toPoly.arity c) → RegionSpecF Z) →
      (Fin (P.toPoly.arity c) → RegionSpecF (2 * Z)) :=
    fun c rs i => refreezeFrontF hZ2 Z hZZ (rs i) with hrfZdef
  -- the per-class tie kernel
  set tieKer : ℕ → ℕ → ℕ := fun κ n =>
    ∑ c : Fin P.toPoly.K,
      ((∑ rs' ∈ frozenCellsF Z (P.toPoly.arity c) mS,
        if (gateF (GdfaF idx (κ % pG) c) rs' mS (Z + 1) n
            ∧ (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) = dstarC n)
        then 1 else 0)
      + ∑ rs ∈ bulkCellsF Z hZ (P.toPoly.arity c) mS,
          (((Finset.range n).filter (fun t : ℕ =>
              Rcell c rs t = (fun i => dstarC n i - Bcell c rs n i)
                ∧ min t (Z + 1) = Z + 1
                ∧ min (n - 1 - t) (Z + clusterWidth (coreSpec rs) - 1)
                    = Z + clusterWidth (coreSpec rs) - 1
                ∧ cellAcc (redM (GdfaF idx (κ % pG) c) mS rs Z) (coreSpec rs)
                    ((bFN (GdfaF idx (κ % pG) c))^[n - 1 - t + 1
                        - (Z + clusterWidth (coreSpec rs))]
                      (cellGclW (redM (GdfaF idx (κ % pG) c) mS rs Z) (coreSpec rs)
                        ((bFN (GdfaF idx (κ % pG) c))^[t - Z]
                          (cellQ0 (redM (GdfaF idx (κ % pG) c) mS rs Z)
                            (coreSpec rs))))))).card
            + (if (gateF (GdfaF idx (κ % pG) c) rs mS Z n
                  ∧ (fun i => RcellH c (rfZ c rs) (2 * Z + 1) i
                      + BcellH c (rfZ c rs) n i) = dstarC n)
              then 1 else 0)))
    with htieKdef
  -- the per-class affineness at p0 (gate fixed at j = κ % pG)
  have htieAff : ∀ κ, SlicePeriodStar.AffineOnResiduesAt p0 (tieKer κ) := by
    intro κ
    have hjlt : κ % pG < pG := Nat.mod_lt κ hpG
    simp only [htieKdef]
    refine SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hp0 (fun c _ => ?_)
    have hQcjdvd : Qc idx (κ % pG) c ∣ p0 :=
      dvd_trans (dvd_trans (dvd_trans
        (Finset.dvd_prod_of_mem (fun c' => Qc idx (κ % pG) c') (Finset.mem_univ c))
        (Finset.dvd_prod_of_mem (fun j => ∏ c' : Fin P.toPoly.K, Qc idx j c')
          (Finset.mem_range.mpr hjlt)))
        (Finset.dvd_prod_of_mem
          (fun idx : ι => ∏ j ∈ Finset.range pG, ∏ c' : Fin P.toPoly.K, Qc idx j c')
          (Finset.mem_univ idx))) hQQdvd
    have hpvGj_p0 : pvG idx (κ % pG) c ∣ p0 :=
      dvd_trans (⟨pstar * p * pvG idx (κ % pG) c * p
            * Nat.factorial (∏ i : Fin P.d,
                max (pvG idx (κ % pG) c * pvG idx (κ % pG) c * SPb c i) 1),
          by rw [hQcdef]; ring⟩ : pvG idx (κ % pG) c ∣ Qc idx (κ % pG) c) hQcjdvd
    have hpstar_p0 : pstar ∣ p0 :=
      dvd_trans (⟨p * (pvG idx (κ % pG) c * pvG idx (κ % pG) c * p)
            * Nat.factorial (∏ i : Fin P.d,
                max (pvG idx (κ % pG) c * pvG idx (κ % pG) c * SPb c i) 1),
          by rw [hQcdef]; ring⟩ : pstar ∣ Qc idx (κ % pG) c) hQcjdvd
    have hp_p0 : p ∣ p0 :=
      dvd_trans (⟨pstar * (pvG idx (κ % pG) c * pvG idx (κ % pG) c * p)
            * Nat.factorial (∏ i : Fin P.d,
                max (pvG idx (κ % pG) c * pvG idx (κ % pG) c * SPb c i) 1),
          by rw [hQcdef]; ring⟩ : p ∣ Qc idx (κ % pG) c) hQcjdvd
    refine SlicePeriodStar.AffineOnResiduesAt.add hp0 ?_ ?_
    · -- frozen arm
      refine SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hp0 (fun rs' hrs' => ?_)
      have hvalid := ((mem_frozenCellsF rs').mp hrs').1
      have hgateEP : SliceOrder.EventuallyPeriodic
          (fun n => gateF (GdfaF idx (κ % pG) c) rs' mS (Z + 1) n) p0 :=
        SliceDstar.EP_of_dvd (gateF_EP' (GdfaF idx (κ % pG) c) (mvG idx (κ % pG) c) (pvG idx (κ % pG) c)
          (hpvG idx (κ % pG) c) (hEPG idx (κ % pG) c) mS hm rs' hvalid (Z + 1) (by omega)) hpvGj_p0
      have hvecEP : SliceOrder.EventuallyPeriodic
          (fun n => (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) = dstarC n) p0 := by
        refine vec_eq_EP_at hp0 (fun i => ?_)
          (fun i => AffineOnResiduesAtZ.of_dvd hpstar hpstar_p0 hp0 (hCaff i))
        exact AffineOnResiduesAtZ.add hp0
          (AffineOnResiduesAtZ.const p0 (Rcell c rs' (Z + 1) i))
          (AffineOnResiduesAtZ.of_dvd hp hp_p0 hp0
            (AffineOnResiduesAtZ.of_recurrence (m := m) hp (fun nn hnn => by
              have hb := congrFun (hBrec c rs' nn hnn) i
              rw [Pi.add_apply] at hb
              exact hb)))
      exact affineOnResiduesAt_indicator_of_EP hp0 (hgateEP.and hvecEP)
    · -- bulk arm
      refine SlicePeriodStar.AffineOnResiduesAt.finsetSum _ _ hp0 (fun rs hrs => ?_)
      have hvalid := ((mem_bulkCellsF hZ rs).mp hrs).1
      refine SlicePeriodStar.AffineOnResiduesAt.add hp0 ?_ ?_
      · -- the bounded eq kernel, lifted to p0
        have hker := CopiedKernels.gatedEqConvolution_bounded
          (u := fun t => ((bFN (GdfaF idx (κ % pG) c))^[t - Z]
            (cellQ0 (redM (GdfaF idx (κ % pG) c) mS rs Z) (coreSpec rs)), min t (Z + 1)))
          (v := fun mm => ((bFN (GdfaF idx (κ % pG) c))^[mm + 1
              - (Z + clusterWidth (coreSpec rs))],
            min mm (Z + clusterWidth (coreSpec rs) - 1)))
          (b := fun qf gf => qf.2 = Z + 1
            ∧ gf.2 = Z + clusterWidth (coreSpec rs) - 1
            ∧ cellAcc (redM (GdfaF idx (κ % pG) c) mS rs Z) (coreSpec rs)
                (gf.1 (cellGclW (redM (GdfaF idx (κ % pG) c) mS rs Z) (coreSpec rs) qf.1)))
          (mu := mvG idx (κ % pG) c + Z + Z + 1) (hpu := hpvG idx (κ % pG) c)
          (hu := by
            intro i hi
            rw [show i + pvG idx (κ % pG) c - Z = (i - Z) + pvG idx (κ % pG) c from by omega,
              congrFun (hEPG idx (κ % pG) c (i - Z) (by omega))
                (cellQ0 (redM (GdfaF idx (κ % pG) c) mS rs Z) (coreSpec rs)),
              show min (i + pvG idx (κ % pG) c) (Z + 1) = Z + 1 from by omega,
              show min i (Z + 1) = Z + 1 from by omega])
          (mv := mvG idx (κ % pG) c + 2 * Z + clusterWidth (coreSpec rs))
          (hpv := hpvG idx (κ % pG) c)
          (hv := by
            intro jj hj
            rw [show jj + pvG idx (κ % pG) c + 1 - (Z + clusterWidth (coreSpec rs))
                = (jj + 1 - (Z + clusterWidth (coreSpec rs))) + pvG idx (κ % pG) c from by omega,
              hEPG idx (κ % pG) c (jj + 1 - (Z + clusterWidth (coreSpec rs))) (by omega),
              show min (jj + pvG idx (κ % pG) c) (Z + clusterWidth (coreSpec rs) - 1)
                = Z + clusterWidth (coreSpec rs) - 1 from by omega,
              show min jj (Z + clusterWidth (coreSpec rs) - 1)
                = Z + clusterWidth (coreSpec rs) - 1 from by omega])
          (R := Rcell c rs) (PR := PR c rs) (hpR := hp)
          (hR := fun jj hj => hRrec c rs jj hj)
          (T := fun n => fun i => dstarC n i - Bcell c rs n i) (hP := hpp)
          (hT := fun i => (AffineOnResiduesAtZ.of_dvd hpstar hpstar_pp hpp (hCaff i)).sub
            hpp (AffineOnResiduesAtZ.of_dvd hp hp_pp hpp
              (AffineOnResiduesAtZ.of_recurrence (m := m) hp (fun nn hnn => by
                have hb := congrFun (hBrec c rs nn hnn) i
                rw [Pi.add_apply] at hb
                exact hb))))
          (SP := SPb c) (hPRb := hPRb c rs)
        refine SlicePeriodStar.AffineOnResiduesAt.congr' (fun n => ?_)
          (hker.of_dvd (hQcpos idx (κ % pG) c) hQcjdvd hp0)
        refine congrArg Finset.card ?_
        convert rfl
      · -- the boundary indicator at p0
        have hgateEP : SliceOrder.EventuallyPeriodic
            (fun n => gateF (GdfaF idx (κ % pG) c) rs mS Z n) p0 :=
          SliceDstar.EP_of_dvd (gateF_EP' (GdfaF idx (κ % pG) c) (mvG idx (κ % pG) c) (pvG idx (κ % pG) c)
            (hpvG idx (κ % pG) c) (hEPG idx (κ % pG) c) mS hm rs hvalid Z (by omega)) hpvGj_p0
        have hvecEP : SliceOrder.EventuallyPeriodic
            (fun n => (fun i => RcellH c (rfZ c rs) (2 * Z + 1) i
              + BcellH c (rfZ c rs) n i) = dstarC n) p0 := by
          refine vec_eq_EP_at hp0 (fun i => ?_)
            (fun i => AffineOnResiduesAtZ.of_dvd hpstar hpstar_p0 hp0 (hCaff i))
          exact AffineOnResiduesAtZ.add hp0
            (AffineOnResiduesAtZ.const p0 (RcellH c (rfZ c rs) (2 * Z + 1) i))
            (AffineOnResiduesAtZ.of_dvd hp3 hp3_p0 hp0
              (AffineOnResiduesAtZ.of_recurrence (m := m3) hp3 (fun nn hnn => by
                have hb := congrFun (hBrecH c (rfZ c rs) nn hnn) i
                rw [Pi.add_apply] at hb
                exact hb)))
        exact affineOnResiduesAt_indicator_of_EP hp0 (hgateEP.and hvecEP)
  refine ⟨fun n => tieKer (n % p0) n, Ncan + N0 + Nbr + 4 * Z + 3, ?_, ?_⟩
  · exact SlicePeriodStar.AffineOnResiduesAt.select (Finset.range p0) tieKer
      (fun n => n % p0) p0 hp0 (fun κ _ => htieAff κ)
      (fun n => Finset.mem_range.mpr (Nat.mod_lt _ hp0))
      (fun κ _ => ⟨0, fun n _ => by simp only []; rw [Nat.add_mod_right]⟩)
  · -- agreement
    intro n hn hdom hD
    have hagree : CopiedDstar.dstarRankGA_m P hV mS n = dstarC n :=
      hCagree n (by omega) hdom hD
    show tieKer (n % p0) n = _
    simp only [htieKdef]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hmod : (n % p0) % pG = n % pG := Nat.mod_mod_of_dvd n hpG_p0
    obtain ⟨QQ, hQQ⟩ : ∃ Q : (Fin (P.toPoly.arity c) → ℕ) → Prop,
        ∀ ī, Q ī ↔ (P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩
          ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
          ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ = CopiedDstar.dstarRankGA_m P hV mS n
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
              P.toPoly.labelOf (copiedSlice mS n) b = D →
              P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
              P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b) :=
      ⟨_, fun ī => Iff.rfl⟩
    have hQsel : ∀ ī, QQ ī → P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ := by
      intro ī h; rw [hQQ ī] at h; exact h.1
    have hQiff : ∀ ī, (∀ i, ī i < (copiedSlice mS n).length) →
        (QQ ī ↔ (P.toPoly.sel c (copiedSlice mS n) ī
          ∧ P.toPoly.labelOf (copiedSlice mS n) ⟨c, ī⟩ = U
          ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ = CopiedDstar.dstarRankGA_m P hV mS n
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
              P.toPoly.labelOf (copiedSlice mS n) b = D →
              P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
              P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)) := by
      intro ī hval
      rw [hQQ ī]
      exact ⟨fun ⟨hs, hrest⟩ => ⟨hs.2, hrest⟩, fun ⟨hs, hrest⟩ => ⟨⟨hval, hs⟩, hrest⟩⟩
    have hQacc : ∀ ī, (∀ i, ī i < (copiedSlice mS n).length) →
        (QQ ī ↔ ((GdfaF idx (n % p0 % pG) c).accepts (markAtN _ (copiedSlice mS n) ī)
          ∧ P.rankOf (copiedSlice mS n) ⟨c, ī⟩ = dstarC n)) := by
      intro ī hval
      rw [hQQ ī, ← hagree, hmod]
      have hb := hbrn n (by omega) hdom hD c ī hval
      constructor
      · rintro ⟨hs, hrest⟩
        exact hb.mp ⟨hs.2, hrest⟩
      · intro h
        obtain ⟨hs, hrest⟩ := hb.mpr h
        exact ⟨⟨hval, hs⟩, hrest⟩
    have hrec' := hrec n (by omega) hdom c QQ hQsel
    refine Eq.trans (Eq.trans ?_ hrec'.symm) ?_
    · -- tieKer c-arm = recount RHS (frozen at Z+1 + bulk Icc)
      congr 1
      · -- frozen arm
        refine Finset.sum_congr rfl (fun rs' hrs' => ?_)
        have hvalid := ((mem_frozenCellsF rs').mp hrs').1
        have hval := cellTupleF_valid rs' mS (Z + 1) n hm hvalid (by omega)
        have hrank : P.rankOf (copiedSlice mS n) ⟨c, cellTupleF rs' mS (Z + 1) n⟩
            = fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i :=
          hwineq c rs' hvalid (Z + 1) n (by omega) (by omega)
        have hiff : ((gateF (GdfaF idx (n % p0 % pG) c) rs' mS (Z + 1) n
              ∧ (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) = dstarC n)
            ↔ QQ (cellTupleF rs' mS (Z + 1) n)) := by
          rw [hQacc _ hval, gateF, hrank]
        by_cases h : (gateF (GdfaF idx (n % p0 % pG) c) rs' mS (Z + 1) n
            ∧ (fun i => Rcell c rs' (Z + 1) i + Bcell c rs' n i) = dstarC n)
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
              ∧ (Rcell c rs t = (fun i => dstarC n i - Bcell c rs n i)
                ∧ min t (Z + 1) = Z + 1
                ∧ min (n - 1 - t) (Z + clusterWidth (coreSpec rs) - 1)
                    = Z + clusterWidth (coreSpec rs) - 1
                ∧ cellAcc (redM (GdfaF idx (n % p0 % pG) c) mS rs Z) (coreSpec rs)
                    ((bFN (GdfaF idx (n % p0 % pG) c))^[n - 1 - t + 1
                        - (Z + clusterWidth (coreSpec rs))]
                      (cellGclW (redM (GdfaF idx (n % p0 % pG) c) mS rs Z) (coreSpec rs)
                        ((bFN (GdfaF idx (n % p0 % pG) c))^[t - Z]
                          (cellQ0 (redM (GdfaF idx (n % p0 % pG) c) mS rs Z)
                            (coreSpec rs)))))))
            ↔ ((Z + 1 ≤ t ∧ t ≤ n - Z - clusterWidth (coreSpec rs))
                ∧ QQ (cellTupleF rs mS t n)) := by
          intro t
          constructor
          · rintro ⟨htn', heq, hfl, hfr, hbit⟩
            have htlo : Z + 1 ≤ t := by omega
            have hthi : t ≤ n - Z - clusterWidth (coreSpec rs) := by omega
            have hval := cellTupleF_valid rs mS t n hm hvalid (by omega)
            have hacc : (GdfaF idx (n % p0 % pG) c).accepts
                (markAtN _ (copiedSlice mS n) (cellTupleF rs mS t n)) := by
              rw [acceptsF_cellTuple_convW (GdfaF idx (n % p0 % pG) c) mS hm rs hvalid t n
                  (by omega) (by omega),
                show n - Z - clusterWidth (coreSpec rs) - t
                  = n - 1 - t + 1 - (Z + clusterWidth (coreSpec rs)) from by omega]
              exact hbit
            have hrank : P.rankOf (copiedSlice mS n) ⟨c, cellTupleF rs mS t n⟩
                = fun i => Rcell c rs t i + Bcell c rs n i :=
              hwineq c rs hvalid t n (by omega) (by omega)
            refine ⟨⟨htlo, hthi⟩, ?_⟩
            rw [hQacc _ hval]
            refine ⟨hacc, ?_⟩
            rw [hrank]
            exact (vec_eq_sub_right _ _ _).mpr heq
          · rintro ⟨⟨htlo, hthi⟩, hQ⟩
            have hval := cellTupleF_valid rs mS t n hm hvalid (by omega)
            rw [hQacc _ hval] at hQ
            obtain ⟨hacc, hrkeq⟩ := hQ
            have hrank : P.rankOf (copiedSlice mS n) ⟨c, cellTupleF rs mS t n⟩
                = fun i => Rcell c rs t i + Bcell c rs n i :=
              hwineq c rs hvalid t n (by omega) (by omega)
            rw [hrank] at hrkeq
            refine ⟨by omega, (vec_eq_sub_right _ _ _).mp hrkeq, by omega, by omega, ?_⟩
            rw [acceptsF_cellTuple_convW (GdfaF idx (n % p0 % pG) c) mS hm rs hvalid t n
              (by omega) (by omega)] at hacc
            rwa [show n - 1 - t + 1 - (Z + clusterWidth (coreSpec rs))
              = n - Z - clusterWidth (coreSpec rs) - t from by omega]
        have hbdiff : ((gateF (GdfaF idx (n % p0 % pG) c) rs mS Z n
              ∧ (fun i => RcellH c (rfZ c rs) (2 * Z + 1) i
                  + BcellH c (rfZ c rs) n i) = dstarC n)
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
          rw [hQacc _ hvalZ, gateF, hrk]
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
    · -- ∑ if QQ = the target tie sum
      refine Finset.sum_congr rfl (fun ī hī => ?_)
      have hval : ∀ i, ī i < (copiedSlice mS n).length := by
        rw [Fintype.mem_piFinset] at hī
        intro i; have := hī i; rwa [Finset.mem_range] at this
      by_cases h : QQ ī
      · rw [if_pos h, if_pos ((hQiff ī hval).mp h)]
      · rw [if_neg h, if_neg (fun hc => h ((hQiff ī hval).mpr hc))]

end CopiedCounts
