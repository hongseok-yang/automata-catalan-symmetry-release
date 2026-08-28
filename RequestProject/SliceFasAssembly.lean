/-
# The §7 `fas` count assembly (arity-1): L6 `tie_count` and L7 `fas_count` (route steps 9–10)

The downstream assembly of the corrected TIE route: with the L4 position-separated gate
(`SliceFasGates.fasU_atomOrd_cfg_gate`), the L5 selector
(`SliceFasSelector.eqRankD_position_selector`), the keystone
(`SliceFasTie.fas_member_eqRank`) and the count kernels (`SliceFasCount`), this file
assembles `fasCount`/`tailUCount` as `AffineOnResidues` functions of `n`.

This file is the designated home for the assembly (NOT `SliceFasCount`, which sits below
`SliceAffineSelect` in the import order): it imports the whole tower.

The present section provides the statement-level kernel clones the assembly consumes:

* `lexEq_count_per_region_blockD` / `lexLt_below_count_per_region_blockD` — the
  block-`D`-parity twins of the `SliceFasCount` count kernels (rank at `1+2j+1` in
  `W_{j+1}`, marked-DFA gate at `1+2j+1`, via `accepts_markAt_blockD`);
* `sum_range_wrappedFlat_split` — the position partition of a full slice sum
  (`pre 0` + blockU positions + blockD positions + `suf 2n+1`).
-/
import RequestProject.SliceAffineSelect
import RequestProject.SliceFasSelector
import RequestProject.SliceFasTie
import RequestProject.SliceProfileDischarge
import RequestProject.SliceProfile

namespace SliceFasAssembly

open WRP Step SliceOrder SliceThreshold SliceAffine SliceDstar SliceLexOrder SliceCount
  SliceMSO MSOMark SliceRankAtom
open scoped Classical

/-! ## The blockD-parity count-kernel twins -/

/-- **`lexEq_count_per_region`, block-`D` parity**: counts loop-indices `j < n` with
`j % m = a`, block-`D` rank `P.rank c W_{j+1} (·↦1+2j+1)` EQUAL to a moving
`AffineOnResiduesZ` threshold `T n`, and the marked-DFA gate on at `1+2j+1`.  Mirror of
`SliceFasCount.lexEq_count_per_region` with the bit decomposed by
`accepts_markAt_blockD`. -/
theorem lexEq_count_per_region_blockD {Gamma : Type*} (P : WRP.Presentation Step Gamma)
    (c : Fin P.toPoly.K) {T : ℕ → Fin P.d → ℤ} (hT : ∀ i, AffineOnResiduesZ (fun n => T n i))
    (m a : ℕ) (hm : 1 ≤ m) (M : DetAuto (Step × Bool)) :
    AffineOnResidues (fun n => ((Finset.range n).filter
      (fun j : ℕ => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1) = T n
        ∧ j % m = a ∧ M.accepts (markAt (wrappedFlat n) (1 + 2 * j + 1)))).card) := by
  obtain ⟨mR, pR, PR, hpR, hR⟩ := SliceRankAtom.rank_blockD_rankAffine P c
  obtain ⟨mu, pu, hpu, hu⟩ := SliceCount.bF_iterate_eventuallyPeriodic M
  obtain ⟨mv, pv, hpv, hv⟩ := SliceCount.bF_func_iterate_eventuallyPeriodic M
  have hu_iter : ∀ s t, mu ≤ s → (bF M)^[s + pu * t] (qpre M) = (bF M)^[s] (qpre M) := by
    intro s t hs
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, hu _ (by omega), ih]
  have hu' : ∀ i, mu ≤ i →
      ((bF M)^[i + pu * m] (qpre M), (i + pu * m) % m) = ((bF M)^[i] (qpre M), i % m) := by
    intro i hi
    refine Prod.ext (hu_iter i m hi) ?_
    show (i + pu * m) % m = i % m
    rw [Nat.mul_comm pu m, Nat.add_mul_mod_self_left]
  have hker := SliceFasCount.affineOnResidues_gatedEqConvolution
    (fun j => ((bF M)^[j] (qpre M), j % m)) (fun mm => (bF M)^[mm])
    (fun qr g => qr.2 = a ∧ M.accept (fStep M (g (M.δ (fStep M qr.1 U) (D, true))) D))
    (Nat.mul_pos hpu hm) hu' hpv hv
    (fun j => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1)) PR hpR hR T hT
  refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_) hker
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  refine and_congr_right
    (fun hj => and_congr_right (fun _ => and_congr Iff.rfl ?_))
  rw [SliceDstar.accepts_markAt_blockD M n j hj]

/-- **`lexLt_below_count_per_region`, block-`D` parity**: counts loop-indices `j < n`
whose block-`D` rank is `lexLt` below the moving threshold and whose gate is on at
`1+2j+1`. -/
theorem lexLt_below_count_per_region_blockD {Gamma : Type*} (P : WRP.Presentation Step Gamma)
    (c : Fin P.toPoly.K) {T : ℕ → Fin P.d → ℤ} (hT : ∀ i, AffineOnResiduesZ (fun n => T n i))
    (M : DetAuto (Step × Bool)) :
    AffineOnResidues (fun n => ((Finset.range n).filter
      (fun j : ℕ => WRP.lexLt (P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1)) (T n)
        ∧ M.accepts (markAt (wrappedFlat n) (1 + 2 * j + 1)))).card) := by
  obtain ⟨mR, pR, PR, hpR, hR⟩ := SliceRankAtom.rank_blockD_rankAffine P c
  obtain ⟨mu, pu, hpu, hu⟩ := SliceCount.bF_iterate_eventuallyPeriodic M
  obtain ⟨mv, pv, hpv, hv⟩ := SliceCount.bF_func_iterate_eventuallyPeriodic M
  have hgc := SliceGatedConv.affineOnResidues_gatedLexConvolution
    (fun j => (bF M)^[j] (qpre M)) (fun mm => (bF M)^[mm])
    (fun q g => M.accept (fStep M (g (M.δ (fStep M q U) (D, true))) D))
    hpu hu hpv hv
    (fun j => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1)) PR hpR hR T hT
  refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_) hgc
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j hj
  rw [Finset.mem_range] at hj
  refine and_congr_right (fun _ => ?_)
  rw [SliceDstar.accepts_markAt_blockD M n j hj]

/-! ## The slice position-sum partition -/

/-- **Position partition of a full slice sum**: `∑_{q < 2(n+1)} g q` splits into the pre
position, the block-`U` positions `1+2j`, the block-`D` positions `1+2j+1`, and the
suffix `2n+1`. -/
theorem sum_range_wrappedFlat_split (g : ℕ → ℕ) (n : ℕ) :
    ∑ q ∈ Finset.range (2 * (n + 1)), g q
      = g 0 + (∑ j ∈ Finset.range n, g (1 + 2 * j))
        + (∑ j ∈ Finset.range n, g (1 + 2 * j + 1)) + g (2 * n + 1) := by
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring, Finset.sum_range_succ,
    Finset.sum_range_succ', SliceCount.sum_pairs (fun i => g (i + 1)) n,
    Finset.sum_add_distrib]
  have e1 : (∑ j ∈ Finset.range n, g (2 * j + 1)) = ∑ j ∈ Finset.range n, g (1 + 2 * j) :=
    Finset.sum_congr rfl (fun j _ => congrArg g (by ring))
  have e2 : (∑ j ∈ Finset.range n, g (2 * j + 1 + 1))
      = ∑ j ∈ Finset.range n, g (1 + 2 * j + 1) :=
    Finset.sum_congr rfl (fun j _ => congrArg g (by ring))
  rw [e1, e2]
  ring

/-! ## Boundary-position acceptance is eventually periodic -/

/-- The marked acceptance at the pre position `0` is eventually periodic in `n` (the
backward iterate function is). -/
theorem accepts_pre_EP (M : DetAuto (Step × Bool)) :
    ∃ p, 1 ≤ p ∧ EventuallyPeriodic (fun n => M.accepts (markAt (wrappedFlat n) 0)) p := by
  obtain ⟨mv, pv, hpv, hv⟩ := SliceCount.bF_func_iterate_eventuallyPeriodic M
  refine ⟨pv, hpv, mv, fun n hn => ?_⟩
  simp only []
  rw [SliceDstar.accepts_markAt_pre M (n + pv), SliceDstar.accepts_markAt_pre M n, hv n hn]

/-! ## L6: the TIE count is affine-on-residues past a threshold on `D`-present slices -/

set_option maxHeartbeats 1600000 in
/-- **`tie_count_affineOnResidues`** (route step L6).  There is an `AffineOnResidues`
function `tie'` agreeing, on every `D`-present slice past a threshold, with the semantic
TIE count: the number of atoms `(c, q)` of `W_n` that are selected, labelled `U`, of rank
EQUAL to `dstarRank n`, and `atomOrd`-preceding every selected `D`-atom of that same rank
(the equal-rank clause of the keystone `fas_member_eqRank`).

Construction: per class `κ = n % p0` and copy `c`, the L4 gate DFA with the L5 data
decides the per-atom condition; the blockU/blockD positions are counted by the
`lexEq_count_per_region` kernels at threshold `T := dstarRank`, the pre/suf positions by
eventually-periodic indicators; the per-class patching is `AffineOnResidues.select`.
Base `+ SliceMSO.buchi`. -/
theorem tie_count_affineOnResidues (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity : ∀ c, P.toPoly.arity c = 1) :
    ∃ (tie' : ℕ → ℕ) (N : ℕ), AffineOnResidues tie' ∧
      ∀ n, N ≤ n →
        (∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧
          P.toPoly.labelOf (wrappedFlat n) a = D) →
        tie' n = ∑ c : Fin P.toPoly.K, ∑ q ∈ Finset.range (wrappedFlat n).length,
          if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
              ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
              ∧ P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩ = dstarRank P hV harity n
              ∧ ∀ b, P.toPoly.selectedAtom (wrappedFlat n) b →
                  P.toPoly.labelOf (wrappedFlat n) b = D →
                  P.rankOf (wrappedFlat n) b = dstarRank P hV harity n →
                  P.toPoly.atomOrd (wrappedFlat n) ⟨c, fun _ => q⟩ b)
          then 1 else 0 := by
  classical
  obtain ⟨M0, mthr, p0, N1, S, Front, Back, hp0, hSb, hsel⟩ :=
    SliceFasSelector.eqRankD_position_selector P hV harity
  have hDR : ∀ i, AffineOnResiduesZ (fun n => dstarRank P hV harity n i) :=
    SliceDstarBridge.dstarRank_affineOnResiduesZ P hV harity
  choose Gdfa hGdfa using fun (κ : ℕ) (c : Fin P.toPoly.K) =>
    SliceFasGates.fasU_atomOrd_cfg_gate P c harity M0 mthr (S κ) (Front κ) (Back κ) (hSb κ)
  -- the pre/suf indicator conditions and their eventual periodicity
  set preCond : ℕ → Fin P.toPoly.K → ℕ → Prop := fun κ c n =>
    (Gdfa κ c).accepts (markAt (wrappedFlat n) 0)
      ∧ P.rank c (wrappedFlat n) (fun _ => 0) = dstarRank P hV harity n with hpreConddef
  set sufCond : ℕ → Fin P.toPoly.K → ℕ → Prop := fun κ c n =>
    (Gdfa κ c).accepts (markAt (wrappedFlat n) (1 + 2 * n))
      ∧ P.rank c (wrappedFlat n) (fun _ => 1 + 2 * n) = dstarRank P hV harity n
    with hsufConddef
  have hpreEP : ∀ κ c, ∃ pp, 1 ≤ pp ∧ EventuallyPeriodic (preCond κ c) pp := by
    intro κ c
    obtain ⟨pa, hpa, hEPa⟩ := accepts_pre_EP (Gdfa κ c)
    obtain ⟨pb, hpb, hEPb⟩ := SliceFasSelector.affineOnResiduesZ_vec_eq_EP
      (F := fun n => P.rank c (wrappedFlat n) (fun _ => 0))
      (G := fun n => dstarRank P hV harity n)
      (fun i => SliceFasBridges.rankAffine_coord_affineOnResiduesZ
        (rank_pre_rankAffine P c) i) hDR
    refine ⟨pa * pb, Nat.mul_pos hpa hpb, ?_⟩
    exact (EP_of_dvd hEPa (dvd_mul_right pa pb)).and
      (EP_of_dvd hEPb (dvd_mul_left pb pa))
  have hsufEP : ∀ κ c, ∃ pp, 1 ≤ pp ∧ EventuallyPeriodic (sufCond κ c) pp := by
    intro κ c
    obtain ⟨pa, hpa, hEPa⟩ := SliceDstar.selS_EP (Gdfa κ c)
    obtain ⟨pb, hpb, hEPb⟩ := SliceFasSelector.affineOnResiduesZ_vec_eq_EP
      (F := fun n => P.rank c (wrappedFlat n) (fun _ => 1 + 2 * n))
      (G := fun n => dstarRank P hV harity n)
      (fun i => SliceFasBridges.rankAffine_coord_affineOnResiduesZ
        (rank_suf_rankAffine P c) i) hDR
    refine ⟨pa * pb, Nat.mul_pos hpa hpb, ?_⟩
    exact (EP_of_dvd hEPa (dvd_mul_right pa pb)).and
      (EP_of_dvd hEPb (dvd_mul_left pb pa))
  -- the per-class kernel count
  set tieKer : ℕ → ℕ → ℕ := fun κ n =>
    ∑ c : Fin P.toPoly.K,
      ((if preCond κ c n then 1 else 0)
        + ((Finset.range n).filter (fun j : ℕ =>
            P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j) = dstarRank P hV harity n
            ∧ j % 1 = 0
            ∧ (Gdfa κ c).accepts (markAt (wrappedFlat n) (1 + 2 * j)))).card
        + ((Finset.range n).filter (fun j : ℕ =>
            P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1) = dstarRank P hV harity n
            ∧ j % 1 = 0
            ∧ (Gdfa κ c).accepts (markAt (wrappedFlat n) (1 + 2 * j + 1)))).card
        + (if sufCond κ c n then 1 else 0)) with htieKerdef
  have htieKerAff : ∀ κ, AffineOnResidues (tieKer κ) := by
    intro κ
    rw [htieKerdef]
    refine AffineOnResidues.finsetSum Finset.univ _ (fun c _ => ?_)
    refine AffineOnResidues.add (AffineOnResidues.add (AffineOnResidues.add ?_ ?_) ?_) ?_
    · obtain ⟨pp, hpp, ⟨mEP, hEP⟩⟩ := hpreEP κ c
      refine affineOnResidues_of_eventuallyPeriodic (m := mEP) (p := pp) hpp
        (fun n hn => ?_)
      rw [if_congr (hEP n hn) rfl rfl]
    · exact SliceFasCount.lexEq_count_per_region P c hDR 1 0 (le_refl 1) (Gdfa κ c)
    · exact lexEq_count_per_region_blockD P c hDR 1 0 (le_refl 1) (Gdfa κ c)
    · obtain ⟨pp, hpp, ⟨mEP, hEP⟩⟩ := hsufEP κ c
      refine affineOnResidues_of_eventuallyPeriodic (m := mEP) (p := pp) hpp
        (fun n hn => ?_)
      rw [if_congr (hEP n hn) rfl rfl]
  refine ⟨fun n => tieKer (n % p0) n, N1, ?_, ?_⟩
  · exact AffineOnResidues.select (Finset.range p0) tieKer (fun n => n % p0) p0 hp0
      (fun κ _ => htieKerAff κ) (fun n => Finset.mem_range.mpr (Nat.mod_lt _ hp0))
      (fun κ _ => ⟨0, fun n _ => by simp only []; rw [Nat.add_mod_right]⟩)
  · -- the agreement on D-present slices past the threshold
    intro n hn hD
    have hlen : (wrappedFlat n).length = 2 * (n + 1) := length_wrappedFlat n
    -- the pointwise bridge: semantic TIE condition at `(c, q)` ⟺ gate accept ∧ rank equality
    have hpoint : ∀ (c : Fin P.toPoly.K) (q : ℕ), q < (wrappedFlat n).length →
        ((P.toPoly.sel c (wrappedFlat n) (fun _ => q)
            ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
            ∧ P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩ = dstarRank P hV harity n
            ∧ ∀ b, P.toPoly.selectedAtom (wrappedFlat n) b →
                P.toPoly.labelOf (wrappedFlat n) b = D →
                P.rankOf (wrappedFlat n) b = dstarRank P hV harity n →
                P.toPoly.atomOrd (wrappedFlat n) ⟨c, fun _ => q⟩ b)
          ↔ ((Gdfa (n % p0) c).accepts (markAt (wrappedFlat n) q)
              ∧ P.rank c (wrappedFlat n) (fun _ => q) = dstarRank P hV harity n)) := by
      intro c q hq
      rw [← hGdfa (n % p0) c n q hq]
      constructor
      · rintro ⟨hs, hl, hr, hall⟩
        refine ⟨⟨⟨fun _ => hq, hs⟩, hl, ?_⟩, hr⟩
        intro b hbsel hbD hbcfg
        exact hall b hbsel hbD ((hsel n hn hD b hbsel hbD).mpr hbcfg)
      · rintro ⟨⟨hsa, hl, hall⟩, hr⟩
        refine ⟨hsa.2, hl, hr, ?_⟩
        intro b hbsel hbD hbr
        exact hall b hbsel hbD ((hsel n hn hD b hbsel hbD).mp hbr)
    show tieKer (n % p0) n = _
    rw [htieKerdef]
    simp only []
    rw [hlen]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    set g : ℕ → ℕ := fun q =>
      if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
          ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
          ∧ P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩ = dstarRank P hV harity n
          ∧ ∀ b, P.toPoly.selectedAtom (wrappedFlat n) b →
              P.toPoly.labelOf (wrappedFlat n) b = D →
              P.rankOf (wrappedFlat n) b = dstarRank P hV harity n →
              P.toPoly.atomOrd (wrappedFlat n) ⟨c, fun _ => q⟩ b)
      then 1 else 0 with hg
    rw [sum_range_wrappedFlat_split g n]
    have h1 : (if preCond (n % p0) c n then (1 : ℕ) else 0) = g 0 := by
      rw [hg]
      simp only []
      refine (if_congr ?_ rfl rfl).symm
      exact hpoint c 0 (by rw [hlen]; omega)
    have h2 : ((Finset.range n).filter (fun j : ℕ =>
          P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j) = dstarRank P hV harity n
          ∧ j % 1 = 0
          ∧ (Gdfa (n % p0) c).accepts (markAt (wrappedFlat n) (1 + 2 * j)))).card
        = ∑ j ∈ Finset.range n, g (1 + 2 * j) := by
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [hg]
      simp only []
      refine if_congr ?_ rfl rfl
      have hq : 1 + 2 * j < (wrappedFlat n).length := by rw [hlen]; omega
      have hrk := (rank_block_prefix_invariant P c n j hj).1
      rw [hpoint c (1 + 2 * j) hq]
      constructor
      · rintro ⟨hr1, _, hacc⟩
        exact ⟨hacc, by rw [hrk]; exact hr1⟩
      · rintro ⟨hacc, hr2⟩
        exact ⟨by rw [← hrk]; exact hr2, Nat.mod_one j, hacc⟩
    have h3 : ((Finset.range n).filter (fun j : ℕ =>
          P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1) = dstarRank P hV harity n
          ∧ j % 1 = 0
          ∧ (Gdfa (n % p0) c).accepts (markAt (wrappedFlat n) (1 + 2 * j + 1)))).card
        = ∑ j ∈ Finset.range n, g (1 + 2 * j + 1) := by
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [hg]
      simp only []
      refine if_congr ?_ rfl rfl
      have hq : 1 + 2 * j + 1 < (wrappedFlat n).length := by rw [hlen]; omega
      have hrk := (rank_block_prefix_invariant P c n j hj).2
      rw [hpoint c (1 + 2 * j + 1) hq]
      constructor
      · rintro ⟨hr1, _, hacc⟩
        exact ⟨hacc, by rw [hrk]; exact hr1⟩
      · rintro ⟨hacc, hr2⟩
        exact ⟨by rw [← hrk]; exact hr2, Nat.mod_one j, hacc⟩
    have h4 : (if sufCond (n % p0) c n then (1 : ℕ) else 0) = g (2 * n + 1) := by
      rw [hg]
      simp only []
      rw [show 2 * n + 1 = 1 + 2 * n from by ring]
      refine (if_congr ?_ rfl rfl).symm
      exact hpoint c (1 + 2 * n) (by rw [hlen]; omega)
    rw [h1, h2, h3, h4]

/-! ## The STRICT count is affine-on-residues -/

set_option maxHeartbeats 1600000 in
/-- **The STRICT count**: the number of selected `U`-labelled atoms whose rank is
`lexLt`-below `dstarRank n` is `AffineOnResidues` (with pointwise agreement at every
`n` — no threshold and no `D`-present hypothesis needed).  The `[sel ∧ U]` gate is
`selectedU_gate`; blockU/blockD positions by the `lexLt_below` kernels at threshold
`T := dstarRank`; pre/suf by eventually-periodic indicators via
`affineOnResiduesZ_lexLt_EP`. -/
theorem strict_count_affineOnResidues (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity : ∀ c, P.toPoly.arity c = 1) :
    ∃ strict' : ℕ → ℕ, AffineOnResidues strict' ∧
      ∀ n, strict' n = ∑ c : Fin P.toPoly.K, ∑ q ∈ Finset.range (wrappedFlat n).length,
        if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
            ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
            ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩) (dstarRank P hV harity n))
        then 1 else 0 := by
  classical
  have hDR : ∀ i, AffineOnResiduesZ (fun n => dstarRank P hV harity n i) :=
    SliceDstarBridge.dstarRank_affineOnResiduesZ P hV harity
  choose Uc hUc using fun (c : Fin P.toPoly.K) => SliceFasGates.selectedU_gate P c harity
  set preCondS : Fin P.toPoly.K → ℕ → Prop := fun c n =>
    (Uc c).accepts (markAt (wrappedFlat n) 0)
      ∧ WRP.lexLt (P.rank c (wrappedFlat n) (fun _ => 0)) (dstarRank P hV harity n)
    with hpreCondSdef
  set sufCondS : Fin P.toPoly.K → ℕ → Prop := fun c n =>
    (Uc c).accepts (markAt (wrappedFlat n) (1 + 2 * n))
      ∧ WRP.lexLt (P.rank c (wrappedFlat n) (fun _ => 1 + 2 * n)) (dstarRank P hV harity n)
    with hsufCondSdef
  have hpreEP : ∀ c, ∃ pp, 1 ≤ pp ∧ EventuallyPeriodic (preCondS c) pp := by
    intro c
    obtain ⟨pa, hpa, hEPa⟩ := accepts_pre_EP (Uc c)
    obtain ⟨pb, hpb, hEPb⟩ := SliceFasSelector.affineOnResiduesZ_lexLt_EP
      (F := fun n => P.rank c (wrappedFlat n) (fun _ => 0))
      (G := fun n => dstarRank P hV harity n)
      (fun i => SliceFasBridges.rankAffine_coord_affineOnResiduesZ
        (rank_pre_rankAffine P c) i) hDR
    exact ⟨pa * pb, Nat.mul_pos hpa hpb,
      (EP_of_dvd hEPa (dvd_mul_right pa pb)).and (EP_of_dvd hEPb (dvd_mul_left pb pa))⟩
  have hsufEP : ∀ c, ∃ pp, 1 ≤ pp ∧ EventuallyPeriodic (sufCondS c) pp := by
    intro c
    obtain ⟨pa, hpa, hEPa⟩ := SliceDstar.selS_EP (Uc c)
    obtain ⟨pb, hpb, hEPb⟩ := SliceFasSelector.affineOnResiduesZ_lexLt_EP
      (F := fun n => P.rank c (wrappedFlat n) (fun _ => 1 + 2 * n))
      (G := fun n => dstarRank P hV harity n)
      (fun i => SliceFasBridges.rankAffine_coord_affineOnResiduesZ
        (rank_suf_rankAffine P c) i) hDR
    exact ⟨pa * pb, Nat.mul_pos hpa hpb,
      (EP_of_dvd hEPa (dvd_mul_right pa pb)).and (EP_of_dvd hEPb (dvd_mul_left pb pa))⟩
  refine ⟨fun n => ∑ c : Fin P.toPoly.K,
    ((if preCondS c n then 1 else 0)
      + ((Finset.range n).filter (fun j : ℕ =>
          WRP.lexLt (P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j))
            (dstarRank P hV harity n)
          ∧ (Uc c).accepts (markAt (wrappedFlat n) (1 + 2 * j)))).card
      + ((Finset.range n).filter (fun j : ℕ =>
          WRP.lexLt (P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1))
            (dstarRank P hV harity n)
          ∧ (Uc c).accepts (markAt (wrappedFlat n) (1 + 2 * j + 1)))).card
      + (if sufCondS c n then 1 else 0)), ?_, ?_⟩
  · refine AffineOnResidues.finsetSum Finset.univ _ (fun c _ => ?_)
    refine AffineOnResidues.add (AffineOnResidues.add (AffineOnResidues.add ?_ ?_) ?_) ?_
    · obtain ⟨pp, hpp, ⟨mEP, hEP⟩⟩ := hpreEP c
      refine affineOnResidues_of_eventuallyPeriodic (m := mEP) (p := pp) hpp
        (fun n hn => ?_)
      rw [if_congr (hEP n hn) rfl rfl]
    · exact SliceFasCount.lexLt_below_count_per_region P c hDR (Uc c)
    · exact lexLt_below_count_per_region_blockD P c hDR (Uc c)
    · obtain ⟨pp, hpp, ⟨mEP, hEP⟩⟩ := hsufEP c
      refine affineOnResidues_of_eventuallyPeriodic (m := mEP) (p := pp) hpp
        (fun n hn => ?_)
      rw [if_congr (hEP n hn) rfl rfl]
  · intro n
    have hlen : (wrappedFlat n).length = 2 * (n + 1) := length_wrappedFlat n
    have hpoint : ∀ (c : Fin P.toPoly.K) (q : ℕ), q < (wrappedFlat n).length →
        ((P.toPoly.sel c (wrappedFlat n) (fun _ => q)
            ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
            ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩) (dstarRank P hV harity n))
          ↔ ((Uc c).accepts (markAt (wrappedFlat n) q)
              ∧ WRP.lexLt (P.rank c (wrappedFlat n) (fun _ => q))
                  (dstarRank P hV harity n))) := by
      intro c q hq
      rw [← hUc c n q hq]
      constructor
      · rintro ⟨hs, hl, hr⟩
        exact ⟨⟨⟨fun _ => hq, hs⟩, hl⟩, hr⟩
      · rintro ⟨⟨hsa, hl⟩, hr⟩
        exact ⟨hsa.2, hl, hr⟩
    rw [hlen]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    set g : ℕ → ℕ := fun q =>
      if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
          ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
          ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩) (dstarRank P hV harity n))
      then 1 else 0 with hg
    rw [sum_range_wrappedFlat_split g n]
    have h1 : (if preCondS c n then (1 : ℕ) else 0) = g 0 := by
      rw [hg]
      simp only []
      refine (if_congr ?_ rfl rfl).symm
      exact hpoint c 0 (by rw [hlen]; omega)
    have h2 : ((Finset.range n).filter (fun j : ℕ =>
          WRP.lexLt (P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j))
            (dstarRank P hV harity n)
          ∧ (Uc c).accepts (markAt (wrappedFlat n) (1 + 2 * j)))).card
        = ∑ j ∈ Finset.range n, g (1 + 2 * j) := by
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [hg]
      simp only []
      refine if_congr ?_ rfl rfl
      have hq : 1 + 2 * j < (wrappedFlat n).length := by rw [hlen]; omega
      have hrk := (rank_block_prefix_invariant P c n j hj).1
      rw [hpoint c (1 + 2 * j) hq]
      constructor
      · rintro ⟨hr1, hacc⟩
        exact ⟨hacc, by rw [hrk]; exact hr1⟩
      · rintro ⟨hacc, hr2⟩
        exact ⟨by rw [← hrk]; exact hr2, hacc⟩
    have h3 : ((Finset.range n).filter (fun j : ℕ =>
          WRP.lexLt (P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1))
            (dstarRank P hV harity n)
          ∧ (Uc c).accepts (markAt (wrappedFlat n) (1 + 2 * j + 1)))).card
        = ∑ j ∈ Finset.range n, g (1 + 2 * j + 1) := by
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [hg]
      simp only []
      refine if_congr ?_ rfl rfl
      have hq : 1 + 2 * j + 1 < (wrappedFlat n).length := by rw [hlen]; omega
      have hrk := (rank_block_prefix_invariant P c n j hj).2
      rw [hpoint c (1 + 2 * j + 1) hq]
      constructor
      · rintro ⟨hr1, hacc⟩
        exact ⟨hacc, by rw [hrk]; exact hr1⟩
      · rintro ⟨hacc, hr2⟩
        exact ⟨by rw [← hrk]; exact hr2, hacc⟩
    have h4 : (if sufCondS c n then (1 : ℕ) else 0) = g (2 * n + 1) := by
      rw [hg]
      simp only []
      rw [show 2 * n + 1 = 1 + 2 * n from by ring]
      refine (if_congr ?_ rfl rfl).symm
      exact hpoint c (1 + 2 * n) (by rw [hlen]; omega)
    rw [h1, h2, h3, h4]

/-! ## L7: the `fas` count is affine-on-residues past a threshold -/

set_option maxHeartbeats 1600000 in
/-- **`fas_count_affineOnResidues`** (route step L7 = original build-order step 9).
There is an `AffineOnResidues` function agreeing with
`SliceProfileDischarge.fasCount` past a threshold.

On a `D`-present slice the per-atom `fas` condition splits by lex-trichotomy of the
atom's rank against `dstarRank n`: strictly below ⇒ the inner `∀` collapses to true
(`fas_inner_collapse`), equal ⇒ the keystone `fas_member_eqRank` turns it into the L6
TIE condition, strictly above ⇒ false.  So `fasCount = STRICT + TIE` there
(`strict_count_affineOnResidues` + `tie_count_affineOnResidues`); on a `D`-absent slice
every selected atom is labelled `U` (`Gamma = Step`), so `fasCount = totalSelectedU`
(`totalSelected_slice_affineOnResidues`).  The two regimes combine by
`AffineOnResidues.select` along the eventually periodic `D`-present gate
(`Dpresent_eventuallyPeriodic`).  Base `+ SliceMSO.buchi`. -/
theorem fas_count_affineOnResidues (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity : ∀ c, P.toPoly.arity c = 1) :
    ∃ (fas' : ℕ → ℕ) (N : ℕ), AffineOnResidues fas' ∧
      ∀ n, N ≤ n → fas' n = SliceProfileDischarge.fasCount P n := by
  classical
  obtain ⟨tie', N1, htieAff, htieAgr⟩ := tie_count_affineOnResidues P hV harity
  obtain ⟨strict', hstrictAff, hstrictAgr⟩ := strict_count_affineOnResidues P hV harity
  have htotAff := totalSelected_slice_affineOnResidues P.toPoly U harity
  obtain ⟨pD, hpD, hDEP⟩ := SliceDstar.Dpresent_eventuallyPeriodic P
  set DP : ℕ → Prop := fun n => ∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧
    P.toPoly.labelOf (wrappedFlat n) a = D with hDPdef
  set selb : ℕ → Bool := fun n => decide (DP n) with hselbdef
  set tot : ℕ → ℕ := fun n =>
    ∑ c : Fin P.toPoly.K, ∑ p ∈ Finset.range (wrappedFlat n).length,
      if (P.toPoly.sel c (wrappedFlat n) (fun _ => p)
          ∧ P.toPoly.label c (wrappedFlat n) (fun _ => p) = U) then 1 else 0 with htotdef
  set f : Bool → ℕ → ℕ := fun b => if b then (fun n => strict' n + tie' n) else tot
    with hfdef
  refine ⟨fun n => f (selb n) n, N1, ?_, ?_⟩
  · refine AffineOnResidues.select Finset.univ f selb pD hpD (fun b _ => ?_)
      (fun n => Finset.mem_univ _) (fun b _ => ?_)
    · cases b
      · exact htotAff
      · exact AffineOnResidues.add hstrictAff htieAff
    · cases b
      · exact (SliceDstarCore.EP_not hDEP).congr
          (fun n => (decide_eq_false_iff_not).symm)
      · exact hDEP.congr (fun n => (decide_eq_true_iff).symm)
  · intro n hn
    have hlen : (wrappedFlat n).length = 2 * (n + 1) := length_wrappedFlat n
    by_cases hDp : DP n
    · -- D-present: fasCount = STRICT + TIE
      have hsb : selb n = true := by
        rw [hselbdef]
        simp only []
        exact decide_eq_true hDp
      obtain ⟨dstar, hdsel, hdD, hdmin, hdrank⟩ := dstarRank_spec P hV harity n hDp
      have hsplit : ∀ (c : Fin P.toPoly.K) (q : ℕ), q < (wrappedFlat n).length →
          ((if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
              ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
              ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
                  (P.toPoly.label b.1 (wrappedFlat n) b.2 = U
                    ∨ P.wrpOrd (wrappedFlat n) ⟨c, fun _ => q⟩ b)) then 1 else 0) : ℕ)
            = (if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
                ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
                ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩)
                    (dstarRank P hV harity n)) then 1 else 0)
              + (if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
                  ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
                  ∧ P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩ = dstarRank P hV harity n
                  ∧ ∀ b, P.toPoly.selectedAtom (wrappedFlat n) b →
                      P.toPoly.labelOf (wrappedFlat n) b = D →
                      P.rankOf (wrappedFlat n) b = dstarRank P hV harity n →
                      P.toPoly.atomOrd (wrappedFlat n) ⟨c, fun _ => q⟩ b)
                then 1 else 0) := by
        intro c q hq
        set A : Prop := (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
          ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
              (P.toPoly.label b.1 (wrappedFlat n) b.2 = U
                ∨ P.wrpOrd (wrappedFlat n) ⟨c, fun _ => q⟩ b)) with hAdef
        set B : Prop := (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
          ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
          ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩)
              (dstarRank P hV harity n)) with hBdef
        set C : Prop := (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
          ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
          ∧ P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩ = dstarRank P hV harity n
          ∧ ∀ b, P.toPoly.selectedAtom (wrappedFlat n) b →
              P.toPoly.labelOf (wrappedFlat n) b = D →
              P.rankOf (wrappedFlat n) b = dstarRank P hV harity n →
              P.toPoly.atomOrd (wrappedFlat n) ⟨c, fun _ => q⟩ b) with hCdef
        by_cases hsU : P.toPoly.sel c (wrappedFlat n) (fun _ => q)
            ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
        · have hasel : P.toPoly.selectedAtom (wrappedFlat n) ⟨c, fun _ => q⟩ :=
            ⟨fun _ => hq, hsU.1⟩
          have hcoll := SliceOutput.fas_inner_collapse P hV (wrappedFlat n) dstar hdsel hdD
            hdmin ⟨c, fun _ => q⟩ hasel
          rcases SliceLexOrder.lexLt_trichot (P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩)
              (dstarRank P hV harity n) with hlt | heq | hgt
          · -- strictly below: the fas condition holds, the TIE one does not
            have hA : A := by
              rw [hAdef]
              exact ⟨hsU.1, hsU.2, hcoll.mpr (Or.inl (by rw [← hdrank]; exact hlt))⟩
            have hB : B := by
              rw [hBdef]
              exact ⟨hsU.1, hsU.2, hlt⟩
            have hC : ¬ C := by
              rw [hCdef]
              rintro ⟨_, _, hreq, _⟩
              exact SliceFasCount.lexLt_ne hlt hreq
            rw [if_pos hA, if_pos hB, if_neg hC]
          · -- equal rank: the fas condition is the TIE condition (keystone)
            have hrankeq : P.rankOf (wrappedFlat n) (⟨c, fun _ => q⟩ : P.toPoly.Atom)
                = P.rankOf (wrappedFlat n) dstar := by rw [heq, hdrank]
            have hkey := SliceFasTie.fas_member_eqRank P hV (wrappedFlat n) dstar hdsel hdD
              hdmin ⟨c, fun _ => q⟩ hasel hrankeq
            have hiff : A ↔ C := by
              rw [hAdef, hCdef]
              constructor
              · rintro ⟨hs, hl, hall⟩
                refine ⟨hs, hl, heq, fun b hb hbD hbr => ?_⟩
                exact (hkey.mp hall) b hb hbD (by rw [← hdrank]; exact hbr)
              · rintro ⟨hs, hl, _, hall⟩
                refine ⟨hs, hl, hkey.mpr (fun b hb hbD hbr => ?_)⟩
                exact hall b hb hbD (by rw [hdrank]; exact hbr)
            have hB : ¬ B := by
              rw [hBdef]
              rintro ⟨_, _, hl⟩
              rw [heq] at hl
              exact SliceLexOrder.lexLt_irrefl _ hl
            rw [if_congr hiff rfl rfl, if_neg hB, Nat.zero_add]
          · -- strictly above: nothing holds
            have hA : ¬ A := by
              rw [hAdef]
              rintro ⟨_, _, hall⟩
              rcases hcoll.mp hall with hl | ⟨he, _⟩
              · refine SliceDstar.lexLt_asymm _ _ hgt ?_
                rw [hdrank]
                exact hl
              · refine SliceLexOrder.lexLt_irrefl (dstarRank P hV harity n) ?_
                have he' : P.rankOf (wrappedFlat n) (⟨c, fun _ => q⟩ : P.toPoly.Atom)
                    = dstarRank P hV harity n := by rw [he, ← hdrank]
                rw [he'] at hgt
                exact hgt
            have hB : ¬ B := by
              rw [hBdef]
              rintro ⟨_, _, hl⟩
              exact SliceDstar.lexLt_asymm _ _ hgt hl
            have hC : ¬ C := by
              rw [hCdef]
              rintro ⟨_, _, hreq, _⟩
              rw [hreq] at hgt
              exact SliceLexOrder.lexLt_irrefl _ hgt
            rw [if_neg hA, if_neg hB, if_neg hC]
        · have hA : ¬ A := by
            rw [hAdef]
            exact fun hcon => hsU ⟨hcon.1, hcon.2.1⟩
          have hB : ¬ B := by
            rw [hBdef]
            exact fun hcon => hsU ⟨hcon.1, hcon.2.1⟩
          have hC : ¬ C := by
            rw [hCdef]
            exact fun hcon => hsU ⟨hcon.1, hcon.2.1⟩
          rw [if_neg hA, if_neg hB, if_neg hC]
      show f (selb n) n = _
      rw [hsb]
      show strict' n + tie' n = _
      calc strict' n + tie' n
          = (∑ c : Fin P.toPoly.K, ∑ q ∈ Finset.range (wrappedFlat n).length,
              if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
                  ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
                  ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩)
                      (dstarRank P hV harity n)) then 1 else 0)
            + (∑ c : Fin P.toPoly.K, ∑ q ∈ Finset.range (wrappedFlat n).length,
              if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
                  ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
                  ∧ P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩ = dstarRank P hV harity n
                  ∧ ∀ b, P.toPoly.selectedAtom (wrappedFlat n) b →
                      P.toPoly.labelOf (wrappedFlat n) b = D →
                      P.rankOf (wrappedFlat n) b = dstarRank P hV harity n →
                      P.toPoly.atomOrd (wrappedFlat n) ⟨c, fun _ => q⟩ b)
                then 1 else 0) := by
            rw [hstrictAgr n, htieAgr n hn hDp]
        _ = ∑ c : Fin P.toPoly.K, ((∑ q ∈ Finset.range (wrappedFlat n).length,
              if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
                  ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
                  ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩)
                      (dstarRank P hV harity n)) then 1 else 0)
            + (∑ q ∈ Finset.range (wrappedFlat n).length,
              if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
                  ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
                  ∧ P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩ = dstarRank P hV harity n
                  ∧ ∀ b, P.toPoly.selectedAtom (wrappedFlat n) b →
                      P.toPoly.labelOf (wrappedFlat n) b = D →
                      P.rankOf (wrappedFlat n) b = dstarRank P hV harity n →
                      P.toPoly.atomOrd (wrappedFlat n) ⟨c, fun _ => q⟩ b)
                then 1 else 0)) := Finset.sum_add_distrib.symm
        _ = ∑ c : Fin P.toPoly.K, ∑ q ∈ Finset.range (wrappedFlat n).length,
              ((if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
                  ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
                  ∧ WRP.lexLt (P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩)
                      (dstarRank P hV harity n)) then 1 else 0)
              + (if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
                  ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
                  ∧ P.rankOf (wrappedFlat n) ⟨c, fun _ => q⟩ = dstarRank P hV harity n
                  ∧ ∀ b, P.toPoly.selectedAtom (wrappedFlat n) b →
                      P.toPoly.labelOf (wrappedFlat n) b = D →
                      P.rankOf (wrappedFlat n) b = dstarRank P hV harity n →
                      P.toPoly.atomOrd (wrappedFlat n) ⟨c, fun _ => q⟩ b)
                then 1 else 0)) :=
            Finset.sum_congr rfl (fun c _ => Finset.sum_add_distrib.symm)
        _ = ∑ c : Fin P.toPoly.K, ∑ q ∈ Finset.range (wrappedFlat n).length,
              if (P.toPoly.sel c (wrappedFlat n) (fun _ => q)
                  ∧ P.toPoly.label c (wrappedFlat n) (fun _ => q) = U
                  ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
                      (P.toPoly.label b.1 (wrappedFlat n) b.2 = U
                        ∨ P.wrpOrd (wrappedFlat n) ⟨c, fun _ => q⟩ b)) then 1 else 0 :=
            Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
              (fun q hq => (hsplit c q (Finset.mem_range.mp hq)).symm))
        _ = SliceProfileDischarge.fasCount P n := rfl
    · -- D-absent: fasCount = totalSelectedU
      have hsb : selb n = false := by
        rw [hselbdef]
        simp only []
        exact decide_eq_false hDp
      show f (selb n) n = _
      rw [hsb]
      show tot n = _
      rw [htotdef]
      simp only []
      refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun q hq => ?_))
      refine (if_congr ?_ rfl rfl).symm
      constructor
      · rintro ⟨hs, hl, _⟩
        exact ⟨hs, hl⟩
      · rintro ⟨hs, hl⟩
        refine ⟨hs, hl, fun b hbsel => ?_⟩
        cases hlb : P.toPoly.labelOf (wrappedFlat n) b with
        | U => exact Or.inl hlb
        | D => exact absurd ⟨b, hbsel, hlb⟩ hDp

/-! ## Step 10: the `tailU` count -/

/-- **`tailU_count_affineOnResidues`** (route step 10).  The complement count
`tailUCount` is `AffineOnResidues` past the same threshold: by the partition
`totalSelectedU = fasCount + tailUCount` (`totalSelectedU_eq_fas_add_tail`) and the
`sub_of_partition` closure, after patching the `fas` witness below the threshold. -/
theorem tailU_count_affineOnResidues (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity : ∀ c, P.toPoly.arity c = 1) :
    ∃ (tail' : ℕ → ℕ) (N : ℕ), AffineOnResidues tail' ∧
      ∀ n, N ≤ n → tail' n = SliceProfileDischarge.tailUCount P n := by
  classical
  obtain ⟨fas', N, hfasAff, hfasAgr⟩ := fas_count_affineOnResidues P hV harity
  have htotAff := totalSelected_slice_affineOnResidues P.toPoly U harity
  set tot : ℕ → ℕ := fun n =>
    ∑ c : Fin P.toPoly.K, ∑ p ∈ Finset.range (wrappedFlat n).length,
      if (P.toPoly.sel c (wrappedFlat n) (fun _ => p)
          ∧ P.toPoly.label c (wrappedFlat n) (fun _ => p) = U) then 1 else 0 with htotdef
  set fas'' : ℕ → ℕ := fun n =>
    if n < N then SliceProfileDischarge.fasCount P n else fas' n with hfas''def
  have hfas''Aff : AffineOnResidues fas'' := by
    refine AffineOnResidues.congr_eventually (N := N) (fun n hn => ?_) hfasAff
    rw [hfas''def]
    simp only []
    rw [if_neg (by omega)]
  have hpart : ∀ n, tot n = fas'' n + (tot n - fas'' n) := by
    intro n
    have htt : tot n = SliceProfileDischarge.fasCount P n
        + SliceProfileDischarge.tailUCount P n :=
      SliceProfileDischarge.totalSelectedU_eq_fas_add_tail P n
    rw [hfas''def]
    simp only []
    by_cases hlt : n < N
    · rw [if_pos hlt]
      omega
    · rw [if_neg hlt]
      have := hfasAgr n (by omega)
      omega
  have htailAff := SliceFasCount.AffineOnResidues.sub_of_partition htotAff hfas''Aff hpart
  refine ⟨fun n => tot n - fas'' n, N, htailAff, fun n hn => ?_⟩
  have htt : tot n = SliceProfileDischarge.fasCount P n
      + SliceProfileDischarge.tailUCount P n :=
    SliceProfileDischarge.totalSelectedU_eq_fas_add_tail P n
  have hagr := hfasAgr n hn
  rw [hfas''def]
  simp only []
  rw [if_neg (by omega)]
  omega

/-! ## Step 14: the arity-1 capstone -/

/-- The slice domain bit of a polyregular presentation is eventually periodic in `n`
(`domainDef` + `mso_slice_eventuallyPeriodic`). -/
theorem domain_slice_EP (Q : Polyreg.Presentation Step Step) :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ n, m ≤ n →
      (Q.domain (wrappedFlat (n + p)) ↔ Q.domain (wrappedFlat n)) := by
  obtain ⟨φ, hφ⟩ := Q.domainDef
  obtain ⟨m, p, hp, hper⟩ := SliceMSO.mso_slice_eventuallyPeriodic φ [U] [U, D] [D]
  refine ⟨m, p, hp, fun n hn => ?_⟩
  rw [hφ, hφ]
  exact hper n hn

set_option maxHeartbeats 1600000 in
/-- **`wrp_slice_profile_affine_arity1`** (route step 14, the CAPSTONE).  The arity-1
instance of the §7 slice-analysis statement, **proved**: for a `Valid` arity-1 WRP
presentation realising `T` (with some slice in the domain — the slice-realizedness
hypothesis matching the session-4 soundness fix of the axiom), the slice profile of `T`
is the graph of a function affine on residue classes of `n`.

This is exactly the conclusion shape of the axiom `wrp_slice_profile_affine` (which is
keyed to the abstract `IsWRP` with no arity hypothesis — so this theorem discharges the
*mathematical content* in the arity-1 case but does not term-replace the axiom; the
`hgrow` hypothesis of the axiom is not needed here).  `g` is the `fasCount`/`tailUCount`
pair on in-domain slices and a fixed realized profile point elsewhere; affineness on each
residue class comes from L7/step 10 + the eventually periodic domain bit, and the set
equality from `exists_isOutput_slice` + `fas_eq_firstAscent_out`.
Base `+ SliceMSO.buchi`. -/
theorem wrp_slice_profile_affine_arity1
    (T : List Step → Option (List Step))
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity : ∀ c, P.toPoly.arity c = 1)
    (hPT : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    (hne : ∃ n : ℕ, 1 ≤ n ∧ ∃ out, T (wrappedFlat n) = some out) :
    ∃ (g : ℕ → ℕ × ℕ) (p m : ℕ), 1 ≤ p ∧ 1 ≤ m ∧
      (∀ j, j < p → ∃ b₁ s₁ b₂ s₂ : ℕ,
        ∀ k, g (m + j + p * k) = (b₁ + k * s₁, b₂ + k * s₂)) ∧
      sliceProfile T = {q : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧ q = g n} := by
  classical
  obtain ⟨n₀, hn₀1, out₀, hTout₀⟩ := hne
  obtain ⟨fas', Nf, hfasAff, hfasAgr⟩ := fas_count_affineOnResidues P hV harity
  obtain ⟨tail', Nt, htailAff, htailAgr⟩ := tailU_count_affineOnResidues P hV harity
  obtain ⟨mf, pf, sf, hpf, hfrec⟩ := hfasAff
  obtain ⟨mt, pt, st, hpt, htrec⟩ := htailAff
  obtain ⟨mD, pD, hpD, hDper⟩ := domain_slice_EP P.toPoly
  set fb : ℕ × ℕ := (firstAscent out₀, tailU out₀) with hfbdef
  set g : ℕ → ℕ × ℕ := fun n =>
    if P.toPoly.domain (wrappedFlat n)
    then (SliceProfileDischarge.fasCount P n, SliceProfileDischarge.tailUCount P n)
    else fb with hgdef
  set p : ℕ := pf * pt * pD with hpdef
  have hp : 1 ≤ p := by rw [hpdef]; exact Nat.mul_pos (Nat.mul_pos hpf hpt) hpD
  set m : ℕ := mf + mt + mD + Nf + Nt + 1 with hmdef
  have hmge : mf ≤ m ∧ mt ≤ m ∧ mD ≤ m ∧ Nf ≤ m ∧ Nt ≤ m ∧ 1 ≤ m := by
    rw [hmdef]; omega
  have hpfd : pf ∣ p := by rw [hpdef]; exact (dvd_mul_right pf pt).mul_right pD
  have hptd : pt ∣ p := by rw [hpdef]; exact (dvd_mul_left pt pf).mul_right pD
  have hpDd : pD ∣ p := by rw [hpdef]; exact dvd_mul_left pD (pf * pt)
  refine ⟨g, p, m, hp, hmge.2.2.2.2.2, ?_, ?_⟩
  · -- per-class affineness
    intro j hj
    have hdomconst : ∀ k, (P.toPoly.domain (wrappedFlat (m + j + p * k))
        ↔ P.toPoly.domain (wrappedFlat (m + j))) := by
      intro k
      refine SliceFasSelector.iff_on_class
        (Pr := fun x => P.toPoly.domain (wrappedFlat x)) hpD hDper
        (by omega) (by omega) ?_
      obtain ⟨t, ht⟩ := hpDd
      rw [ht, show m + j + pD * t * k = m + j + pD * (t * k) from by ring,
        Nat.add_mul_mod_self_left]
    by_cases hcl : P.toPoly.domain (wrappedFlat (m + j))
    · -- in-domain class: ride the fas/tail affine witnesses
      obtain ⟨tf, htf⟩ := hpfd
      obtain ⟨tt, htt⟩ := hptd
      refine ⟨fas' (m + j), tf * sf (m + j - mf), tail' (m + j), tt * st (m + j - mt),
        fun k => ?_⟩
      have hdomk := (hdomconst k).mpr hcl
      have hfas_affine : fas' (m + j + p * k)
          = fas' (m + j) + k * (tf * sf (m + j - mf)) := by
        have h := hfrec (m + j - mf) (tf * k)
        rw [show mf + (m + j - mf) = m + j from by omega] at h
        rw [show m + j + p * k = m + j + pf * (tf * k) from by rw [htf]; ring, h]
        ring
      have htail_affine : tail' (m + j + p * k)
          = tail' (m + j) + k * (tt * st (m + j - mt)) := by
        have h := htrec (m + j - mt) (tt * k)
        rw [show mt + (m + j - mt) = m + j from by omega] at h
        rw [show m + j + p * k = m + j + pt * (tt * k) from by rw [htt]; ring, h]
        ring
      have hfask : SliceProfileDischarge.fasCount P (m + j + p * k)
          = fas' (m + j + p * k) := (hfasAgr _ (by omega)).symm
      have htailk : SliceProfileDischarge.tailUCount P (m + j + p * k)
          = tail' (m + j + p * k) := (htailAgr _ (by omega)).symm
      rw [hgdef]
      simp only []
      rw [if_pos hdomk, hfask, htailk, hfas_affine, htail_affine]
    · -- out-of-domain class: the constant fallback
      refine ⟨fb.1, 0, fb.2, 0, fun k => ?_⟩
      rw [hgdef]
      simp only []
      rw [if_neg (fun hcon => hcl ((hdomconst k).mp hcon))]
      simp
  · -- the slice-profile set equality
    ext q
    simp only [sliceProfile, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn1, out, hTout, hq⟩
      obtain ⟨hdom, hIsOut⟩ := (hPT _ _).mp hTout
      obtain ⟨hfa, hta⟩ :=
        SliceProfileDischarge.fas_eq_firstAscent_out P hV harity n out hIsOut
      refine ⟨n, hn1, ?_⟩
      rw [hq, hgdef]
      simp only []
      rw [if_pos hdom, ← hfa, ← hta]
    · rintro ⟨n, hn1, hq⟩
      by_cases hdom : P.toPoly.domain (wrappedFlat n)
      · obtain ⟨out, hIsOut⟩ := SliceProfileDischarge.exists_isOutput_slice P hV harity n
        obtain ⟨hfa, hta⟩ :=
          SliceProfileDischarge.fas_eq_firstAscent_out P hV harity n out hIsOut
        refine ⟨n, hn1, out, (hPT _ _).mpr ⟨hdom, hIsOut⟩, ?_⟩
        rw [hq, hgdef]
        simp only []
        rw [if_pos hdom, ← hfa, ← hta]
      · refine ⟨n₀, hn₀1, out₀, hTout₀, ?_⟩
        rw [hq, hgdef]
        simp only []
        rw [if_neg hdom, hfbdef]

end SliceFasAssembly
