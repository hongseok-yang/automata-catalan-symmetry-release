/-
# The fibred equal-rank cell selector (§9 tower, Stage F3.7)

The fibred / copied-slice twin of `SliceFasSelectorGA.eqRankD_cell_selector`.
For a WRP-realised, growth-bounded presentation, on the copied slice
`copiedSlice mS n` every selected `D`-atom of EQUAL rank to the d*-rank
`dstarRankGA_m` is captured by a two-arm cell premise `cfgCellGAF`: a bulk arm
over `RegionSpecF B` descriptors carrying residue data `S₁`, and a frozen arm
at the enlarged bound `Bh` carrying singleton data `F₂`.  Per decision D12 the
position clause `cfgPos` is evaluated in REDUCED wrapped coordinates (base
`1 + 2t`, length `2(n+1)`) while the cell EQUALITY is in COPIED coordinates
(`cellTupleF rs mS t n`); per D3 the class period is `p0 = p * pstar * p3`,
the product of the three machine-level periods (bulk setup, the d*-witness pin,
the frozen setup) — every equal-rank EP family divides it.
-/
import RequestProject.CopiedDstarC
import RequestProject.CopiedTieGate
import RequestProject.CopiedTieGateF
import RequestProject.CopiedTieBridge
import RequestProject.SliceFasSelector
import RequestProject.SliceFasSelectorGA
import RequestProject.CopiedRegionF
import RequestProject.CopiedSetup
import RequestProject.CopiedAffineAt

namespace CopiedSelector

open WRP Step MSOMarkN SliceMarkN SliceMSO CopiedCells CopiedDstar CopiedRegionF CopiedAffineAt
open scoped Classical

/-- **One arm of the fibred GA cell premise** (D12: REDUCED coordinates).  The
fibred twin of `SliceFasGatesGA.cfgCellArm`.  The atom `b` is in fibred cell
form over `RegionSpecF Dd` descriptors VALID at boundary width `mS`; the landed
`cfgPos` is evaluated in REDUCED wrapped coordinates (base `1 + 2*t`, length
`(wrappedFlat n).length = 2(n+1)`), while the cell EQUALITY stays in COPIED
coordinates (`cellTupleF rs mS t n`).  The range guard is `t + Dd ≤ n`
(matching `cells_cover_fibred`). -/
def cfgCellArmF {P : WRP.Presentation Step Step} (Dd M mthr : ℕ)
    (S Front Back : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Dd) → Finset ℕ)
    (mS n : ℕ) (b : P.toPoly.Atom) : Prop :=
  ∃ (rs : Fin (P.toPoly.arity b.1) → CopiedCells.RegionSpecF Dd) (t : ℕ),
    (∀ i, (rs i).valid mS) ∧
    t + Dd ≤ n ∧
    b.2 = CopiedDstar.cellTupleF rs mS t n ∧
    SliceFasGates.cfgPos M mthr (S b.1 rs) (Front b.1 rs) (Back b.1 rs)
      (wrappedFlat n).length (1 + 2 * t)

/-- **The fibred GA cell premise** (the fibred twin of `cfgCellGA`): the
two-layer disjunction — the bulk arm over `RegionSpecF B` descriptors carrying
`S₁`, the frozen arm at the enlarged `Bh` carrying `F₂`.  The other Front/Back
slots are FUNCTION-VALUED empty Finsets (`fun _ _ => ∅`, NOT `∅`, since the slot
type is a function). -/
def cfgCellGAF {P : WRP.Presentation Step Step} (B Bh M mthr : ℕ)
    (S1 : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (F2 : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (mS n : ℕ) (b : P.toPoly.Atom) : Prop :=
  cfgCellArmF B M mthr S1 (fun _ _ => ∅) (fun _ _ => ∅) mS n b ∨
  cfgCellArmF Bh M mthr (fun _ _ => ∅) F2 (fun _ _ => ∅) mS n b

/-- **Forward arm bridge, bulk shape** (`cfgPos`→`cfgPosL`): a bulk cell arm in REDUCED
wrapped coordinates lifts to the COPIED landmark `cfgPosL` arm with reflected residues and
the window threshold shifted by `-2` (the empty front/back slots stay empty). -/
theorem cfgCellArmF_imp_FL_bulk {P : WRP.Presentation Step Step} (B M mthr : ℕ)
    (S1 : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (mS n : ℕ) (b : P.toPoly.Atom) (hM : 1 ≤ M) (hm : 1 ≤ mS) (hB : 1 ≤ B)
    (hmthr : 2 ≤ mthr)
    (h : cfgCellArmF B M mthr S1 (fun _ _ => ∅) (fun _ _ => ∅) mS n b) :
    CopiedTieGate.cfgCellArmFL B M (mthr - 2)
      (fun c' rs => (S1 c' rs).image (fun s => (M + 2 - s) % M))
      (fun _ _ => ∅) (fun _ _ => ∅) mS n b := by
  obtain ⟨rs, t, hv, htDd, hcell, hcfg⟩ := h
  rw [length_wrappedFlat] at hcfg
  refine ⟨rs, t, hv, by omega, hcell, ?_⟩
  have hb := CopiedTieBridge.cfgPos_imp_cfgPosL M mthr (S1 b.1 rs) ∅ ∅ mS n t hM hm
    (by omega) hmthr hcfg
  simpa [Finset.image_empty] using hb

/-- **Forward arm bridge, frozen shape**: the frozen (front) cell arm lifts to the `cfgPosL`
front arm with the front offset shifted by `-2`. -/
theorem cfgCellArmF_imp_FL_frozen {P : WRP.Presentation Step Step} (Bh M mthr : ℕ)
    (F2 : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (mS n : ℕ) (b : P.toPoly.Atom) (hM : 1 ≤ M) (hm : 1 ≤ mS) (hBh : 1 ≤ Bh)
    (hmthr : 2 ≤ mthr)
    (h : cfgCellArmF Bh M mthr (fun _ _ => ∅) F2 (fun _ _ => ∅) mS n b) :
    CopiedTieGate.cfgCellArmFL Bh M (mthr - 2)
      (fun _ _ => ∅) (fun c' rs => (F2 c' rs).image (fun f => f - 2))
      (fun _ _ => ∅) mS n b := by
  obtain ⟨rs, t, hv, htDd, hcell, hcfg⟩ := h
  rw [length_wrappedFlat] at hcfg
  refine ⟨rs, t, hv, by omega, hcell, ?_⟩
  have hb := CopiedTieBridge.cfgPos_imp_cfgPosL M mthr ∅ (F2 b.1 rs) ∅ mS n t hM hm
    (by omega) hmthr hcfg
  simpa [Finset.image_empty] using hb

/-- **Forward two-layer bridge**: the selector's `cfgCellGAF` (cfgPos) implies the gate's
`cfgCellGAFL` (cfgPosL) with reflected residues / shifted offsets. -/
theorem cfgCellGAF_imp_cfgCellGAFL {P : WRP.Presentation Step Step} (B Bh M mthr : ℕ)
    (S1 : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
    (F2 : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
    (mS n : ℕ) (b : P.toPoly.Atom) (hM : 1 ≤ M) (hm : 1 ≤ mS) (hB : 1 ≤ B) (hBh : 1 ≤ Bh)
    (hmthr : 2 ≤ mthr)
    (h : cfgCellGAF B Bh M mthr S1 F2 mS n b) :
    CopiedTieGate.cfgCellGAFL B Bh M (mthr - 2)
      (fun c' rs => (S1 c' rs).image (fun s => (M + 2 - s) % M)) (fun _ _ => ∅) (fun _ _ => ∅)
      (fun _ _ => ∅) (fun c' rs => (F2 c' rs).image (fun f => f - 2)) (fun _ _ => ∅) mS n b := by
  rcases h with ha | ha
  · exact Or.inl (cfgCellArmF_imp_FL_bulk B M mthr S1 mS n b hM hm hB hmthr ha)
  · exact Or.inr (cfgCellArmF_imp_FL_frozen Bh M mthr F2 mS n b hM hm hBh hmthr ha)

/-- **The self-contained fibred selector** (F3.7, the fibred twin of
`SliceFasSelectorGA.eqRankD_cell_selector'`).  Six period/structure constants
`(B Bh M mthr pstar p0)` are quantified BEFORE both `C` and `mS`; the iff is
against the SEMANTIC fibred d*-rank `dstarRankGA_m P hV mS n` (D13); the RHS
gate is the 2-arm `cfgCellGAF`.  `pstar ∣ p0` is exposed in-statement; per D3
the witness `p0 = p * pstar * p3` is the product of the three machine-level
periods, so every equal-rank EP family divides it. -/
theorem eqRankD_cell_selector_fibred (P : WRP.Presentation Step Step)
    (hV : P.Valid) :
    ∃ (B Bh M mthrL pstar p0 : ℕ),
      1 ≤ pstar ∧ pstar ∣ p0 ∧ 1 ≤ p0 ∧ B ≤ Bh ∧ M % 2 = 0 ∧ 1 ≤ Bh ∧ 1 ≤ B ∧
      ∀ (C mS : ℕ), 1 ≤ mS →
        (∀ n, P.toPoly.domain (copiedSlice mS n) →
          ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)),
            l.Nodup →
            (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
            l.length ≤ C * (mS + n + 1)) →
      ∃ (N1 : ℕ)
        (S1L : ℕ → (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
        (F2L : ℕ → (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ),
        2 * Bh + 2 ≤ N1 ∧
        (∀ κ c' rs, ∀ r ∈ S1L κ c' rs, r < M ∧ r % 2 = 1) ∧
        (∀ κ c' rs', ∀ f ∈ F2L κ c' rs', f < 2 * Bh + 2 ∧ f % 2 = 1) ∧
        ∀ n, N1 ≤ n → P.toPoly.domain (copiedSlice mS n) →
          (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
            P.toPoly.labelOf (copiedSlice mS n) a = D) →
          ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
            P.toPoly.labelOf (copiedSlice mS n) b = D →
            (P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n ↔
              CopiedTieGate.cfgCellGAFL B Bh M mthrL (S1L (n % p0))
                (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % p0))
                (fun _ _ => ∅) mS n b) := by
  classical
  -- ===== S1: the three hoisted folds + the formula constants =====
  obtain ⟨pstar, hpstar, hdstarC⟩ := CopiedDstarC.dstarC_exists_fibred P hV
  obtain ⟨B, hB1, hcovC⟩ := CopiedCells.cells_cover_fibred P
  obtain ⟨m, p, Mc, hp, hmB, hMc, hbwd, hsetupB⟩ :=
    CopiedSetup.dstar_setup_fibred P B
  set A0 : ℕ := B + m with hA0def
  set tBk : ℕ := 3 * B + m + p + 2 with htBkdef
  set Bh : ℕ := tBk + B with hBhdef
  have hBB : B ≤ Bh := by omega
  have hBh1 : 1 ≤ Bh := by omega
  set M : ℕ := 2 * p with hMdef
  set mthr : ℕ := 2 * tBk with hmthrdef
  have hM2 : M % 2 = 0 := by rw [hMdef]; omega
  have hM : 1 ≤ M := by rw [hMdef]; omega
  obtain ⟨m3, p3, _Mc3, hp3, hm3B, _hMc3, _hbwd3, hsetupBh⟩ :=
    CopiedSetup.dstar_setup_fibred P Bh
  -- D3 with the R1 fix: include the bulk period p as an explicit factor.
  set p0 : ℕ := p * pstar * p3 with hp0def
  have hp0 : 1 ≤ p0 := by
    rw [hp0def]; exact Nat.mul_pos (Nat.mul_pos hp hpstar) hp3
  have hpstardvd : pstar ∣ p0 := ⟨p * p3, by rw [hp0def]; ring⟩
  have hp_dvd_p0 : p ∣ p0 := ⟨pstar * p3, by rw [hp0def]; ring⟩
  have hp3_dvd_p0 : p3 ∣ p0 := ⟨p * pstar, by rw [hp0def]; ring⟩
  refine ⟨B, Bh, M, mthr - 2, pstar, p0, hpstar, hpstardvd, hp0, hBB, hM2, hBh1, hB1, ?_⟩
  intro C mS hm hbud
  -- per-(C,mS) data: the bulk & frozen cell families, the cover, the d*-witness
  obtain ⟨Rcell, Bcell, PR, PBn, hwineq, hRrec, hBrec⟩ := hsetupB mS hm
  obtain ⟨RcellH, BcellH, PRH, PBnH, hwineqH, hRrecH, hBrecH⟩ := hsetupBh mS hm
  obtain ⟨Ncc, hcells⟩ := hcovC C mS hm
  obtain ⟨dstarC, N0, hCaff, hCagree⟩ := hdstarC C mS hm hbud
  -- ===== S2: the two equal-rank EP families against dstarC, pinned at p0 =====
  have hBkEP : ∀ (c' : Fin P.toPoly.K)
      (rs : Fin (P.toPoly.arity c') → RegionSpecF B) (r : ℕ),
      SliceOrder.EventuallyPeriodic
        (fun n => (fun i => Rcell c' rs (A0 + r) i + Bcell c' rs n i) = dstarC n)
        p0 := by
    intro c' rs r
    refine CopiedAffineAt.vec_eq_EP_at hp0 (fun i => ?_) (fun i => ?_)
    · refine AffineOnResiduesAtZ.of_dvd hp hp_dvd_p0 hp0
        (AffineOnResiduesAtZ.of_recurrence (m := m) (S := PBn c' rs i) hp
          (fun n hn => ?_))
      have hb := congrFun (hBrec c' rs n hn) i
      rw [Pi.add_apply] at hb
      show Rcell c' rs (A0 + r) i + Bcell c' rs (n + p) i
        = Rcell c' rs (A0 + r) i + Bcell c' rs n i + PBn c' rs i
      rw [hb]; ring
    · exact AffineOnResiduesAtZ.of_dvd hpstar hpstardvd hp0 (hCaff i)
  have hFzEP : ∀ (c' : Fin P.toPoly.K)
      (rs' : Fin (P.toPoly.arity c') → RegionSpecF Bh),
      SliceOrder.EventuallyPeriodic
        (fun n => (fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' n i) = dstarC n)
        p0 := by
    intro c' rs'
    refine CopiedAffineAt.vec_eq_EP_at hp0 (fun i => ?_) (fun i => ?_)
    · refine AffineOnResiduesAtZ.of_dvd hp3 hp3_dvd_p0 hp0
        (AffineOnResiduesAtZ.of_recurrence (m := m3) (S := PBnH c' rs' i) hp3
          (fun n hn => ?_))
      have hb := congrFun (hBrecH c' rs' n hn) i
      rw [Pi.add_apply] at hb
      show RcellH c' rs' (Bh + 1) i + BcellH c' rs' (n + p3) i
        = RcellH c' rs' (Bh + 1) i + BcellH c' rs' n i + PBnH c' rs' i
      rw [hb]; ring
    · exact AffineOnResiduesAtZ.of_dvd hpstar hpstardvd hp0 (hCaff i)
  choose NBk hNBk using hBkEP
  choose NFz hNFz using hFzEP
  -- ===== S4: the threshold (sups over the per-mS regionTuplesF, R3) =====
  set NEP : ℕ :=
    (Finset.univ.sup (fun c' : Fin P.toPoly.K =>
      (CopiedRank.regionTuplesF B (P.toPoly.arity c') mS).sup (fun rs =>
        (Finset.range p).sup (fun r => NBk c' rs r))))
    ⊔ (Finset.univ.sup (fun c' : Fin P.toPoly.K =>
      (CopiedRank.regionTuplesF Bh (P.toPoly.arity c') mS).sup (fun rs' =>
        NFz c' rs'))) with hNEPdef
  set N1 : ℕ := (2 * Bh + 2) + Ncc + N0 + NEP with hN1def
  have hN1geo : 2 * Bh + 2 ≤ N1 := by rw [hN1def]; omega
  have hNBkLe : ∀ c' rs r, (∀ i, (rs i).valid mS) → r < p → NBk c' rs r ≤ N1 := by
    intro c' rs r hv hr
    have h1 : NBk c' rs r ≤ (Finset.range p).sup (fun r => NBk c' rs r) :=
      Finset.le_sup (Finset.mem_range.mpr hr)
    have h2 : (Finset.range p).sup (fun r => NBk c' rs r)
        ≤ (CopiedRank.regionTuplesF B (P.toPoly.arity c') mS).sup
            (fun rs => (Finset.range p).sup (fun r => NBk c' rs r)) :=
      Finset.le_sup (f := fun rs => (Finset.range p).sup (fun r => NBk c' rs r))
        ((CopiedRank.mem_regionTuplesF rs).mpr hv)
    have h3 : (CopiedRank.regionTuplesF B (P.toPoly.arity c') mS).sup
          (fun rs => (Finset.range p).sup (fun r => NBk c' rs r))
        ≤ Finset.univ.sup (fun c' : Fin P.toPoly.K =>
            (CopiedRank.regionTuplesF B (P.toPoly.arity c') mS).sup
              (fun rs => (Finset.range p).sup (fun r => NBk c' rs r))) :=
      Finset.le_sup (f := fun c' : Fin P.toPoly.K =>
        (CopiedRank.regionTuplesF B (P.toPoly.arity c') mS).sup
          (fun rs => (Finset.range p).sup (fun r => NBk c' rs r)))
        (Finset.mem_univ c')
    have h4 : Finset.univ.sup (fun c' : Fin P.toPoly.K =>
        (CopiedRank.regionTuplesF B (P.toPoly.arity c') mS).sup
          (fun rs => (Finset.range p).sup (fun r => NBk c' rs r))) ≤ NEP := by
      rw [hNEPdef]; exact le_max_left _ _
    rw [hN1def]; omega
  have hNFzLe : ∀ c' rs', (∀ i, (rs' i).valid mS) → NFz c' rs' ≤ N1 := by
    intro c' rs' hv'
    have h1 : NFz c' rs' ≤ (CopiedRank.regionTuplesF Bh (P.toPoly.arity c') mS).sup
        (fun rs' => NFz c' rs') :=
      Finset.le_sup ((CopiedRank.mem_regionTuplesF rs').mpr hv')
    have h2 : (CopiedRank.regionTuplesF Bh (P.toPoly.arity c') mS).sup
          (fun rs' => NFz c' rs')
        ≤ Finset.univ.sup (fun c' : Fin P.toPoly.K =>
            (CopiedRank.regionTuplesF Bh (P.toPoly.arity c') mS).sup
              (fun rs' => NFz c' rs')) :=
      Finset.le_sup (f := fun c' : Fin P.toPoly.K =>
        (CopiedRank.regionTuplesF Bh (P.toPoly.arity c') mS).sup
          (fun rs' => NFz c' rs')) (Finset.mem_univ c')
    have h3 : Finset.univ.sup (fun c' : Fin P.toPoly.K =>
        (CopiedRank.regionTuplesF Bh (P.toPoly.arity c') mS).sup
          (fun rs' => NFz c' rs')) ≤ NEP := by
      rw [hNEPdef]; exact le_max_right _ _
    rw [hN1def]; omega
  -- ===== S5: the representative, the emitters S1/F2, the hygiene, the refine =====
  set rep : ℕ → ℕ := fun κ => N1 * p0 + κ with hrepdef
  set S1 : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpecF B) → Finset ℕ :=
    fun κ c' rs =>
      if (∀ i, clusterFreeF (rs i) = true) then ∅
      else ((Finset.range p).filter (fun r =>
        PR c' rs = (fun _ => 0) ∧
        (fun i => Rcell c' rs (A0 + r) i + Bcell c' rs (rep κ) i)
          = dstarC (rep κ))).image
        (fun r => (1 + 2 * (A0 + r)) % (2 * p)) with hS1def
  set F2 : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpecF Bh) → Finset ℕ :=
    fun κ c' rs' =>
      if ((∀ i, clusterFreeF (rs' i) = true) ∧
          (fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' (rep κ) i)
            = dstarC (rep κ))
      then {2 * Bh + 3} else ∅ with hF2def
  -- the OUTPUT emitters: the cfgPosL residue reflection / front shift of S1, F2
  set S1L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpecF B) → Finset ℕ :=
    fun κ c' rs => (S1 κ c' rs).image (fun s => (M + 2 - s) % M) with hS1Ldef
  set F2L : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpecF Bh) → Finset ℕ :=
    fun κ c' rs' => (F2 κ c' rs').image (fun f => f - 2) with hF2Ldef
  have hS1hyg : ∀ κ c' rs, ∀ x ∈ S1 κ c' rs, x < M ∧ x % 2 = 1 := by
    intro κ c' rs x hx
    rw [hS1def] at hx
    simp only [] at hx
    split at hx
    · exact absurd hx (Finset.notMem_empty x)
    · obtain ⟨r, hrmem, rfl⟩ := Finset.mem_image.mp hx
      rw [SliceFasSelector.odd_mod_two_mul (A0 + r) p hp, hMdef]
      have := Nat.mod_lt (A0 + r) hp
      omega
  have hF2hyg : ∀ κ c' rs', ∀ f ∈ F2 κ c' rs', f % 2 = 1 := by
    intro κ c' rs' f hf
    rw [hF2def] at hf
    simp only [] at hf
    split at hf
    · rw [Finset.mem_singleton] at hf; omega
    · exact absurd hf (Finset.notMem_empty f)
  have hS1Lhyg : ∀ κ c' rs, ∀ r ∈ S1L κ c' rs, r < M ∧ r % 2 = 1 := by
    intro κ c' rs r hr
    rw [hS1Ldef] at hr
    obtain ⟨h1, h2⟩ := CopiedTieBridge.remapS_hygiene M (S1 κ c' rs) hM2
      (fun s hs => (hS1hyg κ c' rs s hs).1) (fun s hs => (hS1hyg κ c' rs s hs).2) r hr
    exact ⟨h2, h1⟩
  have hF2Lhyg : ∀ κ c' rs', ∀ f ∈ F2L κ c' rs', f < 2 * Bh + 2 ∧ f % 2 = 1 := by
    intro κ c' rs' f hf
    rw [hF2Ldef] at hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    rw [hF2def] at hg
    simp only [] at hg
    split at hg
    · rw [Finset.mem_singleton] at hg; constructor <;> omega
    · exact absurd hg (Finset.notMem_empty g)
  refine ⟨N1, S1L, F2L, hN1geo, hS1Lhyg, hF2Lhyg, ?_⟩
  -- ===== S6: per-n entry, the class κ, the modular transport =====
  intro n hn hdom hD b hbsel hbD
  obtain ⟨c', ī⟩ := b
  have hagree : CopiedDstar.dstarRankGA_m P hV mS n = dstarC n :=
    hCagree n (by omega) hdom hD
  have hlenW : (wrappedFlat n).length = 2 * (n + 1) := length_wrappedFlat n
  have hlenC : (copiedSlice mS n).length = 2 * (mS + n) := length_copiedSlice mS n
  set κ : ℕ := n % p0 with hκdef
  have hκlt : κ < p0 := Nat.mod_lt _ hp0
  have hrepmod : rep κ % p0 = κ := by
    rw [hrepdef]; simp only []
    rw [Nat.mul_comm N1 p0, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hκlt
  have hrepN1 : N1 ≤ rep κ := by
    rw [hrepdef]; simp only []
    have := Nat.le_mul_of_pos_right N1 hp0
    omega
  have hmodeq : ∀ qf, qf ∣ p0 → n % qf = rep κ % qf := by
    intro qf hqf
    exact Nat.ModEq.of_dvd hqf (hrepmod.trans hκdef).symm
  have hrankunfold : P.rankOf (copiedSlice mS n) ⟨c', ī⟩
      = P.rank c' (copiedSlice mS n) ī := rfl
  have hnBh : 2 * Bh + 2 ≤ n := le_trans hN1geo hn
  -- ===== S7: the two equal-rank transports n ↔ rep κ =====
  have htransBk : ∀ (rs : Fin (P.toPoly.arity c') → RegionSpecF B) (r : ℕ),
      (∀ i, (rs i).valid mS) → r < p →
      (((fun i => Rcell c' rs (A0 + r) i + Bcell c' rs n i) = dstarC n) ↔
        ((fun i => Rcell c' rs (A0 + r) i + Bcell c' rs (rep κ) i)
          = dstarC (rep κ))) :=
    fun rs r hv hr => SliceFasSelector.iff_on_class
      (Pr := fun x => (fun i => Rcell c' rs (A0 + r) i + Bcell c' rs x i) = dstarC x)
      hp0 (hNBk c' rs r)
      (le_trans (hNBkLe c' rs r hv hr) hn) (le_trans (hNBkLe c' rs r hv hr) hrepN1)
      (hmodeq p0 dvd_rfl)
  have htransFz : ∀ (rs' : Fin (P.toPoly.arity c') → RegionSpecF Bh),
      (∀ i, (rs' i).valid mS) →
      (((fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' n i) = dstarC n) ↔
        ((fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' (rep κ) i)
          = dstarC (rep κ))) :=
    fun rs' hv' => SliceFasSelector.iff_on_class
      (Pr := fun x => (fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' x i)
        = dstarC x)
      hp0 (hNFz c' rs')
      (le_trans (hNFzLe c' rs' hv') hn) (le_trans (hNFzLe c' rs' hv') hrepN1)
      (hmodeq p0 dvd_rfl)
  -- ===== S8: the shared frozen emitter =====
  have emitFrozen : ∀ rs' : Fin (P.toPoly.arity c') → RegionSpecF Bh,
      (∀ i, clusterFreeF (rs' i) = true) → (∀ i, (rs' i).valid mS) →
      ī = CopiedDstar.cellTupleF rs' mS (Bh + 1) n →
      P.rank c' (copiedSlice mS n) ī = dstarC n →
      cfgCellArmF Bh M mthr (fun _ _ => ∅) (F2 κ) (fun _ _ => ∅) mS n ⟨c', ī⟩ := by
    intro rs' hcf' hv' hcell hrk
    have hrkH : (fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' n i) = dstarC n := by
      have h1 := hwineqH c' rs' hv' (Bh + 1) n (by omega) (by omega)
      rw [← h1, ← hcell]; exact hrk
    refine ⟨rs', Bh + 1, hv', by omega, hcell, Or.inr (Or.inl ?_)⟩
    show (1 + 2 * (Bh + 1)) ∈ F2 κ c' rs'
    rw [hF2def]; simp only []
    rw [if_pos ⟨hcf', (htransFz rs' hv').mp hrkH⟩,
      show 1 + 2 * (Bh + 1) = 2 * Bh + 3 from by omega]
    exact Finset.mem_singleton_self _
  constructor
  · -- ===== S9: forward — prove cfgCellGAF (cfgPos), then lift to cfgCellGAFL (cfgPosL) =====
    intro hrank
    suffices hGAF : cfgCellGAF B Bh M mthr (S1 κ) (F2 κ) mS n ⟨c', ī⟩ by
      simp only [hS1Ldef, hF2Ldef]
      exact cfgCellGAF_imp_cfgCellGAFL B Bh M mthr (S1 κ) (F2 κ) mS n ⟨c', ī⟩
        hM hm hB1 hBh1 (by omega) hGAF
    have hrkC : P.rank c' (copiedSlice mS n) ī = dstarC n := by
      rw [← hrankunfold, hrank, hagree]
    have hagree' : CopiedDstar.dstarRankGA' P hV (copiedSlice mS n) = dstarC n :=
      hagree
    obtain ⟨t, htB, htn0, hper⟩ := hcells n (by omega) c' ī hbsel (hbud n hdom c')
    choose rs hrsv hrseq using hper
    have hcell : ī = CopiedDstar.cellTupleF rs mS t n := funext hrseq
    by_cases hcf : ∀ i, clusterFreeF (rs i) = true
    · -- cluster-free: lift to Bh, freeze at the dummy base
      refine Or.inr (emitFrozen (fun i => regionLiftF hBB (rs i)) ?_ ?_ ?_ hrkC)
      · exact fun i => (clusterFreeF_regionLiftF hBB (rs i)).trans (hcf i)
      · exact fun i => (regionLiftF_valid hBB (rs i) mS).mpr (hrsv i)
      · rw [hcell, ← cellTupleF_regionLiftF hBB rs mS t n]
        exact cellTupleF_clusterFree_base (fun i => regionLiftF hBB (rs i))
          (fun i => (clusterFreeF_regionLiftF hBB (rs i)).trans (hcf i)) mS t (Bh + 1) n
    · rcases Nat.lt_or_ge t tBk with hfront | htlow
      · -- front zone
        obtain ⟨rs', hcf', hvlift, heq'⟩ := freeze_front_descrF hBB rs mS t n (by omega)
        exact Or.inr (emitFrozen rs' hcf' (fun i => hvlift i (hrsv i))
          (hcell.trans heq') hrkC)
      rcases Nat.lt_or_ge n (t + tBk) with hback | hbulk
      · -- back zone
        obtain ⟨rs', hcf', hvlift, heq'⟩ := freeze_back_descrF hBB hBh1 rs mS t n
          (by omega) (by omega)
        exact Or.inr (emitFrozen rs' hcf' (fun i => hvlift i (hrsv i))
          (hcell.trans heq') hrkC)
      -- deep bulk
      set r := (t - A0) % p with hrdef
      set kk := (t - A0) / p with hkkdef
      have hr : r < p := Nat.mod_lt _ hp
      have hteq : t = A0 + r + p * kk := by
        rw [hrdef, hkkdef]; have := Nat.mod_add_div (t - A0) p; omega
      have hchainval : ∀ k, Rcell c' rs (A0 + r + p * k)
          = Rcell c' rs (A0 + r) + k • PR c' rs :=
        fun k => SliceRankAtom.RankAffine.iterate (fun j hj => hRrec c' rs j hj)
          (A0 + r) k (by omega)
      by_cases hcol : PR c' rs = (fun _ => 0)
      · -- S10: collinear — emit the bulk residue
        have hchain0 : Rcell c' rs t = Rcell c' rs (A0 + r) := by
          conv_lhs => rw [hteq]
          rw [hchainval kk, hcol]; funext i; simp
        have hpredn : (fun i => Rcell c' rs (A0 + r) i + Bcell c' rs n i) = dstarC n := by
          rw [← hchain0, ← hwineq c' rs hrsv t n (by omega) (by omega), ← hcell]
          exact hrkC
        refine Or.inl ⟨rs, t, hrsv, by omega, hcell, Or.inl ⟨?_, ?_, ?_⟩⟩
        · rw [hmthrdef]; omega
        · rw [hlenW, hmthrdef]; omega
        · rw [hMdef, hS1def]
          simp only []
          rw [if_neg hcf]
          refine Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hr, hcol, (htransBk rs r hrsv hr).mp hpredn⟩, ?_⟩
          exact ((SliceFasSelectorGA.base_mod_iff A0 p t r hp hr (by omega)).mpr
            hrdef.symm).symm
      · -- S11: non-collinear — refute via chain endpoints
        exfalso
        have hmc : kk * p = p * kk := Nat.mul_comm kk p
        have hkk1 : 1 ≤ kk := by
          rw [hkkdef, Nat.le_div_iff_mul_le hp]; omega
        set tl := (n - 3 * B - m - (A0 + r)) / p with htldef
        set jl := A0 + r + p * tl with hjldef
        have hmc2 : tl * p = p * tl := Nat.mul_comm tl p
        have hjlub : jl + 3 * B + m ≤ n := by
          rw [hjldef]
          have h1 : p * tl ≤ n - 3 * B - m - (A0 + r) := by
            rw [htldef, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
          omega
        have hkktl : kk < tl := by
          have hstep : kk + 1 ≤ tl := by
            rw [htldef, Nat.le_div_iff_mul_le hp, Nat.add_mul, Nat.one_mul]; omega
          omega
        have hval_t := cellTupleF_valid rs mS t n hm hrsv (by omega)
        have hacc_t : (Mc c').accepts (markAtN (P.toPoly.arity c') (copiedSlice mS n)
            (CopiedDstar.cellTupleF rs mS t n)) := by
          refine (hMc c' (copiedSlice mS n) _ hval_t).mpr ⟨?_, ?_⟩
          · rw [← hcell]; exact hbsel.2
          · rw [← hcell]; exact hbD
        have htr_left := CopiedDstar.cell_base_transport_left_fibred (Mc c') m p
          (hbwd c') mS hm rs hrsv t n kk (by omega) (by omega) (by omega)
        have hsub : t - kk * p = A0 + r := by omega
        rw [hsub] at htr_left
        have hacc_a := htr_left.mpr hacc_t
        have htr_right := CopiedDstar.cell_base_transport_right_fibred (Mc c') m p
          (hbwd c') mS hm rs hrsv (A0 + r) n tl (by omega) (by omega) (by omega)
        have hbd : A0 + r + tl * p = jl := by rw [hjldef]; omega
        rw [hbd] at htr_right
        have hacc_jl := htr_right.mpr hacc_a
        have hval_a := cellTupleF_valid rs mS (A0 + r) n hm hrsv (by omega)
        have hsl_a := (hMc c' (copiedSlice mS n) _ hval_a).mp hacc_a
        have hval_jl := cellTupleF_valid rs mS jl n hm hrsv (by omega)
        have hsl_jl := (hMc c' (copiedSlice mS n) _ hval_jl).mp hacc_jl
        have hDRn : dstarC n = fun i =>
            (Rcell c' rs (A0 + r) i + Bcell c' rs n i) + (kk : ℤ) * PR c' rs i := by
          have h1 : P.rank c' (copiedSlice mS n) ī
              = fun i => Rcell c' rs t i + Bcell c' rs n i := by
            rw [hcell]; exact hwineq c' rs hrsv t n (by omega) (by omega)
          rw [← hrkC, h1]; funext i
          have h2i := congrFun (hchainval kk) i
          rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at h2i
          rw [show t = A0 + r + p * kk from hteq, h2i]; ring
        rcases SliceFasSelector.chain_min_endpoint
          (fun i => Rcell c' rs (A0 + r) i + Bcell c' rs n i) (PR c' rs)
          kk tl hkk1 hkktl hcol with hfirst | hlast
        · refine CopiedDstarC.dstarRankGA'_lex_min P hV (copiedSlice mS n) hD
            ⟨c', CopiedDstar.cellTupleF rs mS (A0 + r) n⟩ ⟨hval_a, hsl_a.1⟩ hsl_a.2 ?_
          have hrk_a : P.rankOf (copiedSlice mS n)
              ⟨c', CopiedDstar.cellTupleF rs mS (A0 + r) n⟩
              = fun i => Rcell c' rs (A0 + r) i + Bcell c' rs n i :=
            hwineq c' rs hrsv (A0 + r) n (by omega) (by omega)
          rw [hrk_a, hagree', hDRn]
          exact hfirst
        · refine CopiedDstarC.dstarRankGA'_lex_min P hV (copiedSlice mS n) hD
            ⟨c', CopiedDstar.cellTupleF rs mS jl n⟩ ⟨hval_jl, hsl_jl.1⟩ hsl_jl.2 ?_
          have hrk_jl : P.rankOf (copiedSlice mS n)
              ⟨c', CopiedDstar.cellTupleF rs mS jl n⟩
              = fun i => Rcell c' rs jl i + Bcell c' rs n i :=
            hwineq c' rs hrsv jl n (by omega) (by omega)
          have hjl_chain : (fun i => Rcell c' rs jl i + Bcell c' rs n i)
              = fun i => (Rcell c' rs (A0 + r) i + Bcell c' rs n i)
                + (tl : ℤ) * PR c' rs i := by
            funext i
            have h2i := congrFun (hchainval tl) i
            rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at h2i
            rw [show jl = A0 + r + p * tl from hjldef, h2i]; ring
          rw [hrk_jl, hjl_chain, hagree', hDRn]
          exact hlast
  · -- ===== S12/S13: backward — the two arms decode to the rank equation =====
    rintro (⟨rs, t, hv, hzlt, hcell, hcfg⟩ | ⟨rs', t', hv', hzlt, hcell, hcfg⟩)
    · -- S12: the bulk arm (cfgPosL residue: yF+mthr≤z forces t ≥ tBk, no boundary)
      obtain ⟨_, harm⟩ := hcfg
      rcases harm with ⟨hge, hle, r', hr'mem, hreq⟩ | hfront | hback
      · -- residue arm: un-reflect, then transport
        rw [hS1Ldef] at hr'mem
        simp only [] at hr'mem
        obtain ⟨s, hsS1, rfl⟩ := Finset.mem_image.mp hr'mem
        have hslt : s < M := (hS1hyg κ c' rs s hsS1).1
        have hfinal : (1 + 2 * t) % M = s := by
          set q := (M + 2 - s) % M with hq_def
          have hqlt : q < M := by rw [hq_def]; exact Nat.mod_lt _ hM
          have hsr : (s + q) % M = 2 % M := by
            have h1 : q ≡ M + 2 - s [MOD M] := by rw [hq_def]; exact Nat.mod_modEq _ _
            have h2 : (s + q) % M = (s + (M + 2 - s)) % M := Nat.ModEq.add_left s h1
            rw [h2, show s + (M + 2 - s) = M + 2 by omega, Nat.add_mod_left]
          have h2tr : (2 * t + q) % M = 1 % M := by
            have ha : (mS + 1 + (M - q) + q) % M = (mS + 2 * t + q) % M :=
              Nat.ModEq.add_right q hreq
            rw [show mS + 1 + (M - q) + q = mS + 1 + M by omega] at ha
            have hb : (mS + 1 + M) % M = (mS + 1) % M := by
              rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
            rw [hb] at ha
            have hc : (mS + 1) % M = (mS + (2 * t + q)) % M := by
              rw [show mS + (2 * t + q) = mS + 2 * t + q by ring]; exact ha
            exact (Nat.ModEq.add_left_cancel' mS hc).symm
          have hs12 : s % M = (1 + 2 * t) % M := by
            have e1 : (s + (2 * t + q)) % M = (s + 1) % M := Nat.ModEq.add_left s h2tr
            have e3 : (2 * t + (s + q)) % M = (2 * t + 2) % M := Nat.ModEq.add_left (2 * t) hsr
            have e4 : (s + 1) % M = (2 * t + 2) % M := by
              rw [← e1, show s + (2 * t + q) = 2 * t + (s + q) by ring, e3]
            have e5 : (s + 1) % M = (1 + 2 * t + 1) % M := by rw [e4]; congr 1; ring
            exact Nat.ModEq.add_right_cancel' 1 e5
          rw [← hs12, Nat.mod_eq_of_lt hslt]
        have hres : (1 + 2 * t) % M ∈ S1 κ c' rs := by rw [hfinal]; exact hsS1
        rw [hMdef, hS1def] at hres
        simp only [] at hres
        by_cases hcf : ∀ i, clusterFreeF (rs i) = true
        · rw [if_pos hcf] at hres; exact absurd hres (Finset.notMem_empty _)
        · rw [if_neg hcf] at hres
          obtain ⟨r, hrmem, hrimg⟩ := Finset.mem_image.mp hres
          obtain ⟨hrR, hcol, hvalrep⟩ := Finset.mem_filter.mp hrmem
          have hr : r < p := Finset.mem_range.mp hrR
          have hmod : (t - A0) % p = r :=
            (SliceFasSelectorGA.base_mod_iff A0 p t r hp hr (by omega)).mp hrimg.symm
          have hteq : t = A0 + r + p * ((t - A0) / p) := by
            have := Nat.mod_add_div (t - A0) p; omega
          have hchainval : ∀ k, Rcell c' rs (A0 + r + p * k)
              = Rcell c' rs (A0 + r) + k • PR c' rs :=
            fun k => SliceRankAtom.RankAffine.iterate (fun j hj => hRrec c' rs j hj)
              (A0 + r) k (by omega)
          have hchain0 : Rcell c' rs t = Rcell c' rs (A0 + r) := by
            conv_lhs => rw [hteq]
            rw [hchainval ((t - A0) / p), hcol]; funext i; simp
          have hcell2 : ī = CopiedDstar.cellTupleF rs mS t n := hcell
          have hfin : P.rank c' (copiedSlice mS n) ī = dstarC n := by
            rw [hcell2, hwineq c' rs hv t n (by omega) (by omega), hchain0]
            exact (htransBk rs r hv hr).mpr hvalrep
          rw [hrankunfold, hagree]; exact hfin
      · obtain ⟨f', hf'mem, _⟩ := hfront; exact absurd hf'mem (Finset.notMem_empty _)
      · obtain ⟨k, hk, _⟩ := hback; exact absurd hk (Finset.notMem_empty _)
    · -- S13: the frozen arm (cfgPosL front: z = yF + (2Bh+1) pins t' = Bh+1)
      obtain ⟨_, harm⟩ := hcfg
      rcases harm with ⟨_, _, r', hr'mem, _⟩ | hfront | hback
      · exact absurd hr'mem (Finset.notMem_empty _)
      · obtain ⟨f', hf'mem, hcase⟩ := hfront
        rw [hF2Ldef] at hf'mem
        simp only [] at hf'mem
        obtain ⟨g, hgmem, rfl⟩ := Finset.mem_image.mp hf'mem
        rw [hF2def] at hgmem
        simp only [] at hgmem
        by_cases hcond : (∀ i, clusterFreeF (rs' i) = true) ∧
            ((fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' (rep κ) i)
              = dstarC (rep κ))
        · rw [if_pos hcond] at hgmem
          rw [Finset.mem_singleton] at hgmem
          have ht'eq : t' = Bh + 1 := by
            rcases hcase with ⟨hf0, _⟩ | ⟨_, hz⟩ <;> omega
          subst ht'eq
          have hcell2 : ī = CopiedDstar.cellTupleF rs' mS (Bh + 1) n := hcell
          have hfin : P.rank c' (copiedSlice mS n) ī = dstarC n := by
            rw [hcell2, hwineqH c' rs' hv' (Bh + 1) n (by omega) (by omega)]
            exact (htransFz rs' hv').mpr hcond.2
          rw [hrankunfold, hagree]; exact hfin
        · rw [if_neg hcond] at hgmem; exact absurd hgmem (Finset.notMem_empty _)
      · obtain ⟨k, hk, _⟩ := hback; exact absurd hk (Finset.notMem_empty _)

end CopiedSelector
