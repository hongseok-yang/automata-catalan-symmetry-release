/-
# The mS-direction equal-rank cell selector (§9 d4c — the crux of the DFA realization)

The mS-direction analog of `CopiedSelector.eqRankD_cell_selector_fibred` (the n-direction selector,
`∀ mS, ∃ N1, ∀ n ≥ N1, rankOf b = d* ↔ cfgCellGAFL b`).  Here we build the **mS-direction** iff
(`∀ n, ∃ Mbr, ∀ mS ≥ Mbr, …`) RESTRICTED to bounded atoms — which is exactly what the (4c) CORE gate
(`fasU_atomOrd_cellCfg_gate_fibred`) needs to realise the `gate_semantic_split` CORE part.

The growing mid-run is sidestepped by the bounded-atom restriction (`¬inSuf ∧ ¬inPre`); on bounded
(fixed-offset front/back/from-end) cells the analysis ports from the n-direction proof, swapping the
n-direction transports for their mS counterparts:
  • cell-rank affineness: `CopiedSetupMS.rank_cell_affine_mS` (mS) instead of the `Bcell` n-recurrence;
  • the d*-vector: `CopiedDstarCMS.dstarC_exists_fibred_mS` instead of `dstarC_exists_fibred`;
  • the abstract class/chain transports (`SliceFasSelector.iff_on_class`, `chain_min_endpoint`,
    `CopiedDstar.cell_base_transport_*`) port directly (they are direction-agnostic).

This file builds the port brick-by-brick.  First brick: the equal-rank EP-in-mS families.
-/
import RequestProject.CopiedSelUniform
import RequestProject.CopiedTie2b

namespace CopiedSelectorMS

open WRP Step CopiedDstar CopiedDstarCMS CopiedCells SliceOrder CopiedAffineAt CopiedSetupMS
  SliceMSO MSOMarkN SliceMarkN SliceDstarCore CopiedRegionF SliceFamilyCell

/-- **mS-EP family (port of the n-direction `hBkEP`/`hFzEP`).**  For a bounded cell `rs` at base `t`
(`t+B≤n`), the predicate "the cell rank equals the d*-vector `dstarC mS`" is eventually periodic in `mS`,
at the common period = (the cell's per-coordinate mS-periods from `rank_cell_affine_mS`) × (the d*-period
`pstar`).  Parametrised by an abstract affine d*-vector so the actual `dstarC_mS` from
`dstarC_exists_fibred_mS` plugs in at the assembly site. -/
theorem cellRank_eq_dstar_EP_mS {B : ℕ} (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (rs : Fin (P.toPoly.arity c) → CopiedCells.RegionSpecF B) (t n : ℕ) (hB : 1 ≤ B) (htBn : t + B ≤ n)
    (pstar : ℕ) (hpstar : 1 ≤ pstar) (dstarC : ℕ → Fin P.d → ℤ)
    (hdaff : ∀ i, AffineOnResiduesAtZ pstar (fun mS => dstarC mS i)) :
    ∃ pp : ℕ, 1 ≤ pp ∧ SliceOrder.EventuallyPeriodic
      (fun mS => P.rank c (copiedSlice mS n) (cellTupleF rs mS t n) = dstarC mS) pp := by
  choose pf hpf haf using fun i => rank_cell_affine_mS P c rs t n i hB htBn
  refine ⟨pstar * Finset.univ.prod pf, Nat.mul_pos hpstar (Finset.prod_pos (fun i _ => hpf i)), ?_⟩
  refine vec_eq_EP_at (Nat.mul_pos hpstar (Finset.prod_pos (fun i _ => hpf i)))
    (fun i => ?_) (fun i => ?_)
  · exact AffineOnResiduesAtZ.of_dvd (hpf i)
      (dvd_trans (Finset.dvd_prod_of_mem pf (Finset.mem_univ i)) (dvd_mul_left _ _))
      (Nat.mul_pos hpstar (Finset.prod_pos (fun i _ => hpf i))) (haf i)
  · exact AffineOnResiduesAtZ.of_dvd hpstar (dvd_mul_right _ _)
      (Nat.mul_pos hpstar (Finset.prod_pos (fun i _ => hpf i))) (hdaff i)

open Classical in
/-- **The mS-direction equal-rank cell selector (§9 d4c crux, DECOUPLED form).**  The mS-direction
analog of `CopiedSelector.eqRankD_cell_selector_fibred`: for selected-`D` atoms on the copied slice,
the bounded config gate `CopiedTieGate.cfgCellGAFL` (with class-uniform emitters indexed by `mS % p0'`)
characterises exactly the SHALLOW-or-BULK `d*`-achievers — `cfgCellGAFL b ↔ (rankOf b = dstarRankGA_m ∧
¬DeepSuf b ∧ ¬DeepPre b)` — where the deep boundary-run band is carved out by `q_D`/`q_U` and handled
elsewhere (the (4c) run-clauses).  The constants `(B Bh M mthrL pstar p0' q_U q_D)` and per-`n` emitters
`S1L`/`F2L` are hoisted before `mS` (class-uniform, one DFA per `mS`-class for (4c)); the `mS ↔ rep'`
transport rests on `cellRank_eq_dstar_EP_mS`.  The S1 bulk arm records achievement at TWO consecutive bases
(`A0+r`, `A0+r+p`) so collinearity (`PR=0`) is recorded class-uniformly (not re-derived).  Proved for all
`P.d` by abstracting the body over the `d*`-vector and instantiating with `selB` (`P.d>0`) or the trivial
vector (`P.d=0`, where ranks are `Subsingleton`). -/
theorem eqRankD_cell_selector_fibred_mS (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity1 : ∀ c, P.toPoly.arity c = 1) :
    ∃ (B Bh M mthrL pstar p0' q_U q_D A0 p : ℕ),
      1 ≤ pstar ∧ pstar ∣ p0' ∧ 1 ≤ p0' ∧ B ≤ Bh ∧ M % 2 = 0 ∧ 1 ≤ Bh ∧
      1 ≤ B ∧ 1 ≤ p ∧ B + 1 ≤ A0 ∧ 2 * A0 ≤ mthrL ∧ M = 2 * p ∧
      A0 + 2 * p + B + 1 ≤ 2 * Bh + 2 ∧
      -- the rank-decomposition recurrence at THIS selector's own `p`/`A0` (the bridge's
      -- PR=0 chain needs the t-recurrence at the SAME `p` the emitters use; `dstar_setup_fibred`'s
      -- `p`/`A0` are opaque witnesses otherwise).
      (∀ mS, 1 ≤ mS → ∃ (Rcell Bcell : (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → ℕ → Fin P.d → ℤ)
        (PR : (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Fin P.d → ℤ),
        (∀ (c' : Fin P.toPoly.K) (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B),
          (∀ i, (rs i).valid mS) → ∀ t n, B + 1 ≤ t → t + B + 1 ≤ n →
          P.rank c' (copiedSlice mS n) (cellTupleF rs mS t n)
            = fun i => Rcell c' rs t i + Bcell c' rs n i)
        ∧ (∀ (c' : Fin P.toPoly.K)
            (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) (t : ℕ),
          A0 - B ≤ t → Rcell c' rs (t + p) = Rcell c' rs t + PR c' rs)) ∧
      ∀ (n : ℕ), 2 * Bh + 2 ≤ n →
      ∃ (Mbr : ℕ) (dstar : ℕ → Fin P.d → ℤ)
        (S1 : ℕ → (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
        (F2 : ℕ → (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
        (S1L : ℕ → (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
        (F2L : ℕ → (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ),
        1 ≤ Mbr ∧
        (∀ κ c' rs, ∀ r ∈ S1L κ c' rs, r < M ∧ r % 2 = 1) ∧
        (∀ κ c' rs', ∀ f ∈ F2L κ c' rs', f % 2 = 1) ∧
        (∀ κ c' rs, (∀ i, clusterFreeF (rs i) = true) → S1L κ c' rs = ∅) ∧
        (∀ κ c' rs', ¬ (∀ i, (match rs' i with
            | CopiedCells.RegionSpecF.core _ => (True : Prop)
            | CopiedCells.RegionSpecF.prefIdx q => q < q_U
            | CopiedCells.RegionSpecF.sufIdx l => l < q_D)) → F2L κ c' rs' = ∅) ∧
        (∀ κ c' rs, S1 κ c' rs =
          if (∀ i, clusterFreeF (rs i) = true) then ∅
          else ((Finset.range p).filter (fun r =>
            P.rank c' (copiedSlice (Mbr * p0' + κ) n)
                (cellTupleF rs (Mbr * p0' + κ) (A0 + r) n) = dstar (Mbr * p0' + κ)
            ∧ P.rank c' (copiedSlice (Mbr * p0' + κ) n)
                (cellTupleF rs (Mbr * p0' + κ) (A0 + (r + p)) n) = dstar (Mbr * p0' + κ))).image
            (fun r => (1 + 2 * (A0 + r)) % (2 * p))) ∧
        (∀ κ c' rs', F2 κ c' rs' =
          if ((∀ i, clusterFreeF (rs' i) = true)
              ∧ (∀ i, (match rs' i with
                  | CopiedCells.RegionSpecF.core _ => (True : Prop)
                  | CopiedCells.RegionSpecF.prefIdx q => q < q_U
                  | CopiedCells.RegionSpecF.sufIdx l => l < q_D))
              ∧ P.rank c' (copiedSlice (Mbr * p0' + κ) n)
                  (cellTupleF rs' (Mbr * p0' + κ) (Bh + 1) n) = dstar (Mbr * p0' + κ))
          then {2 * Bh + 3} else ∅) ∧
        (∀ κ c' rs, S1L κ c' rs = (S1 κ c' rs).image (fun s => (M + 2 - s) % M)) ∧
        (∀ κ c' rs', F2L κ c' rs' = (F2 κ c' rs').image (fun f => f - 2)) ∧
        (∀ mS, Mbr ≤ mS → P.toPoly.domain (copiedSlice mS n) →
          (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
            P.toPoly.labelOf (copiedSlice mS n) a = D) →
          CopiedDstar.dstarRankGA_m P hV mS n = dstar mS) ∧
        -- mS-leg transport iffs @ threshold Mbr (bulk / frozen): the bridge's rep'→mS transport.
        (∀ (c' : Fin P.toPoly.K)
            (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) (r mS' mS'' : ℕ),
            (fun j => (Sum.inl (rs j) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)))
              ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') → r < 2 * p → (A0 + r) + B ≤ n →
            Mbr ≤ mS' → Mbr ≤ mS'' → mS' % p0' = mS'' % p0' →
            (P.rank c' (copiedSlice mS' n) (cellTupleF rs mS' (A0 + r) n) = dstar mS' ↔
             P.rank c' (copiedSlice mS'' n) (cellTupleF rs mS'' (A0 + r) n) = dstar mS'')) ∧
        (∀ (c' : Fin P.toPoly.K)
            (rs' : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) (mS' mS'' : ℕ),
            (fun j => (Sum.inl (rs' j) : CopiedCells.RegionSpecF Bh ⊕ (ℕ ⊕ ℕ)))
              ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c') → (Bh + 1) + Bh ≤ n →
            Mbr ≤ mS' → Mbr ≤ mS'' → mS' % p0' = mS'' % p0' →
            (P.rank c' (copiedSlice mS' n) (cellTupleF rs' mS' (Bh + 1) n) = dstar mS' ↔
             P.rank c' (copiedSlice mS'' n) (cellTupleF rs' mS'' (Bh + 1) n) = dstar mS'')) ∧
        ∀ mS, Mbr ≤ mS → P.toPoly.domain (copiedSlice mS n) →
          (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
            P.toPoly.labelOf (copiedSlice mS n) a = D) →
          ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
            P.toPoly.labelOf (copiedSlice mS n) b = D →
            (CopiedTieGate.cfgCellGAFL B Bh M mthrL (S1L (mS % p0'))
                (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (mS % p0'))
                (fun _ _ => ∅) mS n b
              ↔
              (P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n
                ∧ ¬ (∃ l, q_D ≤ l ∧ l < mS - 1 ∧ b.2 = fun _ => mS + 2 * n + 1 + l)
                ∧ ¬ (∃ q, q_U ≤ q ∧ q < mS - 1 ∧ b.2 = fun _ => q))) := by
  classical
  -- ===== S1: replicate the dstarC_exists_fibred_mS chain so q_U/q_D/Mc/period align =====
  obtain ⟨B, hB1, _hcov⟩ := CopiedCells.cells_cover_fibred P
  obtain ⟨m, p, Mc, hp, hmB, hMc, hbwd, hsetup⟩ := CopiedSetup.dstar_setup_fibred P B
  obtain ⟨q_U, q_D, hloU, hloD, hsufC, hprefC⟩ := coordCands_cycle_lengths P Mc (3 * B + m)
  set A0 : ℕ := B + m with hA0def
  set tBk : ℕ := 3 * B + m + p + 2 with htBkdef
  set Bh : ℕ := tBk + B with hBhdef
  have hBB : B ≤ Bh := by omega
  have hBh1 : 1 ≤ Bh := by omega
  set M : ℕ := 2 * p with hMdef
  set mthr : ℕ := 2 * tBk with hmthrdef
  have hM2 : M % 2 = 0 := by rw [hMdef]; omega
  have hM : 1 ≤ M := by rw [hMdef]; omega
  -- the two uniform mS-periods: bulk cells (+ selB) at bound B, frozen cells at bound Bh
  obtain ⟨psB, hpsB1, hcertB⟩ := coordCands_period_uniform P hB1 Mc q_U q_D
  obtain ⟨psBh, hpsBh1, hcertBh⟩ := coordCands_period_uniform P hBh1 Mc q_U q_D
  set p0' : ℕ := psB * psBh with hp0'def
  have hp0'1 : 1 ≤ p0' := Nat.mul_pos hpsB1 hpsBh1
  have hpsBdvd : psB ∣ p0' := dvd_mul_right psB psBh
  have hpsBhdvd : psBh ∣ p0' := dvd_mul_left psBh psB
  refine ⟨B, Bh, M, mthr - 2, psB, p0', q_U, q_D, A0, p,
    hpsB1, hpsBdvd, hp0'1, hBB, hM2, hBh1, hB1, hp, (by rw [hA0def]; omega),
    (by omega), hMdef, (by rw [hA0def, hBhdef, htBkdef]; omega),
    (fun mS hmS => by
      obtain ⟨Rcell, Bcell, PR, PBn, hw, hr, _hb⟩ := hsetup mS hmS
      exact ⟨Rcell, Bcell, PR, hw, fun c' rs t ht => hr c' rs t (by omega)⟩), ?_⟩
  intro n hn
  have hcore : ∀ (dstar : ℕ → Fin P.d → ℤ) (N0 : ℕ),
      (∀ i, AffineOnResiduesAtZ p0' (fun mS => dstar mS i)) →
      (∀ mS, N0 ≤ mS → P.toPoly.domain (copiedSlice mS n) →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
          P.toPoly.labelOf (copiedSlice mS n) a = D) →
        CopiedDstar.dstarRankGA_m P hV mS n = dstar mS) →
      ∃ (Mbr : ℕ)
        (S1 : ℕ → (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
        (F2 : ℕ → (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ)
        (S1L : ℕ → (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
        (F2L : ℕ → (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ),
        1 ≤ Mbr ∧
        (∀ κ c' rs, ∀ r ∈ S1L κ c' rs, r < M ∧ r % 2 = 1) ∧
        (∀ κ c' rs', ∀ f ∈ F2L κ c' rs', f % 2 = 1) ∧
        (∀ κ c' rs, (∀ i, clusterFreeF (rs i) = true) → S1L κ c' rs = ∅) ∧
        (∀ κ c' rs', ¬ (∀ i, (match rs' i with
            | CopiedCells.RegionSpecF.core _ => (True : Prop)
            | CopiedCells.RegionSpecF.prefIdx q => q < q_U
            | CopiedCells.RegionSpecF.sufIdx l => l < q_D)) → F2L κ c' rs' = ∅) ∧
        (∀ κ c' rs, S1 κ c' rs =
          if (∀ i, clusterFreeF (rs i) = true) then ∅
          else ((Finset.range p).filter (fun r =>
            P.rank c' (copiedSlice (Mbr * p0' + κ) n)
                (cellTupleF rs (Mbr * p0' + κ) (A0 + r) n) = dstar (Mbr * p0' + κ)
            ∧ P.rank c' (copiedSlice (Mbr * p0' + κ) n)
                (cellTupleF rs (Mbr * p0' + κ) (A0 + (r + p)) n) = dstar (Mbr * p0' + κ))).image
            (fun r => (1 + 2 * (A0 + r)) % (2 * p))) ∧
        (∀ κ c' rs', F2 κ c' rs' =
          if ((∀ i, clusterFreeF (rs' i) = true)
              ∧ (∀ i, (match rs' i with
                  | CopiedCells.RegionSpecF.core _ => (True : Prop)
                  | CopiedCells.RegionSpecF.prefIdx q => q < q_U
                  | CopiedCells.RegionSpecF.sufIdx l => l < q_D))
              ∧ P.rank c' (copiedSlice (Mbr * p0' + κ) n)
                  (cellTupleF rs' (Mbr * p0' + κ) (Bh + 1) n) = dstar (Mbr * p0' + κ))
          then {2 * Bh + 3} else ∅) ∧
        (∀ κ c' rs, S1L κ c' rs = (S1 κ c' rs).image (fun s => (M + 2 - s) % M)) ∧
        (∀ κ c' rs', F2L κ c' rs' = (F2 κ c' rs').image (fun f => f - 2)) ∧
        (∀ mS, Mbr ≤ mS → P.toPoly.domain (copiedSlice mS n) →
          (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
            P.toPoly.labelOf (copiedSlice mS n) a = D) →
          CopiedDstar.dstarRankGA_m P hV mS n = dstar mS) ∧
        (∀ (c' : Fin P.toPoly.K)
            (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) (r mS' mS'' : ℕ),
            (fun j => (Sum.inl (rs j) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)))
              ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') → r < 2 * p → (A0 + r) + B ≤ n →
            Mbr ≤ mS' → Mbr ≤ mS'' → mS' % p0' = mS'' % p0' →
            (P.rank c' (copiedSlice mS' n) (cellTupleF rs mS' (A0 + r) n) = dstar mS' ↔
             P.rank c' (copiedSlice mS'' n) (cellTupleF rs mS'' (A0 + r) n) = dstar mS'')) ∧
        (∀ (c' : Fin P.toPoly.K)
            (rs' : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) (mS' mS'' : ℕ),
            (fun j => (Sum.inl (rs' j) : CopiedCells.RegionSpecF Bh ⊕ (ℕ ⊕ ℕ)))
              ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c') → (Bh + 1) + Bh ≤ n →
            Mbr ≤ mS' → Mbr ≤ mS'' → mS' % p0' = mS'' % p0' →
            (P.rank c' (copiedSlice mS' n) (cellTupleF rs' mS' (Bh + 1) n) = dstar mS' ↔
             P.rank c' (copiedSlice mS'' n) (cellTupleF rs' mS'' (Bh + 1) n) = dstar mS'')) ∧
        ∀ mS, Mbr ≤ mS → P.toPoly.domain (copiedSlice mS n) →
          (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
            P.toPoly.labelOf (copiedSlice mS n) a = D) →
          ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
            P.toPoly.labelOf (copiedSlice mS n) b = D →
            (CopiedTieGate.cfgCellGAFL B Bh M (mthr - 2) (S1L (mS % p0'))
                (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (mS % p0'))
                (fun _ _ => ∅) mS n b
              ↔
              (P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n
                ∧ ¬ (∃ l, q_D ≤ l ∧ l < mS - 1 ∧ b.2 = fun _ => mS + 2 * n + 1 + l)
                ∧ ¬ (∃ q, q_U ≤ q ∧ q < mS - 1 ∧ b.2 = fun _ => q))) := by
    intro dstar N0 hdaff hdagree
    -- ===== S2b: the bulk & frozen equal-rank EP-in-mS families against selB, at p0' =====
    -- bulk arm (bound B): for ds ∈ mixedTuplesF B, "cell rank = selB" is EP-in-mS at p0'
    have hBkEP : ∀ (c' : Fin P.toPoly.K)
        (ds : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (t : ℕ),
        ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') → t + B ≤ n →
        EventuallyPeriodic
          (fun mS => P.rank c' (copiedSlice mS n) (mixedTupleF ds mS t n)
            = dstar mS) p0' := by
      intro c' ds t hds htBn
      refine vec_eq_EP_at hp0'1 (fun i => ?_) hdaff
      obtain ⟨pp, hpp1, hpdvd, _, hAff⟩ := hcertB c' ds hds t n htBn
      exact (hAff i).of_dvd hpp1 (dvd_trans hpdvd hpsBdvd) hp0'1
    -- frozen arm (bound Bh): for ds ∈ mixedTuplesF Bh, "cell rank = selB" is EP-in-mS at p0'
    have hFzEP : ∀ (c' : Fin P.toPoly.K)
        (ds : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh ⊕ (ℕ ⊕ ℕ)) (t : ℕ),
        ds ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c') → t + Bh ≤ n →
        EventuallyPeriodic
          (fun mS => P.rank c' (copiedSlice mS n) (mixedTupleF ds mS t n)
            = dstar mS) p0' := by
      intro c' ds t hds htBn
      refine vec_eq_EP_at hp0'1 (fun i => ?_) hdaff
      obtain ⟨pp, hpp1, hpdvd, _, hAff⟩ := hcertBh c' ds hds t n htBn
      exact (hAff i).of_dvd hpp1 (dvd_trans hpdvd hpsBhdvd) hp0'1
    -- ===== S4: the threshold Mbr (sup over the finite mixedTuplesF of the EP thresholds + agreement) =====
    set NEP : ℕ :=
      (Finset.univ.sup (fun c' : Fin P.toPoly.K =>
        (mixedTuplesF B q_U q_D (P.toPoly.arity c')).sup (fun ds =>
          (Finset.range (2 * p)).sup (fun r =>
            if h : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') ∧ (A0 + r) + B ≤ n
            then (hBkEP c' ds (A0 + r) h.1 h.2).choose else 0))))
      ⊔ (Finset.univ.sup (fun c' : Fin P.toPoly.K =>
        (mixedTuplesF Bh q_U q_D (P.toPoly.arity c')).sup (fun ds =>
          if h : ds ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c') ∧ (Bh + 1) + Bh ≤ n
          then (hFzEP c' ds (Bh + 1) h.1 h.2).choose else 0))) with hNEPdef
    set Mbr : ℕ := max N0 (max (max (2 * q_D + 2) (2 * q_U + 2)) (max 1 NEP)) with hMbrdef
    have hMbr1 : 1 ≤ Mbr := by omega
    -- ===== S5: representative, emitters, hygiene =====
    set rep' : ℕ → ℕ := fun κ => Mbr * p0' + κ with hrep'def
    set S1 : ℕ → (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ :=
      fun κ c' rs =>
        if (∀ i, clusterFreeF (rs i) = true) then ∅
        else ((Finset.range p).filter (fun r =>
          P.rank c' (copiedSlice (rep' κ) n) (cellTupleF rs (rep' κ) (A0 + r) n)
            = dstar (rep' κ)
          ∧ P.rank c' (copiedSlice (rep' κ) n) (cellTupleF rs (rep' κ) (A0 + (r + p)) n)
            = dstar (rep' κ))).image
          (fun r => (1 + 2 * (A0 + r)) % (2 * p)) with hS1def
    set F2 : ℕ → (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ :=
      fun κ c' rs' =>
        if ((∀ i, clusterFreeF (rs' i) = true)
            ∧ (∀ i, (match rs' i with
                | CopiedCells.RegionSpecF.core _ => (True : Prop)
                | CopiedCells.RegionSpecF.prefIdx q => q < q_U
                | CopiedCells.RegionSpecF.sufIdx l => l < q_D))
            ∧ P.rank c' (copiedSlice (rep' κ) n) (cellTupleF rs' (rep' κ) (Bh + 1) n)
              = dstar (rep' κ))
        then {2 * Bh + 3} else ∅ with hF2def
    set S1L : ℕ → (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ :=
      fun κ c' rs => (S1 κ c' rs).image (fun s => (M + 2 - s) % M) with hS1Ldef
    set F2L : ℕ → (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ :=
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
    have hF2Lhyg : ∀ κ c' rs', ∀ f ∈ F2L κ c' rs', f % 2 = 1 := by
      intro κ c' rs' f hf
      rw [hF2Ldef] at hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
      rw [hF2def] at hg
      simp only [] at hg
      split at hg
      · rw [Finset.mem_singleton] at hg; omega
      · exact absurd hg (Finset.notMem_empty g)
    have hS1Lempty : ∀ κ c' rs, (∀ i, clusterFreeF (rs i) = true) → S1L κ c' rs = ∅ := by
      intro κ c' rs hcf
      have hS1e : S1 κ c' rs = ∅ := by rw [hS1def]; exact if_pos hcf
      simp only [hS1Ldef, hS1e, Finset.image_empty]
    have hF2Lempty : ∀ κ c' rs', ¬ (∀ i, (match rs' i with
          | CopiedCells.RegionSpecF.core _ => (True : Prop)
          | CopiedCells.RegionSpecF.prefIdx q => q < q_U
          | CopiedCells.RegionSpecF.sufIdx l => l < q_D)) → F2L κ c' rs' = ∅ := by
      intro κ c' rs' hns
      have hF2e : F2 κ c' rs' = ∅ := by rw [hF2def]; exact if_neg (fun h => hns h.2.1)
      simp only [hF2Ldef, hF2e, Finset.image_empty]
    -- ===== mS-leg transport iffs @ threshold Mbr (∀ c' mS' mS''), exposed for the bridge =====
    have hbkleGen : ∀ (c' : Fin P.toPoly.K)
        (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) (r : ℕ)
        (hds : (fun j => (Sum.inl (rs j) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)))
          ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c')) (hr : r < 2 * p)
        (htBn : (A0 + r) + B ≤ n),
        (hBkEP c' (fun j => Sum.inl (rs j)) (A0 + r) hds htBn).choose ≤ Mbr := by
      intro c' rs r hds hr htBn
      set f : ℕ → ℕ := fun r' =>
        if h : (fun j => (Sum.inl (rs j) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)))
            ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') ∧ (A0 + r') + B ≤ n
        then (hBkEP c' (fun j => Sum.inl (rs j)) (A0 + r') h.1 h.2).choose else 0 with hfdef
      have hr_eq : f r = (hBkEP c' (fun j => Sum.inl (rs j)) (A0 + r) hds htBn).choose := by
        rw [hfdef]; simp only []; rw [dif_pos ⟨hds, htBn⟩]
      have h1 : f r ≤ (Finset.range (2 * p)).sup f := Finset.le_sup (Finset.mem_range.mpr hr)
      have h2 : (Finset.range (2 * p)).sup f
          ≤ (mixedTuplesF B q_U q_D (P.toPoly.arity c')).sup
              (fun ds => (Finset.range (2 * p)).sup (fun r' =>
                if h : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') ∧ (A0 + r') + B ≤ n
                then (hBkEP c' ds (A0 + r') h.1 h.2).choose else 0)) :=
        Finset.le_sup (f := fun ds => (Finset.range (2 * p)).sup (fun r' =>
          if h : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') ∧ (A0 + r') + B ≤ n
          then (hBkEP c' ds (A0 + r') h.1 h.2).choose else 0)) hds
      have h3 : (mixedTuplesF B q_U q_D (P.toPoly.arity c')).sup
              (fun ds => (Finset.range (2 * p)).sup (fun r' =>
                if h : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') ∧ (A0 + r') + B ≤ n
                then (hBkEP c' ds (A0 + r') h.1 h.2).choose else 0))
          ≤ Finset.univ.sup (fun c'' : Fin P.toPoly.K =>
              (mixedTuplesF B q_U q_D (P.toPoly.arity c'')).sup (fun ds =>
                (Finset.range (2 * p)).sup (fun r' =>
                  if h : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c'') ∧ (A0 + r') + B ≤ n
                  then (hBkEP c'' ds (A0 + r') h.1 h.2).choose else 0))) :=
        Finset.le_sup (f := fun c'' : Fin P.toPoly.K =>
          (mixedTuplesF B q_U q_D (P.toPoly.arity c'')).sup (fun ds =>
            (Finset.range (2 * p)).sup (fun r' =>
              if h : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c'') ∧ (A0 + r') + B ≤ n
              then (hBkEP c'' ds (A0 + r') h.1 h.2).choose else 0))) (Finset.mem_univ c')
      have h4 : Finset.univ.sup (fun c'' : Fin P.toPoly.K =>
              (mixedTuplesF B q_U q_D (P.toPoly.arity c'')).sup (fun ds =>
                (Finset.range (2 * p)).sup (fun r' =>
                  if h : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c'') ∧ (A0 + r') + B ≤ n
                  then (hBkEP c'' ds (A0 + r') h.1 h.2).choose else 0))) ≤ NEP := by
        rw [hNEPdef]; exact le_max_left _ _
      have h5 : NEP ≤ Mbr := by omega
      rw [← hr_eq]; omega
    have hfzleGen : ∀ (c' : Fin P.toPoly.K)
        (rs' : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh)
        (hds : (fun j => (Sum.inl (rs' j) : CopiedCells.RegionSpecF Bh ⊕ (ℕ ⊕ ℕ)))
          ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c')) (htBn : (Bh + 1) + Bh ≤ n),
        (hFzEP c' (fun j => Sum.inl (rs' j)) (Bh + 1) hds htBn).choose ≤ Mbr := by
      intro c' rs' hds htBn
      set g : (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh ⊕ (ℕ ⊕ ℕ)) → ℕ :=
        fun ds => if h : ds ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c') ∧ (Bh + 1) + Bh ≤ n
          then (hFzEP c' ds (Bh + 1) h.1 h.2).choose else 0 with hgdef
      have hg_eq : g (fun j => Sum.inl (rs' j))
          = (hFzEP c' (fun j => Sum.inl (rs' j)) (Bh + 1) hds htBn).choose := by
        rw [hgdef]; simp only []; rw [dif_pos ⟨hds, htBn⟩]
      have h2 : g (fun j => Sum.inl (rs' j))
          ≤ (mixedTuplesF Bh q_U q_D (P.toPoly.arity c')).sup g := Finset.le_sup hds
      have h3 : (mixedTuplesF Bh q_U q_D (P.toPoly.arity c')).sup g
          ≤ Finset.univ.sup (fun c'' : Fin P.toPoly.K =>
              (mixedTuplesF Bh q_U q_D (P.toPoly.arity c'')).sup (fun ds =>
                if h : ds ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c'') ∧ (Bh + 1) + Bh ≤ n
                then (hFzEP c'' ds (Bh + 1) h.1 h.2).choose else 0)) :=
        Finset.le_sup (f := fun c'' : Fin P.toPoly.K =>
          (mixedTuplesF Bh q_U q_D (P.toPoly.arity c'')).sup (fun ds =>
            if h : ds ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c'') ∧ (Bh + 1) + Bh ≤ n
            then (hFzEP c'' ds (Bh + 1) h.1 h.2).choose else 0)) (Finset.mem_univ c')
      have h4 : Finset.univ.sup (fun c'' : Fin P.toPoly.K =>
              (mixedTuplesF Bh q_U q_D (P.toPoly.arity c'')).sup (fun ds =>
                if h : ds ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c'') ∧ (Bh + 1) + Bh ≤ n
                then (hFzEP c'' ds (Bh + 1) h.1 h.2).choose else 0)) ≤ NEP := by
        rw [hNEPdef]; exact le_max_right _ _
      have h5 : NEP ≤ Mbr := by omega
      rw [← hg_eq]; omega
    have hbkTransGen : ∀ (c' : Fin P.toPoly.K)
        (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) (r mS' mS'' : ℕ),
        (fun j => (Sum.inl (rs j) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)))
          ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') → r < 2 * p → (A0 + r) + B ≤ n →
        Mbr ≤ mS' → Mbr ≤ mS'' → mS' % p0' = mS'' % p0' →
        (P.rank c' (copiedSlice mS' n) (cellTupleF rs mS' (A0 + r) n) = dstar mS' ↔
         P.rank c' (copiedSlice mS'' n) (cellTupleF rs mS'' (A0 + r) n) = dstar mS'') := by
      intro c' rs r mS' mS'' hds hr htBn hM' hM'' hmod
      have hconv : ∀ x, cellTupleF rs x (A0 + r) n
          = mixedTupleF (fun j => Sum.inl (rs j)) x (A0 + r) n := by
        intro x; funext j; simp only [cellTupleF, mixedTupleF, mixedPosAt]
      have hspec := (hBkEP c' (fun j => Sum.inl (rs j)) (A0 + r) hds htBn).choose_spec
      have hm0le := hbkleGen c' rs r hds hr htBn
      refine SliceFasSelector.iff_on_class
        (Pr := fun x => P.rank c' (copiedSlice x n) (cellTupleF rs x (A0 + r) n) = dstar x)
        hp0'1 ?_ (le_trans hm0le hM') (le_trans hm0le hM'') hmod
      intro x hx
      simp only [hconv]
      exact hspec x hx
    have hfzTransGen : ∀ (c' : Fin P.toPoly.K)
        (rs' : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) (mS' mS'' : ℕ),
        (fun j => (Sum.inl (rs' j) : CopiedCells.RegionSpecF Bh ⊕ (ℕ ⊕ ℕ)))
          ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c') → (Bh + 1) + Bh ≤ n →
        Mbr ≤ mS' → Mbr ≤ mS'' → mS' % p0' = mS'' % p0' →
        (P.rank c' (copiedSlice mS' n) (cellTupleF rs' mS' (Bh + 1) n) = dstar mS' ↔
         P.rank c' (copiedSlice mS'' n) (cellTupleF rs' mS'' (Bh + 1) n) = dstar mS'') := by
      intro c' rs' mS' mS'' hds htBn hM' hM'' hmod
      have hconv : ∀ x, cellTupleF rs' x (Bh + 1) n
          = mixedTupleF (fun j => Sum.inl (rs' j)) x (Bh + 1) n := by
        intro x; funext j; simp only [cellTupleF, mixedTupleF, mixedPosAt]
      have hspec := (hFzEP c' (fun j => Sum.inl (rs' j)) (Bh + 1) hds htBn).choose_spec
      have hm0le := hfzleGen c' rs' hds htBn
      refine SliceFasSelector.iff_on_class
        (Pr := fun x => P.rank c' (copiedSlice x n) (cellTupleF rs' x (Bh + 1) n) = dstar x)
        hp0'1 ?_ (le_trans hm0le hM') (le_trans hm0le hM'') hmod
      intro x hx
      simp only [hconv]
      exact hspec x hx
    refine ⟨Mbr, S1, F2, S1L, F2L, hMbr1, hS1Lhyg, hF2Lhyg, hS1Lempty, hF2Lempty,
      (by intro κ c' rs; simp only [hS1def, hrep'def]),
      (by intro κ c' rs'; simp only [hF2def, hrep'def]),
      (by intro κ c' rs; simp only [hS1Ldef]),
      (by intro κ c' rs'; simp only [hF2Ldef]),
      (fun mS hmS hdom hDp =>
        hdagree mS (le_trans (by rw [hMbrdef]; exact le_max_left _ _) hmS) hdom hDp),
      hbkTransGen, hfzTransGen, ?_⟩
    -- ===== S6: per-(mS) entry, class κ, modular facts, agreement =====
    intro mS hmS hdom hDpres b hbsel hbD
    obtain ⟨c', ī⟩ := b
    have hagree : CopiedDstar.dstarRankGA_m P hV mS n = dstar mS :=
      hdagree mS (by omega) hdom hDpres
    set κ : ℕ := mS % p0' with hκdef
    have hκlt : κ < p0' := Nat.mod_lt _ hp0'1
    have hrep'mod : rep' κ % p0' = κ := by
      rw [hrep'def]; simp only []
      rw [Nat.mul_comm Mbr p0', Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hκlt
    have hrep'Mbr : Mbr ≤ rep' κ := by
      rw [hrep'def]; simp only []
      have := Nat.le_mul_of_pos_right Mbr hp0'1
      omega
    have hmodeq : mS % p0' = rep' κ % p0' := by rw [hrep'mod, hκdef]
    have hrankunfold : P.rankOf (copiedSlice mS n) ⟨c', ī⟩
        = P.rank c' (copiedSlice mS n) ī := rfl
    -- ===== S4b: the EP thresholds are ≤ Mbr (from the NEP sup) =====
    have hbkle : ∀ (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) (r : ℕ)
        (hds : (fun j => (Sum.inl (rs j) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)))
          ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c')) (hr : r < 2 * p) (htBn : (A0 + r) + B ≤ n),
        (hBkEP c' (fun j => Sum.inl (rs j)) (A0 + r) hds htBn).choose ≤ Mbr := by
      intro rs r hds hr htBn
      set f : ℕ → ℕ := fun r' =>
        if h : (fun j => (Sum.inl (rs j) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)))
            ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') ∧ (A0 + r') + B ≤ n
        then (hBkEP c' (fun j => Sum.inl (rs j)) (A0 + r') h.1 h.2).choose else 0 with hfdef
      have hr_eq : f r = (hBkEP c' (fun j => Sum.inl (rs j)) (A0 + r) hds htBn).choose := by
        rw [hfdef]; simp only []; rw [dif_pos ⟨hds, htBn⟩]
      have h1 : f r ≤ (Finset.range (2 * p)).sup f := Finset.le_sup (Finset.mem_range.mpr hr)
      have h2 : (Finset.range (2 * p)).sup f
          ≤ (mixedTuplesF B q_U q_D (P.toPoly.arity c')).sup
              (fun ds => (Finset.range (2 * p)).sup (fun r' =>
                if h : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') ∧ (A0 + r') + B ≤ n
                then (hBkEP c' ds (A0 + r') h.1 h.2).choose else 0)) :=
        Finset.le_sup (f := fun ds => (Finset.range (2 * p)).sup (fun r' =>
          if h : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') ∧ (A0 + r') + B ≤ n
          then (hBkEP c' ds (A0 + r') h.1 h.2).choose else 0)) hds
      have h3 : (mixedTuplesF B q_U q_D (P.toPoly.arity c')).sup
              (fun ds => (Finset.range (2 * p)).sup (fun r' =>
                if h : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') ∧ (A0 + r') + B ≤ n
                then (hBkEP c' ds (A0 + r') h.1 h.2).choose else 0))
          ≤ Finset.univ.sup (fun c'' : Fin P.toPoly.K =>
              (mixedTuplesF B q_U q_D (P.toPoly.arity c'')).sup (fun ds =>
                (Finset.range (2 * p)).sup (fun r' =>
                  if h : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c'') ∧ (A0 + r') + B ≤ n
                  then (hBkEP c'' ds (A0 + r') h.1 h.2).choose else 0))) :=
        Finset.le_sup (f := fun c'' : Fin P.toPoly.K =>
          (mixedTuplesF B q_U q_D (P.toPoly.arity c'')).sup (fun ds =>
            (Finset.range (2 * p)).sup (fun r' =>
              if h : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c'') ∧ (A0 + r') + B ≤ n
              then (hBkEP c'' ds (A0 + r') h.1 h.2).choose else 0))) (Finset.mem_univ c')
      have h4 : Finset.univ.sup (fun c'' : Fin P.toPoly.K =>
              (mixedTuplesF B q_U q_D (P.toPoly.arity c'')).sup (fun ds =>
                (Finset.range (2 * p)).sup (fun r' =>
                  if h : ds ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c'') ∧ (A0 + r') + B ≤ n
                  then (hBkEP c'' ds (A0 + r') h.1 h.2).choose else 0))) ≤ NEP := by
        rw [hNEPdef]; exact le_max_left _ _
      have h5 : NEP ≤ Mbr := by omega
      rw [← hr_eq]; omega
    have hfzle : ∀ (rs' : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh)
        (hds : (fun j => (Sum.inl (rs' j) : CopiedCells.RegionSpecF Bh ⊕ (ℕ ⊕ ℕ)))
          ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c')) (htBn : (Bh + 1) + Bh ≤ n),
        (hFzEP c' (fun j => Sum.inl (rs' j)) (Bh + 1) hds htBn).choose ≤ Mbr := by
      intro rs' hds htBn
      set g : (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh ⊕ (ℕ ⊕ ℕ)) → ℕ :=
        fun ds => if h : ds ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c') ∧ (Bh + 1) + Bh ≤ n
          then (hFzEP c' ds (Bh + 1) h.1 h.2).choose else 0 with hgdef
      have hg_eq : g (fun j => Sum.inl (rs' j))
          = (hFzEP c' (fun j => Sum.inl (rs' j)) (Bh + 1) hds htBn).choose := by
        rw [hgdef]; simp only []; rw [dif_pos ⟨hds, htBn⟩]
      have h2 : g (fun j => Sum.inl (rs' j))
          ≤ (mixedTuplesF Bh q_U q_D (P.toPoly.arity c')).sup g := Finset.le_sup hds
      have h3 : (mixedTuplesF Bh q_U q_D (P.toPoly.arity c')).sup g
          ≤ Finset.univ.sup (fun c'' : Fin P.toPoly.K =>
              (mixedTuplesF Bh q_U q_D (P.toPoly.arity c'')).sup (fun ds =>
                if h : ds ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c'') ∧ (Bh + 1) + Bh ≤ n
                then (hFzEP c'' ds (Bh + 1) h.1 h.2).choose else 0)) :=
        Finset.le_sup (f := fun c'' : Fin P.toPoly.K =>
          (mixedTuplesF Bh q_U q_D (P.toPoly.arity c'')).sup (fun ds =>
            if h : ds ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c'') ∧ (Bh + 1) + Bh ≤ n
            then (hFzEP c'' ds (Bh + 1) h.1 h.2).choose else 0)) (Finset.mem_univ c')
      have h4 : Finset.univ.sup (fun c'' : Fin P.toPoly.K =>
              (mixedTuplesF Bh q_U q_D (P.toPoly.arity c'')).sup (fun ds =>
                if h : ds ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c'') ∧ (Bh + 1) + Bh ≤ n
                then (hFzEP c'' ds (Bh + 1) h.1 h.2).choose else 0)) ≤ NEP := by
        rw [hNEPdef]; exact le_max_right _ _
      have h5 : NEP ≤ Mbr := by omega
      rw [← hg_eq]; omega
    -- ===== S7: the two equal-rank transports mS ↔ rep' κ (via the EP families + iff_on_class) =====
    have htransBk : ∀ (rs : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) (r : ℕ)
        (hds : (fun j => (Sum.inl (rs j) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)))
          ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c')) (hr : r < 2 * p) (htBn : (A0 + r) + B ≤ n),
        ((P.rank c' (copiedSlice mS n) (cellTupleF rs mS (A0 + r) n)
            = dstar mS) ↔
         (P.rank c' (copiedSlice (rep' κ) n) (cellTupleF rs (rep' κ) (A0 + r) n)
            = dstar (rep' κ))) := by
      intro rs r hds hr htBn
      have hconv : ∀ x, cellTupleF rs x (A0 + r) n
          = mixedTupleF (fun j => Sum.inl (rs j)) x (A0 + r) n := by
        intro x; funext j; simp only [cellTupleF, mixedTupleF, mixedPosAt]
      have hspec := (hBkEP c' (fun j => Sum.inl (rs j)) (A0 + r) hds htBn).choose_spec
      have hm0le : (hBkEP c' (fun j => Sum.inl (rs j)) (A0 + r) hds htBn).choose ≤ Mbr :=
        hbkle rs r hds hr htBn
      refine SliceFasSelector.iff_on_class
        (Pr := fun x => P.rank c' (copiedSlice x n) (cellTupleF rs x (A0 + r) n)
          = dstar x)
        hp0'1 ?_ (le_trans hm0le hmS) (le_trans hm0le hrep'Mbr) hmodeq
      intro x hx
      simp only [hconv]
      exact hspec x hx
    have htransFz : ∀ (rs' : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh)
        (hds : (fun j => (Sum.inl (rs' j) : CopiedCells.RegionSpecF Bh ⊕ (ℕ ⊕ ℕ)))
          ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c')) (htBn : (Bh + 1) + Bh ≤ n),
        ((P.rank c' (copiedSlice mS n) (cellTupleF rs' mS (Bh + 1) n)
            = dstar mS) ↔
         (P.rank c' (copiedSlice (rep' κ) n) (cellTupleF rs' (rep' κ) (Bh + 1) n)
            = dstar (rep' κ))) := by
      intro rs' hds htBn
      have hconv : ∀ x, cellTupleF rs' x (Bh + 1) n
          = mixedTupleF (fun j => Sum.inl (rs' j)) x (Bh + 1) n := by
        intro x; funext j; simp only [cellTupleF, mixedTupleF, mixedPosAt]
      have hspec := (hFzEP c' (fun j => Sum.inl (rs' j)) (Bh + 1) hds htBn).choose_spec
      have hm0le : (hFzEP c' (fun j => Sum.inl (rs' j)) (Bh + 1) hds htBn).choose ≤ Mbr :=
        hfzle rs' hds htBn
      refine SliceFasSelector.iff_on_class
        (Pr := fun x => P.rank c' (copiedSlice x n) (cellTupleF rs' x (Bh + 1) n)
          = dstar x)
        hp0'1 ?_ (le_trans hm0le hmS) (le_trans hm0le hrep'Mbr) hmodeq
      intro x hx
      simp only [hconv]
      exact hspec x hx
    -- ===== S8/S9: the iff =====
    have hm1 : 1 ≤ mS := by omega
    obtain ⟨Rcell, Bcell, PR, PBn, hwineq, hRrec, hBrec⟩ := hsetup mS hm1
    have hagree' : CopiedDstar.dstarRankGA' P hV (copiedSlice mS n)
        = dstar mS := hagree
    -- a SHALLOW cell (core / prefIdx q<q_U / sufIdx l<q_D) is never in the deep bands (used by MP)
    have hndeep_of_shallow : ∀ {Dd : ℕ} (rsx : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Dd)
        (tx : ℕ), tx + Dd ≤ n →
        (∀ i, (match rsx i with
          | CopiedCells.RegionSpecF.core _ => (True : Prop)
          | CopiedCells.RegionSpecF.prefIdx q => q < q_U
          | CopiedCells.RegionSpecF.sufIdx l => l < q_D)) →
        ī = cellTupleF rsx mS tx n →
        (¬ (∃ l, q_D ≤ l ∧ l < mS - 1 ∧ ī = fun _ => mS + 2 * n + 1 + l)
          ∧ ¬ (∃ q, q_U ≤ q ∧ q < mS - 1 ∧ ī = fun _ => q)) := by
      intro Dd rsx tx htx hsh hīeq
      have j0 : Fin (P.toPoly.arity c') := ⟨0, by rw [harity1 c']; exact Nat.zero_lt_one⟩
      have hī0 : ī j0 = (rsx j0).posAt mS tx n := by rw [hīeq]; rfl
      have hqU : q_U ≤ mS := by omega
      have hqD : q_D ≤ mS := by omega
      have hshj := hsh j0
      constructor
      · rintro ⟨l, hl1, hl2, hleq⟩
        have hīl : (rsx j0).posAt mS tx n = mS + 2 * n + 1 + l := by rw [← hī0, hleq]
        revert hshj
        cases hrsx : rsx j0 with
        | core r =>
          intro _
          rw [hrsx] at hīl
          have hhi : (CopiedCells.RegionSpecF.core r).posAt mS tx n < mS + 2 * n + 1 := by
            rcases r with _ | _ | ⟨f, e⟩ | ⟨l', e⟩ | ⟨δ, e⟩ <;>
              simp only [CopiedCells.RegionSpecF.posAt, RegionSpec.posAt]
            · omega
            · omega
            · have := f.isLt; cases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
            · have := l'.isLt; cases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
            · have := δ.isLt; cases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
          omega
        | prefIdx q =>
          intro hshj; rw [hrsx] at hīl
          simp only [CopiedCells.RegionSpecF.posAt] at hīl; omega
        | sufIdx l' =>
          intro hshj; rw [hrsx] at hīl
          simp only [CopiedCells.RegionSpecF.posAt] at hīl; omega
      · rintro ⟨q, hq1, hq2, hqeq⟩
        have hīq : (rsx j0).posAt mS tx n = q := by rw [← hī0, hqeq]
        revert hshj
        cases hrsx : rsx j0 with
        | core r =>
          intro _
          rw [hrsx] at hīq
          have hlo : mS - 1 ≤ (CopiedCells.RegionSpecF.core r).posAt mS tx n := by
            simp only [CopiedCells.RegionSpecF.posAt]; omega
          omega
        | prefIdx q' =>
          intro hshj; rw [hrsx] at hīq
          simp only [CopiedCells.RegionSpecF.posAt] at hīq; omega
        | sufIdx l' =>
          intro hshj; rw [hrsx] at hīq
          simp only [CopiedCells.RegionSpecF.posAt] at hīq; omega
    refine ⟨?_, ?_⟩
    · -- ===== MP: cfgCellGAFL → rankOf = d* ∧ ¬DeepSuf ∧ ¬DeepPre =====
      intro hcfg
      have hss : Subsingleton (Fin (P.toPoly.arity c')) := by rw [harity1 c']; infer_instance
      rcases hcfg with ⟨rs, t, hv, hzlt, hcellM, hcfgpos⟩ | ⟨rs', t', hv', hzlt', hcellM', hcfgpos'⟩
      · -- BULK arm
        obtain ⟨_, harm⟩ := hcfgpos
        rcases harm with ⟨hge, hle, r', hr'mem, hreq⟩ | hfront | hback
        · rw [hS1Ldef] at hr'mem
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
            obtain ⟨hrR, hach_r, hach_rp⟩ := Finset.mem_filter.mp hrmem
            have hr : r < p := Finset.mem_range.mp hrR
            have hmod : (t - A0) % p = r :=
              (SliceFasSelectorGA.base_mod_iff A0 p t r hp hr (by omega)).mp hrimg.symm
            have htn_t : t + B ≤ n := by omega
            have hcellM2 : ī = CopiedDstar.cellTupleF rs mS t n := hcellM
            have hsh_bulk : ∀ i, (match rs i with
                | CopiedCells.RegionSpecF.core _ => (True : Prop)
                | CopiedCells.RegionSpecF.prefIdx q => q < q_U
                | CopiedCells.RegionSpecF.sufIdx l => l < q_D) := by
              intro i
              rcases hrsi : rs i with r0 | q | l
              · trivial
              · exfalso; apply hcf; intro i'; rw [Subsingleton.elim i' i, hrsi]; rfl
              · exfalso; apply hcf; intro i'; rw [Subsingleton.elim i' i, hrsi]; rfl
            have hds : (fun j => (Sum.inl (rs j) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)))
                ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') := by
              rw [mem_mixedTuplesF]; intro j; rw [mem_coordCands]
              have hshj := hsh_bulk j
              revert hshj
              cases rs j with
              | core r0 => intro _; exact Or.inl ⟨r0, rfl⟩
              | prefIdx q => intro hshj; exact Or.inr (Or.inl ⟨q, hshj, rfl⟩)
              | sufIdx l => intro hshj; exact Or.inr (Or.inr (Or.inl ⟨l, hshj, rfl⟩))
            have hach_r_mS := (htransBk rs r hds (by omega) (by omega)).mpr hach_r
            have hach_rp_mS := (htransBk rs (r + p) hds (by omega) (by omega)).mpr hach_rp
            have hrr := hRrec c' rs (A0 + r) (by omega)
            have heq : Rcell c' rs (A0 + (r + p)) = Rcell c' rs (A0 + r) := by
              have h1 : (fun i => Rcell c' rs (A0 + (r + p)) i + Bcell c' rs n i)
                  = dstar mS := by
                rw [← hwineq c' rs hv (A0 + (r + p)) n (by omega) (by omega)]; exact hach_rp_mS
              have h2 : (fun i => Rcell c' rs (A0 + r) i + Bcell c' rs n i)
                  = dstar mS := by
                rw [← hwineq c' rs hv (A0 + r) n (by omega) (by omega)]; exact hach_r_mS
              funext i
              have e1 := congrFun (h1.trans h2.symm) i
              omega
            have hPR0 : PR c' rs = (fun _ => 0) := by
              rw [show A0 + r + p = A0 + (r + p) from by ring] at hrr
              rw [heq] at hrr
              funext i; have h := congrFun hrr i; simp only [Pi.add_apply] at h; omega
            have hchain0 : Rcell c' rs t = Rcell c' rs (A0 + r) := by
              have hteq : t = A0 + r + p * ((t - A0) / p) := by
                have := Nat.mod_add_div (t - A0) p; omega
              have hcv : ∀ k, Rcell c' rs (A0 + r + p * k)
                  = Rcell c' rs (A0 + r) + k • PR c' rs :=
                fun k => SliceRankAtom.RankAffine.iterate (fun j hj => hRrec c' rs j hj)
                  (A0 + r) k (by omega)
              conv_lhs => rw [hteq]
              rw [hcv ((t - A0) / p), hPR0]; funext i; simp
            have hfin : P.rank c' (copiedSlice mS n) ī = dstar mS := by
              rw [hcellM2, hwineq c' rs hv t n (by omega) (by omega), hchain0,
                ← hwineq c' rs hv (A0 + r) n (by omega) (by omega)]
              exact hach_r_mS
            refine ⟨?_, ?_, ?_⟩
            · rw [hrankunfold, hagree]; exact hfin
            · exact (hndeep_of_shallow rs t htn_t hsh_bulk hcellM2).1
            · exact (hndeep_of_shallow rs t htn_t hsh_bulk hcellM2).2
        · obtain ⟨f', hf'mem, _⟩ := hfront; exact absurd hf'mem (Finset.notMem_empty _)
        · obtain ⟨k, hk, _⟩ := hback; exact absurd hk (Finset.notMem_empty _)
      · -- FROZEN arm
        obtain ⟨_, harm⟩ := hcfgpos'
        rcases harm with ⟨_, _, r', hr'mem, _⟩ | hfront | hback
        · exact absurd hr'mem (Finset.notMem_empty _)
        · obtain ⟨f', hf'mem, hcase⟩ := hfront
          rw [hF2Ldef] at hf'mem
          simp only [] at hf'mem
          obtain ⟨g, hgmem, rfl⟩ := Finset.mem_image.mp hf'mem
          rw [hF2def] at hgmem
          simp only [] at hgmem
          by_cases hcond : (∀ i, clusterFreeF (rs' i) = true)
              ∧ (∀ i, (match rs' i with
                  | CopiedCells.RegionSpecF.core _ => (True : Prop)
                  | CopiedCells.RegionSpecF.prefIdx q => q < q_U
                  | CopiedCells.RegionSpecF.sufIdx l => l < q_D))
              ∧ P.rank c' (copiedSlice (rep' κ) n) (cellTupleF rs' (rep' κ) (Bh + 1) n)
                = dstar (rep' κ)
          · rw [if_pos hcond] at hgmem
            rw [Finset.mem_singleton] at hgmem
            have ht'eq : t' = Bh + 1 := by rcases hcase with ⟨hf0, _⟩ | ⟨_, hz⟩ <;> omega
            subst ht'eq
            have hcellM'2 : ī = CopiedDstar.cellTupleF rs' mS (Bh + 1) n := hcellM'
            have hds' : (fun j => (Sum.inl (rs' j) : CopiedCells.RegionSpecF Bh ⊕ (ℕ ⊕ ℕ)))
                ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c') := by
              rw [mem_mixedTuplesF]; intro j; rw [mem_coordCands]
              have hshj := hcond.2.1 j
              revert hshj
              cases rs' j with
              | core r0 => intro _; exact Or.inl ⟨r0, rfl⟩
              | prefIdx q => intro hshj; exact Or.inr (Or.inl ⟨q, hshj, rfl⟩)
              | sufIdx l => intro hshj; exact Or.inr (Or.inr (Or.inl ⟨l, hshj, rfl⟩))
            have hfin : P.rank c' (copiedSlice mS n) ī = dstar mS := by
              rw [hcellM'2]; exact (htransFz rs' hds' (by omega)).mpr hcond.2.2
            refine ⟨?_, ?_, ?_⟩
            · rw [hrankunfold, hagree]; exact hfin
            · exact (hndeep_of_shallow rs' (Bh + 1) (by omega) hcond.2.1 hcellM'2).1
            · exact (hndeep_of_shallow rs' (Bh + 1) (by omega) hcond.2.1 hcellM'2).2
          · rw [if_neg hcond] at hgmem; exact absurd hgmem (Finset.notMem_empty _)
        · obtain ⟨k, hk, _⟩ := hback; exact absurd hk (Finset.notMem_empty _)
    · -- ===== MPR: rankOf = d* ∧ ¬DeepSuf ∧ ¬DeepPre → cfgCellGAFL =====
      rintro ⟨hrank, hndsuf, hndpre⟩
      have hrkC : P.rank c' (copiedSlice mS n) ī = dstar mS := by
        rw [← hrankunfold, hrank, hagree]
      have hlenW : (wrappedFlat n).length = 2 * (n + 1) := length_wrappedFlat n
      -- the frozen emitter: a cluster-free + SHALLOW cell achieving d* fires the F2 arm
      have emitFrozen : ∀ rs' : Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh,
          (∀ i, clusterFreeF (rs' i) = true) →
          (∀ i, (match rs' i with
              | CopiedCells.RegionSpecF.core _ => (True : Prop)
              | CopiedCells.RegionSpecF.prefIdx q => q < q_U
              | CopiedCells.RegionSpecF.sufIdx l => l < q_D)) →
          (∀ i, (rs' i).valid mS) →
          ī = cellTupleF rs' mS (Bh + 1) n →
          CopiedSelector.cfgCellArmF Bh M mthr (fun _ _ => ∅) (F2 κ) (fun _ _ => ∅) mS n ⟨c', ī⟩ := by
        intro rs' hcf' hsh' hv' hcellr
        have hach_mS : P.rank c' (copiedSlice mS n) (cellTupleF rs' mS (Bh + 1) n)
            = dstar mS := by rw [← hcellr]; exact hrkC
        have hds : (fun j => (Sum.inl (rs' j) : CopiedCells.RegionSpecF Bh ⊕ (ℕ ⊕ ℕ)))
            ∈ mixedTuplesF Bh q_U q_D (P.toPoly.arity c') := by
          rw [mem_mixedTuplesF]; intro j; rw [mem_coordCands]
          have hshj := hsh' j
          revert hshj
          cases rs' j with
          | core r => intro _; exact Or.inl ⟨r, rfl⟩
          | prefIdx q => intro hshj; exact Or.inr (Or.inl ⟨q, hshj, rfl⟩)
          | sufIdx l => intro hshj; exact Or.inr (Or.inr (Or.inl ⟨l, hshj, rfl⟩))
        have hach_rep := (htransFz rs' hds (by omega)).mp hach_mS
        refine ⟨rs', Bh + 1, hv', by omega, hcellr, Or.inr (Or.inl ?_)⟩
        show (1 + 2 * (Bh + 1)) ∈ F2 κ c' rs'
        rw [hF2def]; simp only []
        rw [if_pos ⟨hcf', hsh', hach_rep⟩, show 1 + 2 * (Bh + 1) = 2 * Bh + 3 from by omega]
        exact Finset.mem_singleton_self _
      suffices hGAF : CopiedSelector.cfgCellGAF B Bh M mthr (S1 κ) (F2 κ) mS n ⟨c', ī⟩ by
        simp only [hS1Ldef, hF2Ldef]
        exact CopiedSelector.cfgCellGAF_imp_cfgCellGAFL B Bh M mthr (S1 κ) (F2 κ) mS n ⟨c', ī⟩
          hM hm1 hB1 hBh1 (by omega) hGAF
      obtain ⟨t, rs, htB, htn0, hrsv, hcell⟩ :=
        cells_cover_one_mS P c' (harity1 c') B hB1 mS n hm1 (by omega) ī hbsel.1
      have hss : Subsingleton (Fin (P.toPoly.arity c')) := by rw [harity1 c']; infer_instance
      have j0 : Fin (P.toPoly.arity c') := ⟨0, by rw [harity1 c']; exact Nat.zero_lt_one⟩
      -- the cover descriptor is SHALLOW (from ¬DeepSuf/¬DeepPre): every lift/freeze preserves this
      have hīconst : ī = fun _ => (rs j0).posAt mS t n := by
        funext j; rw [hcell]
        exact congrArg (fun jj => (rs jj).posAt mS t n) (Subsingleton.elim j j0)
      have hshallow_rs : ∀ i, (match rs i with
          | CopiedCells.RegionSpecF.core _ => (True : Prop)
          | CopiedCells.RegionSpecF.prefIdx q => q < q_U
          | CopiedCells.RegionSpecF.sufIdx l => l < q_D) := by
        intro i
        have hii : rs i = rs j0 := congrArg rs (Subsingleton.elim i j0)
        have hvi : (rs j0).valid mS := hii ▸ hrsv i
        rw [hii]
        rcases hrsi : rs j0 with r | q | l
        · trivial
        · show q < q_U
          by_contra hcon; push Not at hcon
          refine hndpre ⟨q, hcon, ?_, ?_⟩
          · have h := hvi; rw [hrsi] at h; exact h
          · rw [hīconst]; funext _; show (rs j0).posAt mS t n = _
            simp [hrsi, CopiedCells.RegionSpecF.posAt]
        · show l < q_D
          by_contra hcon; push Not at hcon
          refine hndsuf ⟨l, hcon, ?_, ?_⟩
          · have h := hvi; rw [hrsi] at h; exact h
          · rw [hīconst]; funext _; show (rs j0).posAt mS t n = _
            simp [hrsi, CopiedCells.RegionSpecF.posAt]
      -- shallowness transfers through any lift that preserves constructors
      have hshallow_lift : ∀ (f : CopiedCells.RegionSpecF B → CopiedCells.RegionSpecF Bh),
          (∀ r, ∃ r', f (CopiedCells.RegionSpecF.core r) = CopiedCells.RegionSpecF.core r') →
          (∀ q, f (CopiedCells.RegionSpecF.prefIdx q) = CopiedCells.RegionSpecF.prefIdx q) →
          (∀ l, f (CopiedCells.RegionSpecF.sufIdx l) = CopiedCells.RegionSpecF.sufIdx l) →
          ∀ i, (match f (rs i) with
            | CopiedCells.RegionSpecF.core _ => (True : Prop)
            | CopiedCells.RegionSpecF.prefIdx q => q < q_U
            | CopiedCells.RegionSpecF.sufIdx l => l < q_D) := by
        intro f hfc hfp hfl i
        have hsh := hshallow_rs i
        rcases hrsi : rs i with r | q | l
        · obtain ⟨r', hr'⟩ := hfc r; rw [hr']; trivial
        · rw [hfp q]; rw [hrsi] at hsh; exact hsh
        · rw [hfl l]; rw [hrsi] at hsh; exact hsh
      by_cases hcf : ∀ i, clusterFreeF (rs i) = true
      · -- cluster-free: lift to Bh and freeze at the dummy base
        refine Or.inr (emitFrozen (fun i => regionLiftF hBB (rs i)) ?_ ?_ ?_ ?_)
        · exact fun i => (clusterFreeF_regionLiftF hBB (rs i)).trans (hcf i)
        · exact hshallow_lift (regionLiftF hBB) (fun r => ⟨_, rfl⟩)
            (fun _ => rfl) (fun _ => rfl)
        · exact fun i => (regionLiftF_valid hBB (rs i) mS).mpr (hrsv i)
        · rw [hcell, ← cellTupleF_regionLiftF hBB rs mS t n]
          exact cellTupleF_clusterFree_base (fun i => regionLiftF hBB (rs i))
            (fun i => (clusterFreeF_regionLiftF hBB (rs i)).trans (hcf i)) mS t (Bh + 1) n
      · rcases Nat.lt_or_ge t tBk with hfront | htlow
        · -- front zone
          have hfrontB : t + B ≤ Bh := by omega
          refine Or.inr (emitFrozen (fun i => refreezeFrontF hBB t hfrontB (rs i))
            (fun i => clusterFreeF_refreezeFrontF hBB t hfrontB (rs i))
            (hshallow_lift (refreezeFrontF hBB t hfrontB) (fun r => ⟨_, rfl⟩)
              (fun _ => rfl) (fun _ => rfl))
            (fun i => refreezeFrontF_valid hBB t hfrontB (rs i) mS (hrsv i)) ?_)
          rw [hcell]; funext i
          exact (refreezeFrontF_posAt hBB t hfrontB (rs i) mS (Bh + 1) n).symm
        rcases Nat.lt_or_ge n (t + tBk) with hback | hbulk
        · -- back zone
          have hbackB : n ≤ t + Bh := by omega
          refine Or.inr (emitFrozen (fun i => refreezeBackF hBB hBh1 t n hbackB (rs i))
            (fun i => clusterFreeF_refreezeBackF hBB hBh1 t n hbackB (rs i))
            (hshallow_lift (refreezeBackF hBB hBh1 t n hbackB) (fun r => ⟨_, rfl⟩)
              (fun _ => rfl) (fun _ => rfl))
            (fun i => refreezeBackF_valid hBB hBh1 t n hbackB (rs i) mS (hrsv i)) ?_)
          rw [hcell]; funext i
          exact (refreezeBackF_posAt hBB hBh1 t n hbackB htn0 (rs i) mS (Bh + 1)).symm
        -- deep bulk
        set r := (t - A0) % p with hrdef
        set kk := (t - A0) / p with hkkdef
        have hr : r < p := Nat.mod_lt _ hp
        have hteq : t = A0 + r + p * kk := by
          rw [hkkdef, hrdef]; have := Nat.mod_add_div (t - A0) p; omega
        have hchainval : ∀ k, Rcell c' rs (A0 + r + p * k)
            = Rcell c' rs (A0 + r) + k • PR c' rs :=
          fun k => SliceRankAtom.RankAffine.iterate (fun j hj => hRrec c' rs j hj)
            (A0 + r) k (by omega)
        have hds : (fun j => (Sum.inl (rs j) : CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)))
            ∈ mixedTuplesF B q_U q_D (P.toPoly.arity c') := by
          rw [mem_mixedTuplesF]; intro j; rw [mem_coordCands]
          have hshj := hshallow_rs j
          revert hshj
          cases rs j with
          | core r => intro _; exact Or.inl ⟨r, rfl⟩
          | prefIdx q => intro hshj; exact Or.inr (Or.inl ⟨q, hshj, rfl⟩)
          | sufIdx l => intro hshj; exact Or.inr (Or.inr (Or.inl ⟨l, hshj, rfl⟩))
        by_cases hcol : PR c' rs = (fun _ => 0)
        · -- collinear: emit the bulk residue into S1
          have hchain0 : Rcell c' rs t = Rcell c' rs (A0 + r) := by
            conv_lhs => rw [hteq]
            rw [hchainval kk, hcol]; funext i; simp
          have hpredn_mS : P.rank c' (copiedSlice mS n) (cellTupleF rs mS (A0 + r) n)
              = dstar mS := by
            rw [hwineq c' rs hrsv (A0 + r) n (by omega) (by omega), ← hchain0,
              ← hwineq c' rs hrsv t n (by omega) (by omega), ← hcell]
            exact hrkC
          -- second achievement (base A0+(r+p)): collinear (PR=0) ⟹ same rank as A0+r
          have hpredn_mS' : P.rank c' (copiedSlice mS n) (cellTupleF rs mS (A0 + (r + p)) n)
              = dstar mS := by
            rw [hwineq c' rs hrsv (A0 + (r + p)) n (by omega) (by omega)]
            have hrc : Rcell c' rs (A0 + (r + p)) = Rcell c' rs (A0 + r) := by
              rw [show A0 + (r + p) = A0 + r + p from by ring, hRrec c' rs (A0 + r) (by omega), hcol]
              funext i; simp
            rw [hrc, ← hwineq c' rs hrsv (A0 + r) n (by omega) (by omega)]
            exact hpredn_mS
          refine Or.inl ⟨rs, t, hrsv, by omega, hcell, Or.inl ⟨?_, ?_, ?_⟩⟩
          · rw [hmthrdef]; omega
          · rw [hlenW, hmthrdef]; omega
          · rw [hMdef, hS1def]; simp only []; rw [if_neg hcf]
            refine Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr hr,
                (htransBk rs r hds (by omega) (by omega)).mp hpredn_mS,
                (htransBk rs (r + p) hds (by omega) (by omega)).mp hpredn_mS'⟩, ?_⟩
            exact ((SliceFasSelectorGA.base_mod_iff A0 p t r hp hr (by omega)).mpr hrdef.symm).symm
        · -- non-collinear: refute via chain endpoints
          exfalso
          have hkk1 : 1 ≤ kk := by
            rw [hkkdef, Nat.le_div_iff_mul_le hp]; omega
          have hmc : kk * p = p * kk := Nat.mul_comm kk p
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
          have hval_t := cellTupleF_valid rs mS t n hm1 hrsv (by omega)
          have hacc_t : (Mc c').accepts (markAtN (P.toPoly.arity c') (copiedSlice mS n)
              (CopiedDstar.cellTupleF rs mS t n)) := by
            refine (hMc c' (copiedSlice mS n) _ hval_t).mpr ⟨?_, ?_⟩
            · rw [← hcell]; exact hbsel.2
            · rw [← hcell]; exact hbD
          have htr_left := CopiedDstar.cell_base_transport_left_fibred (Mc c') m p
            (hbwd c') mS hm1 rs hrsv t n kk (by omega) (by omega) (by omega)
          have hsub : t - kk * p = A0 + r := by omega
          rw [hsub] at htr_left
          have hacc_a := htr_left.mpr hacc_t
          have htr_right := CopiedDstar.cell_base_transport_right_fibred (Mc c') m p
            (hbwd c') mS hm1 rs hrsv (A0 + r) n tl (by omega) (by omega) (by omega)
          have hbd : A0 + r + tl * p = jl := by rw [hjldef]; omega
          rw [hbd] at htr_right
          have hacc_jl := htr_right.mpr hacc_a
          have hval_a := cellTupleF_valid rs mS (A0 + r) n hm1 hrsv (by omega)
          have hsl_a := (hMc c' (copiedSlice mS n) _ hval_a).mp hacc_a
          have hval_jl := cellTupleF_valid rs mS jl n hm1 hrsv (by omega)
          have hsl_jl := (hMc c' (copiedSlice mS n) _ hval_jl).mp hacc_jl
          have hDRn : dstar mS = fun i =>
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
          · refine CopiedDstarC.dstarRankGA'_lex_min P hV (copiedSlice mS n) hDpres
              ⟨c', CopiedDstar.cellTupleF rs mS (A0 + r) n⟩ ⟨hval_a, hsl_a.1⟩ hsl_a.2 ?_
            have hrk_a : P.rankOf (copiedSlice mS n)
                ⟨c', CopiedDstar.cellTupleF rs mS (A0 + r) n⟩
                = fun i => Rcell c' rs (A0 + r) i + Bcell c' rs n i :=
              hwineq c' rs hrsv (A0 + r) n (by omega) (by omega)
            rw [hrk_a, hagree', hDRn]
            exact hfirst
          · refine CopiedDstarC.dstarRankGA'_lex_min P hV (copiedSlice mS n) hDpres
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

  rcases Nat.eq_zero_or_pos P.d with hd0 | hd
  · obtain ⟨Mbr, S1, F2, S1L, F2L, hrest⟩ := hcore (fun _ _ => 0) 0 (fun i => (hd0 ▸ i).elim0)
      (fun mS _ _ _ => funext (fun i => (hd0 ▸ i).elim0))
    exact ⟨Mbr, (fun _ _ => 0), S1, F2, S1L, F2L, hrest⟩
  · -- d > 0: instantiate hcore with the bounded selector selB
    -- ===== S2: the d*-vector is selB, affine-on-residues at psB (period-align: hcertB) =====
    have haff_selB : ∀ i, AffineOnResiduesAtZ psB
        (fun mS => selB B q_U q_D P Mc n hd mS i) := by
      intro i
      have hgate : ∀ gf ∈ selCands B q_U q_D P Mc n,
          SliceOrder.EventuallyPeriodic gf.1 psB := by
        intro gf hgf
        simp only [selCands, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hgf
        obtain ⟨c, _, t, htmem, ds, hdsmem, rfl⟩ := hgf
        have hwin : t + B ≤ n := by rw [Finset.mem_Icc] at htmem; omega
        obtain ⟨pp, _, hpdvd, hEP, _⟩ := hcertB c ds hdsmem t n hwin
        exact SliceDstar.EP_of_dvd hEP hpdvd
      have haff : ∀ gf ∈ selCands B q_U q_D P Mc n, ∀ j,
          AffineOnResiduesAtZ psB (fun mS => gf.2 mS j) := by
        intro gf hgf j
        simp only [selCands, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hgf
        obtain ⟨c, _, t, htmem, ds, hdsmem, rfl⟩ := hgf
        have hwin : t + B ≤ n := by rw [Finset.mem_Icc] at htmem; omega
        obtain ⟨pp, hpp1, hpdvd, _, hAff⟩ := hcertB c ds hdsmem t n hwin
        exact (hAff j).of_dvd hpp1 hpdvd hpsB1
      have hBIGaff : ∀ j, AffineOnResiduesAtZ psB
          (fun mS => bigDom B q_U q_D P Mc n hd mS j) := by
        intro j
        by_cases hj : j = ⟨0, hd⟩
        · have heq : (fun mS => bigDom B q_U q_D P Mc n hd mS j)
              = (fun mS => (((selCands B q_U q_D P Mc n).map
                  (fun gf => fun mS => gf.2 mS ⟨0, hd⟩)).map (fun f => f mS)).foldr max 0 + 1) := by
            funext mS
            simp only [bigDom, hj, ↓reduceIte, List.map_map, Function.comp_def]
          rw [heq]
          exact (affineOnResiduesAtZ_listMax hpsB1
            ((selCands B q_U q_D P Mc n).map (fun gf => fun mS => gf.2 mS ⟨0, hd⟩))
            (fun f hf => by
              rw [List.mem_map] at hf
              obtain ⟨gf, hgf, rfl⟩ := hf
              exact haff gf hgf ⟨0, hd⟩)).add hpsB1 (AffineOnResiduesAtZ.const psB 1)
        · have heq : (fun mS => bigDom B q_U q_D P Mc n hd mS j) = (fun _ => (0 : ℤ)) := by
            funext mS; simp only [bigDom, if_neg hj]
          rw [heq]; exact AffineOnResiduesAtZ.const psB 0
      show AffineOnResiduesAtZ psB (fun mS => lexMinList (bigDom B q_U q_D P Mc n hd ::
        (selCands B q_U q_D P Mc n).map
          (fun gf => fun mS => if gf.1 mS then gf.2 mS else bigDom B q_U q_D P Mc n hd mS)) mS i)
      exact gated_lexMin_affine_at hpsB1 (selCands B q_U q_D P Mc n) hgate haff
        (bigDom B q_U q_D P Mc n hd) hBIGaff i
    -- selB affine at the COMBINED period p0' (lift from psB)
    have haff_selB0 : ∀ i, AffineOnResiduesAtZ p0'
        (fun mS => selB B q_U q_D P Mc n hd mS i) :=
      fun i => (haff_selB i).of_dvd hpsB1 hpsBdvd hp0'1
    obtain ⟨Mbr, S1, F2, S1L, F2L, hrest⟩ :=
      hcore (selB B q_U q_D P Mc n hd) (max (2 * q_D + 2) (2 * q_U + 2)) haff_selB0
      (fun mS hN0 hdom hDpres => dstarRankGA_m_eq_selB P hV harity1 hB1 Mc hMc q_U q_D hsufC hprefC hd n mS
        (by omega) (by omega) (by omega) (by omega) hDpres)
    exact ⟨Mbr, (selB B q_U q_D P Mc n hd), S1, F2, S1L, F2L, hrest⟩

end CopiedSelectorMS
