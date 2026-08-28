/-
# The fibred constructive `d*`-rank (§9 tower, Stage F3.4 — THE MONOLITH)

The fibred twin of `SliceDstarBridgeGA.dstarC_exists_GA`, with the period
`pstar := p · p₂` HOISTED before the budget and the boundary width (the
wrapped `pg` gate-alignment factor disappears: the anchor-gate sentences are
replaced by `gateF` machine acceptance, whose eventual periodicity is the
machine's `bFN` function period — zero Büchi calls, no alignment fold).

Substitution map (wrapped S0–S12 → fibred): `cells_cover` →
`cells_cover_fibred` (B before C, mS); `dstar_setup_GA` →
`dstar_setup_fibred` (×2: bounds B and B' := 3B + m); `anchorGate.Sat` →
`gateF`; `anchorGate_EP` + `eventuallyPeriodic_align` → `gateF_EP'` +
`EP_of_dvd`; per-candidate slope extraction + `lexLt_eventuallyPeriodic` →
`lexLt_EP_at` at `pstar` directly; `gated_lexMin_affine` →
`gated_lexMin_affine_at`; `cellTuple` → `cellTupleF` (validity threaded from
the per-`mS` explicit descriptor Finsets); `cell_base_transport_*` → the
fibred twins through the fixed reduced machine.
-/
import RequestProject.CopiedSetup
import RequestProject.CopiedGateEP
import RequestProject.CopiedAffineAt
import RequestProject.SliceDstarBridgeGA

namespace CopiedDstarC

open WRP Step SliceOrder SliceLexOrder SliceDstarCore SliceDstar
  SliceDstarBridge SliceBoundaryMinCore SlicePeriodStar SliceFamilyCell
  MSOMarkN SliceMarkN SliceMSO
  CopiedAffineAt CopiedAffineAt.AffineOnResiduesAtZ CopiedCells CopiedRank
  CopiedRegionF CopiedDstar CopiedGateEP
open scoped Classical

/-- No selected `D`-atom's rank lex-precedes the word-generic `d*`-rank. -/
theorem dstarRankGA'_lex_min (P : WRP.Presentation Step Step) (hV : P.Valid)
    (w : List Step)
    (hD : ∃ a, P.toPoly.selectedAtom w a ∧ P.toPoly.labelOf w a = D)
    (b : P.toPoly.Atom) (hbsel : P.toPoly.selectedAtom w b)
    (hbD : P.toPoly.labelOf w b = D) :
    ¬ WRP.lexLt (P.rankOf w b) (CopiedDstar.dstarRankGA' P hV w) := by
  obtain ⟨dstar, hdsel, hdD, hdmin, hdrank⟩ :=
    CopiedDstar.dstarRankGA'_spec P hV w hD
  rw [hdrank]
  rcases hdmin b hbsel hbD with rfl | hord
  · exact lexLt_irrefl _
  · simp only [WRP.Presentation.wrpOrd] at hord
    rcases hord with hlt | ⟨heqr, _⟩
    · exact fun hcon => lexLt_irrefl _ (lexLt_trans _ _ _ hlt hcon)
    · rw [heqr]
      exact lexLt_irrefl _

/-- The pinned twin of `selBvecCoord_affineOnResiduesZ`: the boundary vector
with pinned boundary indices is pinned per coordinate. -/
theorem selBvecCoord_affineOnResiduesAtZ {d : ℕ} (F : ℕ → Fin d → ℤ)
    (m r : ℕ) (PRv : Fin d → ℤ) (takeLast : Bool) (firstSel lastSel : ℕ → ℕ)
    {p : ℕ} (hp : 1 ≤ p)
    (hfs : SlicePeriodStar.AffineOnResiduesAt p firstSel)
    (hls : SlicePeriodStar.AffineOnResiduesAt p lastSel) (i : Fin d) :
    AffineOnResiduesAtZ p (fun N =>
      SliceDstar.selBvecVal F m r PRv takeLast (firstSel N) (lastSel N) i) := by
  cases takeLast with
  | false =>
      have hleg : AffineOnResiduesAtZ p
          (fun N => ((firstSel N : ℕ) : ℤ) * PRv i) :=
        ((natCast hfs).smul (PRv i)).congr' (fun N => mul_comm (PRv i) _)
      refine AffineOnResiduesAtZ.congr' (fun N => ?_)
        ((const p (F (m + r) i)).add hp hleg)
      show F (m + r) i + ((firstSel N : ℕ) : ℤ) * PRv i
        = SliceDstar.selBvecVal F m r PRv false (firstSel N) (lastSel N) i
      simp only [SliceDstar.selBvecVal, Bool.false_eq_true, if_false]
  | true =>
      have hleg : AffineOnResiduesAtZ p
          (fun N => ((lastSel N : ℕ) : ℤ) * PRv i) :=
        ((natCast hls).smul (PRv i)).congr' (fun N => mul_comm (PRv i) _)
      refine AffineOnResiduesAtZ.congr' (fun N => ?_)
        ((const p (F (m + r) i)).add hp hleg)
      show F (m + r) i + ((lastSel N : ℕ) : ℤ) * PRv i
        = SliceDstar.selBvecVal F m r PRv true (firstSel N) (lastSel N) i
      simp only [SliceDstar.selBvecVal, if_true]

set_option maxHeartbeats 1600000 in
/-- **The fibred constructive `d*`-rank exists** (the F3.4 monolith): the
period `pstar = p · p₂` is machine-level, hoisted BEFORE the budget and the
boundary width; per `(C, mS)` there is a per-coordinate `pstar`-pinned
sequence equal to the fibred `d*`-rank on every in-domain `D`-present copied
slice past a threshold. -/
theorem dstarC_exists_fibred (P : WRP.Presentation Step Step) (hV : P.Valid) :
    ∃ pstar : ℕ, 1 ≤ pstar ∧ ∀ C mS : ℕ, 1 ≤ mS →
      (∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)),
        l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
        l.length ≤ C * (mS + n + 1)) →
      ∃ (dstarC : ℕ → Fin P.d → ℤ) (N0 : ℕ),
        (∀ i, AffineOnResiduesAtZ pstar (fun n => dstarC n i)) ∧
        (∀ n, N0 ≤ n → P.toPoly.domain (copiedSlice mS n) →
          (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
            P.toPoly.labelOf (copiedSlice mS n) a = D) →
          CopiedDstar.dstarRankGA_m P hV mS n = dstarC n) := by
  classical
  rcases Nat.eq_zero_or_pos P.d with hd0 | hd
  · exact ⟨1, le_rfl, fun C mS hm hbud => ⟨fun _ _ => 0, 0,
      fun i => (hd0 ▸ i).elim0,
      fun n _ _ _ => funext (fun i => (hd0 ▸ i).elim0)⟩⟩
  -- S2: constants and the two setups (all hoisted)
  obtain ⟨B, hB1, hcovC⟩ := CopiedCells.cells_cover_fibred P
  obtain ⟨m, p, Mc, hp, hmB, hMc, hbwd, hsetup⟩ :=
    CopiedSetup.dstar_setup_fibred P B
  set B' : ℕ := 3 * B + m with hB'def
  have hBB' : B ≤ B' := by omega
  have hB'1 : 1 ≤ B' := by omega
  obtain ⟨m₂, p₂, _Mc₂, hp₂, _hmB₂, _hMc₂, _hbwd₂, hsetup₂⟩ :=
    CopiedSetup.dstar_setup_fibred P B'
  set A0 : ℕ := B + m with hA0def
  refine ⟨p * p₂, Nat.one_le_iff_ne_zero.mpr (by positivity),
    fun C mS hm hbud => ?_⟩
  set pstar : ℕ := p * p₂ with hpstardef
  have hpstar : 1 ≤ pstar := Nat.mul_pos hp hp₂
  obtain ⟨Ncc, hcells⟩ := hcovC C mS hm
  obtain ⟨Rcell, Bcell, PR, PBn, hwineq, hRrec, hBrec⟩ := hsetup mS hm
  obtain ⟨Rcell₂, Bcell₂, _PR₂, PBn₂, hwineq₂, _hRrec₂, hBrec₂⟩ := hsetup₂ mS hm
  set tl : (c : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c) → RegionSpecF B) → Bool :=
    fun c rs => decide (WRP.lexLt (PR c rs) (fun _ => 0)) with htldef
  -- S3: the candidate list and the dominator
  set cands : List ((ℕ → Prop) × (ℕ → Fin P.d → ℤ)) :=
    ((List.finRange P.toPoly.K).flatMap (fun c =>
      ((regionTuplesF B' (P.toPoly.arity c) mS).toList).map (fun rs' =>
        (fun n => gateF (Mc c) rs' mS (B' + 1) n,
         fun n => fun i => Rcell₂ c rs' (B' + 1) i + Bcell₂ c rs' n i))))
    ++ ((List.finRange P.toPoly.K).flatMap (fun c =>
      ((regionTuplesF B (P.toPoly.arity c) mS).toList).flatMap (fun rs =>
        (List.range p).map (fun r =>
          (fun n => gateF (Mc c) rs mS (A0 + r) n,
           fun n => fun i => Bcell c rs n i +
             SliceDstar.selBvecVal (Rcell c rs) A0 r (PR c rs) (tl c rs) 0
               ((n - (4 * B + 2 * m + r)) / p) i))))) with hcandsdef
  set BIG : ℕ → Fin P.d → ℤ := fun n coord =>
    if coord = ⟨0, hd⟩
    then (cands.map (fun gf => gf.2 n ⟨0, hd⟩)).foldr max 0 + 1 else 0
    with hBIGdef
  -- S4: gate periods — machine-level, no alignment fold, zero Büchi
  have hgate : ∀ gf ∈ cands, SliceOrder.EventuallyPeriodic gf.1 pstar := by
    intro gf hgf
    rw [hcandsdef, List.mem_append] at hgf
    rcases hgf with hgf | hgf
    · rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨rs', hrs'mem, rfl⟩ := hgf
      have hv : ∀ i, (rs' i).valid mS :=
        (mem_regionTuplesF rs').mp (Finset.mem_toList.mp hrs'mem)
      exact SliceDstar.EP_of_dvd
        (gateF_EP' (Mc c) m p hp (hbwd c) mS hm rs' hv (B' + 1)
          (Nat.le_succ B'))
        (dvd_mul_right p p₂)
    · rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_flatMap] at hgf
      obtain ⟨rs, hrsmem, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨r, hr, rfl⟩ := hgf
      have hv : ∀ i, (rs i).valid mS :=
        (mem_regionTuplesF rs).mp (Finset.mem_toList.mp hrsmem)
      exact SliceDstar.EP_of_dvd
        (gateF_EP' (Mc c) m p hp (hbwd c) mS hm rs hv (A0 + r)
          (by rw [hA0def]; omega))
        (dvd_mul_right p p₂)
  -- S5: per-coordinate pinned affineness of the candidate values
  have hcaff : ∀ gf ∈ cands, ∀ i, AffineOnResiduesAtZ pstar (fun n => gf.2 n i) := by
    intro gf hgf i
    rw [hcandsdef, List.mem_append] at hgf
    rcases hgf with hgf | hgf
    · rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨rs', _, rfl⟩ := hgf
      have hleg : AffineOnResiduesAtZ pstar (fun n => Bcell₂ c rs' n i) := by
        refine AffineOnResiduesAtZ.of_dvd hp₂ (dvd_mul_left p₂ p) hpstar ?_
        refine AffineOnResiduesAtZ.of_recurrence hp₂ (m := m₂)
          (S := PBn₂ c rs' i) ?_
        intro n hn
        have h := congrFun (hBrec₂ c rs' n hn) i
        rw [Pi.add_apply] at h
        exact h
      exact (const pstar (Rcell₂ c rs' (B' + 1) i)).add hpstar hleg
    · rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_flatMap] at hgf
      obtain ⟨rs, _, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨r, hr, rfl⟩ := hgf
      have hleg : AffineOnResiduesAtZ pstar (fun n => Bcell c rs n i) := by
        refine AffineOnResiduesAtZ.of_dvd hp (dvd_mul_right p p₂) hpstar ?_
        refine AffineOnResiduesAtZ.of_recurrence hp (m := m)
          (S := PBn c rs i) ?_
        intro n hn
        have h := congrFun (hBrec c rs n hn) i
        rw [Pi.add_apply] at h
        exact h
      refine hleg.add hpstar ?_
      exact selBvecCoord_affineOnResiduesAtZ (Rcell c rs) A0 r (PR c rs)
        (tl c rs) (fun _ => 0) (fun n => (n - (4 * B + 2 * m + r)) / p)
        hpstar (SlicePeriodStar.AffineOnResiduesAt.const pstar 0)
        ((CopiedAffineAt.affineOnResiduesAt_natSubDiv (4 * B + 2 * m + r) p
          hp).of_dvd hp (dvd_mul_right p p₂) hpstar) i
  -- S7: the dominator
  have hBIGaff : ∀ i, AffineOnResiduesAtZ pstar (fun n => BIG n i) := by
    intro i
    by_cases hi : i = ⟨0, hd⟩
    · have heq : (fun n => BIG n i)
          = (fun n => ((cands.map (fun gf => fun n => gf.2 n ⟨0, hd⟩)).map
              (fun f => f n)).foldr max 0 + 1) := by
        funext n
        simp only [hBIGdef, hi, ↓reduceIte, List.map_map, Function.comp_def]
      rw [heq]
      exact (CopiedAffineAt.affineOnResiduesAtZ_listMax hpstar
        (cands.map (fun gf => fun n => gf.2 n ⟨0, hd⟩))
        (fun f hf => by
          rw [List.mem_map] at hf
          obtain ⟨gf, hgf, rfl⟩ := hf
          exact hcaff gf hgf ⟨0, hd⟩)).add hpstar (const pstar 1)
    · have heq : (fun n => BIG n i) = (fun _ => (0 : ℤ)) := by
        funext n
        rw [hBIGdef]
        simp only [if_neg hi]
      rw [heq]
      exact const pstar 0
  have hdom : ∀ gf ∈ cands, ∀ n, WRP.lexLt (gf.2 n) (BIG n) := by
    intro gf hgf n
    refine ⟨⟨0, hd⟩, fun j hj => absurd (Fin.lt_def.mp hj)
      (Nat.not_lt_zero _), ?_⟩
    simp only [hBIGdef, ↓reduceIte]
    have hmem : gf.2 n ⟨0, hd⟩ ∈ cands.map (fun gf' => gf'.2 n ⟨0, hd⟩) :=
      List.mem_map.mpr ⟨gf, hgf, rfl⟩
    have := SliceDstarBridge.le_foldr_max hmem
    omega
  -- S8: the witness and its pinned-affine leg
  refine ⟨fun n => lexMinList (BIG :: cands.map
    (fun gf => fun n => if gf.1 n then gf.2 n else BIG n)) n,
    Ncc + 6 * B + 2 * m + 2 * p + 2, ?_, ?_⟩
  · exact fun i => CopiedAffineAt.gated_lexMin_affine_at hpstar cands
      hgate hcaff BIG hBIGaff i
  -- S9: the bridge opening
  intro n hn hdomain hD
  show CopiedDstar.dstarRankGA_m P hV mS n
    = lexMinList (BIG :: cands.map
      (fun gf => fun n => if gf.1 n then gf.2 n else BIG n)) n
  set L := BIG :: cands.map
    (fun gf => fun n => if gf.1 n then gf.2 n else BIG n) with hLdef
  have hLne : L ≠ [] := by
    rw [hLdef]
    simp
  obtain ⟨hmin, hattn⟩ := lexMinList_le L hLne n
  have hmrk : CopiedDstar.dstarRankGA_m P hV mS n
      = CopiedDstar.dstarRankGA' P hV (copiedSlice mS n) := rfl
  obtain ⟨dstar, hdsel, hdD, hdmin, hdrank⟩ :=
    CopiedDstar.dstarRankGA'_spec P hV (copiedSlice mS n) hD
  have hDRle : ∀ b, P.toPoly.selectedAtom (copiedSlice mS n) b →
      P.toPoly.labelOf (copiedSlice mS n) b = D →
      ¬ WRP.lexLt (P.rankOf (copiedSlice mS n) b)
        (CopiedDstar.dstarRankGA_m P hV mS n) := by
    intro b hbsel hbD
    rw [hmrk]
    exact dstarRankGA'_lex_min P hV (copiedSlice mS n) hD b hbsel hbD
  have hmn : m ≤ n := by omega
  -- S10: every on-candidate value is rankOf a selected D-atom
  have hOnIsRank : ∀ gf ∈ cands, gf.1 n →
      ∃ b, P.toPoly.selectedAtom (copiedSlice mS n) b ∧
        P.toPoly.labelOf (copiedSlice mS n) b = D ∧
        gf.2 n = P.rankOf (copiedSlice mS n) b := by
    intro gf hgf hon
    rw [hcandsdef, List.mem_append] at hgf
    rcases hgf with hgf | hgf
    · -- frozen: the gate IS the atom's own acceptance, value at the dummy base
      rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨rs', hrs'mem, rfl⟩ := hgf
      have hv : ∀ i, (rs' i).valid mS :=
        (mem_regionTuplesF rs').mp (Finset.mem_toList.mp hrs'mem)
      have hwin : (B' + 1) + B' ≤ n := by omega
      have hval := cellTupleF_valid rs' mS (B' + 1) n hm hv hwin
      have hsl := (hMc c (copiedSlice mS n) _ hval).mp hon
      refine ⟨⟨c, cellTupleF rs' mS (B' + 1) n⟩, ⟨hval, hsl.1⟩, hsl.2, ?_⟩
      exact (hwineq₂ c rs' hv (B' + 1) n (le_refl _) (by omega)).symm
    · -- bulk: transport RIGHT from the anchor to the boundary base
      rw [List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_flatMap] at hgf
      obtain ⟨rs, hrsmem, hgf⟩ := hgf
      rw [List.mem_map] at hgf
      obtain ⟨r, hr, rfl⟩ := hgf
      rw [List.mem_range] at hr
      have hv : ∀ i, (rs i).valid mS :=
        (mem_regionTuplesF rs).mp (Finset.mem_toList.mp hrsmem)
      obtain ⟨kend, hkenddef⟩ : ∃ k : ℕ, k = (n - (4 * B + 2 * m + r)) / p :=
        ⟨_, rfl⟩
      obtain ⟨kbd, hkbddef⟩ : ∃ k : ℕ, k = (if tl c rs then kend else 0 : ℕ) :=
        ⟨_, rfl⟩
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
      have hacc0 : (Mc c).accepts (markAtN (P.toPoly.arity c)
          (copiedSlice mS n) (cellTupleF rs mS (A0 + r) n)) := hon
      have hmc : kbd * p = p * kbd := Nat.mul_comm kbd p
      have htr := CopiedDstar.cell_base_transport_right_fibred (Mc c) m p
        (hbwd c) mS hm rs hv (A0 + r) n kbd (by rw [hA0def]; omega)
        (by rw [hA0def] at *; omega) (by omega)
      have hacc := htr.mpr hacc0
      have hbd : A0 + r + kbd * p = A0 + r + p * kbd := by omega
      rw [hbd] at hacc
      have hval := cellTupleF_valid rs mS (A0 + r + p * kbd) n hm hv
        (by rw [hA0def] at *; omega)
      have hsl := (hMc c (copiedSlice mS n) _ hval).mp hacc
      refine ⟨⟨c, cellTupleF rs mS (A0 + r + p * kbd) n⟩, ⟨hval, hsl.1⟩,
        hsl.2, ?_⟩
      have hsel_eq : (fun i => Bcell c rs n i +
          SliceDstar.selBvecVal (Rcell c rs) A0 r (PR c rs) (tl c rs) 0
            kend i)
          = fun i => Rcell c rs (A0 + r + p * kbd) i + Bcell c rs n i := by
        funext i
        have hit := congrFun (SliceRankAtom.RankAffine.iterate
          (fun t ht => hRrec c rs t ht) (A0 + r) kbd (by rw [hA0def]; omega)) i
        rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at hit
        rw [SliceDstar.selBvecVal, hit, hkbddef]
        by_cases htl : tl c rs
        · simp only [if_pos htl]
          ring
        · simp only [if_neg htl]
          ring
      show (fun i => Bcell c rs n i + SliceDstar.selBvecVal (Rcell c rs) A0 r
          (PR c rs) (tl c rs) 0 ((n - (4 * B + 2 * m + r)) / p) i)
        = P.rankOf (copiedSlice mS n) _
      rw [← hkenddef, hsel_eq]
      exact (hwineq c rs hv (A0 + r + p * kbd) n
        (by rw [hA0def] at *; omega) (by rw [hA0def] at *; omega)).symm
  have hII : ∀ gf ∈ cands, gf.1 n →
      ¬ WRP.lexLt (gf.2 n) (CopiedDstar.dstarRankGA_m P hV mS n) := by
    intro gf hgf hon
    obtain ⟨b, hbsel, hbD, hbeq⟩ := hOnIsRank gf hgf hon
    rw [hbeq]
    exact hDRle b hbsel hbD
  -- S11: dstar's own candidate is on and not lex-above it (three zones)
  have hI : ∃ gf ∈ cands, gf.1 n ∧
      ¬ WRP.lexLt (CopiedDstar.dstarRankGA_m P hV mS n) (gf.2 n) := by
    clear hII hDRle hOnIsRank
    obtain ⟨c0, ī⟩ := dstar
    obtain ⟨t, htB, htn, hreg⟩ := hcells n (by omega) c0 ī hdsel
      (fun l hnd hl => hbud n hdomain c0 l hnd hl)
    choose rs hregd using hreg
    have hv : ∀ i, (rs i).valid mS := fun i => (hregd i).1
    have hrs : ∀ i, ī i = (rs i).posAt mS t n := fun i => (hregd i).2
    have hīeq : ī = cellTupleF rs mS t n := funext hrs
    have hvalī : ∀ i, ī i < (copiedSlice mS n).length := hdsel.1
    by_cases hfront : t < A0
    · -- FRONT zone: re-freeze and use the frozen candidate at the dummy base
      have hfz : t + B ≤ B' := by omega
      set rs' := fun i => refreezeFrontF hBB' t hfz (rs i) with hrs'def
      have hv' : ∀ i, (rs' i).valid mS :=
        fun i => refreezeFrontF_valid hBB' t hfz (rs i) mS (hv i)
      have htup : cellTupleF rs' mS (B' + 1) n = ī := by
        funext i
        show (refreezeFrontF hBB' t hfz (rs i)).posAt mS (B' + 1) n = ī i
        rw [refreezeFrontF_posAt, ← hrs i]
      refine ⟨(fun n => gateF (Mc c0) rs' mS (B' + 1) n,
        fun n => fun i => Rcell₂ c0 rs' (B' + 1) i + Bcell₂ c0 rs' n i),
        ?_, ?_, ?_⟩
      · rw [hcandsdef]
        exact List.mem_append_left _ (List.mem_flatMap.mpr
          ⟨c0, List.mem_finRange c0, List.mem_map_of_mem
            (Finset.mem_toList.mpr ((mem_regionTuplesF rs').mpr hv'))⟩)
      · show (Mc c0).accepts (markAtN (P.toPoly.arity c0) (copiedSlice mS n)
          (cellTupleF rs' mS (B' + 1) n))
        rw [htup]
        exact (hMc c0 (copiedSlice mS n) ī hvalī).mpr ⟨hdsel.2, hdD⟩
      · have heq : CopiedDstar.dstarRankGA_m P hV mS n
            = fun i => Rcell₂ c0 rs' (B' + 1) i + Bcell₂ c0 rs' n i := by
          rw [hmrk, hdrank]
          show P.rank c0 _ ī = _
          rw [← htup]
          exact hwineq₂ c0 rs' hv' (B' + 1) n (le_refl _) (by omega)
        rw [heq]
        exact lexLt_irrefl _
    · by_cases hbulk : t + 3 * B + m ≤ n
      · -- BULK zone: transport LEFT to the anchor; boundary value dominates
        obtain ⟨r, hrdef⟩ : ∃ rr : ℕ, rr = (t - A0) % p := ⟨_, rfl⟩
        obtain ⟨kd, hkddef⟩ : ∃ kk : ℕ, kk = (t - A0) / p := ⟨_, rfl⟩
        obtain ⟨kend, hkenddef⟩ : ∃ kk : ℕ,
            kk = (n - (4 * B + 2 * m + r)) / p := ⟨_, rfl⟩
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
            show n + 1 - (3 * B + m) - (A0 + r) - 1
              = n - (4 * B + 2 * m + r) from by omega]
        refine ⟨(fun n => gateF (Mc c0) rs mS (A0 + r) n,
          fun n => fun i => Bcell c0 rs n i +
            SliceDstar.selBvecVal (Rcell c0 rs) A0 r (PR c0 rs) (tl c0 rs) 0
              ((n - (4 * B + 2 * m + r)) / p) i), ?_, ?_, ?_⟩
        · rw [hcandsdef]
          exact List.mem_append_right _ (List.mem_flatMap.mpr
            ⟨c0, List.mem_finRange c0, List.mem_flatMap.mpr
              ⟨rs, Finset.mem_toList.mpr ((mem_regionTuplesF rs).mpr hv),
                List.mem_map_of_mem (List.mem_range.mpr hrlt)⟩⟩)
        · -- the gate turns on by leftward transport from t to the anchor
          have hacc_t : (Mc c0).accepts (markAtN (P.toPoly.arity c0)
              (copiedSlice mS n) (cellTupleF rs mS t n)) := by
            refine (hMc c0 (copiedSlice mS n) _
              (cellTupleF_valid rs mS t n hm hv (by omega))).mpr ?_
            rw [← hīeq]
            exact ⟨hdsel.2, hdD⟩
          have htr := CopiedDstar.cell_base_transport_left_fibred (Mc c0) m p
            (hbwd c0) mS hm rs hv t n kd (by omega) (by omega) (by omega)
          have hsub : t - kd * p = A0 + r := by omega
          rw [hsub] at htr
          exact htr.mpr hacc_t
        · -- the boundary value lex-dominates dstar's own member value
          set F : ℕ → Fin P.d → ℤ := fun j i => Rcell c0 rs j i + Bcell c0 rs n i
            with hFdef
          have hrecF : ∀ (i : Fin P.d) (r' k : ℕ),
              F (A0 + r' + p * k) i = F (A0 + r') i + k * PR c0 rs i := by
            intro i r' k
            have hit := congrFun (SliceRankAtom.RankAffine.iterate
              (fun tt htt => hRrec c0 rs tt htt) (A0 + r') k (by omega)) i
            rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at hit
            simp only [hFdef]
            rw [hit]
            ring
          have hflag : tl c0 rs = true ↔ WRP.lexLt (PR c0 rs) (fun _ => 0) := by
            rw [htldef]
            exact decide_eq_true_iff
          have hDeq : CopiedDstar.dstarRankGA_m P hV mS n = F t := by
            rw [hmrk, hdrank]
            show P.rank c0 _ ī = _
            rw [hīeq, hFdef]
            exact hwineq c0 rs hv t n (by omega) (by omega)
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
          show ¬ WRP.lexLt (CopiedDstar.dstarRankGA_m P hV mS n)
            (fun i => Bcell c0 rs n i +
              SliceDstar.selBvecVal (Rcell c0 rs) A0 r (PR c0 rs) (tl c0 rs) 0
                ((n - (4 * B + 2 * m + r)) / p) i)
          rw [hbnd_eq,
            show (n - (4 * B + 2 * m + r)) / p
              = numReps A0 p r (n + 1 - (3 * B + m)) - 1 from by
                rw [hN]; omega,
            hDeq, ← hjeq]
          exact SliceDstarBridge.selBvec_le_member F (PR c0 rs) (tl c0 rs)
            hrecF hflag r (n + 1 - (3 * B + m)) kd (by rw [hN]; omega)
      · -- BACK zone: re-freeze and use the frozen candidate at the dummy base
        have hbz : n ≤ t + B' := by omega
        set rs' := fun i => refreezeBackF hBB' hB'1 t n hbz (rs i) with hrs'def
        have hv' : ∀ i, (rs' i).valid mS :=
          fun i => refreezeBackF_valid hBB' hB'1 t n hbz (rs i) mS (hv i)
        have htup : cellTupleF rs' mS (B' + 1) n = ī := by
          funext i
          show (refreezeBackF hBB' hB'1 t n hbz (rs i)).posAt mS (B' + 1) n
            = ī i
          rw [refreezeBackF_posAt hBB' hB'1 t n hbz htn, ← hrs i]
        refine ⟨(fun n => gateF (Mc c0) rs' mS (B' + 1) n,
          fun n => fun i => Rcell₂ c0 rs' (B' + 1) i + Bcell₂ c0 rs' n i),
          ?_, ?_, ?_⟩
        · rw [hcandsdef]
          exact List.mem_append_left _ (List.mem_flatMap.mpr
            ⟨c0, List.mem_finRange c0, List.mem_map_of_mem
              (Finset.mem_toList.mpr ((mem_regionTuplesF rs').mpr hv'))⟩)
        · show (Mc c0).accepts (markAtN (P.toPoly.arity c0) (copiedSlice mS n)
            (cellTupleF rs' mS (B' + 1) n))
          rw [htup]
          exact (hMc c0 (copiedSlice mS n) ī hvalī).mpr ⟨hdsel.2, hdD⟩
        · have heq : CopiedDstar.dstarRankGA_m P hV mS n
              = fun i => Rcell₂ c0 rs' (B' + 1) i + Bcell₂ c0 rs' n i := by
            rw [hmrk, hdrank]
            show P.rank c0 _ ī = _
            rw [← htup]
            exact hwineq₂ c0 rs' hv' (B' + 1) n (le_refl _) (by omega)
          rw [heq]
          exact lexLt_irrefl _
  -- S12: the endgame (verbatim port)
  obtain ⟨gfd, hgfd, hond, hled⟩ := hI
  set gatedd : ℕ → Fin P.d → ℤ := fun n => if gfd.1 n then gfd.2 n else BIG n
    with hgddef
  have hgddmem : gatedd ∈ L := by
    rw [hLdef]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨gfd, hgfd, rfl⟩)
  have hgddval : gatedd n = gfd.2 n := by
    rw [hgddef]
    simp only [if_pos hond]
  have hDCle : ¬ WRP.lexLt (gatedd n) (lexMinList L n) := hmin gatedd hgddmem
  have hIfinal : ¬ WRP.lexLt (CopiedDstar.dstarRankGA_m P hV mS n)
      (lexMinList L n) := by
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
  have hIIfinal : ¬ WRP.lexLt (lexMinList L n)
      (CopiedDstar.dstarRankGA_m P hV mS n) := by
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
  rcases lexLt_trichot (CopiedDstar.dstarRankGA_m P hV mS n)
    (lexMinList L n) with h | h | h
  · exact absurd h hIfinal
  · exact h
  · exact absurd h hIIfinal

end CopiedDstarC
