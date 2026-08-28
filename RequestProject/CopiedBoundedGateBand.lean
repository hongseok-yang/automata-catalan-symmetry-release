/-
# The BANDED bounded-cell full gate (§9 mS-direction soundness fix — UPDATE 66)

`CopiedBoundedGate.fasU_atomOrd_full_gate_bounded` with the suffix/prefix RUN clauses replaced by their
DEPTH-BANDED variants (`CopiedBandRunGate.sufOrdClauseAtBandTot`/`prefOrdClauseAtBandTot`): the run
clause now fires only on competitors at least `kSuf`/`kPre` deep into the boundary run.  This is the
sound gate the bridge `gate_iff_tie_slice` instantiates (with `kSuf = q_D+2`, `kPre = q_U`, `Ssuf`/`Spre`
the TWO-rep tying residue sets): a two-rep-tying class is uniformly `d*` on the affine régime `[q_D, …)`,
so every banded competitor is a `d*`-achiever and the forward `TIE ⇒ accepts` direction discharges.
-/
import RequestProject.CopiedBoundedGate
import RequestProject.CopiedBandRunGate
import RequestProject.CopiedSelUniform

namespace CopiedBoundedGateBand

open WRP Step MSOMarkN SliceMarkN CopiedCells CopiedSufRunGate CopiedDeepRunGate CopiedFullGate
  CopiedBoundedGate CopiedBandRunGate CopiedDstarCMS CopiedSelUniform CopiedSetupMS

variable (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)

/-- Suffix band soundness in the arity-free update-tuple form.  A competitor
position satisfying the banded final-`D` guard has a genuine suffix-tail depth
`l`; if the active absolute residue class has two adjacent representatives in
the same update-tuple affine table, the update tuple at the competitor rank is
`d*` as well. -/
theorem suffix_rank_eq_dstar_of_two_reps_abs_mod_band_update_slice
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) (ī0 : Fin (P.toPoly.arity c) → ℕ)
    (mS n pc T Q k : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hn : 1 ≤ n) (hpc : 1 ≤ pc) (hQ : 0 < Q) (hpcQ : pc ∣ Q)
    (hk : 2 ≤ k) (hTk : T ≤ k - 2)
    (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l)
    {ρ p : ℕ} (hρ : ρ < Q)
    (h0 : F (T + ((ρ + Q - ((mS + 2 * n + 1 + T) % Q)) % pc))
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1 : F (T + ((ρ + Q - ((mS + 2 * n + 1 + T) % Q)) % pc) + pc)
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (hp : p < (copiedSlice mS n).length)
    (hband : ∃ y, y < (copiedSlice mS n).length ∧ p = y + k ∧
      ((copiedSlice mS n)[y]? = some D ∧
        ∀ q, q < (copiedSlice mS n).length → y < q → (copiedSlice mS n)[q]? = some D))
    (habs : p % Q = ρ) :
    P.rank c (copiedSlice mS n) (Function.update ī0 j0 p)
      = CopiedDstar.dstarRankGA_m P hV mS n := by
  classical
  obtain ⟨l, _hkl, hlm, hp_eq⟩ :=
    CopiedBandRunGate.bandLoSuf_copiedSlice_depth mS n p k hm hn hk hp hband
  have hTl : T ≤ l := by omega
  have habs_l : (mS + 2 * n + 1 + l) % Q = ρ := by
    rw [← hp_eq]
    exact habs
  have hrank :=
    CopiedSelUniform.suffix_rank_eq_dstar_of_two_reps_abs_mod_update_slice P hV
      c j0 ī0 mS n pc T Q F hpc hQ hpcQ hF hag hρ h0 h1 habs_l hTl hlm
  simpa [hp_eq] using hrank

/-- Prefix band soundness in the arity-free update-tuple form.  The copied
slice's prefix band has two boundary exceptions; this wrapper is intentionally
scoped to the genuine prefix-stretch case `p < mS - 1`, where the prefix affine
table applies. -/
theorem prefix_rank_eq_dstar_of_two_reps_abs_mod_band_update_slice
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) (ī0 : Fin (P.toPoly.arity c) → ℕ)
    (mS n pc T Q k : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hm : 1 ≤ mS) (hn : 1 ≤ n) (hpc : 1 ≤ pc) (hQ : 0 < Q) (hpcQ : pc ∣ Q)
    (hTk : T ≤ k)
    (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 l) = F l)
    {ρ p : ℕ} (hρ : ρ < Q)
    (h0 : F (T + ((ρ + Q - (T % Q)) % pc))
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1 : F (T + ((ρ + Q - (T % Q)) % pc) + pc)
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (hrun : (copiedSlice mS n)[p]? = some U ∧
      ∀ q, q < (copiedSlice mS n).length → q < p → (copiedSlice mS n)[q]? = some U)
    (hband : ∃ y, y < (copiedSlice mS n).length ∧ p = y + k ∧
      ((copiedSlice mS n)[y]? = some U ∧
        ∀ q, q < (copiedSlice mS n).length → q < y → (copiedSlice mS n)[q]? = some U))
    (hpref : p < mS - 1) (habs : p % Q = ρ) :
    P.rank c (copiedSlice mS n) (Function.update ī0 j0 p)
      = CopiedDstar.dstarRankGA_m P hV mS n := by
  classical
  rcases CopiedBandRunGate.bandLoPre_copiedSlice_cases mS n p k hm hn hrun hband with
    ⟨l, _hkl, hlm, hp_eq⟩ | hbd
  · have hTl : T ≤ l := by omega
    have habs_l : l % Q = ρ := by
      rw [← hp_eq]
      exact habs
    have hrank :=
      CopiedSelUniform.prefix_rank_eq_dstar_of_two_reps_abs_mod_update_slice P hV
        c j0 ī0 mS n pc T Q F hpc hQ hpcQ hF hag hρ h0 h1 habs_l hTl hlm
    simpa [hp_eq] using hrank
  · rcases hbd with hp_eq | hp_eq <;> omega

/-- The copied slice's first `D` is still uniquely characterized if the
earlier positions are merely known not to be `D`. -/
theorem firstD_of_no_previous_D_copiedSlice (mS n y : ℕ) (hm : 1 ≤ mS) (hn : 1 ≤ n)
    (hD : (copiedSlice mS n)[y]? = some D)
    (hno : ∀ q, q < y → (copiedSlice mS n)[q]? ≠ some D) :
    y = mS + 1 := by
  rcases Nat.lt_trichotomy y (mS + 1) with hlt | heq | hgt
  · exfalso
    rcases Nat.lt_or_ge y mS with hy' | hy'
    · rw [CopiedLandmark.copiedSlice_getElem?_pref mS n y hm hy'] at hD
      exact absurd hD (by simp)
    · have hyy : y = mS := by omega
      have hU := CopiedRank.copiedSlice_getElem?_blockU mS 0 n hm (by omega)
      rw [show mS + 2 * 0 = mS from by omega] at hU
      rw [hyy, hU] at hD
      exact absurd hD (by simp)
  · exact heq
  · exfalso
    have hDfirst := CopiedRank.copiedSlice_getElem?_blockD mS 0 n hm (by omega)
    rw [show mS + 2 * 0 + 1 = mS + 1 from by omega] at hDfirst
    have hnoFirst := hno (mS + 1) hgt
    rw [hDfirst] at hnoFirst
    exact hnoFirst rfl

/-- A from-end suffix offset `k` in the genuine deep tail is the mixed deep
suffix coordinate with offset `k+1`. -/
theorem deepSuf_fromEnd_mixedPosAt {B : ℕ} (mS n t p k : ℕ) (hk : k + 2 ≤ mS)
    (hend : p + 1 + k = (copiedSlice mS n).length) :
    p = mixedPosAt (Sum.inr (Sum.inl (k + 1)) : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) mS t n := by
  rw [length_copiedSlice] at hend
  simp only [mixedPosAt]
  omega

/-- A prefix deep clause with offset `k` pins the competitor to the mixed deep
prefix coordinate with offset `k-2`. -/
theorem deepPre_beforeFirstD_mixedPosAt {B : ℕ} (mS n t p k : ℕ)
    (hm : 1 ≤ mS) (hn : 1 ≤ n) (hk : 3 ≤ k)
    (hfirst : (copiedSlice mS n)[p + k]? = some D ∧
      ∀ q, q < p + k → (copiedSlice mS n)[q]? ≠ some D) :
    p = mixedPosAt (Sum.inr (Sum.inr (k - 2)) : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) mS t n := by
  have hpin := firstD_of_no_previous_D_copiedSlice mS n (p + k) hm hn hfirst.1 hfirst.2
  simp only [mixedPosAt]
  omega

/-- Deep-suffix activation soundness in arbitrary arity: once the mixed deep
tail coordinate at offset `k+1` is active, every tuple satisfying the
corresponding from-end deep suffix guard has rank `d*`.  The guard pins every
coordinate to the same mixed position, so no tuple-fibre scalarization is
needed. -/
theorem deepSuf_rank_eq_dstar_of_active_offset
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) {B : ℕ}
    (mS n t k : ℕ) (hk : k + 2 ≤ mS)
    (hactive : P.rank c (copiedSlice mS n)
        (fun _ : Fin (P.toPoly.arity c) =>
          mixedPosAt (Sum.inr (Sum.inl (k + 1)) : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) mS t n)
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (xb : Fin (P.toPoly.arity c) → ℕ)
    (hguard : ∀ i, ((copiedSlice mS n)[xb i]? = some D ∧
        ∀ q, q < (copiedSlice mS n).length → xb i < q → (copiedSlice mS n)[q]? = some D)
      ∧ xb i + 1 + k = (copiedSlice mS n).length) :
    P.rank c (copiedSlice mS n) xb = CopiedDstar.dstarRankGA_m P hV mS n := by
  have htuple : xb =
      (fun _ : Fin (P.toPoly.arity c) =>
        mixedPosAt (Sum.inr (Sum.inl (k + 1)) : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) mS t n) := by
    funext i
    exact deepSuf_fromEnd_mixedPosAt (B := B) mS n t (xb i) k hk (hguard i).2
  rw [htuple]
  exact hactive

/-- Deep-prefix activation soundness in arbitrary arity.  The gate offset is
`k`, whereas the mixed deep prefix coordinate stores the shifted offset `k-2`
because `mso_position_beforeFirstD k` pins `p + k = firstD = mS+1`. -/
theorem deepPre_rank_eq_dstar_of_active_offset
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) {B : ℕ}
    (mS n t k : ℕ) (hm : 1 ≤ mS) (hn : 1 ≤ n) (hk : 3 ≤ k)
    (hactive : P.rank c (copiedSlice mS n)
        (fun _ : Fin (P.toPoly.arity c) =>
          mixedPosAt (Sum.inr (Sum.inr (k - 2)) : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) mS t n)
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (xb : Fin (P.toPoly.arity c) → ℕ)
    (hguard : ∀ i, ((copiedSlice mS n)[xb i]? = some U ∧
        ∀ q, q < (copiedSlice mS n).length → q < xb i → (copiedSlice mS n)[q]? = some U)
      ∧ ((copiedSlice mS n)[xb i + k]? = some D ∧
        ∀ q, q < xb i + k → (copiedSlice mS n)[q]? ≠ some D)) :
    P.rank c (copiedSlice mS n) xb = CopiedDstar.dstarRankGA_m P hV mS n := by
  have htuple : xb =
      (fun _ : Fin (P.toPoly.arity c) =>
        mixedPosAt (Sum.inr (Sum.inr (k - 2)) : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) mS t n) := by
    funext i
    exact deepPre_beforeFirstD_mixedPosAt (B := B) mS n t (xb i) k hm hn hk (hguard i).2
  rw [htuple]
  exact hactive

/-- Abstract soundness package for the four band/deep activation callbacks used
by the row-indexed bridge.  The arity-1 supplier below proves it by collapsing
the tuple fibre; the arbitrary-arity route should replace that supplier. -/
def BandedRankSoundness (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    (∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
      (ī0 : Fin (P.toPoly.arity c) → ℕ) {B : ℕ}
      (mS n pc T Q k : ℕ) (F : ℕ → Fin P.d → ℤ)
      (_hm : 1 ≤ mS) (_hn : 1 ≤ n) (_hpc : 1 ≤ pc) (_hQ : 0 < Q) (_hpcQ : pc ∣ Q)
      (_hk : 2 ≤ k) (_hTk : T ≤ k - 2) (_hT2 : T + 2 * pc ≤ mS - 1)
      (_hF : RankAffineAtFrom T pc F)
      (_hag : ∀ l, l < mS - 1 →
        P.rank c (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l)
      {ρ ρact : ℕ} (_hρ : ρ < Q)
      (_hρact : ρact = ((ρ + Q - ((mS + 2 * n + 1 + T) % Q)) % pc))
      (_h0 : P.rank c (copiedSlice mS n)
          (CopiedDstar.cellTupleF
            (fun _ : Fin (P.toPoly.arity c) =>
              (RegionSpecF.sufIdx (T + ρact) : RegionSpecF B)) mS (B + 1) n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (_h1 : P.rank c (copiedSlice mS n)
          (CopiedDstar.cellTupleF
            (fun _ : Fin (P.toPoly.arity c) =>
              (RegionSpecF.sufIdx (T + ρact + pc) : RegionSpecF B)) mS (B + 1) n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (xb : Fin (P.toPoly.arity c) → ℕ)
      (_hp : xb j0 < (copiedSlice mS n).length)
      (_hband : ∃ y, y < (copiedSlice mS n).length ∧ xb j0 = y + k ∧
        ((copiedSlice mS n)[y]? = some D ∧
          ∀ q, q < (copiedSlice mS n).length → y < q → (copiedSlice mS n)[q]? = some D))
      (_habs : xb j0 % Q = ρ),
      P.rank c (copiedSlice mS n) xb = CopiedDstar.dstarRankGA_m P hV mS n) ∧
    (∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
      (ī0 : Fin (P.toPoly.arity c) → ℕ) {B : ℕ}
      (mS n pc T Q k : ℕ) (F : ℕ → Fin P.d → ℤ)
      (_hm : 1 ≤ mS) (_hn : 1 ≤ n) (_hpc : 1 ≤ pc) (_hQ : 0 < Q) (_hpcQ : pc ∣ Q)
      (_hTk : T ≤ k) (_hT2 : T + 2 * pc ≤ mS - 1)
      (_hF : RankAffineAtFrom T pc F)
      (_hag : ∀ l, l < mS - 1 →
        P.rank c (copiedSlice mS n) (Function.update ī0 j0 l) = F l)
      {ρ ρact : ℕ} (_hρ : ρ < Q)
      (_hρact : ρact = ((ρ + Q - (T % Q)) % pc))
      (_h0 : P.rank c (copiedSlice mS n)
          (CopiedDstar.cellTupleF
            (fun _ : Fin (P.toPoly.arity c) =>
              (RegionSpecF.prefIdx (T + ρact) : RegionSpecF B)) mS (B + 1) n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (_h1 : P.rank c (copiedSlice mS n)
          (CopiedDstar.cellTupleF
            (fun _ : Fin (P.toPoly.arity c) =>
              (RegionSpecF.prefIdx (T + ρact + pc) : RegionSpecF B)) mS (B + 1) n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (xb : Fin (P.toPoly.arity c) → ℕ)
      (_hrun : (copiedSlice mS n)[xb j0]? = some U ∧
        ∀ q, q < (copiedSlice mS n).length → q < xb j0 → (copiedSlice mS n)[q]? = some U)
      (_hband : ∃ y, y < (copiedSlice mS n).length ∧ xb j0 = y + k ∧
        ((copiedSlice mS n)[y]? = some U ∧
          ∀ q, q < (copiedSlice mS n).length → q < y → (copiedSlice mS n)[q]? = some U))
      (_hpref : xb j0 < mS - 1) (_habs : xb j0 % Q = ρ),
      P.rank c (copiedSlice mS n) xb = CopiedDstar.dstarRankGA_m P hV mS n) ∧
    (∀ (c : Fin P.toPoly.K) (_j0 : Fin (P.toPoly.arity c)) {B : ℕ}
      (mS n t k : ℕ) (_hk : k + 2 ≤ mS)
      (_hactive : P.rank c (copiedSlice mS n)
          (fun _ : Fin (P.toPoly.arity c) =>
            mixedPosAt (Sum.inr (Sum.inl (k + 1)) : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) mS t n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (xb : Fin (P.toPoly.arity c) → ℕ)
      (_hguard : ∀ i, ((copiedSlice mS n)[xb i]? = some D ∧
          ∀ q, q < (copiedSlice mS n).length → xb i < q → (copiedSlice mS n)[q]? = some D)
        ∧ xb i + 1 + k = (copiedSlice mS n).length),
      P.rank c (copiedSlice mS n) xb = CopiedDstar.dstarRankGA_m P hV mS n) ∧
    (∀ (c : Fin P.toPoly.K) (_j0 : Fin (P.toPoly.arity c)) {B : ℕ}
      (mS n t k : ℕ) (_hm : 1 ≤ mS) (_hn : 1 ≤ n) (_hk : 3 ≤ k)
      (_hactive : P.rank c (copiedSlice mS n)
          (fun _ : Fin (P.toPoly.arity c) =>
            mixedPosAt (Sum.inr (Sum.inr (k - 2)) : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) mS t n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (xb : Fin (P.toPoly.arity c) → ℕ)
      (_hguard : ∀ i, ((copiedSlice mS n)[xb i]? = some U ∧
          ∀ q, q < (copiedSlice mS n).length → q < xb i → (copiedSlice mS n)[q]? = some U)
        ∧ ((copiedSlice mS n)[xb i + k]? = some D ∧
          ∀ q, q < xb i + k → (copiedSlice mS n)[q]? ≠ some D)),
      P.rank c (copiedSlice mS n) xb = CopiedDstar.dstarRankGA_m P hV mS n)

/-- Tuple-wide rank soundness for the banded full gate.  Unlike the legacy
`BandedRankSoundness` suffix/prefix branches, the run-band hypotheses guard
every coordinate of the competitor tuple, matching
`CopiedTieSlice.bridgeGateCond` and
`fasU_atomOrd_full_gate_bounded_band`. -/
def BandedTupleRankSoundness (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    (∀ (c : Fin P.toPoly.K) (_j0 : Fin (P.toPoly.arity c))
      (_ī0 : Fin (P.toPoly.arity c) → ℕ) {B : ℕ}
      (mS n pc T Q k : ℕ) (F : ℕ → Fin P.d → ℤ)
      (_hm : 1 ≤ mS) (_hn : 1 ≤ n) (_hpc : 1 ≤ pc) (_hQ : 0 < Q) (_hpcQ : pc ∣ Q)
      (_hk : 2 ≤ k) (_hTk : T ≤ k - 2) (_hT2 : T + 2 * pc ≤ mS - 1)
      (_hF : RankAffineAtFrom T pc F)
      (_hag : ∀ l, l < mS - 1 →
        P.rank c (copiedSlice mS n)
          (Function.update _ī0 _j0 (mS + 2 * n + 1 + l)) = F l)
      {ρ ρact : ℕ} (_hρ : ρ < Q)
      (_hρact : ρact = ((ρ + Q - ((mS + 2 * n + 1 + T) % Q)) % pc))
      (_h0 : P.rank c (copiedSlice mS n)
          (CopiedDstar.cellTupleF
            (fun _ : Fin (P.toPoly.arity c) =>
              (RegionSpecF.sufIdx (T + ρact) : RegionSpecF B)) mS (B + 1) n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (_h1 : P.rank c (copiedSlice mS n)
          (CopiedDstar.cellTupleF
            (fun _ : Fin (P.toPoly.arity c) =>
              (RegionSpecF.sufIdx (T + ρact + pc) : RegionSpecF B)) mS (B + 1) n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (xb : Fin (P.toPoly.arity c) → ℕ)
      (_hval : ∀ i, xb i < (copiedSlice mS n).length)
      (_hguard : ∀ i,
        (((copiedSlice mS n)[xb i]? = some D ∧
            ∀ q, q < (copiedSlice mS n).length → xb i < q →
              (copiedSlice mS n)[q]? = some D)
          ∧ xb i % Q = ρ)
        ∧ (∃ y, y < (copiedSlice mS n).length ∧ xb i = y + k ∧
            ((copiedSlice mS n)[y]? = some D ∧
              ∀ q, q < (copiedSlice mS n).length → y < q →
                (copiedSlice mS n)[q]? = some D))),
      P.rank c (copiedSlice mS n) xb = CopiedDstar.dstarRankGA_m P hV mS n) ∧
    (∀ (c : Fin P.toPoly.K) (_j0 : Fin (P.toPoly.arity c))
      (_ī0 : Fin (P.toPoly.arity c) → ℕ) {B : ℕ}
      (mS n pc T Q k : ℕ) (F : ℕ → Fin P.d → ℤ)
      (_hm : 1 ≤ mS) (_hn : 1 ≤ n) (_hpc : 1 ≤ pc) (_hQ : 0 < Q) (_hpcQ : pc ∣ Q)
      (_hTk : T ≤ k) (_hT2 : T + 2 * pc ≤ mS - 1)
      (_hF : RankAffineAtFrom T pc F)
      (_hag : ∀ l, l < mS - 1 →
        P.rank c (copiedSlice mS n) (Function.update _ī0 _j0 l) = F l)
      {ρ ρact : ℕ} (_hρ : ρ < Q)
      (_hρact : ρact = ((ρ + Q - (T % Q)) % pc))
      (_h0 : P.rank c (copiedSlice mS n)
          (CopiedDstar.cellTupleF
            (fun _ : Fin (P.toPoly.arity c) =>
              (RegionSpecF.prefIdx (T + ρact) : RegionSpecF B)) mS (B + 1) n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (_h1 : P.rank c (copiedSlice mS n)
          (CopiedDstar.cellTupleF
            (fun _ : Fin (P.toPoly.arity c) =>
              (RegionSpecF.prefIdx (T + ρact + pc) : RegionSpecF B)) mS (B + 1) n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (xb : Fin (P.toPoly.arity c) → ℕ)
      (_hval : ∀ i, xb i < (copiedSlice mS n).length)
      (_hguard : ∀ i, CopiedBandRunGate.preBandStrictGuard
        (copiedSlice mS n) Q ρ k (xb i)),
      P.rank c (copiedSlice mS n) xb = CopiedDstar.dstarRankGA_m P hV mS n) ∧
    (∀ (c : Fin P.toPoly.K) (_j0 : Fin (P.toPoly.arity c)) {B : ℕ}
      (mS n t k : ℕ) (_hk : k + 2 ≤ mS)
      (_hactive : P.rank c (copiedSlice mS n)
          (fun _ : Fin (P.toPoly.arity c) =>
            mixedPosAt (Sum.inr (Sum.inl (k + 1)) : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) mS t n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (xb : Fin (P.toPoly.arity c) → ℕ)
      (_hguard : ∀ i, ((copiedSlice mS n)[xb i]? = some D ∧
          ∀ q, q < (copiedSlice mS n).length → xb i < q → (copiedSlice mS n)[q]? = some D)
        ∧ xb i + 1 + k = (copiedSlice mS n).length),
      P.rank c (copiedSlice mS n) xb = CopiedDstar.dstarRankGA_m P hV mS n) ∧
    (∀ (c : Fin P.toPoly.K) (_j0 : Fin (P.toPoly.arity c)) {B : ℕ}
      (mS n t k : ℕ) (_hm : 1 ≤ mS) (_hn : 1 ≤ n) (_hk : 3 ≤ k)
      (_hactive : P.rank c (copiedSlice mS n)
          (fun _ : Fin (P.toPoly.arity c) =>
            mixedPosAt (Sum.inr (Sum.inr (k - 2)) : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) mS t n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (xb : Fin (P.toPoly.arity c) → ℕ)
      (_hguard : ∀ i, ((copiedSlice mS n)[xb i]? = some U ∧
          ∀ q, q < (copiedSlice mS n).length → q < xb i → (copiedSlice mS n)[q]? = some U)
        ∧ ((copiedSlice mS n)[xb i + k]? = some D ∧
          ∀ q, q < xb i + k → (copiedSlice mS n)[q]? ≠ some D)),
      P.rank c (copiedSlice mS n) xb = CopiedDstar.dstarRankGA_m P hV mS n)

/-- The legacy distinguished-coordinate soundness package implies the tuple-wide
package by reading the full run guard at the chosen coordinate.  This keeps
the arity-1/scalarized path compatible while exposing the right target for the
general-arity full bridge. -/
theorem bandedTupleRankSoundness_of_rankSoundness
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hSound : BandedRankSoundness P hV) :
    BandedTupleRankSoundness P hV := by
  rcases hSound with ⟨hSuf, hPre, hDeepSuf, hDeepPre⟩
  refine ⟨?_, ?_, hDeepSuf, hDeepPre⟩
  · intro c j0 ī0 B mS n pc T Q k F hm hn hpc hQ hpcQ hk hTk hT2 hF hag
      ρ ρact hρ hρact h0 h1 xb hval hguard
    exact hSuf c j0 ī0 (B := B) mS n pc T Q k F hm hn hpc hQ hpcQ hk hTk hT2
      hF hag hρ hρact h0 h1 xb (hval j0) (hguard j0).2 (hguard j0).1.2
  · intro c j0 ī0 B mS n pc T Q k F hm hn hpc hQ hpcQ hTk hT2 hF hag
      ρ ρact hρ hρact h0 h1 xb _hval hguard
    have hguardj := hguard j0
    have hrunj :
        (copiedSlice mS n)[xb j0]? = some U ∧
          ∀ q, q < (copiedSlice mS n).length → q < xb j0 →
            (copiedSlice mS n)[q]? = some U :=
      hguardj.1.1
    have hbandj :
        ∃ y, y < (copiedSlice mS n).length ∧ xb j0 = y + k ∧
          ((copiedSlice mS n)[y]? = some U ∧
            ∀ q, q < (copiedSlice mS n).length → q < y →
              (copiedSlice mS n)[q]? = some U) :=
      hguardj.2.1
    have hprefj : xb j0 < mS - 1 := by
      rcases hguardj.2.2 with ⟨z, _hzlen, hpz, hzD, hzNoD⟩
      have hzfirst := firstD_of_no_previous_D_copiedSlice mS n (z + 2) hm hn hzD hzNoD
      omega
    exact hPre c j0 ī0 (B := B) mS n pc T Q k F hm hn hpc hQ hpcQ hTk hT2
      hF hag hρ hρact h0 h1 xb hrunj hbandj hprefj hguardj.1.2

/-- Arity-free core for the band/deep rank callbacks when the run-band
callbacks are phrased over the distinguished-coordinate update tuple and their
two representatives are already supplied in the same affine table.  This is the
non-scalarized part needed by a descriptor-level bridge; the legacy
`BandedRankSoundness` below still asks for arbitrary tuple fibres in the
suffix/prefix band branches. -/
def BandedUpdateRankSoundness (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    (∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
      (ī0 : Fin (P.toPoly.arity c) → ℕ) {_B : ℕ}
      (mS n pc T Q k : ℕ) (F : ℕ → Fin P.d → ℤ)
      (_hm : 1 ≤ mS) (_hn : 1 ≤ n) (_hpc : 1 ≤ pc) (_hQ : 0 < Q) (_hpcQ : pc ∣ Q)
      (_hk : 2 ≤ k) (_hTk : T ≤ k - 2) (_hT2 : T + 2 * pc ≤ mS - 1)
      (_hF : RankAffineAtFrom T pc F)
      (_hag : ∀ l, l < mS - 1 →
        P.rank c (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l)
      {ρ ρact : ℕ} (_hρ : ρ < Q)
      (_hρact : ρact = ((ρ + Q - ((mS + 2 * n + 1 + T) % Q)) % pc))
      (_h0F : F (T + ρact) = CopiedDstar.dstarRankGA_m P hV mS n)
      (_h1F : F (T + ρact + pc) = CopiedDstar.dstarRankGA_m P hV mS n)
      (p : ℕ)
      (_hp : p < (copiedSlice mS n).length)
      (_hband : ∃ y, y < (copiedSlice mS n).length ∧ p = y + k ∧
        ((copiedSlice mS n)[y]? = some D ∧
          ∀ q, q < (copiedSlice mS n).length → y < q → (copiedSlice mS n)[q]? = some D))
      (_habs : p % Q = ρ),
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 p)
        = CopiedDstar.dstarRankGA_m P hV mS n) ∧
    (∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
      (ī0 : Fin (P.toPoly.arity c) → ℕ) {_B : ℕ}
      (mS n pc T Q k : ℕ) (F : ℕ → Fin P.d → ℤ)
      (_hm : 1 ≤ mS) (_hn : 1 ≤ n) (_hpc : 1 ≤ pc) (_hQ : 0 < Q) (_hpcQ : pc ∣ Q)
      (_hTk : T ≤ k) (_hT2 : T + 2 * pc ≤ mS - 1)
      (_hF : RankAffineAtFrom T pc F)
      (_hag : ∀ l, l < mS - 1 →
        P.rank c (copiedSlice mS n) (Function.update ī0 j0 l) = F l)
      {ρ ρact : ℕ} (_hρ : ρ < Q)
      (_hρact : ρact = ((ρ + Q - (T % Q)) % pc))
      (_h0F : F (T + ρact) = CopiedDstar.dstarRankGA_m P hV mS n)
      (_h1F : F (T + ρact + pc) = CopiedDstar.dstarRankGA_m P hV mS n)
      (p : ℕ)
      (_hrun : (copiedSlice mS n)[p]? = some U ∧
        ∀ q, q < (copiedSlice mS n).length → q < p → (copiedSlice mS n)[q]? = some U)
      (_hband : ∃ y, y < (copiedSlice mS n).length ∧ p = y + k ∧
        ((copiedSlice mS n)[y]? = some U ∧
          ∀ q, q < (copiedSlice mS n).length → q < y → (copiedSlice mS n)[q]? = some U))
      (_hpref : p < mS - 1) (_habs : p % Q = ρ),
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 p)
        = CopiedDstar.dstarRankGA_m P hV mS n) ∧
    (∀ (c : Fin P.toPoly.K) (_j0 : Fin (P.toPoly.arity c)) {B : ℕ}
      (mS n t k : ℕ) (_hk : k + 2 ≤ mS)
      (_hactive : P.rank c (copiedSlice mS n)
          (fun _ : Fin (P.toPoly.arity c) =>
            mixedPosAt (Sum.inr (Sum.inl (k + 1)) : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) mS t n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (xb : Fin (P.toPoly.arity c) → ℕ)
      (_hguard : ∀ i, ((copiedSlice mS n)[xb i]? = some D ∧
          ∀ q, q < (copiedSlice mS n).length → xb i < q → (copiedSlice mS n)[q]? = some D)
        ∧ xb i + 1 + k = (copiedSlice mS n).length),
      P.rank c (copiedSlice mS n) xb = CopiedDstar.dstarRankGA_m P hV mS n) ∧
    (∀ (c : Fin P.toPoly.K) (_j0 : Fin (P.toPoly.arity c)) {B : ℕ}
      (mS n t k : ℕ) (_hm : 1 ≤ mS) (_hn : 1 ≤ n) (_hk : 3 ≤ k)
      (_hactive : P.rank c (copiedSlice mS n)
          (fun _ : Fin (P.toPoly.arity c) =>
            mixedPosAt (Sum.inr (Sum.inr (k - 2)) : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) mS t n)
          = CopiedDstar.dstarRankGA_m P hV mS n)
      (xb : Fin (P.toPoly.arity c) → ℕ)
      (_hguard : ∀ i, ((copiedSlice mS n)[xb i]? = some U ∧
          ∀ q, q < (copiedSlice mS n).length → q < xb i → (copiedSlice mS n)[q]? = some U)
        ∧ ((copiedSlice mS n)[xb i + k]? = some D ∧
          ∀ q, q < xb i + k → (copiedSlice mS n)[q]? ≠ some D)),
      P.rank c (copiedSlice mS n) xb = CopiedDstar.dstarRankGA_m P hV mS n)

/-- Public arity-free supplier for `BandedUpdateRankSoundness`. -/
theorem bandedUpdateRankSoundness
    (P : WRP.Presentation Step Step) (hV : P.Valid) :
    BandedUpdateRankSoundness P hV := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c j0 ī0 B mS n pc T Q k F hm hn hpc hQ hpcQ hk hTk _hT2 hF hag
      ρ ρact hρ hρact h0F h1F p hp hband habs
    exact suffix_rank_eq_dstar_of_two_reps_abs_mod_band_update_slice P hV
      c j0 ī0 mS n pc T Q k F hm hn hpc hQ hpcQ hk hTk hF hag hρ
      (by simpa [hρact] using h0F) (by simpa [hρact] using h1F) hp hband habs
  · intro c j0 ī0 B mS n pc T Q k F hm hn hpc hQ hpcQ hTk _hT2 hF hag
      ρ ρact hρ hρact h0F h1F p hrun hband hpref habs
    exact prefix_rank_eq_dstar_of_two_reps_abs_mod_band_update_slice P hV
      c j0 ī0 mS n pc T Q k F hm hn hpc hQ hpcQ hTk hF hag hρ
      (by simpa [hρact] using h0F) (by simpa [hρact] using h1F) hrun hband hpref habs
  · intro c _j0 B mS n t k hk hactive xb hguard
    exact deepSuf_rank_eq_dstar_of_active_offset P hV c mS n t k hk hactive xb hguard
  · intro c _j0 B mS n t k hm hn hk hactive xb hguard
    exact deepPre_rank_eq_dstar_of_active_offset P hV c mS n t k hm hn hk hactive xb hguard

/-- Abstract completeness package for update-shaped suffix/prefix activation
tables.  Unlike `BandedActivationCompleteness`, the stored representatives are
the distinguished-coordinate update tuples themselves, so completeness is just
the affine table equation at the two representatives. -/
def BandedUpdateActivationCompleteness (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    (∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
      (ī0 : Fin (P.toPoly.arity c) → ℕ)
      (mS n pc T ρact : ℕ) (F : ℕ → Fin P.d → ℤ)
      (_hpc : 1 ≤ pc) (_hρact_lt : ρact < pc) (_hT2 : T + 2 * pc ≤ mS - 1)
      (_hag : ∀ l, l < mS - 1 →
        P.rank c (copiedSlice mS n)
          (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l)
      (_h0F : F (T + ρact) = CopiedDstar.dstarRankGA_m P hV mS n)
      (_h1F : F (T + ρact + pc) = CopiedDstar.dstarRankGA_m P hV mS n),
      P.rank c (copiedSlice mS n)
          (Function.update ī0 j0 (mS + 2 * n + 1 + (T + ρact)))
        = CopiedDstar.dstarRankGA_m P hV mS n ∧
      P.rank c (copiedSlice mS n)
          (Function.update ī0 j0 (mS + 2 * n + 1 + (T + ρact + pc)))
        = CopiedDstar.dstarRankGA_m P hV mS n) ∧
    (∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
      (ī0 : Fin (P.toPoly.arity c) → ℕ)
      (mS n pc T ρact : ℕ) (F : ℕ → Fin P.d → ℤ)
      (_hpc : 1 ≤ pc) (_hρact_lt : ρact < pc) (_hT2 : T + 2 * pc ≤ mS - 1)
      (_hag : ∀ l, l < mS - 1 →
        P.rank c (copiedSlice mS n) (Function.update ī0 j0 l) = F l)
      (_h0F : F (T + ρact) = CopiedDstar.dstarRankGA_m P hV mS n)
      (_h1F : F (T + ρact + pc) = CopiedDstar.dstarRankGA_m P hV mS n),
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 (T + ρact))
        = CopiedDstar.dstarRankGA_m P hV mS n ∧
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 (T + ρact + pc))
        = CopiedDstar.dstarRankGA_m P hV mS n)

/-- The update-shaped suffix activation table: local residues whose two
adjacent affine-table representatives are both `d*`. -/
noncomputable def updateSufTieSet
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n pc T : ℕ) : Finset ℕ :=
  (Finset.range pc).filter (fun ρ =>
    P.rank c (copiedSlice mS n)
        (Function.update ī0 j0 (mS + 2 * n + 1 + (T + ρ)))
      = CopiedDstar.dstarRankGA_m P hV mS n ∧
    P.rank c (copiedSlice mS n)
        (Function.update ī0 j0 (mS + 2 * n + 1 + (T + ρ + pc)))
      = CopiedDstar.dstarRankGA_m P hV mS n)

/-- Prefix twin of `updateSufTieSet`. -/
noncomputable def updatePreTieSet
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n pc T : ℕ) : Finset ℕ :=
  (Finset.range pc).filter (fun ρ =>
    P.rank c (copiedSlice mS n) (Function.update ī0 j0 (T + ρ))
      = CopiedDstar.dstarRankGA_m P hV mS n ∧
    P.rank c (copiedSlice mS n) (Function.update ī0 j0 (T + ρ + pc))
      = CopiedDstar.dstarRankGA_m P hV mS n)

/-- Absolute-`Q` suffix residues whose local residue is active in the
update-shaped suffix tie set.  This is the update-table analogue of the bridge
row's `Ssuf` construction. -/
noncomputable def updateSufAbsTieSet
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n pc T Q : ℕ) : Finset ℕ :=
  (Finset.range Q).filter (fun ρ =>
    ((ρ + Q - ((mS + 2 * n + 1 + T) % Q)) % pc) ∈
      updateSufTieSet P hV c j0 ī0 mS n pc T)

/-- Prefix twin of `updateSufAbsTieSet`. -/
noncomputable def updatePreAbsTieSet
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n pc T Q : ℕ) : Finset ℕ :=
  (Finset.range Q).filter (fun ρ =>
    ((ρ + Q - (T % Q)) % pc) ∈ updatePreTieSet P hV c j0 ī0 mS n pc T)

/-- Characterize membership in the update suffix absolute-residue table. -/
theorem mem_updateSufAbsTieSet
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n pc T Q ρ : ℕ) :
    ρ ∈ updateSufAbsTieSet P hV c j0 ī0 mS n pc T Q ↔
      ρ < Q ∧
        ((ρ + Q - ((mS + 2 * n + 1 + T) % Q)) % pc) ∈
          updateSufTieSet P hV c j0 ī0 mS n pc T := by
  simp [updateSufAbsTieSet]

/-- Prefix twin of `mem_updateSufAbsTieSet`. -/
theorem mem_updatePreAbsTieSet
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n pc T Q ρ : ℕ) :
    ρ ∈ updatePreAbsTieSet P hV c j0 ī0 mS n pc T Q ↔
      ρ < Q ∧
        ((ρ + Q - (T % Q)) % pc) ∈ updatePreTieSet P hV c j0 ī0 mS n pc T := by
  simp [updatePreAbsTieSet]

/-- Lift equality of local update suffix tie sets to the absolute `Q`-residue
tables, provided the suffix residue shift is the same. -/
theorem updateSufAbsTieSet_eq_of_tieSet_eq
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n n' pc T Q : ℕ)
    (hshift :
      (mS + 2 * n + 1 + T) % Q = (mS + 2 * n' + 1 + T) % Q)
    (hset :
      updateSufTieSet P hV c j0 ī0 mS n pc T =
        updateSufTieSet P hV c j0 ī0 mS n' pc T) :
    updateSufAbsTieSet P hV c j0 ī0 mS n pc T Q =
      updateSufAbsTieSet P hV c j0 ī0 mS n' pc T Q := by
  ext ρ
  simp [updateSufAbsTieSet, hshift, hset]

/-- Prefix twin of `updateSufAbsTieSet_eq_of_tieSet_eq`: the absolute prefix
shift is independent of `n`, so only local tie-set equality is needed. -/
theorem updatePreAbsTieSet_eq_of_tieSet_eq
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    (ī0 : Fin (P.toPoly.arity c) → ℕ) (mS n n' pc T Q : ℕ)
    (hset :
      updatePreTieSet P hV c j0 ī0 mS n pc T =
        updatePreTieSet P hV c j0 ī0 mS n' pc T) :
    updatePreAbsTieSet P hV c j0 ī0 mS n pc T Q =
      updatePreAbsTieSet P hV c j0 ī0 mS n' pc T Q := by
  ext ρ
  simp [updatePreAbsTieSet, hset]

/-- Store a suffix residue in the update activation table from the abstract
update activation completeness supplier. -/
theorem mem_updateSufTieSet_of_activation
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hActive : BandedUpdateActivationCompleteness P hV)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    (ī0 : Fin (P.toPoly.arity c) → ℕ)
    (mS n pc T ρact : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hpc : 1 ≤ pc) (hρact_lt : ρact < pc) (hT2 : T + 2 * pc ≤ mS - 1)
    (hag : ∀ l, l < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l)
    (h0F : F (T + ρact) = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1F : F (T + ρact + pc) = CopiedDstar.dstarRankGA_m P hV mS n) :
    ρact ∈ updateSufTieSet P hV c j0 ī0 mS n pc T := by
  have hRanks := hActive.1 c j0 ī0 mS n pc T ρact F hpc hρact_lt hT2 hag h0F h1F
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hρact_lt, hRanks⟩

/-- Prefix twin of `mem_updateSufTieSet_of_activation`. -/
theorem mem_updatePreTieSet_of_activation
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hActive : BandedUpdateActivationCompleteness P hV)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    (ī0 : Fin (P.toPoly.arity c) → ℕ)
    (mS n pc T ρact : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hpc : 1 ≤ pc) (hρact_lt : ρact < pc) (hT2 : T + 2 * pc ≤ mS - 1)
    (hag : ∀ l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 l) = F l)
    (h0F : F (T + ρact) = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1F : F (T + ρact + pc) = CopiedDstar.dstarRankGA_m P hV mS n) :
    ρact ∈ updatePreTieSet P hV c j0 ī0 mS n pc T := by
  have hRanks := hActive.2 c j0 ī0 mS n pc T ρact F hpc hρact_lt hT2 hag h0F h1F
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hρact_lt, hRanks⟩

/-- Store an absolute suffix residue in the update activation table from the
abstract update activation completeness supplier.  The local residue is decoded
using the same `Q`-shift as `updateSufAbsTieSet`. -/
theorem mem_updateSufAbsTieSet_of_activation
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hActive : BandedUpdateActivationCompleteness P hV)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    (ī0 : Fin (P.toPoly.arity c) → ℕ)
    (mS n pc T Q ρ : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hpc : 1 ≤ pc) (hρ : ρ < Q) (hT2 : T + 2 * pc ≤ mS - 1)
    (hag : ∀ l, l < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l)
    (h0F :
      F (T + ((ρ + Q - ((mS + 2 * n + 1 + T) % Q)) % pc))
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1F :
      F (T + ((ρ + Q - ((mS + 2 * n + 1 + T) % Q)) % pc) + pc)
        = CopiedDstar.dstarRankGA_m P hV mS n) :
    ρ ∈ updateSufAbsTieSet P hV c j0 ī0 mS n pc T Q := by
  refine (mem_updateSufAbsTieSet P hV c j0 ī0 mS n pc T Q ρ).mpr
    ⟨hρ, ?_⟩
  exact mem_updateSufTieSet_of_activation P hV hActive c j0 ī0 mS n pc T
    ((ρ + Q - ((mS + 2 * n + 1 + T) % Q)) % pc) F hpc
    (Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hpc)) hT2 hag h0F h1F

/-- Prefix twin of `mem_updateSufAbsTieSet_of_activation`. -/
theorem mem_updatePreAbsTieSet_of_activation
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hActive : BandedUpdateActivationCompleteness P hV)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
    (ī0 : Fin (P.toPoly.arity c) → ℕ)
    (mS n pc T Q ρ : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hpc : 1 ≤ pc) (hρ : ρ < Q) (hT2 : T + 2 * pc ≤ mS - 1)
    (hag : ∀ l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 l) = F l)
    (h0F : F (T + ((ρ + Q - (T % Q)) % pc))
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1F : F (T + ((ρ + Q - (T % Q)) % pc) + pc)
        = CopiedDstar.dstarRankGA_m P hV mS n) :
    ρ ∈ updatePreAbsTieSet P hV c j0 ī0 mS n pc T Q := by
  refine (mem_updatePreAbsTieSet P hV c j0 ī0 mS n pc T Q ρ).mpr
    ⟨hρ, ?_⟩
  exact mem_updatePreTieSet_of_activation P hV hActive c j0 ī0 mS n pc T
    ((ρ + Q - (T % Q)) % pc) F hpc
    (Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hpc)) hT2 hag h0F h1F

/-- Public arity-free supplier for update-shaped activation completeness. -/
theorem bandedUpdateActivationCompleteness
    (P : WRP.Presentation Step Step) (hV : P.Valid) :
    BandedUpdateActivationCompleteness P hV := by
  constructor
  · intro c j0 ī0 mS n pc T ρact F hpc hρact_lt hT2 hag h0F h1F
    constructor
    · rw [hag (T + ρact)]
      · exact h0F
      · omega
    · rw [hag (T + ρact + pc)]
      · exact h1F
      · omega
  · intro c j0 ī0 mS n pc T ρact F hpc hρact_lt hT2 hag h0F h1F
    constructor
    · rw [hag (T + ρact)]
      · exact h0F
      · omega
    · rw [hag (T + ρact + pc)]
      · exact h1F
      · omega

/-- Abstract completeness package converting scalar suffix/prefix slope facts
back into the active cell representatives stored in the row table. -/
def BandedActivationCompleteness (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    (∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
      (ī0 : Fin (P.toPoly.arity c) → ℕ) {B : ℕ}
      (mS n pc T ρact : ℕ) (F : ℕ → Fin P.d → ℤ)
      (_hpc : 1 ≤ pc) (_hρact_lt : ρact < pc) (_hT2 : T + 2 * pc ≤ mS - 1)
      (_hag : ∀ l, l < mS - 1 →
        P.rank c (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l)
      (_h0F : F (T + ρact) = CopiedDstar.dstarRankGA_m P hV mS n)
      (_h1F : F (T + ρact + pc) = CopiedDstar.dstarRankGA_m P hV mS n),
      P.rank c (copiedSlice mS n)
            (CopiedDstar.cellTupleF
              (fun _ : Fin (P.toPoly.arity c) =>
                (RegionSpecF.sufIdx (T + ρact) : RegionSpecF B)) mS (B + 1) n)
          = CopiedDstar.dstarRankGA_m P hV mS n ∧
        P.rank c (copiedSlice mS n)
            (CopiedDstar.cellTupleF
              (fun _ : Fin (P.toPoly.arity c) =>
                (RegionSpecF.sufIdx (T + ρact + pc) : RegionSpecF B)) mS (B + 1) n)
          = CopiedDstar.dstarRankGA_m P hV mS n) ∧
    (∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
      (ī0 : Fin (P.toPoly.arity c) → ℕ) {B : ℕ}
      (mS n pc T ρact : ℕ) (F : ℕ → Fin P.d → ℤ)
      (_hpc : 1 ≤ pc) (_hρact_lt : ρact < pc) (_hT2 : T + 2 * pc ≤ mS - 1)
      (_hag : ∀ l, l < mS - 1 →
        P.rank c (copiedSlice mS n) (Function.update ī0 j0 l) = F l)
      (_h0F : F (T + ρact) = CopiedDstar.dstarRankGA_m P hV mS n)
      (_h1F : F (T + ρact + pc) = CopiedDstar.dstarRankGA_m P hV mS n),
      P.rank c (copiedSlice mS n)
            (CopiedDstar.cellTupleF
              (fun _ : Fin (P.toPoly.arity c) =>
                (RegionSpecF.prefIdx (T + ρact) : RegionSpecF B)) mS (B + 1) n)
          = CopiedDstar.dstarRankGA_m P hV mS n ∧
        P.rank c (copiedSlice mS n)
            (CopiedDstar.cellTupleF
              (fun _ : Fin (P.toPoly.arity c) =>
                (RegionSpecF.prefIdx (T + ρact + pc) : RegionSpecF B)) mS (B + 1) n)
          = CopiedDstar.dstarRankGA_m P hV mS n)

/-- **The banded bounded-cell full gate.**  As `fasU_atomOrd_full_gate_bounded`, but the run clauses
carry the band conjunct `∃ y, y + kSuf/kPre = xb i ∧ inRun y`.  One `Mdfa` for the whole `mS`-class. -/
theorem fasU_atomOrd_full_gate_bounded_band (B Bh M mthr q_U q_D kSuf kPre : ℕ)
    (S₁ F₁ K₁ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpecF B) → Finset ℕ)
    (S₂ F₂ K₂ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpecF Bh) → Finset ℕ)
    (Ssuf Spre Dsuf Dpre : (c' : Fin P.toPoly.K) → Finset ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hSsuf : ∀ c' r, r ∈ Ssuf c' → r < Q) (hSpre : ∀ c' r, r ∈ Spre c' → r < Q)
    (hBB : B ≤ Bh) (hBh1 : 1 ≤ Bh) (hM2 : M % 2 = 0)
    (hS₁ : ∀ c' rs, ∀ r ∈ S₁ c' rs, r < M ∧ r % 2 = 1)
    (hS₂ : ∀ c' rs, ∀ r ∈ S₂ c' rs, r < M ∧ r % 2 = 1)
    (hF₁ : ∀ c' rs, ∀ f ∈ F₁ c' rs, f % 2 = 1)
    (hF₂ : ∀ c' rs, ∀ f ∈ F₂ c' rs, f % 2 = 1)
    (hK₁ : ∀ c' rs, ∀ k ∈ K₁ c' rs, k % 2 = 0)
    (hK₂ : ∀ c' rs, ∀ k ∈ K₂ c' rs, k % 2 = 0)
    (hS₁b : ∀ c' rs, rs ∉ boundedTuplesF B (P.toPoly.arity c') q_U q_D → S₁ c' rs = ∅)
    (hF₁b : ∀ c' rs, rs ∉ boundedTuplesF B (P.toPoly.arity c') q_U q_D → F₁ c' rs = ∅)
    (hK₁b : ∀ c' rs, rs ∉ boundedTuplesF B (P.toPoly.arity c') q_U q_D → K₁ c' rs = ∅)
    (hS₂b : ∀ c' rs, rs ∉ boundedTuplesF Bh (P.toPoly.arity c') q_U q_D → S₂ c' rs = ∅)
    (hF₂b : ∀ c' rs, rs ∉ boundedTuplesF Bh (P.toPoly.arity c') q_U q_D → F₂ c' rs = ∅)
    (hK₂b : ∀ c' rs, rs ∉ boundedTuplesF Bh (P.toPoly.arity c') q_U q_D → K₂ c' rs = ∅) :
    ∃ Mdfa : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)),
      ∀ (mS n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ), q_U < mS → q_D < mS → Bh ≤ n →
        (∀ i, ī i < (copiedSlice mS n).length) →
        ((P.toPoly.sel c (copiedSlice mS n) ī
          ∧ P.toPoly.label c (copiedSlice mS n) ī = U
          ∧ (∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
              P.toPoly.labelOf (copiedSlice mS n) b = D →
              CopiedTieGate.cfgCellGAFL B Bh M mthr S₁ F₁ K₁ S₂ F₂ K₂ mS n b →
              P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
          ∧ (∀ (c' : Fin P.toPoly.K) (r : ℕ), r ∈ Ssuf c' →
              ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < (copiedSlice mS n).length) →
                ((∀ i, (((copiedSlice mS n)[xb i]? = some D
                      ∧ ∀ q, q < (copiedSlice mS n).length → xb i < q → (copiedSlice mS n)[q]? = some D)
                    ∧ xb i % Q = r)
                    ∧ (∃ y, y < (copiedSlice mS n).length ∧ xb i = y + kSuf ∧
                        ((copiedSlice mS n)[y]? = some D
                          ∧ ∀ q, q < (copiedSlice mS n).length → y < q → (copiedSlice mS n)[q]? = some D)))
                  ∧ P.toPoly.sel c' (copiedSlice mS n) xb ∧ P.toPoly.label c' (copiedSlice mS n) xb = D) →
                P.toPoly.ord c c' (copiedSlice mS n) ī xb)
            ∧ (∀ (c' : Fin P.toPoly.K) (r : ℕ), r ∈ Spre c' →
                ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < (copiedSlice mS n).length) →
                  (((∀ i, preBandStrictGuard (copiedSlice mS n) Q r kPre (xb i))
                    ∧ P.toPoly.sel c' (copiedSlice mS n) xb)
                    ∧ P.toPoly.label c' (copiedSlice mS n) xb = D) →
                  P.toPoly.ord c c' (copiedSlice mS n) ī xb)
          ∧ (∀ (c' : Fin P.toPoly.K) (k : ℕ), k ∈ Dsuf c' →
              ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < (copiedSlice mS n).length) →
                ((∀ i, (((copiedSlice mS n)[xb i]? = some D
                      ∧ ∀ q, q < (copiedSlice mS n).length → xb i < q → (copiedSlice mS n)[q]? = some D)
                    ∧ xb i + 1 + k = (copiedSlice mS n).length))
                  ∧ P.toPoly.sel c' (copiedSlice mS n) xb ∧ P.toPoly.label c' (copiedSlice mS n) xb = D) →
                P.toPoly.ord c c' (copiedSlice mS n) ī xb)
          ∧ (∀ (c' : Fin P.toPoly.K) (k : ℕ), k ∈ Dpre c' →
              ∀ xb : Fin (P.toPoly.arity c') → ℕ, (∀ i, xb i < (copiedSlice mS n).length) →
                ((∀ i, ((copiedSlice mS n)[xb i]? = some U
                      ∧ ∀ q, q < (copiedSlice mS n).length → q < xb i → (copiedSlice mS n)[q]? = some U)
                    ∧ ((copiedSlice mS n)[xb i + k]? = some D
                      ∧ ∀ q, q < xb i + k → (copiedSlice mS n)[q]? ≠ some D))
                  ∧ P.toPoly.sel c' (copiedSlice mS n) xb ∧ P.toPoly.label c' (copiedSlice mS n) xb = D) →
                P.toPoly.ord c c' (copiedSlice mS n) ī xb))
         ↔ Mdfa.accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)) := by
  obtain ⟨Mdfa, hM⟩ := MSOMarkN.markedDFAN_exists (P.toPoly.arity c)
    (MSO.Formula.and (P.toPoly.selDef c).choose
      (MSO.Formula.and (P.toPoly.labelDef c U).choose
        (MSO.Formula.and
          (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
            ((boundedTuplesF B (P.toPoly.arity c') q_U q_D).toList).map
              (fun rs => CopiedTieGate.cellClauseF P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
                (fun r hr => (hS₁ c' rs r hr).1) rs))))
          (MSO.Formula.and
            (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
              ((boundedTuplesF Bh (P.toPoly.arity c') q_U q_D).toList).map
                (fun rs => CopiedTieGate.cellClauseF P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
                  (fun r hr => (hS₂ c' rs r hr).1) rs))))
            (MSO.Formula.and
              (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                ((Ssuf c').toList).map (fun r => sufOrdClauseAtBandTot P c c' Q r hQ kSuf))))
              (MSO.Formula.and
                (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                  ((Spre c').toList).map (fun r => prefOrdClauseAtBandTot P c c' Q r hQ kPre))))
                (MSO.Formula.and
                  (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                    ((Dsuf c').toList).map (fun k => deepSufOrdClauseAt P c c' k))))
                  (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                    ((Dpre c').toList).map (fun k => deepPreOrdClauseAt P c c' k)))))))))))
  refine ⟨Mdfa, fun mS n ī hqU hqD hBhn hval => ?_⟩
  have hm : 1 ≤ mS := by omega
  have hBn : B ≤ n := le_trans hBB hBhn
  have hn : 1 ≤ n := le_trans hBh1 hBhn
  rw [hM (copiedSlice mS n) ī hval, MSO.Formula.sat_and, MSO.Formula.sat_and,
    MSO.Formula.sat_and, MSO.Formula.sat_and, MSO.Formula.sat_and, MSO.Formula.sat_and,
    MSO.Formula.sat_and]
  constructor
  · rintro ⟨hsel, hlab, hord, hrsuf, hrpre, hdsuf, hdpre⟩
    refine ⟨((P.toPoly.selDef c).choose_spec (copiedSlice mS n) ī).mp hsel,
      ((P.toPoly.labelDef c U).choose_spec (copiedSlice mS n) ī).mp hlab, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨rs, hrsmem, rfl⟩ := hψ
      have hrsv : ∀ i, (rs i).valid mS :=
        boundedTuplesF_valid q_U q_D mS hqU hqD rs (Finset.mem_toList.mp hrsmem)
      rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
        (fun r hr => (hS₁ c' rs r hr).1) rs mS n ī hm hn hBn hM2
        (fun r hr => (hS₁ c' rs r hr).2) (hF₁ c' rs) (hK₁ c' rs) hrsv hval]
      intro t xb hz hxv hcell hsel' hlab' hcfg
      exact hord ⟨c', xb⟩ ⟨hxv, hsel'⟩ hlab' (Or.inl ⟨rs, t, hrsv, hz, hcell, hcfg⟩)
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨rs, hrsmem, rfl⟩ := hψ
      have hrsv : ∀ i, (rs i).valid mS :=
        boundedTuplesF_valid q_U q_D mS hqU hqD rs (Finset.mem_toList.mp hrsmem)
      rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
        (fun r hr => (hS₂ c' rs r hr).1) rs mS n ī hm hn hBhn hM2
        (fun r hr => (hS₂ c' rs r hr).2) (hF₂ c' rs) (hK₂ c' rs) hrsv hval]
      intro t xb hz hxv hcell hsel' hlab' hcfg
      exact hord ⟨c', xb⟩ ⟨hxv, hsel'⟩ hlab' (Or.inr ⟨rs, t, hrsv, hz, hcell, hcfg⟩)
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨r, hrmem, rfl⟩ := hψ
      have hrin : r ∈ Ssuf c' := Finset.mem_toList.mp hrmem
      rw [sufOrdClauseAtBandTot_sat P c c' Q r hQ kSuf (copiedSlice mS n) ī hval,
        Nat.mod_eq_of_lt (hSsuf c' r hrin)]
      exact hrsuf c' r hrin
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨r, hrmem, rfl⟩ := hψ
      have hrin : r ∈ Spre c' := Finset.mem_toList.mp hrmem
      rw [prefOrdClauseAtBandTot_sat P c c' Q r hQ kPre (copiedSlice mS n) ī hval,
        Nat.mod_eq_of_lt (hSpre c' r hrin)]
      exact hrpre c' r hrin
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨k, hkmem, rfl⟩ := hψ
      rw [deepSufOrdClauseAt_sat P c c' k (copiedSlice mS n) ī hval]
      exact hdsuf c' k (Finset.mem_toList.mp hkmem)
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨k, hkmem, rfl⟩ := hψ
      rw [deepPreOrdClauseAt_sat P c c' k (copiedSlice mS n) ī hval]
      exact hdpre c' k (Finset.mem_toList.mp hkmem)
  · rintro ⟨hsel, hlab, hord₁, hord₂, hrsuf', hrpre', hdsuf', hdpre'⟩
    refine ⟨((P.toPoly.selDef c).choose_spec (copiedSlice mS n) ī).mpr hsel,
      ((P.toPoly.labelDef c U).choose_spec (copiedSlice mS n) ī).mpr hlab, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨c', xb⟩ hbsel hbD (⟨rs, t, hrsv, hz, hbcell, hbcfg⟩ | ⟨rs, t, hrsv, hz, hbcell, hbcfg⟩)
      · have hrsbound : rs ∈ boundedTuplesF B (P.toPoly.arity c') q_U q_D := by
          by_contra hns
          rcases hbcfg.2 with ⟨_, _, r, hr, _⟩ | ⟨f, hf, _⟩ | ⟨k, hk, _⟩
          · rw [hS₁b c' rs hns] at hr; exact absurd hr (Finset.notMem_empty r)
          · rw [hF₁b c' rs hns] at hf; exact absurd hf (Finset.notMem_empty f)
          · rw [hK₁b c' rs hns] at hk; exact absurd hk (Finset.notMem_empty k)
        rw [MSOMarkN.sat_andList] at hord₁
        have hclause := hord₁ (CopiedTieGate.cellClauseF P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
            (fun r hr => (hS₁ c' rs r hr).1) rs)
          (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
            List.mem_map_of_mem (Finset.mem_toList.mpr hrsbound)⟩)
        rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
          (fun r hr => (hS₁ c' rs r hr).1) rs mS n ī hm hn hBn hM2
          (fun r hr => (hS₁ c' rs r hr).2) (hF₁ c' rs) (hK₁ c' rs) hrsv hval] at hclause
        exact hclause t xb hz hbsel.1 hbcell hbsel.2 hbD hbcfg
      · have hrsbound : rs ∈ boundedTuplesF Bh (P.toPoly.arity c') q_U q_D := by
          by_contra hns
          rcases hbcfg.2 with ⟨_, _, r, hr, _⟩ | ⟨f, hf, _⟩ | ⟨k, hk, _⟩
          · rw [hS₂b c' rs hns] at hr; exact absurd hr (Finset.notMem_empty r)
          · rw [hF₂b c' rs hns] at hf; exact absurd hf (Finset.notMem_empty f)
          · rw [hK₂b c' rs hns] at hk; exact absurd hk (Finset.notMem_empty k)
        rw [MSOMarkN.sat_andList] at hord₂
        have hclause := hord₂ (CopiedTieGate.cellClauseF P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
            (fun r hr => (hS₂ c' rs r hr).1) rs)
          (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
            List.mem_map_of_mem (Finset.mem_toList.mpr hrsbound)⟩)
        rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
          (fun r hr => (hS₂ c' rs r hr).1) rs mS n ī hm hn hBhn hM2
          (fun r hr => (hS₂ c' rs r hr).2) (hF₂ c' rs) (hK₂ c' rs) hrsv hval] at hclause
        exact hclause t xb hz hbsel.1 hbcell hbsel.2 hbD hbcfg
    · intro c' r hr
      rw [MSOMarkN.sat_andList] at hrsuf'
      have hclause := hrsuf' (sufOrdClauseAtBandTot P c c' Q r hQ kSuf)
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hr)⟩)
      rw [sufOrdClauseAtBandTot_sat P c c' Q r hQ kSuf (copiedSlice mS n) ī hval,
        Nat.mod_eq_of_lt (hSsuf c' r hr)] at hclause
      exact hclause
    · intro c' r hr
      rw [MSOMarkN.sat_andList] at hrpre'
      have hclause := hrpre' (prefOrdClauseAtBandTot P c c' Q r hQ kPre)
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hr)⟩)
      rw [prefOrdClauseAtBandTot_sat P c c' Q r hQ kPre (copiedSlice mS n) ī hval,
        Nat.mod_eq_of_lt (hSpre c' r hr)] at hclause
      exact hclause
    · intro c' k hk
      rw [MSOMarkN.sat_andList] at hdsuf'
      have hclause := hdsuf' (deepSufOrdClauseAt P c c' k)
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hk)⟩)
      rw [deepSufOrdClauseAt_sat P c c' k (copiedSlice mS n) ī hval] at hclause
      exact hclause
    · intro c' k hk
      rw [MSOMarkN.sat_andList] at hdpre'
      have hclause := hdpre' (deepPreOrdClauseAt P c c' k)
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hk)⟩)
      rw [deepPreOrdClauseAt_sat P c c' k (copiedSlice mS n) ī hval] at hclause
      exact hclause

/-- Update-shaped variant with deep-boundary clauses also phrased as
distinguished-coordinate updates of the fixed base tuple.  This is the
formula-level target for the arbitrary-arity update bridge. -/
theorem fasU_atomOrd_full_gate_bounded_band_updateDeep (B Bh M mthr q_U q_D kSuf kPre : ℕ)
    (S₁ F₁ K₁ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpecF B) → Finset ℕ)
    (S₂ F₂ K₂ : (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpecF Bh) → Finset ℕ)
    (Ssuf Spre Dsuf Dpre : (c' : Fin P.toPoly.K) → Finset ℕ)
    (j0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c'))
    (ī0F : (c' : Fin P.toPoly.K) → Fin (P.toPoly.arity c') → ℕ)
    (Q : ℕ) (hQ : 0 < Q)
    (hSsuf : ∀ c' r, r ∈ Ssuf c' → r < Q) (hSpre : ∀ c' r, r ∈ Spre c' → r < Q)
    (hBB : B ≤ Bh) (hBh1 : 1 ≤ Bh) (hM2 : M % 2 = 0)
    (hS₁ : ∀ c' rs, ∀ r ∈ S₁ c' rs, r < M ∧ r % 2 = 1)
    (hS₂ : ∀ c' rs, ∀ r ∈ S₂ c' rs, r < M ∧ r % 2 = 1)
    (hF₁ : ∀ c' rs, ∀ f ∈ F₁ c' rs, f % 2 = 1)
    (hF₂ : ∀ c' rs, ∀ f ∈ F₂ c' rs, f % 2 = 1)
    (hK₁ : ∀ c' rs, ∀ k ∈ K₁ c' rs, k % 2 = 0)
    (hK₂ : ∀ c' rs, ∀ k ∈ K₂ c' rs, k % 2 = 0)
    (hS₁b : ∀ c' rs, rs ∉ boundedTuplesF B (P.toPoly.arity c') q_U q_D → S₁ c' rs = ∅)
    (hF₁b : ∀ c' rs, rs ∉ boundedTuplesF B (P.toPoly.arity c') q_U q_D → F₁ c' rs = ∅)
    (hK₁b : ∀ c' rs, rs ∉ boundedTuplesF B (P.toPoly.arity c') q_U q_D → K₁ c' rs = ∅)
    (hS₂b : ∀ c' rs, rs ∉ boundedTuplesF Bh (P.toPoly.arity c') q_U q_D → S₂ c' rs = ∅)
    (hF₂b : ∀ c' rs, rs ∉ boundedTuplesF Bh (P.toPoly.arity c') q_U q_D → F₂ c' rs = ∅)
    (hK₂b : ∀ c' rs, rs ∉ boundedTuplesF Bh (P.toPoly.arity c') q_U q_D → K₂ c' rs = ∅) :
    ∃ Mdfa : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)),
      ∀ (mS n : ℕ) (ī : Fin (P.toPoly.arity c) → ℕ), q_U < mS → q_D < mS → Bh ≤ n →
        (∀ i, ī i < (copiedSlice mS n).length) →
        (∀ c' i, ī0F c' i < (copiedSlice mS n).length) →
        ((P.toPoly.sel c (copiedSlice mS n) ī
          ∧ P.toPoly.label c (copiedSlice mS n) ī = U
          ∧ (∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
              P.toPoly.labelOf (copiedSlice mS n) b = D →
              CopiedTieGate.cfgCellGAFL B Bh M mthr S₁ F₁ K₁ S₂ F₂ K₂ mS n b →
              P.toPoly.atomOrd (copiedSlice mS n) ⟨c, ī⟩ b)
          ∧ (∀ (c' : Fin P.toPoly.K) (r : ℕ), r ∈ Ssuf c' →
              ∀ p, p < (copiedSlice mS n).length →
                (updateSufBandGuard (copiedSlice mS n) Q r kSuf p
                  ∧ P.toPoly.sel c' (copiedSlice mS n)
                      (Function.update (ī0F c') (j0F c') p)
                  ∧ P.toPoly.label c' (copiedSlice mS n)
                      (Function.update (ī0F c') (j0F c') p) = D) →
                P.toPoly.ord c c' (copiedSlice mS n) ī
                  (Function.update (ī0F c') (j0F c') p))
            ∧ (∀ (c' : Fin P.toPoly.K) (r : ℕ), r ∈ Spre c' →
                ∀ p, p < (copiedSlice mS n).length →
                  (preBandStrictGuard (copiedSlice mS n) Q r kPre p
                    ∧ P.toPoly.sel c' (copiedSlice mS n)
                        (Function.update (ī0F c') (j0F c') p)
                    ∧ P.toPoly.label c' (copiedSlice mS n)
                        (Function.update (ī0F c') (j0F c') p) = D) →
                  P.toPoly.ord c c' (copiedSlice mS n) ī
                    (Function.update (ī0F c') (j0F c') p))
          ∧ (∀ (c' : Fin P.toPoly.K) (k : ℕ), k ∈ Dsuf c' →
              ∀ p, p < (copiedSlice mS n).length →
                ((((copiedSlice mS n)[p]? = some D
                    ∧ ∀ q, q < (copiedSlice mS n).length → p < q →
                        (copiedSlice mS n)[q]? = some D)
                  ∧ p + 1 + k = (copiedSlice mS n).length)
                  ∧ P.toPoly.sel c' (copiedSlice mS n)
                      (Function.update (ī0F c') (j0F c') p)
                  ∧ P.toPoly.label c' (copiedSlice mS n)
                      (Function.update (ī0F c') (j0F c') p) = D) →
                P.toPoly.ord c c' (copiedSlice mS n) ī
                  (Function.update (ī0F c') (j0F c') p))
          ∧ (∀ (c' : Fin P.toPoly.K) (k : ℕ), k ∈ Dpre c' →
              ∀ p, p < (copiedSlice mS n).length →
                ((((copiedSlice mS n)[p]? = some U
                    ∧ ∀ q, q < (copiedSlice mS n).length → q < p →
                        (copiedSlice mS n)[q]? = some U)
                  ∧ ((copiedSlice mS n)[p + k]? = some D
                    ∧ ∀ q, q < p + k → (copiedSlice mS n)[q]? ≠ some D))
                  ∧ P.toPoly.sel c' (copiedSlice mS n)
                      (Function.update (ī0F c') (j0F c') p)
                  ∧ P.toPoly.label c' (copiedSlice mS n)
                      (Function.update (ī0F c') (j0F c') p) = D) →
                P.toPoly.ord c c' (copiedSlice mS n) ī
                  (Function.update (ī0F c') (j0F c') p)))
         ↔ Mdfa.accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī)) := by
  obtain ⟨Mdfa, hM⟩ := MSOMarkN.markedDFAN_exists (P.toPoly.arity c)
    (MSO.Formula.and (P.toPoly.selDef c).choose
      (MSO.Formula.and (P.toPoly.labelDef c U).choose
        (MSO.Formula.and
          (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
            ((boundedTuplesF B (P.toPoly.arity c') q_U q_D).toList).map
              (fun rs => CopiedTieGate.cellClauseF P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
                (fun r hr => (hS₁ c' rs r hr).1) rs))))
          (MSO.Formula.and
            (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
              ((boundedTuplesF Bh (P.toPoly.arity c') q_U q_D).toList).map
                (fun rs => CopiedTieGate.cellClauseF P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
                  (fun r hr => (hS₂ c' rs r hr).1) rs))))
            (MSO.Formula.and
              (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                ((Ssuf c').toList).map (fun r =>
                  updateSufOrdClauseAtBandTot P c c' Q r hQ kSuf (j0F c') (ī0F c')))))
              (MSO.Formula.and
                (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                  ((Spre c').toList).map (fun r =>
                    updatePreOrdClauseAtBandTot P c c' Q r hQ kPre (j0F c') (ī0F c')))))
                (MSO.Formula.and
                  (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                    ((Dsuf c').toList).map (fun k =>
                      updateDeepSufOrdClauseAt P c c' k (j0F c') (ī0F c')))))
                  (MSOMarkN.andList ((List.finRange P.toPoly.K).flatMap (fun c' =>
                    ((Dpre c').toList).map (fun k =>
                      updateDeepPreOrdClauseAt P c c' k (j0F c') (ī0F c'))))))))))))
  refine ⟨Mdfa, fun mS n ī hqU hqD hBhn hval hbase => ?_⟩
  have hm : 1 ≤ mS := by omega
  have hBn : B ≤ n := le_trans hBB hBhn
  have hn : 1 ≤ n := le_trans hBh1 hBhn
  rw [hM (copiedSlice mS n) ī hval, MSO.Formula.sat_and, MSO.Formula.sat_and,
    MSO.Formula.sat_and, MSO.Formula.sat_and, MSO.Formula.sat_and, MSO.Formula.sat_and,
    MSO.Formula.sat_and]
  constructor
  · rintro ⟨hsel, hlab, hord, hrsuf, hrpre, hdsuf, hdpre⟩
    refine ⟨((P.toPoly.selDef c).choose_spec (copiedSlice mS n) ī).mp hsel,
      ((P.toPoly.labelDef c U).choose_spec (copiedSlice mS n) ī).mp hlab, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨rs, hrsmem, rfl⟩ := hψ
      have hrsv : ∀ i, (rs i).valid mS :=
        boundedTuplesF_valid q_U q_D mS hqU hqD rs (Finset.mem_toList.mp hrsmem)
      rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
        (fun r hr => (hS₁ c' rs r hr).1) rs mS n ī hm hn hBn hM2
        (fun r hr => (hS₁ c' rs r hr).2) (hF₁ c' rs) (hK₁ c' rs) hrsv hval]
      intro t xb hz hxv hcell hsel' hlab' hcfg
      exact hord ⟨c', xb⟩ ⟨hxv, hsel'⟩ hlab' (Or.inl ⟨rs, t, hrsv, hz, hcell, hcfg⟩)
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨rs, hrsmem, rfl⟩ := hψ
      have hrsv : ∀ i, (rs i).valid mS :=
        boundedTuplesF_valid q_U q_D mS hqU hqD rs (Finset.mem_toList.mp hrsmem)
      rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
        (fun r hr => (hS₂ c' rs r hr).1) rs mS n ī hm hn hBhn hM2
        (fun r hr => (hS₂ c' rs r hr).2) (hF₂ c' rs) (hK₂ c' rs) hrsv hval]
      intro t xb hz hxv hcell hsel' hlab' hcfg
      exact hord ⟨c', xb⟩ ⟨hxv, hsel'⟩ hlab' (Or.inr ⟨rs, t, hrsv, hz, hcell, hcfg⟩)
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨r, hrmem, rfl⟩ := hψ
      have hrin : r ∈ Ssuf c' := Finset.mem_toList.mp hrmem
      rw [updateSufOrdClauseAtBandTot_sat P c c' Q r hQ kSuf (j0F c') (ī0F c')
          (copiedSlice mS n) ī hval (fun i => hbase c' i),
        Nat.mod_eq_of_lt (hSsuf c' r hrin)]
      exact hrsuf c' r hrin
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨r, hrmem, rfl⟩ := hψ
      have hrin : r ∈ Spre c' := Finset.mem_toList.mp hrmem
      rw [updatePreOrdClauseAtBandTot_sat P c c' Q r hQ kPre (j0F c') (ī0F c')
          (copiedSlice mS n) ī hval (fun i => hbase c' i),
        Nat.mod_eq_of_lt (hSpre c' r hrin)]
      exact hrpre c' r hrin
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨k, hkmem, rfl⟩ := hψ
      rw [updateDeepSufOrdClauseAt_sat P c c' k (j0F c') (ī0F c')
          (copiedSlice mS n) ī hval (fun i => hbase c' i)]
      exact hdsuf c' k (Finset.mem_toList.mp hkmem)
    · rw [MSOMarkN.sat_andList]
      intro ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨c', _, hψ⟩ := hψ
      rw [List.mem_map] at hψ
      obtain ⟨k, hkmem, rfl⟩ := hψ
      rw [updateDeepPreOrdClauseAt_sat P c c' k (j0F c') (ī0F c')
          (copiedSlice mS n) ī hval (fun i => hbase c' i)]
      exact hdpre c' k (Finset.mem_toList.mp hkmem)
  · rintro ⟨hsel, hlab, hord₁, hord₂, hrsuf', hrpre', hdsuf', hdpre'⟩
    refine ⟨((P.toPoly.selDef c).choose_spec (copiedSlice mS n) ī).mpr hsel,
      ((P.toPoly.labelDef c U).choose_spec (copiedSlice mS n) ī).mpr hlab, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨c', xb⟩ hbsel hbD (⟨rs, t, hrsv, hz, hbcell, hbcfg⟩ | ⟨rs, t, hrsv, hz, hbcell, hbcfg⟩)
      · have hrsbound : rs ∈ boundedTuplesF B (P.toPoly.arity c') q_U q_D := by
          by_contra hns
          rcases hbcfg.2 with ⟨_, _, r, hr, _⟩ | ⟨f, hf, _⟩ | ⟨k, hk, _⟩
          · rw [hS₁b c' rs hns] at hr; exact absurd hr (Finset.notMem_empty r)
          · rw [hF₁b c' rs hns] at hf; exact absurd hf (Finset.notMem_empty f)
          · rw [hK₁b c' rs hns] at hk; exact absurd hk (Finset.notMem_empty k)
        rw [MSOMarkN.sat_andList] at hord₁
        have hclause := hord₁ (CopiedTieGate.cellClauseF P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
            (fun r hr => (hS₁ c' rs r hr).1) rs)
          (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
            List.mem_map_of_mem (Finset.mem_toList.mpr hrsbound)⟩)
        rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₁ c' rs) (F₁ c' rs) (K₁ c' rs)
          (fun r hr => (hS₁ c' rs r hr).1) rs mS n ī hm hn hBn hM2
          (fun r hr => (hS₁ c' rs r hr).2) (hF₁ c' rs) (hK₁ c' rs) hrsv hval] at hclause
        exact hclause t xb hz hbsel.1 hbcell hbsel.2 hbD hbcfg
      · have hrsbound : rs ∈ boundedTuplesF Bh (P.toPoly.arity c') q_U q_D := by
          by_contra hns
          rcases hbcfg.2 with ⟨_, _, r, hr, _⟩ | ⟨f, hf, _⟩ | ⟨k, hk, _⟩
          · rw [hS₂b c' rs hns] at hr; exact absurd hr (Finset.notMem_empty r)
          · rw [hF₂b c' rs hns] at hf; exact absurd hf (Finset.notMem_empty f)
          · rw [hK₂b c' rs hns] at hk; exact absurd hk (Finset.notMem_empty k)
        rw [MSOMarkN.sat_andList] at hord₂
        have hclause := hord₂ (CopiedTieGate.cellClauseF P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
            (fun r hr => (hS₂ c' rs r hr).1) rs)
          (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
            List.mem_map_of_mem (Finset.mem_toList.mpr hrsbound)⟩)
        rw [CopiedTieGate.cellClauseF_sat P c c' M mthr (S₂ c' rs) (F₂ c' rs) (K₂ c' rs)
          (fun r hr => (hS₂ c' rs r hr).1) rs mS n ī hm hn hBhn hM2
          (fun r hr => (hS₂ c' rs r hr).2) (hF₂ c' rs) (hK₂ c' rs) hrsv hval] at hclause
        exact hclause t xb hz hbsel.1 hbcell hbsel.2 hbD hbcfg
    · intro c' r hr
      rw [MSOMarkN.sat_andList] at hrsuf'
      have hclause := hrsuf' (updateSufOrdClauseAtBandTot P c c' Q r hQ kSuf
          (j0F c') (ī0F c'))
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hr)⟩)
      rw [updateSufOrdClauseAtBandTot_sat P c c' Q r hQ kSuf (j0F c') (ī0F c')
          (copiedSlice mS n) ī hval (fun i => hbase c' i),
        Nat.mod_eq_of_lt (hSsuf c' r hr)] at hclause
      exact hclause
    · intro c' r hr
      rw [MSOMarkN.sat_andList] at hrpre'
      have hclause := hrpre' (updatePreOrdClauseAtBandTot P c c' Q r hQ kPre
          (j0F c') (ī0F c'))
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hr)⟩)
      rw [updatePreOrdClauseAtBandTot_sat P c c' Q r hQ kPre (j0F c') (ī0F c')
          (copiedSlice mS n) ī hval (fun i => hbase c' i),
        Nat.mod_eq_of_lt (hSpre c' r hr)] at hclause
      exact hclause
    · intro c' k hk
      rw [MSOMarkN.sat_andList] at hdsuf'
      have hclause := hdsuf' (updateDeepSufOrdClauseAt P c c' k (j0F c') (ī0F c'))
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hk)⟩)
      rw [updateDeepSufOrdClauseAt_sat P c c' k (j0F c') (ī0F c')
          (copiedSlice mS n) ī hval (fun i => hbase c' i)] at hclause
      exact hclause
    · intro c' k hk
      rw [MSOMarkN.sat_andList] at hdpre'
      have hclause := hdpre' (updateDeepPreOrdClauseAt P c c' k (j0F c') (ī0F c'))
        (List.mem_flatMap.mpr ⟨c', List.mem_finRange c',
          List.mem_map_of_mem (Finset.mem_toList.mpr hk)⟩)
      rw [updateDeepPreOrdClauseAt_sat P c c' k (j0F c') (ī0F c')
          (copiedSlice mS n) ī hval (fun i => hbase c' i)] at hclause
      exact hclause

end CopiedBoundedGateBand
