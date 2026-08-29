/-
# TWO-rep tying folds (§9 mS-direction)

The banded run clause's activation set must be the TWO-rep tying set
`{r ∈ [0,pcF) : rank(sufIdx (Ts+r)) = d* ∧ rank(sufIdx (Ts+r+pcF)) = d*}` — a single-representative
set will not do.  A single representative achieving the global min `d*` does NOT
force the class to be slope-0: an increasing-slope class can have its shallowest band member hit `d*`
while deeper band members are selected non-achievers.  Two same-class reps both equal to `d*` force the
affine class to be constant (`affine_class_uniform`, two equal points ⟹ slope 0), so the whole class —
and hence every banded competitor — is a `d*`-achiever, which is exactly what the forward `TIE ⇒ accepts`
direction needs.

These sets still fold EP-in-`mS`: the conjunction of the two per-representative rank transports of
`CopiedTie2b` is EP at the product period, and the `range pcF` filter folds with it.
-/
import RequestProject.CopiedTie2b

namespace CopiedAchSetFold

open WRP Step CopiedTie2b CopiedCells CopiedDstar
open scoped Classical

/-! ## Guarded range-filter fold + the ACTUAL-form (`= dstarRankGA_m`) two-rep folds

The activation sets the bridge feeds the gate are in ACTUAL form (`rank = dstarRankGA_m`, what COVERAGE
and the selector speak), folded through the `CopiedTie2b` per-class transports in both directions —
both carry domain + D-present guards, so the fold is guarded. -/

/-- The domain ∧ D-present guard at the copied slice (as a function of the fold variable). -/
abbrev domDp (P : WRP.Presentation Step Step) (mS n : ℕ) : Prop :=
  P.toPoly.domain (copiedSlice mS n) ∧
    ∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧ P.toPoly.labelOf (copiedSlice mS n) a = D

/-- Fixed-period n-class transport for zero-base suffix/prefix update tuples.
The canonical coordinate data uses the non-moving tuple `fun _ => 0`; this
lemma packages the descriptor `cellTupleF` n-transport with one coordinate
updated to the suffix or prefix stretch. -/
theorem updateZero_achievesDstar_iff_on_n_class_of_budget
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (Cbud : ℕ)
    (hbudC : ∀ (mS : ℕ), 1 ≤ mS →
      ∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ Cbud * (mS + n + 1)) :
    ∃ (p0 : ℕ), 1 ≤ p0 ∧
      (∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) (mS q : ℕ),
        1 ≤ mS → q < mS - 1 →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
          domDp P mS n → domDp P mS n' →
          ((P.rank c (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c) => 0) j0
                (mS + 2 * n + 1 + q))
              = CopiedDstar.dstarRankGA_m P hV mS n) ↔
           (P.rank c (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c) => 0) j0
                (mS + 2 * n' + 1 + q))
              = CopiedDstar.dstarRankGA_m P hV mS n'))) ∧
      (∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) (mS q : ℕ),
        1 ≤ mS → q < mS - 1 →
        ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
          domDp P mS n → domDp P mS n' →
          ((P.rank c (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c) => 0) j0 q)
              = CopiedDstar.dstarRankGA_m P hV mS n) ↔
           (P.rank c (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c) => 0) j0 q)
              = CopiedDstar.dstarRankGA_m P hV mS n'))) := by
  classical
  obtain ⟨p0, hp0, hn⟩ :=
    CopiedTie2b.achievesDstar_iff_on_n_class_of_budget P hV Cbud hbudC (B := 1)
      (by omega)
  refine ⟨p0, hp0, ?_, ?_⟩
  · intro c j0 mS q hm hq
    let rs0 : Fin (P.toPoly.arity c) → RegionSpecF 1 := fun _ => RegionSpecF.prefIdx 0
    let rs : Fin (P.toPoly.arity c) → RegionSpecF 1 :=
      Function.update rs0 j0 (RegionSpecF.sufIdx q)
    have hvalid : ∀ i, (rs i).valid mS := by
      intro i
      by_cases hi : i = j0
      · subst hi
        simp [rs, rs0, RegionSpecF.valid, hq]
      · have hm2 : 2 ≤ mS := by omega
        simp [rs, rs0, Function.update_of_ne hi, RegionSpecF.valid]
        omega
    obtain ⟨N0, hN0⟩ := hn c rs mS hm hvalid 2 (by omega)
    refine ⟨max N0 4, fun n n' hn0 hn0' hmod hG hG' => ?_⟩
    have hstep := hN0 n n'
      (le_trans (le_max_left _ _) hn0)
      (le_trans (le_max_left _ _) hn0')
      (by omega) (by omega) hmod hG.1 hG.2 hG'.1 hG'.2
    have hcell :
        cellTupleF rs mS 2 n =
          Function.update (fun _ : Fin (P.toPoly.arity c) => 0) j0
            (mS + 2 * n + 1 + q) := by
      rw [show rs = Function.update rs0 j0 (RegionSpecF.sufIdx q) from rfl,
        CopiedDstarCMS.cellTupleF_update_sufIdx]
      have hbase : cellTupleF rs0 mS 2 n = fun _ : Fin (P.toPoly.arity c) => 0 := by
        funext i
        simp [rs0, cellTupleF, RegionSpecF.posAt]
      rw [hbase]
    have hcell' :
        cellTupleF rs mS 2 n' =
          Function.update (fun _ : Fin (P.toPoly.arity c) => 0) j0
            (mS + 2 * n' + 1 + q) := by
      rw [show rs = Function.update rs0 j0 (RegionSpecF.sufIdx q) from rfl,
        CopiedDstarCMS.cellTupleF_update_sufIdx]
      have hbase : cellTupleF rs0 mS 2 n' = fun _ : Fin (P.toPoly.arity c) => 0 := by
        funext i
        simp [rs0, cellTupleF, RegionSpecF.posAt]
      rw [hbase]
    rw [hcell, hcell'] at hstep
    exact hstep
  · intro c j0 mS q hm hq
    let rs0 : Fin (P.toPoly.arity c) → RegionSpecF 1 := fun _ => RegionSpecF.prefIdx 0
    let rs : Fin (P.toPoly.arity c) → RegionSpecF 1 :=
      Function.update rs0 j0 (RegionSpecF.prefIdx q)
    have hvalid : ∀ i, (rs i).valid mS := by
      intro i
      by_cases hi : i = j0
      · subst hi
        simp [rs, rs0, RegionSpecF.valid, hq]
      · have hm2 : 2 ≤ mS := by omega
        simp [rs, rs0, Function.update_of_ne hi, RegionSpecF.valid]
        omega
    obtain ⟨N0, hN0⟩ := hn c rs mS hm hvalid 2 (by omega)
    refine ⟨max N0 4, fun n n' hn0 hn0' hmod hG hG' => ?_⟩
    have hstep := hN0 n n'
      (le_trans (le_max_left _ _) hn0)
      (le_trans (le_max_left _ _) hn0')
      (by omega) (by omega) hmod hG.1 hG.2 hG'.1 hG'.2
    have hcell :
        cellTupleF rs mS 2 n =
          Function.update (fun _ : Fin (P.toPoly.arity c) => 0) j0 q := by
      rw [show rs = Function.update rs0 j0 (RegionSpecF.prefIdx q) from rfl,
        CopiedDstarCMS.cellTupleF_update_prefIdx]
      have hbase : cellTupleF rs0 mS 2 n = fun _ : Fin (P.toPoly.arity c) => 0 := by
        funext i
        simp [rs0, cellTupleF, RegionSpecF.posAt]
      rw [hbase]
    have hcell' :
        cellTupleF rs mS 2 n' =
          Function.update (fun _ : Fin (P.toPoly.arity c) => 0) j0 q := by
      rw [show rs = Function.update rs0 j0 (RegionSpecF.prefIdx q) from rfl,
        CopiedDstarCMS.cellTupleF_update_prefIdx]
      have hbase : cellTupleF rs0 mS 2 n' = fun _ : Fin (P.toPoly.arity c) => 0 := by
        funext i
        simp [rs0, cellTupleF, RegionSpecF.posAt]
      rw [hbase]
    rw [hcell, hcell'] at hstep
    exact hstep

/-- Fixed-period n-fold for zero-base update suffix tying sets.  This is the
direct consumer of the zero-base single-update transport above. -/
theorem tyingSuf2_update_zero_fold_n_actual_fixed_period
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (p0 : ℕ)
    (hn : ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) (mS q : ℕ),
      1 ≤ mS → q < mS - 1 →
      ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
        domDp P mS n → domDp P mS n' →
        ((P.rank c (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c) => 0) j0
              (mS + 2 * n + 1 + q))
            = CopiedDstar.dstarRankGA_m P hV mS n) ↔
         (P.rank c (copiedSlice mS n')
            (Function.update (fun _ : Fin (P.toPoly.arity c) => 0) j0
              (mS + 2 * n' + 1 + q))
            = CopiedDstar.dstarRankGA_m P hV mS n')))
    (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
    (Ts pcF mS : ℕ) (hm : 1 ≤ mS) (hmval : Ts + 2 * pcF ≤ mS - 1) :
    ∃ N, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
        domDp P mS n → domDp P mS n' →
        (Finset.range pcF).filter (fun r =>
            P.rank c' (copiedSlice mS n)
                (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                  (mS + 2 * n + 1 + (Ts + r)))
              = CopiedDstar.dstarRankGA_m P hV mS n
            ∧ P.rank c' (copiedSlice mS n)
                (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                  (mS + 2 * n + 1 + (Ts + r + pcF)))
              = CopiedDstar.dstarRankGA_m P hV mS n)
          = (Finset.range pcF).filter (fun r =>
            P.rank c' (copiedSlice mS n')
                (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                  (mS + 2 * n' + 1 + (Ts + r)))
              = CopiedDstar.dstarRankGA_m P hV mS n'
            ∧ P.rank c' (copiedSlice mS n')
                (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                  (mS + 2 * n' + 1 + (Ts + r + pcF)))
              = CopiedDstar.dstarRankGA_m P hV mS n') := by
  have key : ∀ r, ∃ N, r < pcF → ∀ n n', N ≤ n → N ≤ n' →
      n % p0 = n' % p0 → domDp P mS n → domDp P mS n' →
      ((P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                (mS + 2 * n + 1 + (Ts + r)))
            = CopiedDstar.dstarRankGA_m P hV mS n
          ∧ P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                (mS + 2 * n + 1 + (Ts + r + pcF)))
            = CopiedDstar.dstarRankGA_m P hV mS n) ↔
       (P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                (mS + 2 * n' + 1 + (Ts + r)))
            = CopiedDstar.dstarRankGA_m P hV mS n'
          ∧ P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0
                (mS + 2 * n' + 1 + (Ts + r + pcF)))
            = CopiedDstar.dstarRankGA_m P hV mS n')) := by
    intro r
    by_cases hr : r < pcF
    · have hq1 : Ts + r < mS - 1 := by omega
      have hq2 : Ts + r + pcF < mS - 1 := by omega
      obtain ⟨N1, hN1⟩ := hn c' j0 mS (Ts + r) hm hq1
      obtain ⟨N2, hN2⟩ := hn c' j0 mS (Ts + r + pcF) hm hq2
      refine ⟨max N1 N2, fun _ n n' hn1 hn2 hmod hG hG' => ?_⟩
      have e1 := hN1 n n' (le_trans (le_max_left _ _) hn1)
        (le_trans (le_max_left _ _) hn2) hmod hG hG'
      have e2 := hN2 n n' (le_trans (le_max_right _ _) hn1)
        (le_trans (le_max_right _ _) hn2) hmod hG hG'
      exact ⟨fun ⟨a, b⟩ => ⟨e1.mp a, e2.mp b⟩,
        fun ⟨a, b⟩ => ⟨e1.mpr a, e2.mpr b⟩⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose Nf hNf using key
  refine ⟨(Finset.range pcF).sup Nf, fun n n' hn1 hn2 hmod hG hG' => ?_⟩
  apply Finset.filter_congr
  intro r hr
  exact hNf r (Finset.mem_range.mp hr) n n'
    (le_trans (Finset.le_sup hr) hn1) (le_trans (Finset.le_sup hr) hn2) hmod hG hG'

/-- Fixed-period n-fold for zero-base update prefix tying sets. -/
theorem tyingPre2_update_zero_fold_n_actual_fixed_period
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (p0 : ℕ)
    (hn : ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) (mS q : ℕ),
      1 ≤ mS → q < mS - 1 →
      ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
        domDp P mS n → domDp P mS n' →
        ((P.rank c (copiedSlice mS n)
            (Function.update (fun _ : Fin (P.toPoly.arity c) => 0) j0 q)
            = CopiedDstar.dstarRankGA_m P hV mS n) ↔
         (P.rank c (copiedSlice mS n')
            (Function.update (fun _ : Fin (P.toPoly.arity c) => 0) j0 q)
            = CopiedDstar.dstarRankGA_m P hV mS n')))
    (c' : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c'))
    (Tp pcF mS : ℕ) (hm : 1 ≤ mS) (hmval : Tp + 2 * pcF ≤ mS - 1) :
    ∃ N, ∀ n n', N ≤ n → N ≤ n' → n % p0 = n' % p0 →
        domDp P mS n → domDp P mS n' →
        (Finset.range pcF).filter (fun r =>
            P.rank c' (copiedSlice mS n)
                (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0 (Tp + r))
              = CopiedDstar.dstarRankGA_m P hV mS n
            ∧ P.rank c' (copiedSlice mS n)
                (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0 (Tp + r + pcF))
              = CopiedDstar.dstarRankGA_m P hV mS n)
          = (Finset.range pcF).filter (fun r =>
            P.rank c' (copiedSlice mS n')
                (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0 (Tp + r))
              = CopiedDstar.dstarRankGA_m P hV mS n'
            ∧ P.rank c' (copiedSlice mS n')
                (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0 (Tp + r + pcF))
              = CopiedDstar.dstarRankGA_m P hV mS n') := by
  have key : ∀ r, ∃ N, r < pcF → ∀ n n', N ≤ n → N ≤ n' →
      n % p0 = n' % p0 → domDp P mS n → domDp P mS n' →
      ((P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0 (Tp + r))
            = CopiedDstar.dstarRankGA_m P hV mS n
          ∧ P.rank c' (copiedSlice mS n)
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0 (Tp + r + pcF))
            = CopiedDstar.dstarRankGA_m P hV mS n) ↔
       (P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0 (Tp + r))
            = CopiedDstar.dstarRankGA_m P hV mS n'
          ∧ P.rank c' (copiedSlice mS n')
              (Function.update (fun _ : Fin (P.toPoly.arity c') => 0) j0 (Tp + r + pcF))
            = CopiedDstar.dstarRankGA_m P hV mS n')) := by
    intro r
    by_cases hr : r < pcF
    · have hq1 : Tp + r < mS - 1 := by omega
      have hq2 : Tp + r + pcF < mS - 1 := by omega
      obtain ⟨N1, hN1⟩ := hn c' j0 mS (Tp + r) hm hq1
      obtain ⟨N2, hN2⟩ := hn c' j0 mS (Tp + r + pcF) hm hq2
      refine ⟨max N1 N2, fun _ n n' hn1 hn2 hmod hG hG' => ?_⟩
      have e1 := hN1 n n' (le_trans (le_max_left _ _) hn1)
        (le_trans (le_max_left _ _) hn2) hmod hG hG'
      have e2 := hN2 n n' (le_trans (le_max_right _ _) hn1)
        (le_trans (le_max_right _ _) hn2) hmod hG hG'
      exact ⟨fun ⟨a, b⟩ => ⟨e1.mp a, e2.mp b⟩,
        fun ⟨a, b⟩ => ⟨e1.mpr a, e2.mpr b⟩⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose Nf hNf using key
  refine ⟨(Finset.range pcF).sup Nf, fun n n' hn1 hn2 hmod hG hG' => ?_⟩
  apply Finset.filter_congr
  intro r hr
  exact hNf r (Finset.mem_range.mp hr) n n'
    (le_trans (Finset.le_sup hr) hn1) (le_trans (Finset.le_sup hr) hn2) hmod hG hG'

end CopiedAchSetFold
