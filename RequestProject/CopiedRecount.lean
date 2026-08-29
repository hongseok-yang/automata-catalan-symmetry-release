/-
# The fibred canonical recount (§9 tower, Stage F3.8) — index layer

Parallel stage (depends only on F3.2): the fibred twins of the canonical
cell index `frozenCells`/`bulkCells`/`cellIndex` and the recount that
converts a selected-tuple sum into a frozen sum plus a bulk per-base sum.

This file delivers the INDEX layer: the per-`mS` explicit `Finset`s
`frozenCellsF`/`bulkCellsF`/`cellIndexF` (built from `regionTuplesF` — a
`piFinset` over the index `Fin k`, never a `RegionSpecF` `Fintype` instance,
audit C7) and `cellIndexF_valid`.  The canonical classification and recount
(the long `posAt_inj` case bash) follow.
-/
import RequestProject.CopiedRegionF
import RequestProject.SliceCellClassifyGA

namespace CopiedRecount

open WRP SliceFamilyCell CopiedCells CopiedRank CopiedRegionF CopiedDstar SliceFasCountGA
open scoped Classical

/-- The fibred frozen cells: cluster-free descriptor tuples (every coordinate
pinned), as an explicit per-`mS` `Finset`. -/
noncomputable def frozenCellsF (Z k mS : ℕ) : Finset (Fin k → RegionSpecF Z) :=
  (regionTuplesF Z k mS).filter (fun rs => ∀ i, clusterFreeF (rs i) = true)

theorem mem_frozenCellsF {Z k mS : ℕ} (rs : Fin k → RegionSpecF Z) :
    rs ∈ frozenCellsF Z k mS ↔
      ((∀ i, (rs i).valid mS) ∧ ∀ i, clusterFreeF (rs i) = true) := by
  rw [frozenCellsF, Finset.mem_filter, mem_regionTuplesF]

/-- The fibred bulk cells: cluster-bearing tuples with offset-`0` canonicity
(some coordinate rides the window at offset `0`). -/
noncomputable def bulkCellsF (Z : ℕ) (hZ : 1 ≤ Z) (k mS : ℕ) :
    Finset (Fin k → RegionSpecF Z) :=
  (regionTuplesF Z k mS).filter
    (fun rs => ∃ i e, rs i = .core (.cluster ⟨0, hZ⟩ e))

theorem mem_bulkCellsF {Z : ℕ} (hZ : 1 ≤ Z) {k mS : ℕ}
    (rs : Fin k → RegionSpecF Z) :
    rs ∈ bulkCellsF Z hZ k mS ↔
      ((∀ i, (rs i).valid mS) ∧ ∃ i e, rs i = .core (.cluster ⟨0, hZ⟩ e)) := by
  rw [bulkCellsF, Finset.mem_filter, mem_regionTuplesF]

/-- The fibred canonical cell index: frozen cells at the dummy base `Z + 1`,
bulk cells over their exact base windows `Z ≤ t`, `t + clusterWidthF + Z ≤ n`. -/
noncomputable def cellIndexF (Z : ℕ) (hZ : 1 ≤ Z) (k mS n : ℕ) :
    Finset ((Fin k → RegionSpecF Z) × ℕ) :=
  (frozenCellsF Z k mS ×ˢ {Z + 1}) ∪
  ((bulkCellsF Z hZ k mS ×ˢ Finset.Icc Z n).filter
    (fun rt => rt.2 + clusterWidthF rt.1 + Z ≤ n))

theorem mem_cellIndexF {Z : ℕ} (hZ : 1 ≤ Z) {k mS n : ℕ}
    (rt : (Fin k → RegionSpecF Z) × ℕ) :
    rt ∈ cellIndexF Z hZ k mS n ↔
      ((rt.1 ∈ frozenCellsF Z k mS ∧ rt.2 = Z + 1) ∨
       (rt.1 ∈ bulkCellsF Z hZ k mS ∧ rt.2 ∈ Finset.Icc Z n
         ∧ rt.2 + clusterWidthF rt.1 + Z ≤ n)) := by
  rw [cellIndexF, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
    Finset.mem_product, Finset.mem_singleton]
  tauto

/-- **Index validity**: every cell-tuple coordinate of a canonical index entry
is in-slice (past `n ≥ 2Z + 2`). -/
theorem cellIndexF_valid {Z k mS n : ℕ} {hZ : 1 ≤ Z} (hm : 1 ≤ mS)
    (hn : 2 * Z + 2 ≤ n) (rt : (Fin k → RegionSpecF Z) × ℕ)
    (hrt : rt ∈ cellIndexF Z hZ k mS n) :
    ∀ i, cellTupleF rt.1 mS rt.2 n i < (copiedSlice mS n).length := by
  rw [mem_cellIndexF hZ] at hrt
  rcases hrt with ⟨hfr, hb⟩ | ⟨hbk, hbase, hwin⟩
  · -- frozen: base Z + 1, window (Z+1) + Z ≤ n
    have hv := ((mem_frozenCellsF rt.1).mp hfr).1
    rw [hb]
    exact cellTupleF_valid rt.1 mS (Z + 1) n hm hv (by omega)
  · -- bulk: base t with t + clusterWidthF + Z ≤ n, so t + Z ≤ n
    have hv := ((mem_bulkCellsF hZ rt.1).mp hbk).1
    exact cellTupleF_valid rt.1 mS rt.2 n hm hv (by omega)

/-! ## Canonical classification: existence -/

/-- **Canonical existence, fibred**: past the threshold, every selected tuple
on an in-domain copied slice is the fibred cell tuple of SOME canonical index
entry.  The re-pinning re-files each `core`-cluster coordinate into its
canonical base (offset-`0` canonicity) or a back-pin; `core` non-clusters and
the stretch descriptors `prefIdx`/`sufIdx` pass through unchanged. -/
theorem canonical_exists_fibred (P : WRP.Presentation Step Step) :
    ∃ Z : ℕ, ∃ hZ : 1 ≤ Z, ∀ C mS : ℕ, 1 ≤ mS →
      (∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)),
        l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
        l.length ≤ C * (mS + n + 1)) →
      ∃ Ncan, ∀ n, Ncan ≤ n → P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
        P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ →
        ∃ rt ∈ cellIndexF Z hZ (P.toPoly.arity c) mS n,
          ī = cellTupleF rt.1 mS rt.2 n := by
  classical
  obtain ⟨Z, hZ, hcovC⟩ := CopiedCells.cells_cover_fibred P
  refine ⟨Z, hZ, fun C mS hm hbud => ?_⟩
  obtain ⟨Ncc, hcells⟩ := hcovC C mS hm
  refine ⟨Ncc + 2 * Z + 2, fun n hn hdom c ī hsel => ?_⟩
  obtain ⟨t₀, ht₀Z, ht₀n, hper⟩ := hcells n (by omega) c ī hsel
    (fun l hnd hl => hbud n hdom c l hnd hl)
  choose rs₀ hv₀ hrs₀ using hper
  -- the middle blocks of the cover's `core`-cluster coordinates
  set mids : Finset ℕ := (Finset.univ : Finset (Fin (P.toPoly.arity c))).biUnion
    (fun i => match rs₀ i with
      | .core (RegionSpec.cluster δ _) =>
          if Z ≤ t₀ + δ.1 ∧ t₀ + δ.1 + Z + 1 ≤ n then {t₀ + δ.1} else ∅
      | _ => ∅) with hmidsdef
  have hmids_mem : ∀ x ∈ mids, t₀ ≤ x ∧ x + Z + 1 ≤ n := by
    intro x hx
    rw [hmidsdef, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hx⟩ := hx
    rcases hri : rs₀ i with r | q | l
    · rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
        rw [hri] at hx <;> simp only [] at hx
      · exact absurd hx (Finset.notMem_empty x)
      · exact absurd hx (Finset.notMem_empty x)
      · exact absurd hx (Finset.notMem_empty x)
      · exact absurd hx (Finset.notMem_empty x)
      · split at hx
        · rw [Finset.mem_singleton] at hx
          subst hx
          exact ⟨by omega, by omega⟩
        · exact absurd hx (Finset.notMem_empty x)
    · rw [hri] at hx; exact absurd hx (Finset.notMem_empty x)
    · rw [hri] at hx; exact absurd hx (Finset.notMem_empty x)
  have hmids_spread : ∀ x ∈ mids, x < t₀ + Z := by
    intro x hx
    rw [hmidsdef, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hx⟩ := hx
    rcases hri : rs₀ i with r | q | l
    · rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
        rw [hri] at hx <;> simp only [] at hx
      · exact absurd hx (Finset.notMem_empty x)
      · exact absurd hx (Finset.notMem_empty x)
      · exact absurd hx (Finset.notMem_empty x)
      · exact absurd hx (Finset.notMem_empty x)
      · split at hx
        · rw [Finset.mem_singleton] at hx
          have := δ.isLt
          omega
        · exact absurd hx (Finset.notMem_empty x)
    · rw [hri] at hx; exact absurd hx (Finset.notMem_empty x)
    · rw [hri] at hx; exact absurd hx (Finset.notMem_empty x)
  by_cases hne : mids.Nonempty
  · -- the bulk arm
    set t := mids.min' hne with htdef
    have htmem := mids.min'_mem hne
    have htle : ∀ x ∈ mids, t ≤ x := fun x hx => mids.min'_le x hx
    obtain ⟨ht₀t, htZn⟩ := hmids_mem t htmem
    have htsp := hmids_spread t htmem
    set rs' : Fin (P.toPoly.arity c) → RegionSpecF Z := fun i =>
      match rs₀ i with
      | .core (RegionSpec.cluster δ e) =>
          if Z ≤ t₀ + δ.1 ∧ t₀ + δ.1 + Z + 1 ≤ n
          then .core (RegionSpec.cluster ⟨(t₀ + δ.1 - t) % Z, Nat.mod_lt _ hZ⟩ e)
          else .core (RegionSpec.back ⟨(n - 1 - (t₀ + δ.1)) % Z, Nat.mod_lt _ hZ⟩ e)
      | r => r with hrs'def
    have hmid_iff : ∀ (i : Fin (P.toPoly.arity c)) (δ : Fin Z) (e : Bool),
        rs₀ i = .core (.cluster δ e) →
        ((Z ≤ t₀ + δ.1 ∧ t₀ + δ.1 + Z + 1 ≤ n) ↔ t₀ + δ.1 ∈ mids) := by
      intro i δ e hri
      constructor
      · intro hcond
        rw [hmidsdef, Finset.mem_biUnion]
        refine ⟨i, Finset.mem_univ i, ?_⟩
        rw [hri]
        simp only []
        rw [if_pos hcond]
        exact Finset.mem_singleton_self _
      · intro hmem
        exact (hmids_mem _ hmem).imp (fun h => by omega) (fun h => h)
    have htup : ī = cellTupleF rs' mS t n := by
      funext i
      show ī i = (rs' i).posAt mS t n
      rw [hrs'def]
      simp only []
      rcases hri : rs₀ i with r | q | l
      · rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
        · rw [hrs₀ i, hri]; rfl
        · rw [hrs₀ i, hri]; rfl
        · rw [hrs₀ i, hri]; rfl
        · rw [hrs₀ i, hri]; rfl
        · simp only []
          by_cases hcond : Z ≤ t₀ + δ.1 ∧ t₀ + δ.1 + Z + 1 ≤ n
          · rw [if_pos hcond]
            have hmem : t₀ + δ.1 ∈ mids := (hmid_iff i δ e hri).mp hcond
            have hge : t ≤ t₀ + δ.1 := htle _ hmem
            have hlt : t₀ + δ.1 - t < Z := by
              have := hmids_spread _ hmem; omega
            show ī i = mS - 1 + (1 + 2 * (t + (t₀ + δ.1 - t) % Z) + _)
            rw [Nat.mod_eq_of_lt hlt, hrs₀ i, hri]
            show mS - 1 + (1 + 2 * (t₀ + δ.1) + _) = _
            congr 2
            omega
          · rw [if_neg hcond]
            have hback : n - Z ≤ t₀ + δ.1 := by omega
            have hub : t₀ + δ.1 ≤ n - 1 := by have := δ.isLt; omega
            have hlt : n - 1 - (t₀ + δ.1) < Z := by omega
            show ī i = mS - 1 + (1 + 2 * (n - 1 - (n - 1 - (t₀ + δ.1)) % Z) + _)
            rw [Nat.mod_eq_of_lt hlt, hrs₀ i, hri]
            show mS - 1 + (1 + 2 * (t₀ + δ.1) + _) = _
            congr 2
            omega
      · rw [hrs₀ i, hri]; rfl
      · rw [hrs₀ i, hri]; rfl
    -- offset-0 canonicity at the minimizing coordinate, and the window
    refine ⟨(rs', t), ?_, htup⟩
    rw [mem_cellIndexF hZ]
    right
    have hmids_wit : ∀ x ∈ mids, ∃ (i : Fin (P.toPoly.arity c)) (δ : Fin Z)
        (e : Bool), rs₀ i = .core (.cluster δ e) ∧ x = t₀ + δ.1
          ∧ (Z ≤ t₀ + δ.1 ∧ t₀ + δ.1 + Z + 1 ≤ n) := by
      intro x hx
      rw [hmidsdef, Finset.mem_biUnion] at hx
      obtain ⟨i, _, hx⟩ := hx
      rcases hri : rs₀ i with r | q | l
      · rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
          rw [hri] at hx <;> simp only [] at hx
        · exact absurd hx (Finset.notMem_empty x)
        · exact absurd hx (Finset.notMem_empty x)
        · exact absurd hx (Finset.notMem_empty x)
        · exact absurd hx (Finset.notMem_empty x)
        · split at hx
          · rw [Finset.mem_singleton] at hx
            exact ⟨i, δ, e, hri, hx, by assumption⟩
          · exact absurd hx (Finset.notMem_empty x)
      · rw [hri] at hx; exact absurd hx (Finset.notMem_empty x)
      · rw [hri] at hx; exact absurd hx (Finset.notMem_empty x)
    have hmin_wit : ∃ (i : Fin (P.toPoly.arity c)) (e : Bool),
        rs' i = .core (.cluster ⟨0, hZ⟩ e) := by
      obtain ⟨i, δ, e, hri, hxt, hcond⟩ := hmids_wit t htmem
      refine ⟨i, e, ?_⟩
      rw [hrs'def]
      simp only []
      rw [hri]
      simp only []
      rw [if_pos hcond]
      congr 2
      refine Fin.ext ?_
      show (t₀ + δ.1 - t) % Z = 0
      rw [show t₀ + δ.1 - t = 0 from by omega]
      exact Nat.zero_mod Z
    have hvalid' : ∀ i, (rs' i).valid mS := by
      intro i
      rw [hrs'def]
      simp only []
      rcases hri : rs₀ i with r | q | l
      · rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · simp only []; split <;> exact trivial
      · show q < mS - 1; have := hv₀ i; rw [hri] at this; exact this
      · show l < mS - 1; have := hv₀ i; rw [hri] at this; exact this
    have hwidth : t + clusterWidthF rs' + Z ≤ n := by
      have hsup : clusterWidthF rs' ≤ n - Z - t := by
        refine Finset.sup_le (fun i _ => ?_)
        show widthAtF (rs' i) ≤ n - Z - t
        rw [hrs'def]
        simp only []
        rcases hri : rs₀ i with r | q | l
        · rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;> simp only []
          · exact Nat.zero_le _
          · exact Nat.zero_le _
          · exact Nat.zero_le _
          · exact Nat.zero_le _
          · by_cases hcond : Z ≤ t₀ + δ.1 ∧ t₀ + δ.1 + Z + 1 ≤ n
            · rw [if_pos hcond]
              show (t₀ + δ.1 - t) % Z + 1 ≤ n - Z - t
              have hmem : t₀ + δ.1 ∈ mids := (hmid_iff i δ e hri).mp hcond
              have hge : t ≤ t₀ + δ.1 := htle _ hmem
              have hlt : t₀ + δ.1 - t < Z := by
                have := hmids_spread _ hmem; omega
              rw [Nat.mod_eq_of_lt hlt]
              omega
            · rw [if_neg hcond]
              exact Nat.zero_le _
        · exact Nat.zero_le _
        · exact Nat.zero_le _
      omega
    refine ⟨?_, ?_, hwidth⟩
    · rw [mem_bulkCellsF hZ]
      exact ⟨hvalid', hmin_wit.imp (fun i ⟨e, he⟩ => ⟨e, he⟩)⟩
    · rw [Finset.mem_Icc]; omega
  · -- the frozen arm
    set rs' : Fin (P.toPoly.arity c) → RegionSpecF Z := fun i =>
      match rs₀ i with
      | .core (RegionSpec.cluster δ e) =>
          .core (RegionSpec.back ⟨(n - 1 - (t₀ + δ.1)) % Z, Nat.mod_lt _ hZ⟩ e)
      | r => r with hrs'def
    have hnomid : ∀ (i : Fin (P.toPoly.arity c)) (δ : Fin Z) (e : Bool),
        rs₀ i = .core (.cluster δ e) →
        ¬(Z ≤ t₀ + δ.1 ∧ t₀ + δ.1 + Z + 1 ≤ n) := by
      intro i δ e hri hcond
      refine hne ⟨t₀ + δ.1, ?_⟩
      rw [hmidsdef, Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [hri]
      simp only []
      rw [if_pos hcond]
      exact Finset.mem_singleton_self _
    have htup : ī = cellTupleF rs' mS (Z + 1) n := by
      funext i
      show ī i = (rs' i).posAt mS (Z + 1) n
      rw [hrs'def]
      simp only []
      rcases hri : rs₀ i with r | q | l
      · rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
        · rw [hrs₀ i, hri]; rfl
        · rw [hrs₀ i, hri]; rfl
        · rw [hrs₀ i, hri]; rfl
        · rw [hrs₀ i, hri]; rfl
        · have hcond := hnomid i δ e hri
          have hback : n - Z ≤ t₀ + δ.1 := by omega
          have hub : t₀ + δ.1 ≤ n - 1 := by have := δ.isLt; omega
          have hlt : n - 1 - (t₀ + δ.1) < Z := by omega
          show ī i = mS - 1 + (1 + 2 * (n - 1 - (n - 1 - (t₀ + δ.1)) % Z) + _)
          rw [Nat.mod_eq_of_lt hlt, hrs₀ i, hri]
          show mS - 1 + (1 + 2 * (t₀ + δ.1) + _) = _
          congr 2
          omega
      · rw [hrs₀ i, hri]; rfl
      · rw [hrs₀ i, hri]; rfl
    refine ⟨(rs', Z + 1), ?_, htup⟩
    rw [mem_cellIndexF hZ]
    left
    refine ⟨?_, rfl⟩
    rw [mem_frozenCellsF]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · -- validity
      rw [hrs'def]
      simp only []
      rcases hri : rs₀ i with r | q | l
      · rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
      · show q < mS - 1; have := hv₀ i; rw [hri] at this; exact this
      · show l < mS - 1; have := hv₀ i; rw [hri] at this; exact this
    · -- cluster-freedom
      rw [hrs'def]
      simp only []
      rcases hri : rs₀ i with r | q | l
      · rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;> rfl
      · rfl
      · rfl

/-! ## Canonical classification: uniqueness -/

/-- A copied-slice position is MIDDLE when its block sits clear of both
boundary zones. -/
def MidPosF (Z mS n q : ℕ) : Prop :=
  ∃ j, (q = mS + 2 * j ∨ q = mS + 2 * j + 1) ∧ Z ≤ j ∧ j + Z + 1 ≤ n

/-- An upper bound on a `core` position with the cluster window. -/
theorem corePos_le {Z : ℕ} (rr : RegionSpec Z) (t n : ℕ) (hZn : Z ≤ n)
    (hw : ∀ δ e, rr = .cluster δ e → t + δ.1 + Z + 1 ≤ n) :
    rr.posAt t n ≤ 1 + 2 * n := by
  rcases rr with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;> simp only [RegionSpec.posAt]
  · omega
  · omega
  · have := f.isLt; rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · have := l.isLt; rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · have := hw δ e rfl; rcases e <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Cluster-free (and valid) fibred descriptors never describe a copied middle
position. -/
theorem not_midPosF_clusterFree {Z : ℕ} (r : RegionSpecF Z)
    (hcf : clusterFreeF r = true) (mS t n : ℕ) (hm : 1 ≤ mS)
    (hv : r.valid mS) :
    ¬ MidPosF Z mS n (r.posAt mS t n) := by
  rintro ⟨j, hq, hjZ, hjn⟩
  rcases r with rr | q | l
  · -- core: shifted wrapped argument
    rcases rr with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
      simp only [RegionSpecF.posAt, RegionSpec.posAt] at hq
    · rcases hq with h | h <;> omega
    · rcases hq with h | h <;> omega
    · have := f.isLt
      rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] at hq <;>
        rcases hq with h | h <;> omega
    · have := l.isLt
      rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] at hq <;>
        rcases hq with h | h <;> omega
    · exact (clusterFreeF_core _).mp hcf
  · -- prefIdx: position q < mS - 1 < mS + 2j
    have hq' : q < mS - 1 := hv
    rcases hq with h | h <;>
      (rw [show (RegionSpecF.prefIdx q).posAt mS t n = q from rfl] at h; omega)
  · -- sufIdx: position mS + 2n + 1 + l, above every middle block
    have hl' : l < mS - 1 := hv
    rcases hq with h | h <;>
      (rw [show (RegionSpecF.sufIdx l).posAt mS t n = mS + 2 * n + 1 + l
        from rfl] at h; omega)

/-- **Fibred position injectivity at a shared base**: two valid descriptors
whose cluster blocks sit in the middle zone and whose positions agree are
equal.  Same-zone via the wrapped `posAt_inj_bulk` (core) or stretch-index
equality; cross-zone is a disjoint-position contradiction. -/
theorem posAt_inj_bulk_fibred {Z : ℕ} (mS n t : ℕ) (hm : 1 ≤ mS) (hZt : Z ≤ t)
    (htn : t + Z + 1 ≤ n) (hn : 2 * Z + 2 ≤ n) (r r' : RegionSpecF Z)
    (hv : r.valid mS) (hv' : r'.valid mS)
    (hr : ∀ δ : Fin Z, ∀ e, r = .core (.cluster δ e) → t + δ.1 + Z + 1 ≤ n)
    (hr' : ∀ δ : Fin Z, ∀ e, r' = .core (.cluster δ e) → t + δ.1 + Z + 1 ≤ n)
    (h : r.posAt mS t n = r'.posAt mS t n) : r = r' := by
  have hZn : Z ≤ n := by omega
  rcases r with rr | q | l <;> rcases r' with rr' | q' | l'
  · -- core / core: cancel the shift and delegate to the wrapped lemma
    have hcore : rr.posAt t n = rr'.posAt t n := by
      have := h
      simp only [RegionSpecF.posAt] at this
      omega
    have hwrap := SliceFasCountGA.posAt_inj_bulk n t hZt htn hn rr rr'
      (fun δ e hc => hr δ e (by rw [hc])) (fun δ e hc => hr' δ e (by rw [hc]))
      hcore
    rw [hwrap]
  · -- core / prefIdx: zones disjoint
    exfalso
    have hq' : q' < mS - 1 := hv'
    simp only [RegionSpecF.posAt] at h
    omega
  · -- core / sufIdx
    exfalso
    have hle := corePos_le rr t n hZn (fun δ e hc => hr δ e (by rw [hc]))
    simp only [RegionSpecF.posAt] at h
    omega
  · -- prefIdx / core
    exfalso
    have hq : q < mS - 1 := hv
    simp only [RegionSpecF.posAt] at h
    omega
  · -- prefIdx / prefIdx
    simp only [RegionSpecF.posAt] at h
    rw [h]
  · -- prefIdx / sufIdx
    exfalso
    have hq : q < mS - 1 := hv
    simp only [RegionSpecF.posAt] at h
    omega
  · -- sufIdx / core
    exfalso
    have hle := corePos_le rr' t n hZn (fun δ e hc => hr' δ e (by rw [hc]))
    simp only [RegionSpecF.posAt] at h
    omega
  · -- sufIdx / prefIdx
    exfalso
    have hq' : q' < mS - 1 := hv'
    simp only [RegionSpecF.posAt] at h
    omega
  · -- sufIdx / sufIdx
    simp only [RegionSpecF.posAt] at h
    rw [show l = l' from by omega]

/-- The offset-`0` coordinate of a bulk cell sits at a middle position. -/
theorem bulk_midF {Z k : ℕ} (hZ : 1 ≤ Z) (rsb : Fin k → RegionSpecF Z)
    (mS tb n : ℕ) (hm : 1 ≤ mS)
    (hwit : ∃ i e, rsb i = .core (.cluster ⟨0, hZ⟩ e))
    (htb : Z ≤ tb) (hw : tb + clusterWidthF rsb + Z ≤ n) :
    ∃ i, MidPosF Z mS n (cellTupleF rsb mS tb n i) := by
  obtain ⟨i, e, hi⟩ := hwit
  have hW : 1 ≤ clusterWidthF rsb := by
    have := cluster_lt_widthF rsb i ⟨0, hZ⟩ e hi
    omega
  refine ⟨i, tb, ?_, htb, by omega⟩
  show (rsb i).posAt mS tb n = _ ∨ (rsb i).posAt mS tb n = _
  rw [hi]
  simp only [RegionSpecF.posAt, RegionSpec.posAt]
  rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- **Canonical uniqueness, fibred**: a selected tuple is the fibred cell
tuple of EXACTLY ONE canonical index entry. -/
theorem canonical_unique_fibred {Z k : ℕ} (hZ : 1 ≤ Z) (mS n : ℕ)
    (hm : 1 ≤ mS) (hn : 2 * Z + 2 ≤ n)
    (rt rt' : (Fin k → RegionSpecF Z) × ℕ)
    (hrt : rt ∈ cellIndexF Z hZ k mS n) (hrt' : rt' ∈ cellIndexF Z hZ k mS n)
    (h : cellTupleF rt.1 mS rt.2 n = cellTupleF rt'.1 mS rt'.2 n) : rt = rt' := by
  obtain ⟨rs, t⟩ := rt
  obtain ⟨rs', t'⟩ := rt'
  rw [mem_cellIndexF hZ] at hrt hrt'
  simp only [] at hrt hrt'
  rcases hrt with ⟨hfr, ht⟩ | ⟨hbk, hbase, hw⟩ <;>
    rcases hrt' with ⟨hfr', ht'⟩ | ⟨hbk', hbase', hw'⟩
  · -- frozen / frozen
    rw [ht, ht'] at h ⊢
    refine Prod.ext ?_ rfl
    funext i
    have hi := congrFun h i
    obtain ⟨hv, hcf⟩ := (mem_frozenCellsF rs).mp hfr
    obtain ⟨hv', hcf'⟩ := (mem_frozenCellsF rs').mp hfr'
    refine posAt_inj_bulk_fibred mS n (Z + 1) hm (by omega) (by omega) hn
      (rs i) (rs' i) (hv i) (hv' i) (fun δ e hc => ?_) (fun δ e hc => ?_) hi
    · have := hcf i; rw [hc] at this; simp [clusterFreeF] at this
    · have := hcf' i; rw [hc] at this; simp [clusterFreeF] at this
  · -- frozen / bulk
    exfalso
    rw [Finset.mem_Icc] at hbase'
    obtain ⟨i, hmid⟩ := bulk_midF hZ rs' mS t' n hm
      ((mem_bulkCellsF hZ rs').mp hbk').2 hbase'.1 hw'
    rw [← congrFun h i] at hmid
    obtain ⟨hv, hcf⟩ := (mem_frozenCellsF rs).mp hfr
    exact not_midPosF_clusterFree (rs i) (hcf i) mS t n hm (hv i) hmid
  · -- bulk / frozen
    exfalso
    rw [Finset.mem_Icc] at hbase
    obtain ⟨i, hmid⟩ := bulk_midF hZ rs mS t n hm
      ((mem_bulkCellsF hZ rs).mp hbk).2 hbase.1 hw
    rw [congrFun h i] at hmid
    obtain ⟨hv', hcf'⟩ := (mem_frozenCellsF rs').mp hfr'
    exact not_midPosF_clusterFree (rs' i) (hcf' i) mS t' n hm (hv' i) hmid
  · -- bulk / bulk: the offset-0 coordinates pin the bases, then posAt_inj
    obtain ⟨hv, hwit⟩ := (mem_bulkCellsF hZ rs).mp hbk
    obtain ⟨hv', hwit'⟩ := (mem_bulkCellsF hZ rs').mp hbk'
    rw [Finset.mem_Icc] at hbase hbase'
    have htt' : t = t' := by
      obtain ⟨i, e, hi⟩ := hwit
      obtain ⟨i', e', hi'⟩ := hwit'
      have hpi := congrFun h i
      have hpi' := congrFun h i'
      -- t' ≤ t : read rs's offset-0 coordinate through rs'
      have h1 : (RegionSpecF.core (.cluster ⟨0, hZ⟩ e)).posAt mS t n
          = (rs' i).posAt mS t' n := by
        rw [← hi]; exact hpi
      simp only [RegionSpecF.posAt, RegionSpec.posAt] at h1
      have hge : t' ≤ t := by
        rcases hci : rs' i with rr | q | l
        · rcases rr with _ | _ | ⟨f, e₂⟩ | ⟨l, e₂⟩ | ⟨δ, e₂⟩ <;>
            rw [hci] at h1
          · rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] at h1 <;> omega
          · rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] at h1 <;> omega
          · have := f.isLt
            rcases e <;> rcases e₂ <;>
              simp only [Bool.toNat_false, Bool.toNat_true] at h1 <;> omega
          · have := l.isLt
            rcases e <;> rcases e₂ <;>
              simp only [Bool.toNat_false, Bool.toNat_true] at h1 <;> omega
          · have hwd := cluster_lt_widthF rs' i δ e₂ hci
            rcases e <;> rcases e₂ <;>
              simp only [Bool.toNat_false, Bool.toNat_true] at h1 <;> omega
        · have hq : q < mS - 1 := by have := hv' i; rw [hci] at this; exact this
          rw [hci] at h1
          rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] at h1 <;> omega
        · have hl : l < mS - 1 := by have := hv' i; rw [hci] at this; exact this
          rw [hci] at h1
          rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] at h1 <;> omega
      have h2 : (rs i').posAt mS t n
          = (RegionSpecF.core (.cluster ⟨0, hZ⟩ e')).posAt mS t' n := by
        rw [← hi']; exact hpi'
      simp only [RegionSpecF.posAt, RegionSpec.posAt] at h2
      have hle : t ≤ t' := by
        rcases hci : rs i' with rr | q | l
        · rcases rr with _ | _ | ⟨f, e₂⟩ | ⟨l, e₂⟩ | ⟨δ, e₂⟩ <;>
            rw [hci] at h2
          · rcases e' <;> simp only [Bool.toNat_false, Bool.toNat_true] at h2 <;> omega
          · rcases e' <;> simp only [Bool.toNat_false, Bool.toNat_true] at h2 <;> omega
          · have := f.isLt
            rcases e' <;> rcases e₂ <;>
              simp only [Bool.toNat_false, Bool.toNat_true] at h2 <;> omega
          · have := l.isLt
            rcases e' <;> rcases e₂ <;>
              simp only [Bool.toNat_false, Bool.toNat_true] at h2 <;> omega
          · have hwd := cluster_lt_widthF rs i' δ e₂ hci
            rcases e' <;> rcases e₂ <;>
              simp only [Bool.toNat_false, Bool.toNat_true] at h2 <;> omega
        · have hq : q < mS - 1 := by have := hv i'; rw [hci] at this; exact this
          rw [hci] at h2
          rcases e' <;> simp only [Bool.toNat_false, Bool.toNat_true] at h2 <;> omega
        · have hl : l < mS - 1 := by have := hv i'; rw [hci] at this; exact this
          rw [hci] at h2
          rcases e' <;> simp only [Bool.toNat_false, Bool.toNat_true] at h2 <;> omega
      omega
    subst htt'
    have hWpos : 1 ≤ clusterWidthF rs := by
      obtain ⟨j, ej, hj⟩ := hwit
      have := cluster_lt_widthF rs j ⟨0, hZ⟩ ej hj; omega
    refine Prod.ext ?_ rfl
    funext i
    have hi := congrFun h i
    exact posAt_inj_bulk_fibred mS n t hm (by omega) (by omega) hn
      (rs i) (rs' i) (hv i) (hv' i)
      (fun δ e hc => by have := cluster_lt_widthF rs i δ e hc; omega)
      (fun δ e hc => by have := cluster_lt_widthF rs' i δ e hc; omega)
      hi

/-- **The fibred canonical classification** (Stage F3.8 interface): past the
threshold, every selected tuple on an in-domain copied slice is the fibred
cell tuple of EXACTLY ONE canonical index entry. -/
theorem canonical_classification_fibred (P : WRP.Presentation Step Step) :
    ∃ Z : ℕ, ∃ hZ : 1 ≤ Z, ∀ C mS : ℕ, 1 ≤ mS →
      (∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)),
        l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
        l.length ≤ C * (mS + n + 1)) →
      ∃ Ncan, ∀ n, Ncan ≤ n → P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
        P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ →
        ∃! rt : (Fin (P.toPoly.arity c) → RegionSpecF Z) × ℕ,
          rt ∈ cellIndexF Z hZ (P.toPoly.arity c) mS n
            ∧ ī = cellTupleF rt.1 mS rt.2 n := by
  obtain ⟨Z, hZ, hex⟩ := canonical_exists_fibred P
  refine ⟨Z, hZ, fun C mS hm hbud => ?_⟩
  obtain ⟨Ncan, hexn⟩ := hex C mS hm hbud
  refine ⟨Ncan + 2 * Z + 2, fun n hn hdom c ī hsel => ?_⟩
  obtain ⟨rt, hmem, htup⟩ := hexn n (by omega) hdom c ī hsel
  refine ⟨rt, ⟨hmem, htup⟩, ?_⟩
  rintro rt' ⟨hmem', htup'⟩
  exact canonical_unique_fibred hZ mS n hm (by omega) rt' rt hmem' hmem
    (by rw [← htup', ← htup])

/-! ## The canonical recount -/

/-- **The fibred canonical recount** (the Stage F3.8 deliverable): the tuple
sum of any selectedness-implying predicate's indicator equals the
frozen-cell sum plus the per-bulk-cell base counts. -/
theorem canonical_recount_fibred (P : WRP.Presentation Step Step) :
    ∃ Z : ℕ, ∃ hZ : 1 ≤ Z, ∀ C mS : ℕ, 1 ≤ mS →
      (∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)),
        l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
        l.length ≤ C * (mS + n + 1)) →
      ∃ Ncan, ∀ n, Ncan ≤ n → P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K)
          (Q : (Fin (P.toPoly.arity c) → ℕ) → Prop),
        (∀ ī, Q ī → P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩) →
        (∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
            Finset.range (copiedSlice mS n).length), if Q ī then 1 else 0)
          = (∑ rs' ∈ frozenCellsF Z (P.toPoly.arity c) mS,
              if Q (cellTupleF rs' mS (Z + 1) n) then 1 else 0)
            + ∑ rs ∈ bulkCellsF Z hZ (P.toPoly.arity c) mS,
                ((Finset.Icc Z (n - Z - clusterWidthF rs)).filter
                  (fun t => Q (cellTupleF rs mS t n))).card := by
  classical
  obtain ⟨Z, hZ, hclass⟩ := canonical_classification_fibred P
  refine ⟨Z, hZ, fun C mS hm hbud => ?_⟩
  obtain ⟨Ncan, hclassn⟩ := hclass C mS hm hbud
  refine ⟨Ncan + 2 * Z + 2, fun n hn hdom c Q hQ => ?_⟩
  rw [← Finset.card_filter]
  -- the central bijection onto the filtered cell index
  have hbij : ((Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
        Finset.range (copiedSlice mS n).length)).filter Q).card
      = ((cellIndexF Z hZ (P.toPoly.arity c) mS n).filter
          (fun rt => Q (cellTupleF rt.1 mS rt.2 n))).card := by
    refine Finset.card_bij'
      (i := fun ī hī => Classical.choose
        (hclassn n (by omega) hdom c ī
          (hQ ī (Finset.mem_filter.mp hī).2)).exists)
      (j := fun rt hrt => cellTupleF rt.1 mS rt.2 n) ?_ ?_ ?_ ?_
    · intro ī hī
      have hspec := Classical.choose_spec
        (hclassn n (by omega) hdom c ī (hQ ī (Finset.mem_filter.mp hī).2)).exists
      rw [Finset.mem_filter]
      refine ⟨hspec.1, ?_⟩
      rw [← hspec.2]
      exact (Finset.mem_filter.mp hī).2
    · intro rt hrt
      rw [Finset.mem_filter] at hrt
      rw [Finset.mem_filter]
      refine ⟨?_, hrt.2⟩
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range]
      exact cellIndexF_valid hm (by omega) rt hrt.1 i
    · intro ī hī
      have hspec := Classical.choose_spec
        (hclassn n (by omega) hdom c ī (hQ ī (Finset.mem_filter.mp hī).2)).exists
      exact hspec.2.symm
    · intro rt hrt
      rw [Finset.mem_filter] at hrt
      have hsel : P.toPoly.selectedAtom (copiedSlice mS n)
          ⟨c, cellTupleF rt.1 mS rt.2 n⟩ := hQ _ hrt.2
      have huniq := hclassn n (by omega) hdom c (cellTupleF rt.1 mS rt.2 n) hsel
      exact huniq.unique (Classical.choose_spec huniq.exists) ⟨hrt.1, rfl⟩
  rw [hbij]
  -- split the index into its two arms
  rw [cellIndexF, Finset.filter_union,
    Finset.card_union_of_disjoint (by
      refine Finset.disjoint_filter_filter ?_
      rw [Finset.disjoint_left]
      intro rt h1 h2
      rw [Finset.mem_product, mem_frozenCellsF] at h1
      rw [Finset.mem_filter, Finset.mem_product, mem_bulkCellsF] at h2
      obtain ⟨i, e, hi⟩ := h2.1.1.2
      have hcf := h1.1.2 i
      rw [hi] at hcf
      simp [clusterFreeF] at hcf)]
  congr 1
  · -- the frozen arm
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun rs' hrs' => ?_)
    rw [Finset.sum_singleton]
  · -- the bulk arm
    rw [Finset.filter_filter, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun rs hrs => ?_)
    rw [Finset.card_filter]
    have hsplit : ∀ t : ℕ,
        (if (t + clusterWidthF rs + Z ≤ n ∧ Q (cellTupleF rs mS t n))
          then 1 else 0)
          = (if t + clusterWidthF rs + Z ≤ n
              then (if Q (cellTupleF rs mS t n) then 1 else 0) else 0) := by
      intro t
      by_cases h1 : t + clusterWidthF rs + Z ≤ n
      · by_cases h2 : Q (cellTupleF rs mS t n)
        · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]
        · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg h2]
      · rw [if_neg (fun h => h1 h.1), if_neg h1]
    calc ∑ t ∈ Finset.Icc Z n,
          (if (t + clusterWidthF rs + Z ≤ n ∧ Q (cellTupleF rs mS t n))
            then 1 else 0)
        = ∑ t ∈ Finset.Icc Z n, (if t + clusterWidthF rs + Z ≤ n
            then (if Q (cellTupleF rs mS t n) then 1 else 0) else 0) :=
          Finset.sum_congr rfl (fun t _ => hsplit t)
      _ = ∑ t ∈ (Finset.Icc Z n).filter (fun t => t + clusterWidthF rs + Z ≤ n),
            (if Q (cellTupleF rs mS t n) then 1 else 0) := (Finset.sum_filter _ _).symm
      _ = ∑ t ∈ Finset.Icc Z (n - Z - clusterWidthF rs),
            (if Q (cellTupleF rs mS t n) then 1 else 0) := by
          refine Finset.sum_congr ?_ (fun t _ => rfl)
          refine Finset.ext (fun t => ?_)
          rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
          omega

end CopiedRecount
