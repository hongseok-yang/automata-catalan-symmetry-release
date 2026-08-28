/-
# GA-7.1/7.2 — the canonical cell classification and the recount
# (`SliceFasCountGA` namespace, part 2/3)

The conceptual core of the counting layer: the POSITION-DETERMINED canonical classification makes tuple ↦ (descriptor,
base) a function, so every selectedness-implying tuple count partitions EXACTLY
into finitely many frozen cells plus per-bulk-cell 1-parameter base counts.

* `frozenCells` / `bulkCells` (offset-0 canonicity) / `cellIndex`;
* `canonical_exists` (re-pinning the `cells_cover` descriptor by position),
  `posAt_inj_bulk` + `canonical_unique`, and the `∃!` `canonical_classification`;
* `canonical_recount` — the bijection-and-split serving all three counts.
-/
import RequestProject.SliceCellConvGA

namespace SliceFasCountGA

open WRP Step SliceFamilyCell SliceDstarGA SliceDstarGateGA SliceFasGatesGA
  SliceThreshold SliceAffine SliceOrder MSOMarkN SliceMarkN SliceFasSelectorGA
open scoped Classical

/-! ## GA-7.1: the canonical position-determined cell classification -/

/-- The frozen cells: cluster-free descriptor tuples (counted at the dummy base). -/
noncomputable def frozenCells (Z k : ℕ) : Finset (Fin k → RegionSpec Z) :=
  Finset.univ.filter (fun rs => ∀ i, clusterFree (rs i))

/-- The bulk cells: cluster-bearing tuples with OFFSET-0 CANONICITY — some
coordinate rides the window at offset `0`. -/
noncomputable def bulkCells (Z : ℕ) (hZ : 1 ≤ Z) (k : ℕ) :
    Finset (Fin k → RegionSpec Z) :=
  Finset.univ.filter (fun rs => ∃ i e, rs i = .cluster ⟨0, hZ⟩ e)

/-- The canonical cell index: frozen cells at the dummy base `Z + 1`, bulk cells over
their exact base windows `Z ≤ t`, `t + clusterWidth + Z ≤ n`. -/
noncomputable def cellIndex (Z : ℕ) (hZ : 1 ≤ Z) (k n : ℕ) :
    Finset ((Fin k → RegionSpec Z) × ℕ) :=
  (frozenCells Z k ×ˢ {Z + 1}) ∪
  ((bulkCells Z hZ k ×ˢ Finset.Icc Z n).filter
    (fun rt => rt.2 + clusterWidth rt.1 + Z ≤ n))

/-- **Canonical classification, existence**: past the threshold, every selected tuple
on an in-domain slice is the cell tuple of SOME canonical index entry. -/
theorem canonical_exists (P : WRP.Presentation Step Step) (C : ℕ)
    (hbud : ∀ n, P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) :
    ∃ Z Ncan : ℕ, ∃ hZ : 1 ≤ Z, ∀ n, Ncan ≤ n →
      P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
        P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩ →
        ∃ rt ∈ cellIndex Z hZ (P.toPoly.arity c) n, ī = cellTuple rt.1 rt.2 n := by
  classical
  obtain ⟨Z, Ncc, hZ, hcells⟩ := SliceFamilyCell.cells_cover P C
  refine ⟨Z, Ncc + 2 * Z + 2, hZ, fun n hn hdom c ī hsel => ?_⟩
  obtain ⟨t₀, ht₀Z, ht₀n, hper⟩ := hcells n (by omega) c ī hsel (hbud n hdom c)
  choose rs₀ hrs₀ using hper
  -- the middle blocks of the cover's cluster coordinates
  set mids : Finset ℕ := (Finset.univ : Finset (Fin (P.toPoly.arity c))).biUnion
    (fun i => match rs₀ i with
      | RegionSpec.cluster δ _ =>
          if Z ≤ t₀ + δ.1 ∧ t₀ + δ.1 + Z + 1 ≤ n then {t₀ + δ.1} else ∅
      | _ => ∅) with hmidsdef
  have hmids_mem : ∀ x ∈ mids, t₀ ≤ x ∧ x + Z + 1 ≤ n := by
    intro x hx
    rw [hmidsdef, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hx⟩ := hx
    rcases hri : rs₀ i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
      rw [hri] at hx <;> simp only [] at hx
    · exact absurd hx (Finset.notMem_empty x)
    · exact absurd hx (Finset.notMem_empty x)
    · exact absurd hx (Finset.notMem_empty x)
    · exact absurd hx (Finset.notMem_empty x)
    · split at hx
      · rw [Finset.mem_singleton] at hx
        subst hx
        constructor
        · omega
        · omega
      · exact absurd hx (Finset.notMem_empty x)
  have hmids_spread : ∀ x ∈ mids, x < t₀ + Z := by
    intro x hx
    rw [hmidsdef, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hx⟩ := hx
    rcases hri : rs₀ i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
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
  by_cases hne : mids.Nonempty
  · -- the bulk arm
    set t := mids.min' hne with htdef
    have htmem := mids.min'_mem hne
    have htle : ∀ x ∈ mids, t ≤ x := fun x hx => mids.min'_le x hx
    obtain ⟨ht₀t, htZn⟩ := hmids_mem t htmem
    have htsp := hmids_spread t htmem
    set rs' : Fin (P.toPoly.arity c) → RegionSpec Z := fun i =>
      match rs₀ i with
      | RegionSpec.cluster δ e =>
          if Z ≤ t₀ + δ.1 ∧ t₀ + δ.1 + Z + 1 ≤ n
          then RegionSpec.cluster ⟨(t₀ + δ.1 - t) % Z, Nat.mod_lt _ hZ⟩ e
          else RegionSpec.back ⟨(n - 1 - (t₀ + δ.1)) % Z, Nat.mod_lt _ hZ⟩ e
      | r => r with hrs'def
    -- every cover cluster's middle test is equivalent to membership in mids
    have hmid_iff : ∀ (i : Fin (P.toPoly.arity c)) (δ : Fin Z) (e : Bool),
        rs₀ i = .cluster δ e →
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
        exact hmids_mem _ hmem |>.imp (fun h => by omega) (fun h => h)
    -- the tuple is the cell at base t
    have htup : ī = cellTuple rs' t n := by
      funext i
      show ī i = (rs' i).posAt t n
      rw [hrs'def]
      simp only []
      rcases hri : rs₀ i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
      · rw [hrs₀ i, hri]
        rfl
      · rw [hrs₀ i, hri]
        rfl
      · rw [hrs₀ i, hri]
        rfl
      · rw [hrs₀ i, hri]
        rfl
      · simp only []
        by_cases hcond : Z ≤ t₀ + δ.1 ∧ t₀ + δ.1 + Z + 1 ≤ n
        · rw [if_pos hcond]
          have hmem : t₀ + δ.1 ∈ mids := (hmid_iff i δ e hri).mp hcond
          have hge : t ≤ t₀ + δ.1 := htle _ hmem
          have hlt : t₀ + δ.1 - t < Z := by
            have := hmids_spread _ hmem
            omega
          show ī i = 1 + 2 * (t + (t₀ + δ.1 - t) % Z) + _
          rw [Nat.mod_eq_of_lt hlt, hrs₀ i, hri]
          show 1 + 2 * (t₀ + δ.1) + _ = _
          congr 2
          omega
        · rw [if_neg hcond]
          have hback : n - Z ≤ t₀ + δ.1 := by omega
          have hub : t₀ + δ.1 ≤ n - 1 := by
            have := δ.isLt
            omega
          have hlt : n - 1 - (t₀ + δ.1) < Z := by omega
          show ī i = 1 + 2 * (n - 1 - (n - 1 - (t₀ + δ.1)) % Z) + _
          rw [Nat.mod_eq_of_lt hlt, hrs₀ i, hri]
          show 1 + 2 * (t₀ + δ.1) + _ = _
          congr 2
          omega
    -- membership: offset-0 canonicity at the minimizing coordinate, and the window
    refine ⟨(rs', t), ?_, htup⟩
    rw [cellIndex, Finset.mem_union]
    right
    rw [Finset.mem_filter, Finset.mem_product]
    have hmids_wit : ∀ x ∈ mids, ∃ (i : Fin (P.toPoly.arity c)) (δ : Fin Z)
        (e : Bool), rs₀ i = .cluster δ e ∧ x = t₀ + δ.1
          ∧ (Z ≤ t₀ + δ.1 ∧ t₀ + δ.1 + Z + 1 ≤ n) := by
      intro x hx
      rw [hmidsdef, Finset.mem_biUnion] at hx
      obtain ⟨i, _, hx⟩ := hx
      rcases hri : rs₀ i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
        rw [hri] at hx <;> simp only [] at hx
      · exact absurd hx (Finset.notMem_empty x)
      · exact absurd hx (Finset.notMem_empty x)
      · exact absurd hx (Finset.notMem_empty x)
      · exact absurd hx (Finset.notMem_empty x)
      · split at hx
        · rw [Finset.mem_singleton] at hx
          exact ⟨i, δ, e, hri, hx, by assumption⟩
        · exact absurd hx (Finset.notMem_empty x)
    have hmin_wit : ∃ (i : Fin (P.toPoly.arity c)) (e : Bool),
        rs' i = .cluster ⟨0, hZ⟩ e := by
      obtain ⟨i, δ, e, hri, hxt, hcond⟩ := hmids_wit t htmem
      refine ⟨i, e, ?_⟩
      rw [hrs'def]
      simp only []
      rw [hri]
      simp only []
      rw [if_pos hcond]
      congr 1
      refine Fin.ext ?_
      show (t₀ + δ.1 - t) % Z = 0
      rw [show t₀ + δ.1 - t = 0 from by omega]
      exact Nat.zero_mod Z
    have hwidth : t + clusterWidth rs' + Z ≤ n := by
      have hsup : clusterWidth rs' ≤ n - Z - t := by
        refine Finset.sup_le (fun i _ => ?_)
        rw [hrs'def]
        simp only []
        rcases hri : rs₀ i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;> simp only []
        · omega
        · omega
        · omega
        · omega
        · by_cases hcond : Z ≤ t₀ + δ.1 ∧ t₀ + δ.1 + Z + 1 ≤ n
          · rw [if_pos hcond]
            simp only []
            have hmem : t₀ + δ.1 ∈ mids := (hmid_iff i δ e hri).mp hcond
            have hge : t ≤ t₀ + δ.1 := htle _ hmem
            have hlt : t₀ + δ.1 - t < Z := by
              have := hmids_spread _ hmem
              omega
            rw [Nat.mod_eq_of_lt hlt]
            omega
          · rw [if_neg hcond]
            simp only []
            omega
      omega
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [bulkCells, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hmin_wit⟩
    · rw [Finset.mem_Icc]
      omega
    · exact hwidth
  · -- the frozen arm
    set rs' : Fin (P.toPoly.arity c) → RegionSpec Z := fun i =>
      match rs₀ i with
      | RegionSpec.cluster δ e =>
          RegionSpec.back ⟨(n - 1 - (t₀ + δ.1)) % Z, Nat.mod_lt _ hZ⟩ e
      | r => r with hrs'def
    have hnomid : ∀ (i : Fin (P.toPoly.arity c)) (δ : Fin Z) (e : Bool),
        rs₀ i = .cluster δ e → ¬(Z ≤ t₀ + δ.1 ∧ t₀ + δ.1 + Z + 1 ≤ n) := by
      intro i δ e hri hcond
      refine hne ⟨t₀ + δ.1, ?_⟩
      rw [hmidsdef, Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [hri]
      simp only []
      rw [if_pos hcond]
      exact Finset.mem_singleton_self _
    have htup : ī = cellTuple rs' (Z + 1) n := by
      funext i
      show ī i = (rs' i).posAt (Z + 1) n
      rw [hrs'def]
      simp only []
      rcases hri : rs₀ i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
      · rw [hrs₀ i, hri]
        rfl
      · rw [hrs₀ i, hri]
        rfl
      · rw [hrs₀ i, hri]
        rfl
      · rw [hrs₀ i, hri]
        rfl
      · have hcond := hnomid i δ e hri
        have hback : n - Z ≤ t₀ + δ.1 := by omega
        have hub : t₀ + δ.1 ≤ n - 1 := by
          have := δ.isLt
          omega
        have hlt : n - 1 - (t₀ + δ.1) < Z := by omega
        show ī i = 1 + 2 * (n - 1 - (n - 1 - (t₀ + δ.1)) % Z) + _
        rw [Nat.mod_eq_of_lt hlt, hrs₀ i, hri]
        show 1 + 2 * (t₀ + δ.1) + _ = _
        congr 2
        omega
    refine ⟨(rs', Z + 1), ?_, htup⟩
    rw [cellIndex, Finset.mem_union]
    left
    rw [Finset.mem_product, Finset.mem_singleton]
    refine ⟨?_, rfl⟩
    rw [frozenCells, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun i => ?_⟩
    rw [hrs'def]
    simp only []
    rcases hri : rs₀ i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩
    all_goals trivial


/-! ## GA-7.1 part B: uniqueness of the classification -/

/-- A position is MIDDLE when its block sits clear of both boundary zones. -/
def MidPos (Z n q : ℕ) : Prop :=
  ∃ j, (q = 1 + 2 * j ∨ q = 1 + 2 * j + 1) ∧ Z ≤ j ∧ j + Z + 1 ≤ n

/-- Cluster-free descriptors never describe middle positions. -/
theorem not_midPos_clusterFree {Z : ℕ} (r : RegionSpec Z) (hcf : clusterFree r)
    (t n : ℕ) : ¬ MidPos Z n (r.posAt t n) := by
  rintro ⟨j, hq, hjZ, hjn⟩
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    simp only [RegionSpec.posAt] at hq
  · rcases hq with h | h <;> omega
  · rcases hq with h | h <;> omega
  · have := f.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] at hq <;>
      rcases hq with h | h <;> omega
  · have := l.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] at hq <;>
      rcases hq with h | h <;> omega
  · exact hcf

/-- **Position injectivity at a shared base**: two descriptors whose cluster blocks
sit in the middle zone and whose positions agree are equal. -/
theorem posAt_inj_bulk {Z : ℕ} (n t : ℕ) (hZt : Z ≤ t) (htn : t + Z + 1 ≤ n)
    (hn : 2 * Z + 2 ≤ n) (r r' : RegionSpec Z)
    (hr : ∀ δ : Fin Z, ∀ e, r = .cluster δ e → t + δ.1 + Z + 1 ≤ n)
    (hr' : ∀ δ : Fin Z, ∀ e, r' = .cluster δ e → t + δ.1 + Z + 1 ≤ n)
    (h : r.posAt t n = r'.posAt t n) : r = r' := by
  rcases hcr : r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    rcases hcr' : r' with _ | _ | ⟨f', e'⟩ | ⟨l', e'⟩ | ⟨δ', e'⟩
  case pre.pre =>
    rfl
  case pre.suf =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      omega)
  case pre.front =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case pre.back =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := l'.isLt
      rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case pre.cluster =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case suf.pre =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      omega)
  case suf.suf =>
    rfl
  case suf.front =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := f'.isLt
      rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case suf.back =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := l'.isLt
      rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case suf.cluster =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := hr' δ' e' hcr'
      rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case front.pre =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      rcases e with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case front.suf =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := f.isLt
      rcases e with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case front.front =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    have := f.isLt
    have := f'.isLt
    rcases e with _ | _ <;> rcases e' with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] at h
    · exact congrArg₂ _ (Fin.ext (by omega)) rfl
    · exact absurd h (by omega)
    · exact absurd h (by omega)
    · exact congrArg₂ _ (Fin.ext (by omega)) rfl
  case front.back =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := f.isLt
      have := l'.isLt
      rcases e with _ | _ <;> rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case front.cluster =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := f.isLt
      rcases e with _ | _ <;> rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case back.pre =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := l.isLt
      rcases e with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case back.suf =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := l.isLt
      rcases e with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case back.front =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := l.isLt
      have := f'.isLt
      rcases e with _ | _ <;> rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case back.back =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    have := l.isLt
    have := l'.isLt
    rcases e with _ | _ <;> rcases e' with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] at h
    · exact congrArg₂ _ (Fin.ext (by omega)) rfl
    · exact absurd h (by omega)
    · exact absurd h (by omega)
    · exact congrArg₂ _ (Fin.ext (by omega)) rfl
  case back.cluster =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := l.isLt
      have := hr' δ' e' hcr'
      rcases e with _ | _ <;> rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case cluster.pre =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := hr δ e hcr
      rcases e with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case cluster.suf =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := hr δ e hcr
      rcases e with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case cluster.front =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := f'.isLt
      rcases e with _ | _ <;> rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case cluster.back =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    exact absurd h (by
      have := l'.isLt
      have := hr δ e hcr
      rcases e with _ | _ <;> rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  case cluster.cluster =>
    rw [hcr, hcr'] at h
    simp only [RegionSpec.posAt] at h
    rcases e with _ | _ <;> rcases e' with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] at h
    · exact congrArg₂ _ (Fin.ext (by omega)) rfl
    · exact absurd h (by omega)
    · exact absurd h (by omega)
    · exact congrArg₂ _ (Fin.ext (by omega)) rfl

/-- Unpacked `cellIndex` membership. -/
theorem mem_cellIndex {Z k n : ℕ} {hZ : 1 ≤ Z}
    {rt : (Fin k → RegionSpec Z) × ℕ} :
    rt ∈ cellIndex Z hZ k n ↔
      ((∀ i, clusterFree (rt.1 i)) ∧ rt.2 = Z + 1) ∨
      ((∃ i e, rt.1 i = .cluster ⟨0, hZ⟩ e) ∧ Z ≤ rt.2 ∧
        rt.2 + clusterWidth rt.1 + Z ≤ n) := by
  rw [cellIndex, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, frozenCells, bulkCells,
    Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro (⟨⟨-, hcf⟩, ht⟩ | ⟨⟨⟨-, hwit⟩, ht1, -⟩, hw⟩)
    · exact Or.inl ⟨hcf, ht⟩
    · exact Or.inr ⟨hwit, ht1, hw⟩
  · rintro (⟨hcf, ht⟩ | ⟨hwit, ht1, hw⟩)
    · exact Or.inl ⟨⟨Finset.mem_univ _, hcf⟩, ht⟩
    · exact Or.inr ⟨⟨⟨Finset.mem_univ _, hwit⟩, ht1, by omega⟩, hw⟩

/-- Bulk members have width at least 1. -/
theorem bulk_width_pos {Z k : ℕ} {hZ : 1 ≤ Z} {rs : Fin k → RegionSpec Z}
    (hwit : ∃ i e, rs i = .cluster ⟨0, hZ⟩ e) : 1 ≤ clusterWidth rs := by
  obtain ⟨i, e, hi⟩ := hwit
  have := cluster_lt_width rs i ⟨0, hZ⟩ e hi
  omega

/-- **Canonical classification, uniqueness**: index entries sharing a cell tuple are
equal. -/
theorem canonical_unique {Z k : ℕ} (hZ : 1 ≤ Z) (n : ℕ) (hn : 2 * Z + 2 ≤ n)
    (rt rt' : (Fin k → RegionSpec Z) × ℕ)
    (hrt : rt ∈ cellIndex Z hZ k n) (hrt' : rt' ∈ cellIndex Z hZ k n)
    (h : cellTuple rt.1 rt.2 n = cellTuple rt'.1 rt'.2 n) : rt = rt' := by
  obtain ⟨rs, t⟩ := rt
  obtain ⟨rs', t'⟩ := rt'
  rw [mem_cellIndex] at hrt hrt'
  simp only [] at hrt hrt'
  -- the bulk offset-0 coordinate's position is middle; frozen positions never are
  have hbulk_mid : ∀ (rsb : Fin k → RegionSpec Z) (tb : ℕ),
      (∃ i e, rsb i = .cluster ⟨0, hZ⟩ e) → Z ≤ tb →
      tb + clusterWidth rsb + Z ≤ n →
      ∃ i, MidPos Z n (cellTuple rsb tb n i) := by
    intro rsb tb hwit htb hw
    obtain ⟨i, e, hi⟩ := hwit
    have hW := bulk_width_pos (hZ := hZ) ⟨i, e, hi⟩
    refine ⟨i, tb, ?_, htb, by omega⟩
    show (rsb i).posAt tb n = _ ∨ (rsb i).posAt tb n = _
    rw [hi]
    rcases e with _ | _
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hrt with ⟨hcf, ht⟩ | ⟨hwit, ht1, hw⟩ <;>
    rcases hrt' with ⟨hcf', ht'⟩ | ⟨hwit', ht1', hw'⟩
  · -- frozen / frozen
    subst ht
    subst ht'
    refine Prod.ext ?_ rfl
    funext i
    have hi := congrFun h i
    refine posAt_inj_bulk n (Z + 1) (by omega) (by omega) hn (rs i) (rs' i)
      (fun δ e hc => ?_) (fun δ e hc => ?_) hi
    · have hx := hcf i
      rw [hc] at hx
      exact hx.elim
    · have hx := hcf' i
      rw [hc] at hx
      exact hx.elim
  · -- frozen / bulk: contradiction via the middle coordinate
    exfalso
    obtain ⟨i, hmid⟩ := hbulk_mid rs' t' hwit' ht1' hw'
    rw [← congrFun h i] at hmid
    exact not_midPos_clusterFree (rs i) (hcf i) _ n hmid
  · -- bulk / frozen
    exfalso
    obtain ⟨i, hmid⟩ := hbulk_mid rs t hwit ht1 hw
    rw [congrFun h i] at hmid
    exact not_midPos_clusterFree (rs' i) (hcf' i) _ n hmid
  · -- bulk / bulk: the offset-0 coordinates pin the bases
    have hWpos := bulk_width_pos (hZ := hZ) hwit
    have hWpos' := bulk_width_pos (hZ := hZ) hwit'
    have htt' : t = t' := by
      -- t ≥ t'
      obtain ⟨i, e, hi⟩ := hwit
      obtain ⟨i', e', hi'⟩ := hwit'
      have hpi := congrFun h i
      have hpi' := congrFun h i'
      -- position of the offset-0 coordinate of rs, read through rs'
      have h1 : (RegionSpec.cluster ⟨0, hZ⟩ e).posAt t n = (rs' i).posAt t' n := by
        rw [← hi]
        exact hpi
      have h2 : (rs i').posAt t n = (RegionSpec.cluster ⟨0, hZ⟩ e').posAt t' n := by
        rw [← hi']
        exact hpi'
      have hge : t' ≤ t := by
        rcases hci : rs' i with _ | _ | ⟨f, e₂⟩ | ⟨l, e₂⟩ | ⟨δ, e₂⟩ <;>
          rw [hci] at h1 <;> simp only [RegionSpec.posAt] at h1
        · exact absurd h1 (by rcases e with _ | _ <;>
            simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
        · exact absurd h1 (by
            rcases e with _ | _ <;>
              simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
        · exact absurd h1 (by
            have := f.isLt
            rcases e with _ | _ <;> rcases e₂ with _ | _ <;>
              simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
        · exact absurd h1 (by
            have := l.isLt
            rcases e with _ | _ <;> rcases e₂ with _ | _ <;>
              simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
        · have hwd := cluster_lt_width rs' i δ e₂ hci
          rcases e with _ | _ <;> rcases e₂ with _ | _ <;>
            simp only [Bool.toNat_false, Bool.toNat_true] at h1 <;> omega
      have hle : t ≤ t' := by
        rcases hci : rs i' with _ | _ | ⟨f, e₂⟩ | ⟨l, e₂⟩ | ⟨δ, e₂⟩ <;>
          rw [hci] at h2 <;> simp only [RegionSpec.posAt] at h2
        · exact absurd h2 (by rcases e' with _ | _ <;>
            simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
        · exact absurd h2 (by
            rcases e' with _ | _ <;>
              simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
        · exact absurd h2 (by
            have := f.isLt
            rcases e' with _ | _ <;> rcases e₂ with _ | _ <;>
              simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
        · exact absurd h2 (by
            have := l.isLt
            rcases e' with _ | _ <;> rcases e₂ with _ | _ <;>
              simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
        · have hwd := cluster_lt_width rs i' δ e₂ hci
          rcases e' with _ | _ <;> rcases e₂ with _ | _ <;>
            simp only [Bool.toNat_false, Bool.toNat_true] at h2 <;> omega
      omega
    subst htt'
    refine Prod.ext ?_ rfl
    funext i
    have hi := congrFun h i
    exact posAt_inj_bulk n t (by omega) (by omega) hn (rs i) (rs' i)
      (fun δ e hc => by
        have := cluster_lt_width rs i δ e hc
        omega)
      (fun δ e hc => by
        have := cluster_lt_width rs' i δ e hc
        omega)
      hi

/-- **The canonical classification** (GA-7.1): past the threshold, every selected
tuple on an in-domain slice is the cell tuple of EXACTLY ONE canonical index entry. -/
theorem canonical_classification (P : WRP.Presentation Step Step) (C : ℕ)
    (hbud : ∀ n, P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) :
    ∃ Z Ncan : ℕ, ∃ hZ : 1 ≤ Z, ∀ n, Ncan ≤ n →
      P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
        P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩ →
        ∃! rt : (Fin (P.toPoly.arity c) → RegionSpec Z) × ℕ,
          rt ∈ cellIndex Z hZ (P.toPoly.arity c) n ∧ ī = cellTuple rt.1 rt.2 n := by
  obtain ⟨Z, Ncan, hZ, hex⟩ := canonical_exists P C hbud
  refine ⟨Z, Ncan + 2 * Z + 2, hZ, fun n hn hdom c ī hsel => ?_⟩
  obtain ⟨rt, hmem, htup⟩ := hex n (by omega) hdom c ī hsel
  refine ⟨rt, ⟨hmem, htup⟩, ?_⟩
  rintro rt' ⟨hmem', htup'⟩
  exact canonical_unique hZ n (by omega) rt' rt hmem' hmem (by rw [← htup', ← htup])


/-! ## GA-7.2: the abstract-predicate recount -/

/-- Cell tuples of index members are valid positions. -/
theorem cellIndex_valid {Z k n : ℕ} {hZ : 1 ≤ Z} (hn : 2 * Z + 2 ≤ n)
    {rt : (Fin k → RegionSpec Z) × ℕ} (hrt : rt ∈ cellIndex Z hZ k n) :
    ∀ i, cellTuple rt.1 rt.2 n i < (wrappedFlat n).length := by
  rw [mem_cellIndex] at hrt
  rcases hrt with ⟨-, ht⟩ | ⟨hwit, ht1, hw⟩
  · rw [ht]
    exact SliceDstarGateGA.cellTuple_valid rt.1 (Z + 1) n (by omega)
  · have hW := bulk_width_pos (hZ := hZ) hwit
    exact SliceDstarGateGA.cellTuple_valid rt.1 rt.2 n (by omega)

/-- **The canonical recount** (GA-7.2): the tuple sum of any selectedness-implying
predicate's indicator equals the frozen-cell sum plus the per-bulk-cell base counts. -/
theorem canonical_recount (P : WRP.Presentation Step Step) (C : ℕ)
    (hbud : ∀ n, P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) :
    ∃ Z Ncan : ℕ, ∃ hZ : 1 ≤ Z, ∀ n, Ncan ≤ n →
      P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (Q : (Fin (P.toPoly.arity c) → ℕ) → Prop),
        (∀ ī, Q ī → P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩) →
        (∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
            Finset.range (wrappedFlat n).length), if Q ī then 1 else 0)
          = (∑ rs' ∈ frozenCells Z (P.toPoly.arity c),
              if Q (cellTuple rs' (Z + 1) n) then 1 else 0)
            + ∑ rs ∈ bulkCells Z hZ (P.toPoly.arity c),
                ((Finset.Icc Z (n - Z - clusterWidth rs)).filter
                  (fun t => Q (cellTuple rs t n))).card := by
  classical
  obtain ⟨Z, Ncan, hZ, hclass⟩ := canonical_classification P C hbud
  refine ⟨Z, Ncan + 2 * Z + 2, hZ, fun n hn hdom c Q hQ => ?_⟩
  -- the indicator sum as a filter card
  rw [← Finset.card_filter]
  -- the central bijection onto the filtered cell index
  have hbij : ((Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
        Finset.range (wrappedFlat n).length)).filter Q).card
      = ((cellIndex Z hZ (P.toPoly.arity c) n).filter
          (fun rt => Q (cellTuple rt.1 rt.2 n))).card := by
    refine Finset.card_bij'
      (i := fun ī hī => Classical.choose
        (hclass n (by omega) hdom c ī
          (hQ ī (Finset.mem_filter.mp hī).2)).exists)
      (j := fun rt hrt => cellTuple rt.1 rt.2 n) ?_ ?_ ?_ ?_
    · intro ī hī
      have hspec := Classical.choose_spec
        (hclass n (by omega) hdom c ī (hQ ī (Finset.mem_filter.mp hī).2)).exists
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
      exact cellIndex_valid (by omega) hrt.1 i
    · intro ī hī
      have hspec := Classical.choose_spec
        (hclass n (by omega) hdom c ī (hQ ī (Finset.mem_filter.mp hī).2)).exists
      exact hspec.2.symm
    · intro rt hrt
      rw [Finset.mem_filter] at hrt
      have hsel : P.toPoly.selectedAtom (wrappedFlat n) ⟨c, cellTuple rt.1 rt.2 n⟩ :=
        hQ _ hrt.2
      have huniq := hclass n (by omega) hdom c (cellTuple rt.1 rt.2 n) hsel
      exact huniq.unique (Classical.choose_spec huniq.exists) ⟨hrt.1, rfl⟩
  rw [hbij]
  -- split the index into its two arms
  rw [cellIndex, Finset.filter_union,
    Finset.card_union_of_disjoint (by
      refine Finset.disjoint_filter_filter ?_
      rw [Finset.disjoint_left]
      intro rt h1 h2
      rw [Finset.mem_product, frozenCells, Finset.mem_filter] at h1
      rw [Finset.mem_filter, Finset.mem_product, bulkCells, Finset.mem_filter] at h2
      obtain ⟨i, e, hi⟩ := h2.1.1.2
      have := h1.1.2 i
      rw [hi] at this
      exact this.elim)]
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
        (if (t + clusterWidth rs + Z ≤ n ∧ Q (cellTuple rs t n)) then 1 else 0)
          = (if t + clusterWidth rs + Z ≤ n
              then (if Q (cellTuple rs t n) then 1 else 0) else 0) := by
      intro t
      by_cases h1 : t + clusterWidth rs + Z ≤ n
      · by_cases h2 : Q (cellTuple rs t n)
        · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]
        · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg h2]
      · rw [if_neg (fun h => h1 h.1), if_neg h1]
    calc ∑ t ∈ Finset.Icc Z n,
          (if (t + clusterWidth rs + Z ≤ n ∧ Q (cellTuple rs t n)) then 1 else 0)
        = ∑ t ∈ Finset.Icc Z n, (if t + clusterWidth rs + Z ≤ n
            then (if Q (cellTuple rs t n) then 1 else 0) else 0) :=
          Finset.sum_congr rfl (fun t _ => hsplit t)
      _ = ∑ t ∈ (Finset.Icc Z n).filter (fun t => t + clusterWidth rs + Z ≤ n),
            (if Q (cellTuple rs t n) then 1 else 0) := (Finset.sum_filter _ _).symm
      _ = ∑ t ∈ Finset.Icc Z (n - Z - clusterWidth rs),
            (if Q (cellTuple rs t n) then 1 else 0) := by
          refine Finset.sum_congr ?_ (fun t _ => rfl)
          refine Finset.ext (fun t => ?_)
          rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
          omega

end SliceFasCountGA
