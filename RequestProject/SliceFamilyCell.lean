/-
# The family cell descriptors (route GA-4/5/6/7 shared infrastructure)

The adjudicated GA design organises the eventually-selected atoms into FAMILIES: each
coordinate of an atom is pinned to the front, pinned to the back, or rides the single
mobile bulk cluster.  This file provides the shared descriptor type:

* `RegionSpec B` — the per-coordinate region at pin/offset bound `B`: the pre letter,
  the suffix letter, a front-pinned block `f < B` (with its `U`/`D` half), a
  back-pinned block `n−1−l` (`l < B`), or the cluster block `t+δ` (`δ < B`);
* `RegionSpec.posAt` — the slice position it describes at cluster base `t` on `W_n`;
* `cells_cover` — the COVER form of `SliceGrowthCollapse.one_cluster_cells`: beyond
  the thresholds, every budget-respecting selected atom is `fun i => (r i).posAt t n`
  for some per-coordinate regions and some base `B ≤ t ≤ n − B`.

Uniqueness/canonicity (the GA-7 partition form) lives in `SliceCellClassifyGA.lean`;
GA-4's rank decomposition and GA-5's candidate analysis need only the cover.

Axiom-clean modulo Büchi (inherited from `one_cluster_cells`).
-/
import RequestProject.SliceGrowthCollapse

namespace SliceFamilyCell

/-- Per-coordinate region descriptor at pin/offset bound `B`. -/
inductive RegionSpec (B : ℕ) where
  | pre
  | suf
  | front (f : Fin B) (e : Bool)
  | back (l : Fin B) (e : Bool)
  | cluster (δ : Fin B) (e : Bool)
  deriving DecidableEq, Fintype

/-- The slice position described by a region, at cluster base `t` on `W_n`. -/
def RegionSpec.posAt {B : ℕ} : RegionSpec B → (t n : ℕ) → ℕ
  | .pre, _, _ => 0
  | .suf, _, n => 1 + 2 * n
  | .front f e, _, _ => 1 + 2 * f.val + e.toNat
  | .back l e, _, n => 1 + 2 * (n - 1 - l.val) + e.toNat
  | .cluster δ e, t, _ => 1 + 2 * (t + δ.val) + e.toNat

/-- **The cover form of the cells theorem**: beyond the thresholds, every
budget-respecting selected atom is described coordinatewise by regions at a single
cluster base `t` with `B ≤ t` and `t + B ≤ n`. -/
theorem cells_cover (P : WRP.Presentation Step Step) (C : ℕ) :
    ∃ B N : ℕ, 1 ≤ B ∧ ∀ n, N ≤ n → ∀ c : Fin P.toPoly.K,
      ∀ ī : Fin (P.toPoly.arity c) → ℕ,
      P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩ →
      (∀ l : List (Fin (P.toPoly.arity c) → ℕ), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) →
      ∃ t : ℕ, B ≤ t ∧ t + B ≤ n ∧
        ∀ i, ∃ r : RegionSpec B, ī i = r.posAt t n := by
  obtain ⟨B, N, hB1, hcells⟩ := SliceGrowthCollapse.one_cluster_cells P C
  refine ⟨B, max N (2 * B), hB1, ?_⟩
  intro n hn c ī hsel hcard
  have h2B : 2 * B ≤ n := le_trans (le_max_right _ _) hn
  rcases hcells n (le_trans (le_max_left _ _) hn) c ī hsel hcard with
    hflat | ⟨t, htB, htn, _, hall⟩
  · -- no bulk cluster: any admissible base works; take t := B
    refine ⟨B, le_refl B, by omega, fun i => ?_⟩
    rcases hflat i with h0 | hsuf | ⟨f, hf, hbl⟩ | ⟨e, he1, heB, hbl⟩
    · exact ⟨.pre, h0⟩
    · exact ⟨.suf, hsuf⟩
    · rcases hbl with h | h
      · exact ⟨.front ⟨f, hf⟩ false, by simp [RegionSpec.posAt]; omega⟩
      · exact ⟨.front ⟨f, hf⟩ true, by simp [RegionSpec.posAt]; omega⟩
    · rcases hbl with h | h
      · exact ⟨.back ⟨e - 1, by omega⟩ false, by simp [RegionSpec.posAt]; omega⟩
      · exact ⟨.back ⟨e - 1, by omega⟩ true, by simp [RegionSpec.posAt]; omega⟩
  · -- one bulk cluster at base t
    refine ⟨t, htB, htn, fun i => ?_⟩
    rcases hall i with h0 | hsuf | ⟨f, hf, hbl⟩ | ⟨e, he1, heB, hbl⟩ | ⟨δ, hδ, hbl⟩
    · exact ⟨.pre, h0⟩
    · exact ⟨.suf, hsuf⟩
    · rcases hbl with h | h
      · exact ⟨.front ⟨f, hf⟩ false, by simp [RegionSpec.posAt]; omega⟩
      · exact ⟨.front ⟨f, hf⟩ true, by simp [RegionSpec.posAt]; omega⟩
    · rcases hbl with h | h
      · exact ⟨.back ⟨e - 1, by omega⟩ false, by simp [RegionSpec.posAt]; omega⟩
      · exact ⟨.back ⟨e - 1, by omega⟩ true, by simp [RegionSpec.posAt]; omega⟩
    · rcases hbl with h | h
      · exact ⟨.cluster ⟨δ, hδ⟩ false, by simp [RegionSpec.posAt]; omega⟩
      · exact ⟨.cluster ⟨δ, hδ⟩ true, by simp [RegionSpec.posAt]; omega⟩

end SliceFamilyCell
