/-
# The fibred cells layer (§9 tower, Stage D cells)

The copied slice `U^(mS−1) (UD)^n D^(mS−1)` (wrapped) adds two boundary
stretches to the wrapped-flat position taxonomy.  This file extends the
GA descriptor type accordingly and delivers the fibred cover form:

* `RegionSpecF B` — a wrapped-flat descriptor (`core`), a prefix-stretch
  index (`prefIdx q`, position `q < mS−1`), or a suffix-stretch offset
  (`sufIdx l`, position `mS+2n+1+l`, `l < mS−1`).  The TYPE is
  `mS`-independent; only `valid` reads `mS`.  Deliberately NO `Fintype`
  instance (frozen design CS-4): per-`mS` enumerations must be explicit
  `Finset`s so they can never leak into a `Finset.univ` period product.
* `position_cases_copied` — the five-way position split on the copied slice.
* `cells_cover_fibred` — the cover form of the fibred cells theorem: beyond
  thresholds (`B` before the budget and `mS`), every budget-respecting
  selected atom is described coordinatewise by valid descriptors at a single
  cluster base `B ≤ t ≤ n − B`.
-/
import RequestProject.CopiedCluster
import RequestProject.SliceFamilyCell

open SliceFamilyCell

namespace CopiedCells

/-- Per-coordinate region descriptor on the copied slice: a wrapped-flat
descriptor, a prefix-stretch index, or a suffix-stretch offset. -/
inductive RegionSpecF (B : ℕ) where
  | core (r : RegionSpec B)
  | prefIdx (q : ℕ)
  | sufIdx (l : ℕ)
  deriving DecidableEq

/-- The copied-slice position described, at boundary width `mS` and cluster
base `t`: `core` descriptors are the wrapped-flat positions shifted by the
prefix stretch `mS − 1`. -/
def RegionSpecF.posAt {B : ℕ} : RegionSpecF B → (mS t n : ℕ) → ℕ
  | .core r, mS, t, n => mS - 1 + r.posAt t n
  | .prefIdx q, _, _, _ => q
  | .sufIdx l, mS, _, n => mS + 2 * n + 1 + l

/-- Boundary validity at width `mS`: stretch indices must lie inside the
stretches; `core` descriptors are unconstrained. -/
def RegionSpecF.valid {B : ℕ} : RegionSpecF B → (mS : ℕ) → Prop
  | .core _, _ => True
  | .prefIdx q, mS => q < mS - 1
  | .sufIdx l, mS => l < mS - 1

/-- Five-way position classification on the copied slice: prefix stretch,
pre letter, middle block (explicit witness `(q − mS) / 2`), suffix letter,
suffix stretch. -/
theorem position_cases_copied (mS q n : ℕ) (hm : 1 ≤ mS)
    (_hq : q < 2 * (mS + n)) :
    q < mS - 1 ∨ q = mS - 1
      ∨ ((q - mS) / 2 < n ∧ (q = mS + 2 * ((q - mS) / 2)
          ∨ q = mS + 2 * ((q - mS) / 2) + 1))
      ∨ q = mS + 2 * n ∨ mS + 2 * n + 1 ≤ q := by
  omega

/-- **The fibred cover form** (the Stage D external interface): beyond a
machine-determined `B` (before the budget and `mS`) and a threshold `N`
(after them), every budget-respecting selected atom of the copied slice is
described coordinatewise by valid descriptors at one cluster base
`B ≤ t ≤ n − B`. -/
theorem cells_cover_fibred (P : WRP.Presentation Step Step) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ C mS : ℕ, 1 ≤ mS → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ c : Fin P.toPoly.K, ∀ ī : Fin (P.toPoly.arity c) → ℕ,
      P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ →
      (∀ l : List (Fin (P.toPoly.arity c) → ℕ), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
        l.length ≤ C * (mS + n + 1)) →
      ∃ t : ℕ, B ≤ t ∧ t + B ≤ n ∧
        ∀ i, ∃ r : RegionSpecF B, r.valid mS ∧ ī i = r.posAt mS t n := by
  classical
  obtain ⟨B, hB1, hocC⟩ := CopiedCluster.one_cluster_fibred P
  refine ⟨B, hB1, fun C mS hm => ?_⟩
  obtain ⟨N, hoc⟩ := hocC C mS hm
  refine ⟨max N (2 * B), fun n hn c ī hsel hcard => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have h2B : 2 * B ≤ n := le_trans (le_max_right _ _) hn
  have hlen : (copiedSlice mS n).length = 2 * (mS + n) := length_copiedSlice mS n
  have hval : ∀ i, ī i < 2 * (mS + n) := by
    intro i
    have h := hsel.1 i
    rw [hlen] at h
    exact h
  -- the inhabited admissible middle blocks
  set S : Finset ℕ := (Finset.range n).filter
    (fun j => B ≤ j ∧ j + B ≤ n ∧
      ∃ i, ī i = mS + 2 * j ∨ ī i = mS + 2 * j + 1) with hS
  have hSmem : ∀ j, j ∈ S ↔ (j < n ∧ B ≤ j ∧ j + B ≤ n ∧
      ∃ i, ī i = mS + 2 * j ∨ ī i = mS + 2 * j + 1) := by
    intro j
    rw [hS, Finset.mem_filter, Finset.mem_range]
  by_cases hSne : S.Nonempty
  · -- one bulk cluster, based at the least inhabited admissible block
    set t := S.min' hSne with htdef
    have htS := S.min'_mem hSne
    rw [hSmem] at htS
    obtain ⟨htn, htB, htBn, i₀, hi₀⟩ := htS
    refine ⟨t, htB, htBn, fun i => ?_⟩
    rcases position_cases_copied mS (ī i) n hm (hval i) with
      hpre | hP | ⟨hjn, hblk⟩ | hsuf | hsuf'
    · exact ⟨.prefIdx (ī i), hpre, rfl⟩
    · exact ⟨.core .pre, trivial, by
        simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
    · set j := (ī i - mS) / 2 with hjdef
      by_cases hf : j < B
      · rcases hblk with h | h
        · exact ⟨.core (.front ⟨j, hf⟩ false), trivial, by
            simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
        · exact ⟨.core (.front ⟨j, hf⟩ true), trivial, by
            simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
      · by_cases hb : j + B ≤ n
        · have hjS : j ∈ S := (hSmem j).mpr ⟨hjn, by omega, hb, ⟨i, hblk⟩⟩
          have htj : t ≤ j := S.min'_le j hjS
          have hjt : j < t + B := by
            by_contra hcon
            push Not at hcon
            exact hoc n hnN c ī hsel hcard i₀ i t j hi₀ hblk htB hcon hb
          rcases hblk with h | h
          · exact ⟨.core (.cluster ⟨j - t, by omega⟩ false), trivial, by
              simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
          · exact ⟨.core (.cluster ⟨j - t, by omega⟩ true), trivial, by
              simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
        · rcases hblk with h | h
          · exact ⟨.core (.back ⟨n - 1 - j, by omega⟩ false), trivial, by
              simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
          · exact ⟨.core (.back ⟨n - 1 - j, by omega⟩ true), trivial, by
              simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
    · exact ⟨.core .suf, trivial, by
        simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
    · refine ⟨.sufIdx (ī i - (mS + 2 * n + 1)), ?_, ?_⟩
      · show ī i - (mS + 2 * n + 1) < mS - 1
        have h := hval i
        omega
      · show ī i = mS + 2 * n + 1 + (ī i - (mS + 2 * n + 1))
        omega
  · -- no bulk cluster: park the base at t := B
    refine ⟨B, le_refl B, by omega, fun i => ?_⟩
    rcases position_cases_copied mS (ī i) n hm (hval i) with
      hpre | hP | ⟨hjn, hblk⟩ | hsuf | hsuf'
    · exact ⟨.prefIdx (ī i), hpre, rfl⟩
    · exact ⟨.core .pre, trivial, by
        simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
    · set j := (ī i - mS) / 2 with hjdef
      by_cases hf : j < B
      · rcases hblk with h | h
        · exact ⟨.core (.front ⟨j, hf⟩ false), trivial, by
            simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
        · exact ⟨.core (.front ⟨j, hf⟩ true), trivial, by
            simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
      · by_cases hb : j + B ≤ n
        · exact absurd ⟨j, (hSmem j).mpr ⟨hjn, by omega, hb, ⟨i, hblk⟩⟩⟩ hSne
        · rcases hblk with h | h
          · exact ⟨.core (.back ⟨n - 1 - j, by omega⟩ false), trivial, by
              simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
          · exact ⟨.core (.back ⟨n - 1 - j, by omega⟩ true), trivial, by
              simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
    · exact ⟨.core .suf, trivial, by
        simp [RegionSpecF.posAt, RegionSpec.posAt]; omega⟩
    · refine ⟨.sufIdx (ī i - (mS + 2 * n + 1)), ?_, ?_⟩
      · show ī i - (mS + 2 * n + 1) < mS - 1
        have h := hval i
        omega
      · show ī i = mS + 2 * n + 1 + (ī i - (mS + 2 * n + 1))
        omega

end CopiedCells
