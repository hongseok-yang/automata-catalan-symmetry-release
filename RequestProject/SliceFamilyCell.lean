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

Uniqueness/canonicity (the GA-7 partition form) is deliberately deferred; GA-4's rank
decomposition and GA-5's candidate analysis need only the cover.

Axiom-clean modulo Büchi (inherited from `one_cluster_cells`).
-/
import RequestProject.SliceGrowthCollapse

namespace SliceFamilyCell

open Step

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

open SliceGrowthCollapse in
/-- **The flanked taxonomy** (GA-5 prep): beyond the thresholds, every
budget-respecting selected atom splits as front pins (blocks `< B''`), back pins
(offsets `< B''`), and at most ONE mobile window `[t, u]` of width `< B''` whose
`G`-block flanks are coordinate-free — the form whose cluster the GA-5 transport can
slide with `acceptsN_moveGroup`.  Two pigeonhole gaps replace any freezing scan: a
front gap `[a, a+G)` found just right of the one-cluster bound and a back gap
`[b, b+G)` found just left of `n − B`; the mobile window is `[min, max]` of the
coordinates between the gaps. -/
theorem atom_cell_flanked (P : WRP.Presentation Step Step) (C G : ℕ) :
    ∃ B'' N : ℕ, 1 ≤ B'' ∧ ∀ n, N ≤ n → ∀ c : Fin P.toPoly.K,
      ∀ ī : Fin (P.toPoly.arity c) → ℕ,
      P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩ →
      (∀ l : List (Fin (P.toPoly.arity c) → ℕ), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) →
      (∀ i, ī i = 0 ∨ ī i = 1 + 2 * n
          ∨ (∃ f, f < B'' ∧ inBlock (ī i) f)
          ∨ (∃ e, 1 ≤ e ∧ e < B'' ∧ inBlock (ī i) (n - e)))
      ∨ (∃ t u : ℕ, G + 1 ≤ t ∧ t ≤ u ∧ u < t + B'' ∧ u + G + 1 ≤ n ∧
          (∃ i₀, inBlock (ī i₀) t) ∧ (∃ i₁, inBlock (ī i₁) u) ∧
          (∀ j, t - G ≤ j → j < t → ∀ i, ī i ≠ 1 + 2 * j ∧ ī i ≠ 1 + 2 * j + 1) ∧
          (∀ j, u < j → j ≤ u + G → ∀ i, ī i ≠ 1 + 2 * j ∧ ī i ≠ 1 + 2 * j + 1) ∧
          ∀ i, ī i = 0 ∨ ī i = 1 + 2 * n
            ∨ (∃ f, f < B'' ∧ inBlock (ī i) f)
            ∨ (∃ e, 1 ≤ e ∧ e < B'' ∧ inBlock (ī i) (n - e))
            ∨ (∃ δ, δ < B'' ∧ inBlock (ī i) (t + δ) ∧ t + δ ≤ u)) := by
  classical
  obtain ⟨B, N₁, hB1, hoc⟩ := SliceGrowthCollapse.one_cluster P C
  set A : ℕ := Finset.univ.sup (fun c : Fin P.toPoly.K => P.toPoly.arity c) with hAdef
  set B'' : ℕ := B + (A + 1) * G + 1 with hB''def
  refine ⟨B'', max N₁ (3 * B'' + 3), by omega, ?_⟩
  intro n hn c ī hsel hcard
  have hnN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 * B'' + 3 ≤ n := le_trans (le_max_right _ _) hn
  have hAc : P.toPoly.arity c ≤ A :=
    Finset.le_sup (f := fun c : Fin P.toPoly.K => P.toPoly.arity c) (Finset.mem_univ c)
  have hmul : (P.toPoly.arity c + 1) * G ≤ (A + 1) * G :=
    Nat.mul_le_mul_right G (by omega)
  have hval : ∀ i, ī i < 2 * (n + 1) := by
    intro i
    have := hsel.1 i
    rwa [length_wrappedFlat] at this
  -- the two coordinate-free gaps
  obtain ⟨a, halo, hatop, hagap⟩ := SliceGrowthCollapse.exists_unmarked_gap ī G B
  obtain ⟨b, hblo, hbtop, hbgap⟩ :=
    SliceGrowthCollapse.exists_unmarked_gap ī G (n - B - (P.toPoly.arity c + 1) * G)
  have hbn : b + G ≤ n - B := by omega
  have hab : a + G < b := by omega
  -- the mobile coordinate blocks
  set S : Finset ℕ := (Finset.range n).filter
    (fun j => a + G ≤ j ∧ j < b ∧ ∃ i, inBlock (ī i) j) with hSdef
  have hSmem : ∀ j, j ∈ S ↔ (j < n ∧ a + G ≤ j ∧ j < b ∧ ∃ i, inBlock (ī i) j) := by
    intro j
    rw [hSdef, Finset.mem_filter, Finset.mem_range]
  by_cases hSne : S.Nonempty
  · right
    set t := S.min' hSne with htdef
    set u := S.max' hSne with hudef
    have htS := S.min'_mem hSne
    rw [hSmem] at htS
    obtain ⟨htn, hta, htb, i₀, hi₀⟩ := htS
    have huS := S.max'_mem hSne
    rw [hSmem] at huS
    obtain ⟨hun, hua, hub, i₁, hi₁⟩ := huS
    have htu : t ≤ u := S.min'_le u (S.max'_mem hSne)
    have hwidth : u < t + B := by
      by_contra hcon
      push Not at hcon
      exact hoc n hnN₁ c ī hsel hcard i₀ i₁ t u hi₀ hi₁ (by omega) hcon (by omega)
    refine ⟨t, u, by omega, htu, by omega, by omega, ⟨i₀, hi₀⟩, ⟨i₁, hi₁⟩, ?_, ?_, ?_⟩
    · -- the left flank is coordinate-free
      intro j hj1 hj2 i
      by_cases hja : j < a + G
      · exact hagap j (by omega) hja i
      · constructor
        · intro hcon
          have hjS : j ∈ S := (hSmem j).mpr ⟨by omega, by omega, by omega, i, Or.inl hcon⟩
          have := S.min'_le j hjS
          omega
        · intro hcon
          have hjS : j ∈ S := (hSmem j).mpr ⟨by omega, by omega, by omega, i, Or.inr hcon⟩
          have := S.min'_le j hjS
          omega
    · -- the right flank is coordinate-free
      intro j hj1 hj2 i
      by_cases hjb : b ≤ j
      · exact hbgap j hjb (by omega) i
      · constructor
        · intro hcon
          have hjS : j ∈ S := (hSmem j).mpr ⟨by omega, by omega, by omega, i, Or.inl hcon⟩
          have := S.le_max' j hjS
          omega
        · intro hcon
          have hjS : j ∈ S := (hSmem j).mpr ⟨by omega, by omega, by omega, i, Or.inr hcon⟩
          have := S.le_max' j hjS
          omega
    · -- the per-coordinate split
      intro i
      rcases SliceGrowthCollapse.position_cases (ī i) n (hval i) with h0 | hsuf | ⟨hjn, hblk⟩
      · left; exact h0
      · right; left; exact hsuf
      · set j := (ī i - 1) / 2 with hjdef
        rcases Nat.lt_or_ge j a with hja | hja
        · right; right; left
          exact ⟨j, by omega, hblk⟩
        · rcases Nat.lt_or_ge j (a + G) with hjaG | hjaG
          · exfalso
            rcases hblk with h | h
            · exact (hagap j hja hjaG i).1 h
            · exact (hagap j hja hjaG i).2 h
          · rcases Nat.lt_or_ge j b with hjb | hjb
            · have hjS : j ∈ S := (hSmem j).mpr ⟨hjn, hjaG, hjb, i, hblk⟩
              have h1 := S.min'_le j hjS
              have h2 := S.le_max' j hjS
              right; right; right; right
              refine ⟨j - t, by omega, ?_, by omega⟩
              have harg : t + (j - t) = j := by omega
              rw [harg]
              exact hblk
            · rcases Nat.lt_or_ge j (b + G) with hjbG | hjbG
              · exfalso
                rcases hblk with h | h
                · exact (hbgap j hjb hjbG i).1 h
                · exact (hbgap j hjb hjbG i).2 h
              · right; right; right; left
                refine ⟨n - j, by omega, by omega, ?_⟩
                have harg : n - (n - j) = j := by omega
                rw [harg]
                exact hblk
  · -- no mobile window: the all-pinned split
    left
    intro i
    rcases SliceGrowthCollapse.position_cases (ī i) n (hval i) with h0 | hsuf | ⟨hjn, hblk⟩
    · left; exact h0
    · right; left; exact hsuf
    · set j := (ī i - 1) / 2 with hjdef
      rcases Nat.lt_or_ge j a with hja | hja
      · right; right; left
        exact ⟨j, by omega, hblk⟩
      · rcases Nat.lt_or_ge j (a + G) with hjaG | hjaG
        · exfalso
          rcases hblk with h | h
          · exact (hagap j hja hjaG i).1 h
          · exact (hagap j hja hjaG i).2 h
        · rcases Nat.lt_or_ge j b with hjb | hjb
          · exact absurd ⟨j, (hSmem j).mpr ⟨hjn, hjaG, hjb, i, hblk⟩⟩ hSne
          · rcases Nat.lt_or_ge j (b + G) with hjbG | hjbG
            · exfalso
              rcases hblk with h | h
              · exact (hbgap j hjb hjbG i).1 h
              · exact (hbgap j hjb hjbG i).2 h
            · right; right; right
              refine ⟨n - j, by omega, by omega, ?_⟩
              have harg : n - (n - j) = j := by omega
              rw [harg]
              exact hblk


end SliceFamilyCell
