/-
# Semilinear function graphs are eventually affine on residue classes

The converse of `SliceSemilinear.isSemilinear2_of_affineInPeriod`: a semilinear
set that happens to be the graph of a function is, beyond a threshold, affine on
each residue class of a period `p` read off from the ambient linear
decomposition — the finitely many step vectors of the components.  Since `p` is
extracted before any row is fixed, a semilinear graph in `ℕ³` read as a family
of rows has eventually-affine rows at ONE period, uniform in the row.
-/
import RequestProject.SliceSemilinearN

namespace SemilinearGraphAffine

open SlicePeriodStar

/-! ## Linear-set toolkit -/

/-- Adding any multiple of an available step keeps a point inside a linear set. -/
private theorem linearSet_add_step {d : ℕ} {base : Fin d → ℕ}
    {steps : Finset (Fin d → ℕ)} {v : Fin d → ℕ}
    (hv : v ∈ LinearSet d base steps) {s₀ : Fin d → ℕ} (hs₀ : s₀ ∈ steps) (c : ℕ) :
    (fun i => v i + c * s₀ i) ∈ LinearSet d base steps := by
  classical
  obtain ⟨coeffs, hveq⟩ := hv
  refine ⟨Function.update coeffs s₀ (coeffs s₀ + c), ?_⟩
  funext i
  have hvi : v i = base i + steps.sum (fun s => coeffs s * s i) := by rw [hveq]
  have hsum : steps.sum (fun s => Function.update coeffs s₀ (coeffs s₀ + c) s * s i)
      = steps.sum (fun s => coeffs s * s i) + c * s₀ i := by
    rw [← Finset.insert_erase hs₀,
      Finset.sum_insert (Finset.notMem_erase s₀ steps),
      Finset.sum_insert (Finset.notMem_erase s₀ steps), Function.update_self]
    have herase : (steps.erase s₀).sum
        (fun s => Function.update coeffs s₀ (coeffs s₀ + c) s * s i)
        = (steps.erase s₀).sum (fun s => coeffs s * s i) :=
      Finset.sum_congr rfl fun s hs => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
    rw [herase]
    ring
  show v i + c * s₀ i
      = base i + steps.sum (fun s => Function.update coeffs s₀ (coeffs s₀ + c) s * s i)
  rw [hsum, hvi]
  ring

/-- A point of a linear set in `ℕ³` whose middle coordinate exceeds
`base 1 + (first coordinate) · Σ steps` must come from a step that leaves the
first coordinate alone and strictly increases the middle one: steps with a
positive first component carry coefficients bounded by the first coordinate. -/
private theorem exists_free_step {base : Fin 3 → ℕ} {steps : Finset (Fin 3 → ℕ)}
    {v : Fin 3 → ℕ} (hv : v ∈ LinearSet 3 base steps)
    (hlarge : base 1 + v 0 * steps.sum (fun s => s 1) < v 1) :
    ∃ s ∈ steps, s 0 = 0 ∧ 0 < s 1 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨coeffs, hveq⟩ := hv
  have hv0 : v 0 = base 0 + steps.sum (fun s => coeffs s * s 0) := by rw [hveq]
  have hv1 : v 1 = base 1 + steps.sum (fun s => coeffs s * s 1) := by rw [hveq]
  have hbound : ∀ s ∈ steps, coeffs s * s 1 ≤ v 0 * s 1 := by
    intro s hs
    rcases Nat.eq_zero_or_pos (s 0) with h0 | h0
    · have hz : s 1 = 0 := Nat.le_zero.mp (hcon s hs h0)
      rw [hz, Nat.mul_zero, Nat.mul_zero]
    · have h1 : coeffs s * s 0 ≤ steps.sum (fun t => coeffs t * t 0) :=
        Finset.single_le_sum (f := fun t => coeffs t * t 0) (fun _ _ => Nat.zero_le _) hs
      have h2 : coeffs s * 1 ≤ coeffs s * s 0 :=
        Nat.mul_le_mul (le_refl (coeffs s)) (by omega)
      rw [Nat.mul_one] at h2
      exact Nat.mul_le_mul (by omega) (le_refl (s 1))
  have hfinal : v 1 ≤ base 1 + v 0 * steps.sum (fun s => s 1) := by
    rw [hv1, Finset.mul_sum]
    exact Nat.add_le_add_left (Finset.sum_le_sum hbound) _
  omega

/-! ## Assembling pinned affineness from one progression per residue class -/

/-- One affine arithmetic progression inside every residue class mod `p`
suffices for `AffineOnResiduesAt p`: rebase all the progressions to the common
threshold `p · (sup of their starting points)`, which is `0` mod `p`. -/
private theorem affineOnResiduesAt_of_classwise {p : ℕ} (hp : 1 ≤ p) {g : ℕ → ℕ}
    (h : ∀ j, j < p → ∃ M b s : ℕ, M % p = j ∧ ∀ k, g (M + p * k) = b + k * s) :
    AffineOnResiduesAt p g := by
  classical
  choose! M b s hmod hval using h
  refine ⟨p * (Finset.range p).sup M, fun j hj => ?_⟩
  have hsup : M j ≤ (Finset.range p).sup M := Finset.le_sup (Finset.mem_range.mpr hj)
  have hmul : 1 * (Finset.range p).sup M ≤ p * (Finset.range p).sup M :=
    Nat.mul_le_mul hp (le_refl _)
  rw [Nat.one_mul] at hmul
  have hle : M j ≤ p * (Finset.range p).sup M + j := by omega
  have hTj : (p * (Finset.range p).sup M + j) % p = j := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hj
  obtain ⟨d, hd⟩ : p ∣ p * (Finset.range p).sup M + j - M j := by
    refine (Nat.modEq_iff_dvd' hle).mp ?_
    have hcongr : M j % p = (p * (Finset.range p).sup M + j) % p := by
      rw [hTj, hmod j hj]
    exact hcongr
  refine ⟨b j + d * s j, s j, fun k => ?_⟩
  have harg : p * (Finset.range p).sup M + j + p * k = M j + p * (d + k) := by
    have hexp : p * (d + k) = p * d + p * k := by ring
    omega
  rw [harg, hval j hj (d + k)]
  ring

/-! ## The converse -/

/-- A semilinear function graph in `ℕ³`, viewed as a family of rows indexed by
the first coordinate, has eventually-affine rows with a period uniform in the
row. -/
private theorem graph3_uniform (f : ℕ → ℕ → ℕ)
    (hS : IsSemilinearNd 3 {v : Fin 3 → ℕ | f (v 0) (v 1) = v 2}) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ m : ℕ, AffineOnResiduesAt p (fun n => f m n) := by
  classical
  obtain ⟨comps, hcomp, hunion⟩ := hS
  choose! baseF stepsF hbsF using hcomp
  -- the period: every nonzero middle component of every step divides it
  set p : ℕ :=
    comps.prod (fun C => (stepsF C).prod (fun s => if s 1 = 0 then 1 else s 1)) with hp_def
  have hp1 : 1 ≤ p := by
    rw [hp_def]
    refine Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun C _ => ?_)
    refine Finset.prod_ne_zero_iff.mpr fun s _ => ?_
    by_cases hs : s 1 = 0
    · rw [if_pos hs]; omega
    · rw [if_neg hs]; exact hs
  have hdvd : ∀ C ∈ comps, ∀ s ∈ stepsF C, s 1 ≠ 0 → s 1 ∣ p := by
    intro C hC s hs hne
    have h1 : (if s 1 = 0 then 1 else s 1)
        ∣ (stepsF C).prod (fun s => if s 1 = 0 then 1 else s 1) :=
      Finset.dvd_prod_of_mem _ hs
    rw [if_neg hne] at h1
    rw [hp_def]
    exact h1.trans (Finset.dvd_prod_of_mem _ hC)
  refine ⟨p, hp1, fun m => ?_⟩
  refine affineOnResiduesAt_of_classwise hp1 ?_
  intro j hj
  -- a starting point in the class `j`, beyond the reach of every component's
  -- row-`m` section built from steps that move the row
  set N : ℕ := comps.sum (fun C => baseF C 1 + m * (stepsF C).sum (fun s => s 1)) + 1 with hN
  set n₀ : ℕ := p * N + j with hn₀
  have hn₀mod : n₀ % p = j := by
    rw [hn₀, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hj
  have hNle : N ≤ n₀ := by
    have h1 : 1 * N ≤ p * N := Nat.mul_le_mul hp1 (le_refl N)
    rw [Nat.one_mul] at h1
    omega
  have hc0 : (![m, n₀, f m n₀] : Fin 3 → ℕ) 0 = m := rfl
  have hc1 : (![m, n₀, f m n₀] : Fin 3 → ℕ) 1 = n₀ := rfl
  have hc2 : (![m, n₀, f m n₀] : Fin 3 → ℕ) 2 = f m n₀ := rfl
  have hmem : (![m, n₀, f m n₀] : Fin 3 → ℕ) ∈ ⋃ C ∈ comps, C := by
    rw [← hunion]
    show f ((![m, n₀, f m n₀] : Fin 3 → ℕ) 0) ((![m, n₀, f m n₀] : Fin 3 → ℕ) 1)
        = (![m, n₀, f m n₀] : Fin 3 → ℕ) 2
    rw [hc0, hc1, hc2]
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨C, hC, hvC⟩ := hmem
  rw [hbsF C hC] at hvC
  -- the component carries a step that stays in row `m` and advances the argument
  have hlarge : baseF C 1 + (![m, n₀, f m n₀] : Fin 3 → ℕ) 0 * (stepsF C).sum (fun s => s 1)
      < (![m, n₀, f m n₀] : Fin 3 → ℕ) 1 := by
    rw [hc0, hc1]
    have h1 : baseF C 1 + m * (stepsF C).sum (fun s => s 1)
        ≤ comps.sum (fun C => baseF C 1 + m * (stepsF C).sum (fun s => s 1)) :=
      Finset.single_le_sum
        (f := fun C => baseF C 1 + m * (stepsF C).sum (fun s => s 1))
        (fun _ _ => Nat.zero_le _) hC
    omega
  obtain ⟨s₀, hs₀, hs₀0, hs₀1⟩ := exists_free_step hvC hlarge
  have hu : s₀ 1 ∣ p := hdvd C hC s₀ hs₀ (by omega)
  have hqu : p / s₀ 1 * s₀ 1 = p := Nat.div_mul_cancel hu
  refine ⟨n₀, f m n₀, p / s₀ 1 * s₀ 2, hn₀mod, fun k => ?_⟩
  have hmemk : (fun i => (![m, n₀, f m n₀] : Fin 3 → ℕ) i + p / s₀ 1 * k * s₀ i)
      ∈ LinearSet 3 (baseF C) (stepsF C) := linearSet_add_step hvC hs₀ _
  have hmemS : f ((![m, n₀, f m n₀] : Fin 3 → ℕ) 0 + p / s₀ 1 * k * s₀ 0)
      ((![m, n₀, f m n₀] : Fin 3 → ℕ) 1 + p / s₀ 1 * k * s₀ 1)
      = (![m, n₀, f m n₀] : Fin 3 → ℕ) 2 + p / s₀ 1 * k * s₀ 2 := by
    have h1 : (fun i => (![m, n₀, f m n₀] : Fin 3 → ℕ) i + p / s₀ 1 * k * s₀ i)
        ∈ ⋃ C ∈ comps, C :=
      Set.mem_iUnion₂.mpr ⟨C, hC, by rw [hbsF C hC]; exact hmemk⟩
    rw [← hunion] at h1
    exact h1
  rw [hc0, hc1, hc2] at hmemS
  have erow : m + p / s₀ 1 * k * s₀ 0 = m := by rw [hs₀0]; ring
  have earg : n₀ + p / s₀ 1 * k * s₀ 1 = n₀ + p * k := by rw [mul_right_comm, hqu]
  have eval : f m n₀ + p / s₀ 1 * k * s₀ 2 = f m n₀ + k * (p / s₀ 1 * s₀ 2) := by ring
  rw [erow, earg, eval] at hmemS
  exact hmemS

end SemilinearGraphAffine

/-- A semilinear function graph in `ℕ²` is eventually affine on residue classes. -/
theorem semilinearGraph_affineOnResiduesAt
    (f : ℕ → ℕ) (hS : IsSemilinearNd 2 {v : Fin 2 → ℕ | f (v 0) = v 1}) :
    ∃ p : ℕ, 1 ≤ p ∧ SlicePeriodStar.AffineOnResiduesAt p f := by
  have hsel : Function.Injective (![1, 2] : Fin 2 → Fin 3) := by decide
  have h3 : IsSemilinearNd 3 {v : Fin 3 → ℕ | (fun _ n => f n) (v 0) (v 1) = v 2} :=
    SliceSemilinearN.isSemilinearNd_comap_injective (![1, 2] : Fin 2 → Fin 3) hsel hS
  obtain ⟨p, hp, hall⟩ := SemilinearGraphAffine.graph3_uniform (fun _ n => f n) h3
  exact ⟨p, hp, hall 0⟩

/-- A semilinear function graph in `ℕ³`, viewed as a family of rows indexed by the
first coordinate, has eventually-affine rows with a period uniform in the row. -/
theorem semilinearGraph3_affineOnResiduesAt_uniform
    (f : ℕ → ℕ → ℕ) (hS : IsSemilinearNd 3 {v : Fin 3 → ℕ | f (v 0) (v 1) = v 2}) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ m : ℕ, SlicePeriodStar.AffineOnResiduesAt p (fun n => f m n) :=
  SemilinearGraphAffine.graph3_uniform f hS
