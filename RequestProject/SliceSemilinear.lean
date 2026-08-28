/-
# A semilinear-sets toolkit for `thm:wrp-slice-semilinearity`

Reusable closure lemmas for `IsSemilinear2` (singletons, finite unions) and the
key building block: the graph of an **affine sequence over an arithmetic
progression** `k ↦ (A(n₀+pk)+B, C(n₀+pk)+D)` is semilinear.  These are the atoms
of the §7 reduction: on the wrapped-flat slice the first-ascent profile is, by
the paper's one-loop slice analysis, *affine on residue classes of `n`*, and an
affine-on-residues function has a semilinear graph.
-/
import RequestProject.Semilinearity
import RequestProject.SliceAutomata

namespace SliceSemilinear

/-- Finite unions of semilinear sets are semilinear (any dimension). -/
theorem isSemilinearNd_union {d : ℕ} {S T : Set (Fin d → ℕ)}
    (hS : IsSemilinearNd d S) (hT : IsSemilinearNd d T) : IsSemilinearNd d (S ∪ T) := by
  classical
  obtain ⟨cs, hcs, hScs⟩ := hS
  obtain ⟨ct, hct, hTct⟩ := hT
  refine ⟨cs ∪ ct, fun C hC => ?_, ?_⟩
  · rcases Finset.mem_union.mp hC with h | h
    · exact hcs C h
    · exact hct C h
  · rw [hScs, hTct]; ext v
    simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_union, exists_prop]
    constructor
    · rintro (⟨i, hi, hv⟩ | ⟨i, hi, hv⟩)
      · exact ⟨i, Or.inl hi, hv⟩
      · exact ⟨i, Or.inr hi, hv⟩
    · rintro ⟨i, (hi | hi), hv⟩
      · exact Or.inl ⟨i, hi, hv⟩
      · exact Or.inr ⟨i, hi, hv⟩

/-- A singleton in `ℕ²` is semilinear. -/
theorem isSemilinear2_singleton (x y : ℕ) : IsSemilinear2 {(x, y)} := by
  refine ⟨{LinearSet 2 ![x, y] ∅}, fun C hC => ?_, ?_⟩
  · rw [Finset.mem_singleton] at hC; exact ⟨![x, y], ∅, hC⟩
  · ext v
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_iUnion,
      Finset.mem_singleton, exists_prop, exists_eq_left, LinearSet, Finset.sum_empty, add_zero]
    constructor
    · rintro ⟨h0, h1⟩
      refine ⟨fun _ => 0, ?_⟩
      funext i; fin_cases i <;> simp [h0, h1]
    · rintro ⟨_, hv⟩
      refine ⟨?_, ?_⟩
      · have := congrFun hv 0; simpa using this
      · have := congrFun hv 1; simpa using this

/-- The graph of an affine sequence over an arithmetic progression,
`{(A(n₀+pk)+B, C(n₀+pk)+D) : k ∈ ℕ}`, is semilinear. -/
theorem isSemilinear2_arithProg (A B C D n₀ p : ℕ) :
    IsSemilinear2 {q : ℕ × ℕ | ∃ k : ℕ,
      q = (A * (n₀ + p * k) + B, C * (n₀ + p * k) + D)} := by
  refine ⟨{LinearSet 2 ![A * n₀ + B, C * n₀ + D] {![A * p, C * p]}}, fun Cc hC => ?_, ?_⟩
  · rw [Finset.mem_singleton] at hC; exact ⟨_, _, hC⟩
  · ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_singleton, exists_prop,
      exists_eq_left, LinearSet, Finset.sum_singleton]
    constructor
    · rintro ⟨k, hk⟩
      have hv0 : v 0 = A * (n₀ + p * k) + B := congrArg Prod.fst hk
      have hv1 : v 1 = C * (n₀ + p * k) + D := congrArg Prod.snd hk
      refine ⟨fun _ => k, ?_⟩
      funext i
      fin_cases i <;>
        simp only [Fin.mk_zero, Fin.mk_one, hv0, hv1, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
    · rintro ⟨coeffs, hv⟩
      refine ⟨coeffs ![A * p, C * p], ?_⟩
      have h0 := congrFun hv 0
      have h1 := congrFun hv 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      rw [Prod.ext_iff]
      exact ⟨by simp only [h0]; ring, by simp only [h1]; ring⟩

/-- Rewriting helper for `IsSemilinear2`. -/
theorem isSemilinear2_congr {S T : Set (ℕ × ℕ)} (h : S = T) (hS : IsSemilinear2 S) :
    IsSemilinear2 T := h ▸ hS

theorem isSemilinear2_union {S T : Set (ℕ × ℕ)} (hS : IsSemilinear2 S) (hT : IsSemilinear2 T) :
    IsSemilinear2 (S ∪ T) :=
  isSemilinearNd_union hS hT

/-- The empty set is semilinear. -/
theorem isSemilinear2_empty : IsSemilinear2 (∅ : Set (ℕ × ℕ)) := by
  refine ⟨∅, fun C hC => absurd hC (Finset.notMem_empty C), ?_⟩
  simp

/-- A finite indexed union of semilinear subsets of `ℕ²` is semilinear. -/
theorem isSemilinear2_biUnion {ι : Type*} (s : Finset ι) (f : ι → Set (ℕ × ℕ))
    (h : ∀ i ∈ s, IsSemilinear2 (f i)) : IsSemilinear2 (⋃ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isSemilinear2_empty
  | insert a s ha ih =>
      rw [Finset.set_biUnion_insert]
      exact isSemilinear2_union (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **The §7 counting kernel.**  A pair-valued function `g` that is, beyond a
threshold `n₀ ≥ 1`, *jointly affine on each residue class mod `p`* has a
semilinear graph over `n ≥ 1`.  This is the proved bridge from the paper's
slice-affineness conclusion to `thm:wrp-slice-semilinearity`. -/
theorem isSemilinear2_of_affineOnResidues (g : ℕ → ℕ × ℕ) (p n₀ : ℕ)
    (hp : 1 ≤ p) (hn₀ : 1 ≤ n₀)
    (haff : ∀ r : Fin p, ∃ a b c d : ℕ,
      ∀ n, n₀ ≤ n → n % p = (r : ℕ) → g n = (a * n + b, c * n + d)) :
    IsSemilinear2 {q : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧ q = g n} := by
  classical
  have hsplit : {q : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧ q = g n} =
      (⋃ n ∈ Finset.Ico 1 n₀, {g n}) ∪
      (⋃ j ∈ Finset.range p, {q : ℕ × ℕ | ∃ k : ℕ, q = g (n₀ + j + p * k)}) := by
    ext q
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_Ico,
      Finset.mem_range, Set.mem_singleton_iff, exists_prop]
    constructor
    · rintro ⟨n, hn1, rfl⟩
      rcases lt_or_ge n n₀ with hlt | hge
      · exact Or.inl ⟨n, ⟨hn1, hlt⟩, rfl⟩
      · refine Or.inr ⟨(n - n₀) % p, Nat.mod_lt _ hp, (n - n₀) / p, ?_⟩
        congr 1
        have := Nat.mod_add_div (n - n₀) p
        omega
    · rintro (⟨n, ⟨hn1, _⟩, rfl⟩ | ⟨j, _, k, rfl⟩)
      · exact ⟨n, hn1, rfl⟩
      · exact ⟨n₀ + j + p * k, by omega, rfl⟩
  rw [hsplit]
  apply isSemilinear2_union
  · exact isSemilinear2_biUnion _ _ (fun n _ => isSemilinear2_singleton (g n).1 (g n).2)
  · refine isSemilinear2_biUnion _ _ (fun j _ => ?_)
    obtain ⟨a, b, c, d, haffj⟩ := haff ⟨(n₀ + j) % p, Nat.mod_lt _ hp⟩
    have hpiece : {q : ℕ × ℕ | ∃ k : ℕ, q = g (n₀ + j + p * k)} =
        {q : ℕ × ℕ | ∃ k : ℕ,
          q = (a * (n₀ + j + p * k) + b, c * (n₀ + j + p * k) + d)} := by
      ext q
      simp only [Set.mem_ofPred_eq]
      have hmod : ∀ k, (n₀ + j + p * k) % p = (n₀ + j) % p := fun k =>
        Nat.add_mul_mod_self_left (n₀ + j) p k
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, haffj (n₀ + j + p * k) (by omega) (hmod k)⟩
      · rintro ⟨k, rfl⟩
        exact ⟨k, (haffj (n₀ + j + p * k) (by omega) (hmod k)).symm⟩
    rw [hpiece]
    exact isSemilinear2_arithProg a b c d (n₀ + j) p

/-- **Decomposition skeleton.**  If, beyond a threshold `m ≥ 1`, the graph of `g`
on each residue class mod `p` is semilinear (`hpiece`), then the whole graph over
`n ≥ 1` is semilinear.  Splits `{n ≥ 1}` into the finite part `[1, m)` plus the
`p` arithmetic progressions `{m + j + p·k : k}`. -/
theorem isSemilinear2_of_decomp (g : ℕ → ℕ × ℕ) (p m : ℕ) (hp : 1 ≤ p) (_hm : 1 ≤ m)
    (hpiece : ∀ j, j < p → IsSemilinear2 {q : ℕ × ℕ | ∃ k : ℕ, q = g (m + j + p * k)}) :
    IsSemilinear2 {q : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧ q = g n} := by
  classical
  have hsplit : {q : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧ q = g n} =
      (⋃ n ∈ Finset.Ico 1 m, {g n}) ∪
      (⋃ j ∈ Finset.range p, {q : ℕ × ℕ | ∃ k : ℕ, q = g (m + j + p * k)}) := by
    ext q
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_Ico,
      Finset.mem_range, Set.mem_singleton_iff, exists_prop]
    constructor
    · rintro ⟨n, hn1, rfl⟩
      rcases lt_or_ge n m with hlt | hge
      · exact Or.inl ⟨n, ⟨hn1, hlt⟩, rfl⟩
      · refine Or.inr ⟨(n - m) % p, Nat.mod_lt _ hp, (n - m) / p, ?_⟩
        congr 1
        have := Nat.mod_add_div (n - m) p
        omega
    · rintro (⟨n, ⟨hn1, _⟩, rfl⟩ | ⟨j, _, k, rfl⟩)
      · exact ⟨n, hn1, rfl⟩
      · exact ⟨m + j + p * k, by omega, rfl⟩
  rw [hsplit]
  exact isSemilinear2_union
    (isSemilinear2_biUnion _ _ (fun n _ => isSemilinear2_singleton (g n).1 (g n).2))
    (isSemilinear2_biUnion _ _ (fun j hj => hpiece j (Finset.mem_range.mp hj)))

/-- **The §7 counting kernel (faithful, period-index form).**  If, beyond a
threshold `m ≥ 1` and on each residue class `j` mod `p`, the pair `g(m + j + p·k)`
is affine in the period index `k` (`= (b₁ + k·s₁, b₂ + k·s₂)`), then the graph of
`g` over `n ≥ 1` is semilinear.  This is the form a bounded count actually takes
(the per-class slope `step/p` need not be an integer), and matches the output of
`SliceAutomata.recurrence_affineOnResidues`. -/
theorem isSemilinear2_of_affineInPeriod (g : ℕ → ℕ × ℕ) (p m : ℕ) (hp : 1 ≤ p) (hm : 1 ≤ m)
    (haff : ∀ j, j < p → ∃ b₁ s₁ b₂ s₂ : ℕ,
      ∀ k, g (m + j + p * k) = (b₁ + k * s₁, b₂ + k * s₂)) :
    IsSemilinear2 {q : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧ q = g n} := by
  refine isSemilinear2_of_decomp g p m hp hm (fun j hj => ?_)
  obtain ⟨b₁, s₁, b₂, s₂, hbs⟩ := haff j hj
  have hpiece : {q : ℕ × ℕ | ∃ k : ℕ, q = g (m + j + p * k)} =
      {q : ℕ × ℕ | ∃ k : ℕ, q = (s₁ * (0 + 1 * k) + b₁, s₂ * (0 + 1 * k) + b₂)} := by
    ext q
    simp only [Set.mem_ofPred_eq]
    constructor <;> rintro ⟨k, rfl⟩ <;>
      exact ⟨k, by rw [hbs k, Prod.ext_iff]; constructor <;> ring⟩
  rw [hpiece]
  exact isSemilinear2_arithProg s₁ b₁ s₂ b₂ 0 1

/-- **Bounded counting (paper `lem:presburger-counting`), fully proved for the slice.**  If the
two statistics `fas`/`tailU` are partial sums of *eventually-periodic increment*
sequences (`incFas`, `incTailU`, common period `p` from threshold `m`), then their
joint profile `{(Σ_{i<n} incFas, Σ_{i<n} incTailU) : n ≥ 1}` is semilinear.  No
counting axiom is needed: the per-period increments make each statistic affine in
the period index (`recurrence_affineOnResidues`), which the kernel
`isSemilinear2_of_affineInPeriod` turns into semilinearity. -/
theorem count_pair_semilinear (incFas incTailU : ℕ → ℕ) (p m : ℕ) (hp : 1 ≤ p) (hm : 1 ≤ m)
    (hFas : ∀ i, m ≤ i → incFas (i + p) = incFas i)
    (hTailU : ∀ i, m ≤ i → incTailU (i + p) = incTailU i) :
    IsSemilinear2 {q : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧
      q = ((Finset.range n).sum incFas, (Finset.range n).sum incTailU)} := by
  refine isSemilinear2_of_affineInPeriod
    (fun n => ((Finset.range n).sum incFas, (Finset.range n).sum incTailU)) p m hp hm
    (fun j _ => ?_)
  refine ⟨(Finset.range (m + j)).sum incFas, (Finset.Ico m (m + p)).sum incFas,
    (Finset.range (m + j)).sum incTailU, (Finset.Ico m (m + p)).sum incTailU, fun k => ?_⟩
  have hf := SliceAutomata.recurrence_affineOnResidues (fun n => (Finset.range n).sum incFas)
    m p ((Finset.Ico m (m + p)).sum incFas)
    (SliceAutomata.partialSum_recurrence' incFas m p hFas) k j
  have ht := SliceAutomata.recurrence_affineOnResidues (fun n => (Finset.range n).sum incTailU)
    m p ((Finset.Ico m (m + p)).sum incTailU)
    (SliceAutomata.partialSum_recurrence' incTailU m p hTailU) k j
  simp only [smul_eq_mul] at hf ht
  rw [show m + j + p * k = m + p * k + j from by ring]
  exact Prod.ext hf ht

end SliceSemilinear
