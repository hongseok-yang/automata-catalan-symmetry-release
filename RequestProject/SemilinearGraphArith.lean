/-
# Signed arithmetic on functions with semilinear graphs

Functions `ℕ^p → ℕ` whose graph `{(x, f x)} ⊆ ℕ^(p+1)` is semilinear are closed under fixed
signed combinations: if `g` satisfies one ℕ-linear identity
`g x + ∑_{i ∈ t} f i x = ∑_{i ∈ s} f i x` against finitely many such `f i`, then `g` has a
semilinear graph too.  This is the closure property an inclusion–exclusion computation of a
cardinality needs, the subtractions being phrased additively so that no truncated ℕ-subtraction
appears.

The proof is the working idiom of `SemilinearMinMax.lean`: the graph is described by a
first-order formula over `(ℕ, 0, 1, +)` that existentially quantifies the values `n i = f i x`,
conjoins the (semilinear, hence Presburger-definable) graph conditions and one linear equation,
and is transported back through Mathlib's Ginsburg–Spanier bridge
`FirstOrder.Language.presburger.definable_iff_isSemilinearSet`.  Only the existential
quantifier is taken by hand, through `IsSemilinearSet.proj`.

## Main results

* `isSemilinearSet_affine_eq`, `isSemilinearSet_forms_eq`: one inhomogeneous (resp. homogeneous)
  ℕ-linear equation between coordinate forms cuts out a semilinear set.
* `isSemilinearSet_comap`: semilinearity transports along an arbitrary reindexing of
  coordinates, not merely a bijective one.
* `isSemilinearSet_graph_signed`: the signed combination, in the `Finset` packaging
  (positive part `s`, negative part `t`); `isSemilinearSet_graph_signedBool` is the
  sign-function packaging.
* `isSemilinearSet_graph_sum`, `isSemilinearSet_graph_add`, `isSemilinearSet_graph_sub`:
  the unsigned sum over a `Finset`, and the two binary cases.
* `isSemilinearSet_graph_signedAffine`: the signed combination with a constant offset on
  each side of the identity.
* `isSemilinearSet_graph_congr`, `isSemilinearSet_graph_const`, `isSemilinearSet_graph_coord`:
  the degenerate inputs — a function equal to one with a semilinear graph, a constant, a
  coordinate projection.

Graphs are packed as in `PresburgerCounting.count_graph_semilinear`: the arguments sit on
`Fin.castSucc` and the value on `Fin.last p`.

No `sorry`, no new axiom.
-/
import RequestProject.SemilinearMinMax

namespace SemilinearGraphArith

open Set FirstOrder Language

/-! ## Atoms: linear equations and coordinate reindexing -/

section Atoms

/-- An inhomogeneous ℕ-linear equation between two affine forms in the coordinates cuts out a
semilinear set. -/
theorem isSemilinearSet_affine_eq {γ : Type*} [Fintype γ] (c d : ℕ) (a b : γ → ℕ) :
    IsSemilinearSet {x : γ → ℕ | c + ∑ i, a i * x i = d + ∑ i, b i * x i} := by
  have h := Nat.isSemilinearSet_setOfPred_mulVec_eq (ι := Fin 1) (κ := γ)
    ![c] ![d] (Matrix.of fun (_ : Fin 1) i => a i) (Matrix.of fun (_ : Fin 1) i => b i)
  convert h using 1
  ext x
  simp [funext_iff, Matrix.mulVec, Matrix.vecHead, dotProduct]

/-- A homogeneous ℕ-linear equation between two linear forms in the coordinates cuts out a
semilinear set. -/
theorem isSemilinearSet_forms_eq {γ : Type*} [Fintype γ] (a b : γ → ℕ) :
    IsSemilinearSet {x : γ → ℕ | ∑ i, a i * x i = ∑ i, b i * x i} := by
  have h := isSemilinearSet_affine_eq (γ := γ) 0 0 a b
  convert h using 1
  ext x
  simp

/-- **Coordinate reindexing.**  Semilinearity is preserved by pulling back along an arbitrary
map `σ` of index types; injectivity of `σ` is not needed.  This is
`Set.Definable.preimage_comp` transported through the Ginsburg–Spanier bridge. -/
theorem isSemilinearSet_comap {α β : Type*} [Finite α] [Finite β] (σ : α → β)
    {S : Set (α → ℕ)} (hS : IsSemilinearSet S) :
    IsSemilinearSet {u : β → ℕ | (fun i => u (σ i)) ∈ S} := by
  rw [← presburger.definable_iff_isSemilinearSet (A := (∅ : Set ℕ))]
  exact (hS.definable (A := (∅ : Set ℕ))).preimage_comp σ

end Atoms

/-! ## The signed combination -/

section Signed

variable {p : ℕ} {ι : Type*} [Fintype ι]

/-- The one linear equation of the signed combination, read in the extended index type
`Fin (p+1) ⊕ ι`: the value coordinate plus the negative block equals the positive block. -/
private theorem isSemilinearSet_signEqn (s t : Finset ι) :
    IsSemilinearSet {u : Fin (p + 1) ⊕ ι → ℕ |
      u (Sum.inl (Fin.last p)) + ∑ i ∈ t, u (Sum.inr i) = ∑ i ∈ s, u (Sum.inr i)} := by
  classical
  have h := isSemilinearSet_forms_eq (γ := Fin (p + 1) ⊕ ι)
    (Sum.elim (fun k => if k = Fin.last p then 1 else 0) (fun i => if i ∈ t then 1 else 0))
    (Sum.elim (fun _ => 0) (fun i => if i ∈ s then 1 else 0))
  convert h using 1
  ext u
  simp [Fintype.sum_sum_type, ite_mul, Finset.sum_ite_mem]

/-- **Signed combinations preserve semilinear graphs.**

Let each `f i : ℕ^p → ℕ` have a semilinear graph and let `g` satisfy the single ℕ-linear
identity `g x + ∑_{i ∈ t} f i x = ∑_{i ∈ s} f i x` for all `x` (the negative part `t`
appearing on the left, so that no truncated subtraction is involved).  Then `g` has a
semilinear graph.

The graph of `g` is cut out of `ℕ^(p+1)` by the formula obtained from the auxiliary set in
`ℕ^(p+1) × ℕ^ι` that pins the extra coordinates to the values `f i x` and imposes the linear
identity; the extra coordinates are then projected away. -/
theorem isSemilinearSet_graph_signed (f : ι → (Fin p → ℕ) → ℕ)
    (hf : ∀ i, IsSemilinearSet
      {z : Fin (p + 1) → ℕ | f i (fun j => z j.castSucc) = z (Fin.last p)})
    (s t : Finset ι) (g : (Fin p → ℕ) → ℕ)
    (hg : ∀ x, g x + ∑ i ∈ t, f i x = ∑ i ∈ s, f i x) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ | g (fun j => z j.castSucc) = z (Fin.last p)} := by
  classical
  -- Each graph condition, read in the extended index type.
  have hA : ∀ i : ι, IsSemilinearSet {u : Fin (p + 1) ⊕ ι → ℕ |
      f i (fun j => u (Sum.inl j.castSucc)) = u (Sum.inr i)} := by
    intro i
    have h := isSemilinearSet_comap
      (σ := fun k : Fin (p + 1) =>
        if k = Fin.last p then (Sum.inr i : Fin (p + 1) ⊕ ι) else Sum.inl k) (hf i)
    convert h using 1
    ext u
    -- `j.castSucc ≠ Fin.last p` resolves the branch on the argument coordinates
    simp
  -- Their finite conjunction.
  have hAll : IsSemilinearSet {u : Fin (p + 1) ⊕ ι → ℕ |
      ∀ i : ι, f i (fun j => u (Sum.inl j.castSucc)) = u (Sum.inr i)} := by
    rw [← presburger.definable_iff_isSemilinearSet (A := (∅ : Set ℕ))]
    have h := Set.definable_iInter_of_finite
      (fun i : ι => (hA i).definable (A := (∅ : Set ℕ)))
    convert h using 1
    ext u
    simp [Set.mem_iInter]
  have hproj := (hAll.inter (isSemilinearSet_signEqn (p := p) s t)).proj
  convert hproj using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro hz
    refine ⟨fun i => f i (fun j => z j.castSucc), fun i => rfl, ?_⟩
    rw [← hz]
    exact hg _
  · rintro ⟨y, hy1, hy2⟩
    have hy : ∀ i, y i = f i (fun j => z j.castSucc) := fun i => (hy1 i).symm
    rw [Finset.sum_congr rfl fun i _ => hy i, Finset.sum_congr rfl fun i _ => hy i] at hy2
    have hgz := hg (fun j => z j.castSucc)
    omega

/-- **Signed combinations, sign-function packaging.**  The signs are given by `ε : ι → Bool`:
`g` plus the `false`-block equals the `true`-block. -/
theorem isSemilinearSet_graph_signedBool (f : ι → (Fin p → ℕ) → ℕ)
    (hf : ∀ i, IsSemilinearSet
      {z : Fin (p + 1) → ℕ | f i (fun j => z j.castSucc) = z (Fin.last p)})
    (ε : ι → Bool) (g : (Fin p → ℕ) → ℕ)
    (hg : ∀ x, g x + ∑ i ∈ Finset.univ.filter (fun i => ε i = false), f i x
      = ∑ i ∈ Finset.univ.filter (fun i => ε i = true), f i x) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ | g (fun j => z j.castSucc) = z (Fin.last p)} :=
  isSemilinearSet_graph_signed f hf (Finset.univ.filter (fun i => ε i = true))
    (Finset.univ.filter (fun i => ε i = false)) g hg

/-- **Plain sums preserve semilinear graphs.**  The unsigned case `t = ∅` of
`isSemilinearSet_graph_signed`. -/
theorem isSemilinearSet_graph_sum (f : ι → (Fin p → ℕ) → ℕ)
    (hf : ∀ i, IsSemilinearSet
      {z : Fin (p + 1) → ℕ | f i (fun j => z j.castSucc) = z (Fin.last p)})
    (s : Finset ι) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ |
      (∑ i ∈ s, f i (fun j => z j.castSucc)) = z (Fin.last p)} :=
  isSemilinearSet_graph_signed f hf s ∅ (fun x => ∑ i ∈ s, f i x) (by simp)

/-- The plain sum with an explicitly named value function. -/
theorem isSemilinearSet_graph_sum' (f : ι → (Fin p → ℕ) → ℕ)
    (hf : ∀ i, IsSemilinearSet
      {z : Fin (p + 1) → ℕ | f i (fun j => z j.castSucc) = z (Fin.last p)})
    (s : Finset ι) (g : (Fin p → ℕ) → ℕ) (hg : ∀ x, g x = ∑ i ∈ s, f i x) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ | g (fun j => z j.castSucc) = z (Fin.last p)} :=
  isSemilinearSet_graph_signed f hf s ∅ g (by simp [hg])

end Signed

/-! ## Degenerate and binary cases -/

section Small

variable {p : ℕ}

/-- **Congruence.**  A function pointwise equal to one with a semilinear graph has a semilinear
graph. -/
theorem isSemilinearSet_graph_congr {f g : (Fin p → ℕ) → ℕ} (h : ∀ x, f x = g x)
    (hf : IsSemilinearSet
      {z : Fin (p + 1) → ℕ | f (fun j => z j.castSucc) = z (Fin.last p)}) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ | g (fun j => z j.castSucc) = z (Fin.last p)} := by
  convert hf using 1
  ext z
  simp only [Set.mem_ofPred_eq, h]

/-- **Constants.**  The graph of the constant function with value `c` is semilinear. -/
theorem isSemilinearSet_graph_const (c : ℕ) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ | c = z (Fin.last p)} := by
  classical
  have h := isSemilinearSet_affine_eq (γ := Fin (p + 1)) c 0
    (fun _ => 0) (fun k => if k = Fin.last p then 1 else 0)
  convert h using 1
  ext z
  simp [ite_mul]

variable {f₁ f₂ g : (Fin p → ℕ) → ℕ}

/-- **Coordinate projections.**  The graph of `x ↦ x j₀` is semilinear. -/
theorem isSemilinearSet_graph_coord (j₀ : Fin p) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ | z j₀.castSucc = z (Fin.last p)} := by
  classical
  have h := isSemilinearSet_forms_eq (γ := Fin (p + 1))
    (fun k => if k = j₀.castSucc then 1 else 0) (fun k => if k = Fin.last p then 1 else 0)
  convert h using 1
  ext z
  simp [ite_mul]

private theorem pair_graphs
    (h₁ : IsSemilinearSet
      {z : Fin (p + 1) → ℕ | f₁ (fun j => z j.castSucc) = z (Fin.last p)})
    (h₂ : IsSemilinearSet
      {z : Fin (p + 1) → ℕ | f₂ (fun j => z j.castSucc) = z (Fin.last p)}) :
    ∀ i : Fin 2, IsSemilinearSet
      {z : Fin (p + 1) → ℕ | (![f₁, f₂] : Fin 2 → (Fin p → ℕ) → ℕ) i
        (fun j => z j.castSucc) = z (Fin.last p)} := by
  intro i
  fin_cases i
  · simpa using h₁
  · simpa using h₂

/-- **Binary sum.**  The graph of `f₁ + f₂` is semilinear. -/
theorem isSemilinearSet_graph_add
    (h₁ : IsSemilinearSet
      {z : Fin (p + 1) → ℕ | f₁ (fun j => z j.castSucc) = z (Fin.last p)})
    (h₂ : IsSemilinearSet
      {z : Fin (p + 1) → ℕ | f₂ (fun j => z j.castSucc) = z (Fin.last p)}) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ |
      f₁ (fun j => z j.castSucc) + f₂ (fun j => z j.castSucc) = z (Fin.last p)} := by
  refine isSemilinearSet_graph_signed (![f₁, f₂] : Fin 2 → (Fin p → ℕ) → ℕ)
    (pair_graphs h₁ h₂) {0, 1} ∅ (fun x => f₁ x + f₂ x) ?_
  intro x
  rw [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]
  simp

/-- **Binary difference.**  If `g x + f₂ x = f₁ x` for all `x` and both `f₁`, `f₂` have
semilinear graphs, so does `g`. -/
theorem isSemilinearSet_graph_sub
    (h₁ : IsSemilinearSet
      {z : Fin (p + 1) → ℕ | f₁ (fun j => z j.castSucc) = z (Fin.last p)})
    (h₂ : IsSemilinearSet
      {z : Fin (p + 1) → ℕ | f₂ (fun j => z j.castSucc) = z (Fin.last p)})
    (hg : ∀ x, g x + f₂ x = f₁ x) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ | g (fun j => z j.castSucc) = z (Fin.last p)} := by
  refine isSemilinearSet_graph_signed (![f₁, f₂] : Fin 2 → (Fin p → ℕ) → ℕ)
    (pair_graphs h₁ h₂) {0} {1} g ?_
  intro x
  simpa using hg x

end Small

variable {p : ℕ} {ι : Type*} [Fintype ι]

/-- **Signed combinations with constant offsets.**  The identity defining `g` may carry a
constant on each side: `g x + c + ∑_{i ∈ t} f i x = d + ∑_{i ∈ s} f i x`. -/
theorem isSemilinearSet_graph_signedAffine (f : ι → (Fin p → ℕ) → ℕ)
    (hf : ∀ i, IsSemilinearSet
      {z : Fin (p + 1) → ℕ | f i (fun j => z j.castSucc) = z (Fin.last p)})
    (c d : ℕ) (s t : Finset ι) (g : (Fin p → ℕ) → ℕ)
    (hg : ∀ x, g x + (c + ∑ i ∈ t, f i x) = d + ∑ i ∈ s, f i x) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ | g (fun j => z j.castSucc) = z (Fin.last p)} :=
  isSemilinearSet_graph_sub
    (f₁ := fun x => d + ∑ i ∈ s, f i x) (f₂ := fun x => c + ∑ i ∈ t, f i x)
    (isSemilinearSet_graph_add (f₁ := fun _ => d) (f₂ := fun x => ∑ i ∈ s, f i x)
      (isSemilinearSet_graph_const d) (isSemilinearSet_graph_sum f hf s))
    (isSemilinearSet_graph_add (f₁ := fun _ => c) (f₂ := fun x => ∑ i ∈ t, f i x)
      (isSemilinearSet_graph_const c) (isSemilinearSet_graph_sum f hf t))
    hg

end SemilinearGraphArith
