/-
# Unique representation for proper linear sets

A *proper* linear set is a coset `a +ᵥ closure t` of a finitely generated additive submonoid
whose generators (periods) `t` are linearly independent over `ℕ`
(`IsProperLinearSet` in Mathlib).  Linear independence makes the coefficient tuple of a point
unique, so the points of a proper linear set are in bijection with the coefficient tuples
`t → ℕ`.  This file supplies that bijection, its counting corollary, and one consequence:
a period whose parameter part vanishes forces an infinite parameter-fibre.
-/
import Mathlib

namespace ProperLinearRep

open Set Pointwise AddSubmonoid

variable {M : Type*} [AddCommMonoid M]

/-- The coefficient-evaluation map of a finite set of periods: a coefficient tuple
`l : t → ℕ` is sent to the combination `∑ s ∈ t, l s • s`. -/
def periodSum (t : Finset M) (l : t → ℕ) : M := ∑ s : t, l s • (s : M)

theorem periodSum_apply (t : Finset M) (l : t → ℕ) :
    periodSum t l = ∑ s : t, l s • (s : M) := rfl

/-- The coefficient tuple that selects a single period `u ∈ t` with multiplicity `n`. -/
noncomputable def singleCoeff {t : Finset M} {u : M} (hu : u ∈ t) (n : ℕ) : t → ℕ := by
  classical
  exact fun v => if v = ⟨u, hu⟩ then n else 0

omit [AddCommMonoid M] in
@[simp]
theorem singleCoeff_self {t : Finset M} {u : M} (hu : u ∈ t) (n : ℕ) :
    singleCoeff hu n ⟨u, hu⟩ = n := by
  classical
  simp [singleCoeff]

omit [AddCommMonoid M] in
theorem singleCoeff_of_ne {t : Finset M} {u : M} (hu : u ∈ t) (n : ℕ) {v : t}
    (hv : v ≠ ⟨u, hu⟩) : singleCoeff hu n v = 0 := by
  classical
  simp [singleCoeff, hv]

theorem periodSum_singleCoeff {t : Finset M} {u : M} (hu : u ∈ t) (n : ℕ) :
    periodSum t (singleCoeff hu n) = n • u := by
  rw [periodSum_apply, Finset.sum_eq_single_of_mem (⟨u, hu⟩ : t) (Finset.mem_univ _)]
  · simp
  · intro v _ hv
    simp [singleCoeff_of_ne hu n hv]

/-! ## 1. Unique representation -/

/-- **Unique representation.** If the periods `t` are linearly independent over `ℕ`, the
coefficient-evaluation map `l ↦ ∑ s ∈ t, l s • s` is injective. -/
theorem periodSum_injective {t : Finset M} (ht : LinearIndepOn ℕ id (t : Set M)) :
    Function.Injective (periodSum t) := by
  classical
  intro l₁ l₂ h
  have key := linearIndepOn_finset_iffₛ.1 ht
  set f₁ : M → ℕ := fun x => if hx : x ∈ t then l₁ ⟨x, hx⟩ else 0 with hf₁
  set f₂ : M → ℕ := fun x => if hx : x ∈ t then l₂ ⟨x, hx⟩ else 0 with hf₂
  have hsum : ∀ (l : t → ℕ) (f : M → ℕ), (∀ x (hx : x ∈ t), f x = l ⟨x, hx⟩) →
      ∑ x ∈ t, f x • id x = periodSum t l := by
    intro l f hf
    rw [periodSum_apply, Finset.univ_eq_attach, ← Finset.sum_attach t (fun x => f x • id x)]
    exact Finset.sum_congr rfl fun x _ => by simp [hf x.1 x.2]
  have h₁ : ∑ x ∈ t, f₁ x • id x = periodSum t l₁ := hsum l₁ f₁ (by intro x hx; simp [hf₁, hx])
  have h₂ : ∑ x ∈ t, f₂ x • id x = periodSum t l₂ := hsum l₂ f₂ (by intro x hx; simp [hf₂, hx])
  have := key f₁ f₂ (by rw [h₁, h₂, h])
  funext x
  have hx := this x.1 x.2
  simpa [hf₁, hf₂, x.2] using hx

/-! ## 2. Membership characterisation -/

/-- **Membership in a linear set.** A point lies in `a +ᵥ closure t` exactly when it is
`a` plus a combination of the periods with natural coefficients. -/
theorem mem_vadd_closure_iff (a : M) (t : Finset M) (x : M) :
    x ∈ a +ᵥ (closure (t : Set M) : Set M) ↔ ∃ l : t → ℕ, x = a + periodSum t l := by
  simp only [Set.mem_vadd_set, SetLike.mem_coe, AddSubmonoid.mem_closure_finset',
    vadd_eq_add, periodSum_apply]
  constructor
  · rintro ⟨y, ⟨l, rfl⟩, rfl⟩
    exact ⟨l, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨_, ⟨l, rfl⟩, rfl⟩

/-! ## 3. The bijection -/

variable [IsCancelAdd M]

/-- The coefficient map of a *proper* linear set is injective. -/
theorem vadd_periodSum_injective (a : M) {t : Finset M} (ht : LinearIndepOn ℕ id (t : Set M)) :
    Function.Injective (fun l : t → ℕ => a + periodSum t l) := fun _ _ h =>
  periodSum_injective ht (add_left_cancel h)

/-- **Points of a proper linear set are in bijection with coefficient tuples.** -/
noncomputable def properLinearEquiv (a : M) (t : Finset M)
    (ht : LinearIndepOn ℕ id (t : Set M)) :
    (t → ℕ) ≃ (a +ᵥ (closure (t : Set M) : Set M) : Set M) :=
  Equiv.ofBijective
    (fun l => ⟨a + periodSum t l, (mem_vadd_closure_iff a t _).2 ⟨l, rfl⟩⟩)
    ⟨fun _ _ h => vadd_periodSum_injective a ht (congrArg Subtype.val h),
      by
        rintro ⟨x, hx⟩
        obtain ⟨l, rfl⟩ := (mem_vadd_closure_iff a t x).1 hx
        exact ⟨l, rfl⟩⟩

@[simp]
theorem properLinearEquiv_apply (a : M) (t : Finset M) (ht : LinearIndepOn ℕ id (t : Set M))
    (l : t → ℕ) : (properLinearEquiv a t ht l : M) = a + periodSum t l := rfl

/-- **Counting form of the bijection.** For a proper linear set `a +ᵥ closure t` and any
predicate `P`, the points of the set satisfying `P` are equinumerous with the coefficient
tuples whose combination satisfies `P`.  Taking `P` to be "the parameter part equals `x`"
turns a fibre count into a count of coefficient tuples. -/
theorem card_sep_eq_card_coeffs (a : M) (t : Finset M)
    (ht : LinearIndepOn ℕ id (t : Set M)) (P : M → Prop) :
    Nat.card {x : M | x ∈ a +ᵥ (closure (t : Set M) : Set M) ∧ P x}
      = Nat.card {l : t → ℕ | P (a + periodSum t l)} := by
  refine Nat.card_congr (Equiv.symm (Equiv.ofBijective
    (fun l : {l : t → ℕ | P (a + periodSum t l)} =>
      (⟨a + periodSum t l.1, ⟨(mem_vadd_closure_iff a t _).2 ⟨l.1, rfl⟩, l.2⟩⟩ :
        {x : M | x ∈ a +ᵥ (closure (t : Set M) : Set M) ∧ P x})) ⟨?_, ?_⟩))
  · rintro ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h
    exact Subtype.ext (vadd_periodSum_injective a ht (congrArg Subtype.val h))
  · rintro ⟨x, hx, hPx⟩
    obtain ⟨l, rfl⟩ := (mem_vadd_closure_iff a t x).1 hx
    exact ⟨⟨l, hPx⟩, rfl⟩

/-- The intersection form of `card_sep_eq_card_coeffs`. -/
theorem card_inter_eq_card_coeffs (a : M) (t : Finset M)
    (ht : LinearIndepOn ℕ id (t : Set M)) (s : Set M) :
    Nat.card ↥((a +ᵥ (closure (t : Set M) : Set M) : Set M) ∩ s)
      = Nat.card {l : t → ℕ | a + periodSum t l ∈ s} :=
  card_sep_eq_card_coeffs a t ht (· ∈ s)

/-! ## 4. Periods must move the parameter -/

section Periods

variable {ι κ : Type*}

/-- **Periods move the parameter.**  If a proper linear set `a +ᵥ closure t` is contained in
a set all of whose parameter-fibres (fibres of `w ↦ w ∘ Sum.inl`) are finite, then every
period `u ∈ t` has a nonzero parameter part: otherwise raising the coefficient of `u` produces
infinitely many distinct points of one fibre. -/
theorem exists_inl_ne_zero_of_mem_periods {s : Set (ι ⊕ κ → ℕ)}
    (hfin : ∀ x : ι → ℕ, Set.Finite {w | w ∈ s ∧ w ∘ Sum.inl = x})
    {a : ι ⊕ κ → ℕ} {t : Finset (ι ⊕ κ → ℕ)}
    (ht : LinearIndepOn ℕ id (t : Set (ι ⊕ κ → ℕ)))
    (hsub : (a +ᵥ (AddSubmonoid.closure (t : Set (ι ⊕ κ → ℕ)) : Set (ι ⊕ κ → ℕ))) ⊆ s)
    {u : ι ⊕ κ → ℕ} (hu : u ∈ t) :
    ∃ i, u (Sum.inl i) ≠ 0 := by
  by_contra hcon
  have hzero : ∀ i, u (Sum.inl i) = 0 := by
    intro i
    by_contra hi
    exact hcon ⟨i, hi⟩
  set g : ℕ → (ι ⊕ κ → ℕ) := fun n => a + n • u with hg
  have hginj : Function.Injective g := by
    intro n m hnm
    have h1 : a + periodSum t (singleCoeff hu n) = a + periodSum t (singleCoeff hu m) := by
      simpa [hg, periodSum_singleCoeff] using hnm
    simpa using congrFun (vadd_periodSum_injective a ht h1) (⟨u, hu⟩ : t)
  have hmem : ∀ n : ℕ, g n ∈ {w | w ∈ s ∧ w ∘ Sum.inl = a ∘ Sum.inl} := by
    intro n
    refine ⟨hsub ((mem_vadd_closure_iff a t (g n)).2
      ⟨singleCoeff hu n, by simp [hg, periodSum_singleCoeff]⟩), ?_⟩
    funext i
    simp [hg, hzero i]
  exact absurd (Set.infinite_of_injective_forall_mem hginj hmem) (hfin _).not_infinite

/-- Fibre finiteness transfers from a relation to its graph packed as `ι ⊕ κ → ℕ`, which is
the hypothesis shape `exists_inl_ne_zero_of_mem_periods` consumes. -/
theorem finite_fibre_of_finite {R : (ι → ℕ) → (κ → ℕ) → Prop}
    (hfin : ∀ x : ι → ℕ, Set.Finite {y : κ → ℕ | R x y}) (x : ι → ℕ) :
    Set.Finite {w : ι ⊕ κ → ℕ | w ∈ {w | R (w ∘ Sum.inl) (w ∘ Sum.inr)} ∧ w ∘ Sum.inl = x} := by
  have hinj : Set.InjOn (fun w : ι ⊕ κ → ℕ => w ∘ Sum.inr)
      {w : ι ⊕ κ → ℕ | w ∈ {w | R (w ∘ Sum.inl) (w ∘ Sum.inr)} ∧ w ∘ Sum.inl = x} := by
    intro w₁ h₁ w₂ h₂ h
    funext j
    cases j with
    | inl i => exact congrFun (h₁.2.trans h₂.2.symm) i
    | inr j => exact congrFun h j
  refine Set.Finite.of_finite_image (Set.Finite.subset (hfin x) ?_) hinj
  rintro y ⟨w, ⟨hw, hwx⟩, rfl⟩
  simpa [hwx] using hw

end Periods

end ProperLinearRep
