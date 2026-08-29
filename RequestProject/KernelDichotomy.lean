/-
# The kernel dichotomy for the parameter map of a proper linear set

A proper linear set `a +ᵥ closure t` is parametrised bijectively by coefficient tuples
`l : t → ℕ` (`ProperLinearRep`).  Splitting the ambient coordinates into a *parameter*
block and a *fibre* block, the parameter of a point depends on the coefficient tuple
through the affine map `parMap`, and two tuples share a parameter exactly when their
difference lies in the integer kernel `InKer` of the linear part.

This file proves the dichotomy that a linear bound on fibre sizes forces on that kernel:
the kernel cannot contain two independent vectors, hence is cyclic, hence every fibre is an
arithmetic progression whose direction is a single tuple fixed once and for all, and whose
length is the number of points in the fibre.

The three steps are `not_indep_of_bound` (two independent kernel vectors put quadratically
many tuples over one parameter value), `exists_kernel_generator` (a kernel with no
independent pair is cyclic) and `fibre_eq_progression` (a cyclic kernel makes each fibre a
contiguous progression).  `properLinear_fibre_progression` and `relation_fibre_progression`
transfer the conclusion from coefficient tuples to the points of the proper linear set.
-/
import RequestProject.ProperLinearRep

namespace KernelDichotomy

open Set

variable {ι n : Type} [Fintype n]

/-! ## The parameter map and its integer kernel -/

/-- Parameter part of the point built from a coefficient tuple: `b` is the parameter part of
the base point and `B s` the parameter part of the period indexed by `s`. -/
def parMap (B : n → ι → ℕ) (b : ι → ℕ) (l : n → ℕ) : ι → ℕ :=
  fun i => b i + ∑ s, l s * B s i

/-- Integer coefficient increments annihilated by the parameter parts of the periods. -/
def InKer (B : n → ι → ℕ) (d : n → ℤ) : Prop :=
  ∀ i, ∑ s, d s * (B s i : ℤ) = 0

theorem inKer_zero (B : n → ι → ℕ) : InKer B 0 := by
  intro i; simp

theorem InKer.add {B : n → ι → ℕ} {d e : n → ℤ} (hd : InKer B d) (he : InKer B e) :
    InKer B (d + e) := by
  intro i
  have : ∑ s, (d + e) s * (B s i : ℤ)
      = (∑ s, d s * (B s i : ℤ)) + ∑ s, e s * (B s i : ℤ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by simp [add_mul]
  rw [this, hd i, he i, add_zero]

theorem InKer.zsmul {B : n → ι → ℕ} {d : n → ℤ} (hd : InKer B d) (k : ℤ) :
    InKer B (fun s => k * d s) := by
  intro i
  have : ∑ s, k * d s * (B s i : ℤ) = k * ∑ s, d s * (B s i : ℤ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [this, hd i, mul_zero]

theorem InKer.neg {B : n → ι → ℕ} {d : n → ℤ} (hd : InKer B d) :
    InKer B (fun s => -d s) := by
  simpa using hd.zsmul (-1)

theorem InKer.sub {B : n → ι → ℕ} {d e : n → ℤ} (hd : InKer B d) (he : InKer B e) :
    InKer B (fun s => d s - e s) := by
  intro i
  have h := (hd.add he.neg) i
  simpa [sub_eq_add_neg] using h

/-- Casting the parameter map to `ℤ`. -/
theorem parMap_cast (B : n → ι → ℕ) (b : ι → ℕ) (l : n → ℕ) (i : ι) :
    ((parMap B b l i : ℕ) : ℤ) = (b i : ℤ) + ∑ s, (l s : ℤ) * (B s i : ℤ) := by
  simp [parMap]

/-- Two coefficient tuples with the same parameter differ by a kernel vector. -/
theorem inKer_sub_of_parMap_eq {B : n → ι → ℕ} {b : ι → ℕ} {l l' : n → ℕ}
    (h : parMap B b l = parMap B b l') :
    InKer B (fun s => (l s : ℤ) - (l' s : ℤ)) := by
  intro i
  have hc : ((parMap B b l i : ℕ) : ℤ) = ((parMap B b l' i : ℕ) : ℤ) := by
    rw [congrFun h i]
  rw [parMap_cast, parMap_cast] at hc
  have : ∑ s, ((l s : ℤ) - (l' s : ℤ)) * (B s i : ℤ)
      = (∑ s, (l s : ℤ) * (B s i : ℤ)) - ∑ s, (l' s : ℤ) * (B s i : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [this]
  omega

/-- Shifting a coefficient tuple by a kernel vector does not move the parameter. -/
theorem parMap_eq_of_shift {B : n → ι → ℕ} {b : ι → ℕ} {l l' : n → ℕ} {d : n → ℤ}
    (hd : InKer B d) (h : ∀ s, (l' s : ℤ) = (l s : ℤ) + d s) :
    parMap B b l' = parMap B b l := by
  funext i
  have hstep : ∑ s, (l' s : ℤ) * (B s i : ℤ)
      = ∑ s, (l s : ℤ) * (B s i : ℤ) := by
    have e : ∑ s, (l' s : ℤ) * (B s i : ℤ)
        = (∑ s, (l s : ℤ) * (B s i : ℤ)) + ∑ s, d s * (B s i : ℤ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by rw [h s]; ring
    rw [e, hd i, add_zero]
  have : ((parMap B b l' i : ℕ) : ℤ) = ((parMap B b l i : ℕ) : ℤ) := by
    rw [parMap_cast, parMap_cast, hstep]
  exact_mod_cast this

/-! ## The quadratic obstruction

Two independent integer kernel vectors let a single parameter value carry quadratically
many coefficient tuples, which no linear bound on fibre sizes tolerates.
-/

section Obstruction

variable [Fintype ι]

private theorem neg_mul_natAbs_le (M c : ℕ) (hc : c ≤ M) (z : ℤ) :
    -((M : ℤ) * (z.natAbs : ℤ)) ≤ (c : ℤ) * z := by
  have h0 : |(c : ℤ) * z| = (c : ℤ) * (z.natAbs : ℤ) := by
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg c), Int.abs_eq_natAbs]
  have h1 : -((c : ℤ) * (z.natAbs : ℤ)) ≤ (c : ℤ) * z := by
    rw [← h0]; exact neg_abs_le _
  have h2 : (c : ℤ) * (z.natAbs : ℤ) ≤ (M : ℤ) * (z.natAbs : ℤ) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Int.natCast_nonneg _)
  linarith

private theorem count_arith {C amax Amax Bd M q : ℕ}
    (hBd : Bd = C * (amax + 1 + Amax)) (hM : M = Bd + 1)
    (h1 : (M + 1) * (M + 1) ≤ q) (h2 : q ≤ C * (amax + M * Amax + 1)) : False := by
  have hM1 : 0 < M := by omega
  have e1 : amax + 1 ≤ (amax + 1) * M := Nat.le_mul_of_pos_right _ hM1
  have e2 : M * Amax = Amax * M := Nat.mul_comm _ _
  have key : amax + M * Amax + 1 ≤ (amax + 1 + Amax) * M := by
    calc amax + M * Amax + 1 = (amax + 1) + M * Amax := by ring
      _ ≤ (amax + 1) * M + Amax * M := Nat.add_le_add e1 (le_of_eq e2)
      _ = (amax + 1 + Amax) * M := by ring
  have h3 : q ≤ Bd * M := by
    calc q ≤ C * (amax + M * Amax + 1) := h2
      _ ≤ C * ((amax + 1 + Amax) * M) := Nat.mul_le_mul_left C key
      _ = Bd * M := by rw [hBd]; ring
  have hq : (M + 1) * (M + 1) ≤ Bd * M := le_trans h1 h3
  rw [hM] at hq
  nlinarith [hq]

/-- **The quadratic obstruction.**  Suppose every parameter fibre of the coefficient space is
finite and has at most `C * (‖x‖_∞ + 1)` elements.  Then no two integer kernel vectors are
linearly independent: independence would let one parameter value carry quadratically many
coefficient tuples. -/
theorem not_indep_of_bound {B : n → ι → ℕ} {b : ι → ℕ} {C : ℕ}
    (hfin : ∀ x : ι → ℕ, Set.Finite {l : n → ℕ | parMap B b l = x})
    (hbd : ∀ x : ι → ℕ, Nat.card {l : n → ℕ | parMap B b l = x} ≤ C * (Finset.univ.sup x + 1))
    {d₁ d₂ : n → ℤ} (h₁ : InKer B d₁) (h₂ : InKer B d₂)
    (hind : ∀ c₁ c₂ : ℤ, (∀ s, c₁ * d₁ s + c₂ * d₂ s = 0) → c₁ = 0 ∧ c₂ = 0) :
    False := by
  classical
  set w : n → ℕ := fun s => (d₁ s).natAbs + (d₂ s).natAbs with hw
  set amax : ℕ := Finset.univ.sup b with hamax
  set Amax : ℕ := Finset.univ.sup (fun i => ∑ s, w s * B s i) with hAmax
  set Bd : ℕ := C * (amax + 1 + Amax) with hBd
  set M : ℕ := Bd + 1 with hM
  -- The quadratic family of coefficient tuples.
  set L : Fin (M + 1) × Fin (M + 1) → (n → ℕ) :=
    fun p s => (((M * w s : ℕ) : ℤ) + (p.1.1 : ℤ) * d₁ s + (p.2.1 : ℤ) * d₂ s).toNat with hL
  have hcast : ∀ (p : Fin (M + 1) × Fin (M + 1)) (s : n),
      ((L p s : ℕ) : ℤ) = ((M * w s : ℕ) : ℤ) + (p.1.1 : ℤ) * d₁ s + (p.2.1 : ℤ) * d₂ s := by
    intro p s
    refine Int.toNat_of_nonneg ?_
    have b1 := neg_mul_natAbs_le M p.1.1 (Nat.lt_succ_iff.1 p.1.2) (d₁ s)
    have b2 := neg_mul_natAbs_le M p.2.1 (Nat.lt_succ_iff.1 p.2.2) (d₂ s)
    have hsplit : ((M * w s : ℕ) : ℤ)
        = (M : ℤ) * ((d₁ s).natAbs : ℤ) + (M : ℤ) * ((d₂ s).natAbs : ℤ) := by
      rw [hw]; push_cast; ring
    rw [hsplit]
    linarith
  -- All of them share one parameter value.
  set x : ι → ℕ := fun i => b i + M * (∑ s, w s * B s i) with hx
  have hpar : ∀ p, parMap B b (L p) = x := by
    intro p
    funext i
    have step : ∀ s : n, ((L p s : ℕ) : ℤ) * (B s i : ℤ)
        = (M : ℤ) * ((w s * B s i : ℕ) : ℤ)
          + ((p.1.1 : ℤ) * (d₁ s * (B s i : ℤ)) + (p.2.1 : ℤ) * (d₂ s * (B s i : ℤ))) := by
      intro s; rw [hcast p s]; push_cast; ring
    have key : ∑ s, ((L p s : ℕ) : ℤ) * (B s i : ℤ)
        = (M : ℤ) * ∑ s, ((w s * B s i : ℕ) : ℤ) := by
      rw [Finset.sum_congr rfl (fun s _ => step s), Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        h₁ i, h₂ i]
      ring
    have hz : ((parMap B b (L p) i : ℕ) : ℤ) = ((x i : ℕ) : ℤ) := by
      rw [parMap_cast, key, hx]
      push_cast
      ring
    exact_mod_cast hz
  -- Distinctness of the family.
  have hinj : Function.Injective L := by
    intro p q hpq
    have hd : ∀ s, ((p.1.1 : ℤ) - (q.1.1 : ℤ)) * d₁ s + ((p.2.1 : ℤ) - (q.2.1 : ℤ)) * d₂ s = 0 := by
      intro s
      have hs := congrFun hpq s
      have e1 := hcast p s
      have e2 := hcast q s
      rw [hs, e2] at e1
      linear_combination -e1
    obtain ⟨g1, g2⟩ := hind _ _ hd
    have i1 : p.1 = q.1 := by
      apply Fin.ext
      have : (p.1.1 : ℤ) = (q.1.1 : ℤ) := by linarith
      exact_mod_cast this
    have i2 : p.2 = q.2 := by
      apply Fin.ext
      have : (p.2.1 : ℤ) = (q.2.1 : ℤ) := by linarith
      exact_mod_cast this
    exact Prod.ext i1 i2
  -- Counting.
  have : Finite {l : n → ℕ | parMap B b l = x} := (hfin x).to_subtype
  have hcard : (M + 1) * (M + 1) ≤ Nat.card {l : n → ℕ | parMap B b l = x} := by
    have hle := Nat.card_le_card_of_injective
      (fun p : Fin (M + 1) × Fin (M + 1) => (⟨L p, hpar p⟩ : {l : n → ℕ | parMap B b l = x}))
      (fun p q h => hinj (congrArg Subtype.val h))
    have hcp : Nat.card (Fin (M + 1) × Fin (M + 1)) = (M + 1) * (M + 1) := by simp
    rw [hcp] at hle
    exact hle
  have hsup : Finset.univ.sup x ≤ amax + M * Amax := by
    refine Finset.sup_le fun i _ => ?_
    have g1 : b i ≤ amax := Finset.le_sup (Finset.mem_univ i)
    have g2 : (∑ s, w s * B s i) ≤ Amax := Finset.le_sup (f := fun i => ∑ s, w s * B s i)
      (Finset.mem_univ i)
    exact Nat.add_le_add g1 (Nat.mul_le_mul_left M g2)
  refine count_arith hBd hM hcard ?_
  calc Nat.card {l : n → ℕ | parMap B b l = x} ≤ C * (Finset.univ.sup x + 1) := hbd x
    _ ≤ C * (amax + M * Amax + 1) := Nat.mul_le_mul_left C (Nat.succ_le_succ hsup)

end Obstruction

/-! ## From rank at most one to a single generator

Evaluating at a coordinate on which some kernel vector is nonzero is injective on a kernel
without independent pairs, so the kernel embeds in `ℤ` and inherits its cyclicity.
-/

/-- **The kernel is cyclic.**  If no two kernel vectors are linearly independent, one kernel
vector generates all of them. -/
theorem exists_kernel_generator {B : n → ι → ℕ}
    (hno : ∀ d₁ d₂ : n → ℤ, InKer B d₁ → InKer B d₂ →
      (∀ c₁ c₂ : ℤ, (∀ s, c₁ * d₁ s + c₂ * d₂ s = 0) → c₁ = 0 ∧ c₂ = 0) → False) :
    ∃ d : n → ℤ, InKer B d ∧ ∀ d' : n → ℤ, InKer B d' → ∃ k : ℤ, ∀ s, d' s = k * d s := by
  classical
  by_cases htriv : ∀ d : n → ℤ, InKer B d → ∀ s, d s = 0
  · exact ⟨0, inKer_zero B, fun d' hd' => ⟨0, fun s => by simp [htriv d' hd' s]⟩⟩
  obtain ⟨d₀, hd₀, s₀, hs₀⟩ : ∃ d : n → ℤ, InKer B d ∧ ∃ s, d s ≠ 0 := by
    by_contra hc
    exact htriv fun d hd s => by by_contra hs; exact hc ⟨d, hd, s, hs⟩
  -- A kernel vector vanishing at `s₀` vanishes everywhere.
  have hvan : ∀ f : n → ℤ, InKer B f → f s₀ = 0 → ∀ s, f s = 0 := by
    intro f hf hfs₀ s₁
    by_contra hs₁
    refine hno f d₀ hf hd₀ fun c₁ c₂ hc => ?_
    have hc₂ : c₂ = 0 := by
      have h := hc s₀
      rw [hfs₀, mul_zero, zero_add] at h
      exact (mul_eq_zero.1 h).resolve_right hs₀
    have hc₁ : c₁ = 0 := by
      have h := hc s₁
      rw [hc₂, zero_mul, add_zero] at h
      exact (mul_eq_zero.1 h).resolve_right hs₁
    exact ⟨hc₁, hc₂⟩
  -- Hence evaluation at `s₀` is injective on the kernel.
  have hinj : ∀ d e : n → ℤ, InKer B d → InKer B e → d s₀ = e s₀ → ∀ s, d s = e s := by
    intro d e hd he hde s
    have := hvan _ (hd.sub he) (by simp [hde]) s
    omega
  -- The image of the kernel under that evaluation is a subgroup of `ℤ`, hence cyclic.
  let H : AddSubgroup ℤ :=
    { carrier := {m : ℤ | ∃ d : n → ℤ, InKer B d ∧ d s₀ = m}
      zero_mem' := ⟨0, inKer_zero B, rfl⟩
      add_mem' := by
        rintro _ _ ⟨d, hd, rfl⟩ ⟨e, he, rfl⟩
        exact ⟨d + e, hd.add he, rfl⟩
      neg_mem' := by
        rintro _ ⟨d, hd, rfl⟩
        exact ⟨fun s => -d s, hd.neg, rfl⟩ }
  obtain ⟨m, hm⟩ := Int.subgroup_cyclic H
  have hmH : m ∈ H := by
    rw [hm]
    exact AddSubgroup.subset_closure rfl
  obtain ⟨d, hd, hdm⟩ := hmH
  refine ⟨d, hd, fun d' hd' => ?_⟩
  have hmem : d' s₀ ∈ H := ⟨d', hd', rfl⟩
  rw [hm, AddSubgroup.mem_closure_singleton] at hmem
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, fun s => ?_⟩
  refine hinj d' (fun s => k * d s) hd' (hd.zsmul k) ?_ s
  rw [hdm, ← hk]
  simp

/-! ## Fibres are arithmetic progressions

A cyclic kernel with generator `d` cuts each fibre out of a line `l₁ + ℤ d`; the constraint
`l ≥ 0` selects an order-convex, finite, nonempty set of multipliers, i.e. an interval.
-/

section Progression

/-- Counting an arithmetic-progression fibre: the length is the number of points, provided
distinct indices give distinct tuples (automatic once the step is nonzero, and vacuous for
progressions of length at most one). -/
private theorem card_fibre_eq {B : n → ι → ℕ} {b : ι → ℕ} {d : n → ℤ} {x : ι → ℕ}
    {l₀ : n → ℕ} {len : ℕ}
    (hiff : ∀ l : n → ℕ,
      parMap B b l = x ↔ ∃ j : ℕ, j < len ∧ ∀ s, (l s : ℤ) = (l₀ s : ℤ) + j * d s)
    (hreal : ∀ j : ℕ, j < len → ∃ l : n → ℕ, ∀ s, (l s : ℤ) = (l₀ s : ℤ) + j * d s)
    (hnd : len ≤ 1 ∨ ∃ s, d s ≠ 0) :
    Nat.card {l : n → ℕ | parMap B b l = x} = len := by
  classical
  choose f hf using fun j : Fin len => hreal j.1 j.2
  have hfmem : ∀ j : Fin len, parMap B b (f j) = x := fun j => (hiff _).2 ⟨j.1, j.2, hf j⟩
  refine (Nat.card_eq_of_bijective
    (fun j : Fin len => (⟨f j, hfmem j⟩ : {l : n → ℕ | parMap B b l = x})) ⟨?_, ?_⟩).symm.trans
    (Nat.card_eq_fintype_card.trans (Fintype.card_fin len))
  · intro j₁ j₂ h
    rcases hnd with hlen | ⟨sd, hsd⟩
    · have : Subsingleton (Fin len) := Fin.subsingleton_iff_le_one.2 hlen
      exact Subsingleton.elim _ _
    · have hfe : f j₁ = f j₂ := congrArg Subtype.val h
      have e1 := hf j₁ sd
      have e2 := hf j₂ sd
      rw [congrFun hfe sd, e2] at e1
      have hmul : (j₁.1 : ℤ) * d sd = (j₂.1 : ℤ) * d sd := by linarith
      have : (j₁.1 : ℤ) = (j₂.1 : ℤ) := mul_right_cancel₀ hsd hmul
      exact Fin.ext (by exact_mod_cast this)
  · rintro ⟨l, hl⟩
    obtain ⟨j, hjlt, hjs⟩ := (hiff l).1 hl
    refine ⟨⟨j, hjlt⟩, Subtype.ext (funext fun s => ?_)⟩
    have : ((f ⟨j, hjlt⟩ s : ℕ) : ℤ) = ((l s : ℕ) : ℤ) := by
      rw [hf ⟨j, hjlt⟩ s, hjs s]
    exact_mod_cast this

/-- The progression description of a fibre, together with the side condition that makes its
length the number of points. -/
private theorem fibre_progression_aux {B : n → ι → ℕ} {b : ι → ℕ} {d : n → ℤ}
    (hd : InKer B d)
    (hgen : ∀ d' : n → ℤ, InKer B d' → ∃ k : ℤ, ∀ s, d' s = k * d s)
    (hfin : ∀ x : ι → ℕ, Set.Finite {l : n → ℕ | parMap B b l = x})
    (x : ι → ℕ) :
    ∃ (l₀ : n → ℕ) (len : ℕ),
      (∀ l : n → ℕ,
        parMap B b l = x ↔ ∃ j : ℕ, j < len ∧ ∀ s, (l s : ℤ) = (l₀ s : ℤ) + j * d s) ∧
      (∀ j : ℕ, j < len → ∃ l : n → ℕ, ∀ s, (l s : ℤ) = (l₀ s : ℤ) + j * d s) ∧
      (len ≤ 1 ∨ ∃ s, d s ≠ 0) := by
  classical
  by_cases hne : ∃ l₁ : n → ℕ, parMap B b l₁ = x
  swap
  · refine ⟨0, 0, fun l => ⟨fun h => absurd ⟨l, h⟩ hne, ?_⟩, fun j hj => ?_, Or.inl (by omega)⟩
    · rintro ⟨j, hj, -⟩
      exact absurd hj (Nat.not_lt_zero j)
    · exact absurd hj (Nat.not_lt_zero j)
  obtain ⟨l₁, hl₁⟩ := hne
  -- The degenerate case of a trivial kernel: every fibre is a singleton.
  by_cases hd0 : ∀ s, d s = 0
  · refine ⟨l₁, 1, fun l => ⟨fun h => ⟨0, Nat.zero_lt_one, fun s => ?_⟩, ?_⟩,
      fun j _ => ⟨l₁, fun s => by rw [hd0 s]; ring⟩, Or.inl le_rfl⟩
    · obtain ⟨k, hk⟩ := hgen _ (inKer_sub_of_parMap_eq (h.trans hl₁.symm))
      have hks := hk s
      rw [hd0 s, mul_zero] at hks
      push_cast
      omega
    · rintro ⟨j, -, hj⟩
      have hll : l = l₁ := by
        funext s
        have := hj s
        rw [hd0 s, mul_zero, add_zero] at this
        exact_mod_cast this
      rw [hll]
      exact hl₁
  obtain ⟨sd, hsd⟩ : ∃ s, d s ≠ 0 := by
    by_contra hc
    exact hd0 fun s => by by_contra h; exact hc ⟨s, h⟩
  -- Multipliers that keep the shifted tuple nonnegative, and the tuple they produce.
  set K : Set ℤ := {k : ℤ | ∀ s, 0 ≤ (l₁ s : ℤ) + k * d s} with hKdef
  set φ : ℤ → (n → ℕ) := fun k s => ((l₁ s : ℤ) + k * d s).toNat with hφdef
  have hφcast : ∀ k ∈ K, ∀ s, ((φ k s : ℕ) : ℤ) = (l₁ s : ℤ) + k * d s := by
    intro k hk s
    simp only [hφdef]
    exact Int.toNat_of_nonneg (hk s)
  have hφmem : ∀ k ∈ K, parMap B b (φ k) = x := fun k hk =>
    (parMap_eq_of_shift (hd.zsmul k) (hφcast k hk)).trans hl₁
  have hmemφ : ∀ l : n → ℕ, parMap B b l = x → ∃ k ∈ K, l = φ k := by
    intro l hl
    obtain ⟨k, hk⟩ := hgen _ (inKer_sub_of_parMap_eq (hl.trans hl₁.symm))
    have hcast : ∀ s, (l s : ℤ) = (l₁ s : ℤ) + k * d s := by
      intro s; have := hk s; omega
    refine ⟨k, fun s => ?_, ?_⟩
    · rw [← hcast s]; positivity
    · funext s
      simp only [hφdef, ← hcast s, Int.toNat_natCast]
  -- `K` is finite, nonempty and order-convex, hence an interval.
  have hKinj : Set.InjOn φ K := by
    intro k1 hk1 k2 hk2 h
    have e1 := hφcast k1 hk1 sd
    have e2 := hφcast k2 hk2 sd
    rw [congrFun h sd, e2] at e1
    have : k1 * d sd = k2 * d sd := by linarith
    exact mul_right_cancel₀ hsd this
  have hKfin : K.Finite := by
    refine Set.Finite.of_finite_image ((hfin x).subset ?_) hKinj
    rintro _ ⟨k, hk, rfl⟩
    exact hφmem k hk
  have hK0 : (0 : ℤ) ∈ K := by intro s; simp
  have hKne : hKfin.toFinset.Nonempty := ⟨0, hKfin.mem_toFinset.2 hK0⟩
  set kmin : ℤ := hKfin.toFinset.min' hKne with hkmindef
  set kmax : ℤ := hKfin.toFinset.max' hKne with hkmaxdef
  have hkminK : kmin ∈ K := hKfin.mem_toFinset.1 (hKfin.toFinset.min'_mem hKne)
  have hkmaxK : kmax ∈ K := hKfin.mem_toFinset.1 (hKfin.toFinset.max'_mem hKne)
  have hKlo : ∀ k ∈ K, kmin ≤ k := fun k hk =>
    hKfin.toFinset.min'_le k (hKfin.mem_toFinset.2 hk)
  have hKhi : ∀ k ∈ K, k ≤ kmax := fun k hk =>
    hKfin.toFinset.le_max' k (hKfin.mem_toFinset.2 hk)
  have hKconv : ∀ k : ℤ, kmin ≤ k → k ≤ kmax → k ∈ K := by
    intro k h1 h2 s
    rcases le_or_gt 0 (d s) with hds | hds
    · have hmul : kmin * d s ≤ k * d s := mul_le_mul_of_nonneg_right h1 hds
      have := hkminK s
      linarith
    · have hmul : kmax * d s ≤ k * d s := mul_le_mul_of_nonpos_right h2 hds.le
      have := hkmaxK s
      linarith
  refine ⟨φ kmin, (kmax - kmin + 1).toNat, fun l => ⟨?_, ?_⟩, fun j hj => ?_, Or.inr ⟨sd, hsd⟩⟩
  · intro hl
    obtain ⟨k, hkK, rfl⟩ := hmemφ l hl
    have h1 := hKlo k hkK
    have h2 := hKhi k hkK
    refine ⟨(k - kmin).toNat, by omega, fun s => ?_⟩
    rw [hφcast k hkK s, hφcast kmin hkminK s, Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ k - kmin)]
    ring
  · rintro ⟨j, hj, hjs⟩
    have hk : kmin + (j : ℤ) ∈ K := hKconv _ (by omega) (by omega)
    have hll : l = φ (kmin + (j : ℤ)) := by
      funext s
      have hcast : ((l s : ℕ) : ℤ) = ((φ (kmin + (j : ℤ)) s : ℕ) : ℤ) := by
        rw [hjs s, hφcast (kmin + (j : ℤ)) hk s, hφcast kmin hkminK s]
        ring
      exact_mod_cast hcast
    rw [hll]
    exact hφmem _ hk
  · have hk : kmin + (j : ℤ) ∈ K := hKconv _ (by omega) (by omega)
    refine ⟨φ (kmin + (j : ℤ)), fun s => ?_⟩
    rw [hφcast (kmin + (j : ℤ)) hk s, hφcast kmin hkminK s]
    ring

/-- **Coefficient fibres are arithmetic progressions.**  If a single kernel vector `d`
generates the kernel and the parameter fibres are finite, then each fibre of `parMap` is the
arithmetic progression with step `d` of some length starting at some tuple: every index below
that length is realised by an actual tuple, and the length is the number of points. -/
theorem fibre_eq_progression {B : n → ι → ℕ} {b : ι → ℕ} {d : n → ℤ}
    (hd : InKer B d)
    (hgen : ∀ d' : n → ℤ, InKer B d' → ∃ k : ℤ, ∀ s, d' s = k * d s)
    (hfin : ∀ x : ι → ℕ, Set.Finite {l : n → ℕ | parMap B b l = x})
    (x : ι → ℕ) :
    ∃ (l₀ : n → ℕ) (len : ℕ),
      (∀ l : n → ℕ,
        parMap B b l = x ↔ ∃ j : ℕ, j < len ∧ ∀ s, (l s : ℤ) = (l₀ s : ℤ) + j * d s) ∧
      (∀ j : ℕ, j < len → ∃ l : n → ℕ, ∀ s, (l s : ℤ) = (l₀ s : ℤ) + j * d s) ∧
      Nat.card {l : n → ℕ | parMap B b l = x} = len := by
  obtain ⟨l₀, len, hiff, hreal, hnd⟩ := fibre_progression_aux hd hgen hfin x
  exact ⟨l₀, len, hiff, hreal, card_fibre_eq hiff hreal hnd⟩

end Progression

/-! ## The dichotomy in coefficient space -/

section Dichotomy

variable [Fintype ι]

/-- **The kernel dichotomy, coefficient form.**  A linear bound on the size of the parameter
fibres forces the integer kernel to be cyclic, and then every fibre of `parMap` is an
arithmetic progression whose step `d` does not depend on the parameter. -/
theorem exists_uniform_progression {B : n → ι → ℕ} {b : ι → ℕ} {C : ℕ}
    (hfin : ∀ x : ι → ℕ, Set.Finite {l : n → ℕ | parMap B b l = x})
    (hbd : ∀ x : ι → ℕ, Nat.card {l : n → ℕ | parMap B b l = x} ≤ C * (Finset.univ.sup x + 1)) :
    ∃ d : n → ℤ, InKer B d ∧ ∀ x : ι → ℕ, ∃ (l₀ : n → ℕ) (len : ℕ),
      (∀ l : n → ℕ,
        parMap B b l = x ↔ ∃ j : ℕ, j < len ∧ ∀ s, (l s : ℤ) = (l₀ s : ℤ) + j * d s) ∧
      (∀ j : ℕ, j < len → ∃ l : n → ℕ, ∀ s, (l s : ℤ) = (l₀ s : ℤ) + j * d s) ∧
      Nat.card {l : n → ℕ | parMap B b l = x} = len :=
  let ⟨d, hd, hgen⟩ :=
    exists_kernel_generator fun _ _ h₁ h₂ hind => not_indep_of_bound hfin hbd h₁ h₂ hind
  ⟨d, hd, fun x => fibre_eq_progression hd hgen hfin x⟩

end Dichotomy

/-! ## Transfer to a proper linear set -/

section ProperLinear

open Pointwise ProperLinearRep

variable {κ : Type}

/-- Pointwise value of `periodSum` in a function space. -/
private theorem periodSum_apply' (t : Finset (ι ⊕ κ → ℕ)) (l : t → ℕ) (v : ι ⊕ κ) :
    periodSum t l v = ∑ s : t, l s * (s : ι ⊕ κ → ℕ) v := by
  rw [periodSum_apply]
  simp

variable [Fintype ι]

/-- **Fibres of a proper linear set are arithmetic progressions with a fixed direction.**

Let `S ⊆ ℕ^ι × ℕ^κ` be a proper linear set whose parameter fibres are finite and of size at
most `C * (‖x‖_∞ + 1)`.  Then a single direction `δ : κ → ℤ`, independent of the parameter,
serves every fibre: the fibre over `x` is the arithmetic progression of step `δ` starting at
some `y₀` and of some length `len`, and each index below `len` is realised.  Empty and
singleton fibres are the cases `len = 0` and `len = 1`. -/
theorem properLinear_fibre_progression {S : Set (ι ⊕ κ → ℕ)}
    (hS : IsProperLinearSet S)
    (hfin : ∀ x : ι → ℕ, Set.Finite {y : κ → ℕ | Sum.elim x y ∈ S}) {C : ℕ}
    (hbd : ∀ x : ι → ℕ,
      Nat.card {y : κ → ℕ | Sum.elim x y ∈ S} ≤ C * (Finset.univ.sup x + 1)) :
    ∃ δ : κ → ℤ, ∀ x : ι → ℕ, ∃ (y₀ : κ → ℕ) (len : ℕ),
      (∀ y : κ → ℕ,
        Sum.elim x y ∈ S ↔ ∃ j : ℕ, j < len ∧ ∀ c, (y c : ℤ) = (y₀ c : ℤ) + j * δ c) ∧
      (∀ j : ℕ, j < len → ∃ y : κ → ℕ, ∀ c, (y c : ℤ) = (y₀ c : ℤ) + j * δ c) ∧
      Nat.card {y : κ → ℕ | Sum.elim x y ∈ S} = len := by
  classical
  rw [isProperLinearSet_iff] at hS
  obtain ⟨a, t, ht, rfl⟩ := hS
  set B : t → ι → ℕ := fun s i => (s : ι ⊕ κ → ℕ) (Sum.inl i) with hB
  set bb : ι → ℕ := fun i => a (Sum.inl i) with hbb
  -- The fibre part of the point attached to a coefficient tuple.
  set G : (t → ℕ) → κ → ℕ := fun l c => (a + periodSum t l) (Sum.inr c) with hG
  have hinl : ∀ (l : t → ℕ) (i : ι), (a + periodSum t l) (Sum.inl i) = parMap B bb l i := by
    intro l i
    simp [hB, hbb, parMap, periodSum_apply']
  have hmem : ∀ (x : ι → ℕ) (y : κ → ℕ),
      Sum.elim x y ∈ (a +ᵥ (AddSubmonoid.closure (t : Set (ι ⊕ κ → ℕ)) : Set (ι ⊕ κ → ℕ)))
        ↔ ∃ l : t → ℕ, parMap B bb l = x ∧ G l = y := by
    intro x y
    rw [mem_vadd_closure_iff]
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨l, funext fun i => ?_, funext fun c => ?_⟩
      · rw [← hinl l i, ← hl]; rfl
      · show (a + periodSum t l) (Sum.inr c) = y c
        rw [← hl]; rfl
    · rintro ⟨l, h1, h2⟩
      refine ⟨l, funext fun v => ?_⟩
      cases v with
      | inl i => exact ((hinl l i).trans (congrFun h1 i)).symm
      | inr c => exact (congrFun h2 c).symm
  -- Coefficient tuples over a fixed parameter are determined by their fibre part.
  have hGinj : ∀ (x : ι → ℕ) (l l' : t → ℕ), parMap B bb l = x → parMap B bb l' = x →
      G l = G l' → l = l' := by
    intro x l l' hl hl' h
    refine vadd_periodSum_injective a ht ?_
    show a + periodSum t l = a + periodSum t l'
    funext v
    cases v with
    | inl i => rw [hinl l i, hinl l' i, hl, hl']
    | inr c => exact congrFun h c
  have hfinC : ∀ x : ι → ℕ, Set.Finite {l : t → ℕ | parMap B bb l = x} := by
    intro x
    refine Set.Finite.of_finite_image (f := G) ((hfin x).subset ?_) ?_
    · rintro _ ⟨l, hl, rfl⟩
      exact (hmem x _).2 ⟨l, hl, rfl⟩
    · exact fun l hl l' hl' h => hGinj x l l' hl hl' h
  have hcardEq : ∀ x : ι → ℕ, Nat.card {l : t → ℕ | parMap B bb l = x}
      = Nat.card {y : κ → ℕ |
          Sum.elim x y ∈ (a +ᵥ (AddSubmonoid.closure (t : Set (ι ⊕ κ → ℕ)) : Set (ι ⊕ κ → ℕ)))} := by
    intro x
    refine Nat.card_congr (Equiv.ofBijective
      (fun l : {l : t → ℕ | parMap B bb l = x} => (⟨G l.1, (hmem x _).2 ⟨l.1, l.2, rfl⟩⟩ :
        {y : κ → ℕ | Sum.elim x y ∈
          (a +ᵥ (AddSubmonoid.closure (t : Set (ι ⊕ κ → ℕ)) : Set (ι ⊕ κ → ℕ)))}))
      ⟨?_, ?_⟩)
    · rintro ⟨l, hl⟩ ⟨l', hl'⟩ h
      exact Subtype.ext (hGinj x l l' hl hl' (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      obtain ⟨l, hl, rfl⟩ := (hmem x y).1 hy
      exact ⟨⟨l, hl⟩, rfl⟩
  obtain ⟨d, hd, hprog⟩ := exists_uniform_progression (B := B) (b := bb) (C := C) hfinC
    (fun x => (hcardEq x).symm ▸ hbd x)
  set δ : κ → ℤ := fun c => ∑ s : t, d s * ((s : ι ⊕ κ → ℕ) (Sum.inr c) : ℤ) with hδ
  have hstep : ∀ (l l' : t → ℕ) (j : ℕ), (∀ s, (l s : ℤ) = (l' s : ℤ) + j * d s) →
      ∀ c : κ, ((G l c : ℕ) : ℤ) = ((G l' c : ℕ) : ℤ) + j * δ c := by
    intro l l' j h c
    have e : ∀ m : t → ℕ, ((G m c : ℕ) : ℤ)
        = (a (Sum.inr c) : ℤ) + ∑ s : t, (m s : ℤ) * ((s : ι ⊕ κ → ℕ) (Sum.inr c) : ℤ) := by
      intro m
      simp [hG, periodSum_apply']
    have hsum : ∑ s : t, (l s : ℤ) * ((s : ι ⊕ κ → ℕ) (Sum.inr c) : ℤ)
        = (∑ s : t, (l' s : ℤ) * ((s : ι ⊕ κ → ℕ) (Sum.inr c) : ℤ)) + (j : ℤ) * δ c := by
      rw [hδ, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by rw [h s]; ring
    rw [e l, e l', hsum]
    ring
  refine ⟨δ, fun x => ?_⟩
  obtain ⟨l₀, len, hiff, hreal, hcard⟩ := hprog x
  refine ⟨G l₀, len, fun y => ?_, fun j hj => ?_, (hcardEq x).symm.trans hcard⟩
  · rw [hmem x y]
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨j, hjlt, hjs⟩ := (hiff l).1 hl
      exact ⟨j, hjlt, fun c => hstep l l₀ j hjs c⟩
    · rintro ⟨j, hjlt, hy⟩
      obtain ⟨l, hls⟩ := hreal j hjlt
      refine ⟨l, (hiff l).2 ⟨j, hjlt, hls⟩, funext fun c => ?_⟩
      exact_mod_cast (hstep l l₀ j hls c).trans (hy c).symm
  · obtain ⟨l, hls⟩ := hreal j hj
    exact ⟨G l, fun c => hstep l l₀ j hls c⟩

/-- **The axiom-shaped packaging.**  For a relation `R ⊆ ℕ^p × ℕ^q` whose graph is a proper
linear set, with finite fibres of size at most `C * (‖x‖_∞ + 1)`, one direction `δ` serves
every fibre: `{y | R x y}` is the arithmetic progression of step `δ` from some `y₀` of some
length `len`, every index below `len` is realised, and `len` is the fibre count. -/
theorem relation_fibre_progression {p q : ℕ} (R : (Fin p → ℕ) → (Fin q → ℕ) → Prop)
    (hR : IsProperLinearSet {w : Fin p ⊕ Fin q → ℕ | R (w ∘ Sum.inl) (w ∘ Sum.inr)})
    (hfin : ∀ x : Fin p → ℕ, Set.Finite {y : Fin q → ℕ | R x y}) {C : ℕ}
    (hbd : ∀ x : Fin p → ℕ, Nat.card {y : Fin q → ℕ | R x y} ≤ C * (Finset.univ.sup x + 1)) :
    ∃ δ : Fin q → ℤ, ∀ x : Fin p → ℕ, ∃ (y₀ : Fin q → ℕ) (len : ℕ),
      (∀ y : Fin q → ℕ, R x y ↔ ∃ j : ℕ, j < len ∧ ∀ c, (y c : ℤ) = (y₀ c : ℤ) + j * δ c) ∧
      (∀ j : ℕ, j < len → ∃ y : Fin q → ℕ, ∀ c, (y c : ℤ) = (y₀ c : ℤ) + j * δ c) ∧
      Nat.card {y : Fin q → ℕ | R x y} = len := by
  have hset : ∀ (x : Fin p → ℕ) (y : Fin q → ℕ),
      (Sum.elim x y ∈ {w : Fin p ⊕ Fin q → ℕ | R (w ∘ Sum.inl) (w ∘ Sum.inr)}) ↔ R x y := by
    intro x y
    have h1 : (Sum.elim x y) ∘ Sum.inl = x := funext fun _ => rfl
    have h2 : (Sum.elim x y) ∘ Sum.inr = y := funext fun _ => rfl
    simp only [Set.mem_ofPred_eq, h1, h2]
  have heq : ∀ x : Fin p → ℕ,
      {y : Fin q → ℕ | Sum.elim x y ∈ {w : Fin p ⊕ Fin q → ℕ | R (w ∘ Sum.inl) (w ∘ Sum.inr)}}
        = {y : Fin q → ℕ | R x y} := fun x => Set.ext fun y => hset x y
  obtain ⟨δ, hδ⟩ := properLinear_fibre_progression hR
    (fun x => by rw [heq x]; exact hfin x) (C := C) (fun x => by rw [heq x]; exact hbd x)
  refine ⟨δ, fun x => ?_⟩
  obtain ⟨y₀, len, h1, h2, h3⟩ := hδ x
  refine ⟨y₀, len, fun y => (hset x y).symm.trans (h1 y), h2, ?_⟩
  rw [← heq x]
  exact h3

end ProperLinear

end KernelDichotomy
