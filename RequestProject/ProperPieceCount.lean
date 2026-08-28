/-
# Counting one proper linear piece

The kernel dichotomy (`KernelDichotomy.properLinear_fibre_progression`) presents each
parameter-fibre of a proper linear set with a linear fibre bound as an arithmetic
progression `{y₀(x) + j·δ : j < len(x)}` whose direction `δ` does not depend on the
parameter `x`.  This file turns that description into semilinearity statements.

The pivot is an *index set*: a semilinear `V ⊆ ℕ^p × ℕ` whose `x`-fibre is the initial
segment `{j | j < N x}` of the count function `N`.  A count graph reconstructed from such
an index set is semilinear, because `N x = k` is the first-order condition
`∀ j, ((x, j) ∈ V ↔ j < k)`.  Building `V` for a proper linear piece uses the fibrewise
coordinate minimisation of `SemilinearMinMax`: fixing a coordinate `c₀` with `δ c₀ ≠ 0`,
the fibre-minimal value of `c₀` is attained at an end of the progression, and the fibre
points are exactly those whose `c₀`-coordinate is that minimum plus a multiple of
`|δ c₀|`, the multiplier running over `{0, …, len(x) - 1}`.

## Main results

* `isSemilinearSet_countGraph_of_indexSet`: an index set with initial-segment fibres yields
  a semilinear count graph.
* `isSemilinearSet_properPiece_countGraph`: the count graph of a proper linear set with
  finite, linearly bounded parameter-fibres is semilinear.  `count_graph_properLinear` is
  the same statement in the relational packaging of `lem:presburger-counting`.
* `card_inter_eq_card_indices`: intersecting a progression fibre with any set is counted by
  the indices it hits, via the bijection `j ↦ y₀ + j·δ`.
* `isSemilinearSet_indexSet_inter`: that index set is semilinear inside `ℕ^p × ℕ`, and
  `exists_indexSet_inter` packages it as the one-dimensional replacement for a fibre count.

All statements are unconditional; no counting input is admitted.
-/
import Mathlib
import RequestProject.ProperLinearRep
import RequestProject.SemilinearMinMax
import RequestProject.KernelDichotomy

namespace ProperPieceCount

open Set FirstOrder Language

/-! ## Presburger atoms carrying constants -/

section Atoms

variable {A : Set ℕ}

/-- A single ℕ-linear equation between two linear forms in the coordinates is semilinear. -/
private theorem isSemilinearSet_forms_eq {γ : Type} [Fintype γ] (a b : γ → ℕ) :
    IsSemilinearSet {x : γ → ℕ | ∑ i, a i * x i = ∑ i, b i * x i} := by
  have h := Nat.isSemilinearSet_setOfPred_mulVec_eq (ι := Fin 1) (κ := γ) 0 0
      (Matrix.of fun (_ : Fin 1) i => a i) (Matrix.of fun (_ : Fin 1) i => b i)
  convert h using 1
  ext x
  simp [funext_iff, Matrix.mulVec, dotProduct]

/-- The three-coordinate pattern `v 0 = v 1 + D * v 2` with a fixed multiplier `D`. -/
private theorem isSemilinearSet_eq_add_mul3 (D : ℕ) :
    IsSemilinearSet {v : Fin 3 → ℕ | v 0 = v 1 + D * v 2} := by
  have h := isSemilinearSet_forms_eq (γ := Fin 3) ![1, 0, 0] ![0, 1, D]
  convert h using 1
  ext v
  simp [Fin.sum_univ_three]

/-- `g a = g b + D * g c` for three coordinates and a fixed multiplier is
Presburger-definable. -/
theorem definable_eq_add_mul {γ : Type} [Finite γ] (a b c : γ) (D : ℕ) :
    A.Definable presburger {g : γ → ℕ | g a = g b + D * g c} := by
  have h := ((isSemilinearSet_eq_add_mul3 D).definable (A := A)).preimage_comp
    (![a, b, c] : Fin 3 → γ)
  convert h using 1
  ext g
  simp

/-- `g a = D` for a fixed constant `D` is Presburger-definable. -/
theorem definable_coord_const {γ : Type} [Finite γ] (a : γ) (D : ℕ) :
    A.Definable presburger {g : γ → ℕ | g a = D} := by
  have h := ((IsSemilinearSet.singleton (M := Fin 1 → ℕ) (fun _ => D)).definable
    (A := A)).preimage_comp (fun _ : Fin 1 => a)
  convert h using 1
  ext g
  simp [funext_iff]

end Atoms

/-! ## From an index set to a count graph

An *index set* for a count function `N : ℕ^p → ℕ` is a set `V ⊆ ℕ^p × ℕ` whose fibre over
`x` is the initial segment `{j | j < N x}`.  Reading `N x = k` as
`∀ j, ((x, j) ∈ V ↔ j < k)` makes the count graph first-order over `V`.
-/

section CountGraph

/-- **A semilinear index set gives a semilinear count graph.**  If `V ⊆ ℕ^p × ℕ` is
semilinear and its fibre over `x` is `{j | j < N x}`, then the graph of `N`, packed as
`Fin (p+1) → ℕ` with the parameters on `Fin.castSucc` and the value on `Fin.last p`, is
semilinear. -/
theorem isSemilinearSet_countGraph_of_indexSet {p : ℕ} {V : Set (Fin p ⊕ Fin 1 → ℕ)}
    (hV : IsSemilinearSet V) {N : (Fin p → ℕ) → ℕ}
    (hN : ∀ (x : Fin p → ℕ) (j : ℕ), Sum.elim x (fun _ => j) ∈ V ↔ j < N x) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ | N (fun i => z i.castSucc) = z (Fin.last p)} := by
  classical
  rw [← presburger.definable_iff_isSemilinearSet (A := (∅ : Set ℕ))]
  have hVd : (∅ : Set ℕ).Definable presburger V := hV.definable
  set f : Fin p ⊕ Fin 1 → Fin (p + 1) ⊕ Fin 1 :=
    Sum.elim (fun i => Sum.inl i.castSucc) (fun _ => Sum.inr 0) with hf
  have hcomp : ∀ (z : Fin (p + 1) → ℕ) (u : Fin 1 → ℕ),
      (Sum.elim z u) ∘ f = Sum.elim (fun i : Fin p => z i.castSucc) (fun _ : Fin 1 => u 0) := by
    intro z u
    funext v
    cases v with
    | inl i => rfl
    | inr k => rfl
  have h1 := hVd.preimage_comp f
  have h2 : (∅ : Set ℕ).Definable presburger
      {g : Fin (p + 1) ⊕ Fin 1 → ℕ | g (Sum.inl (Fin.last p)) ≤ g (Sum.inr 0)} :=
    SemilinearMinMax.definable_coord_le _ _
  have h4 := ((h1.inter h2.compl).union (h1.compl.inter h2)).forall_of_finite (β := Fin 1)
  convert h4 using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
    Set.mem_preimage, hcomp, Sum.elim_inl, Sum.elim_inr, not_le]
  constructor
  · intro hz u
    by_cases hu : u 0 < z (Fin.last p)
    · exact Or.inl ⟨(hN _ (u 0)).2 (by omega), hu⟩
    · exact Or.inr ⟨fun hc => absurd ((hN _ (u 0)).1 hc) (by omega), by omega⟩
  · intro h
    have key : ∀ j : ℕ, j < N (fun i : Fin p => z i.castSucc) ↔ j < z (Fin.last p) := by
      intro j
      rcases h (fun _ => j) with ⟨hc, hlt⟩ | ⟨hc, hle⟩
      · exact ⟨fun _ => hlt, fun _ => (hN _ j).1 hc⟩
      · exact ⟨fun hj => absurd ((hN _ j).2 hj) hc, fun hj => by omega⟩
    have h1 := (key (N (fun i : Fin p => z i.castSucc)))
    have h2 := (key (z (Fin.last p)))
    omega

end CountGraph

/-! ## The index set of a progression fibre

Fix a coordinate `c₀` on which the direction `δ` of the progression is nonzero and put
`D = |δ c₀|`.  Reading a fibre point off its `c₀`-coordinate is injective, and the
`c₀`-coordinates of the fibre are `min + j·D` for `j < len`, the minimum being attained at
whichever end of the progression `δ c₀` points away from.
-/

section Core

variable {q : ℕ}

/-- **The fibre is indexed by the `c₀`-offset from its minimum.**  For a fibre described as
the progression `{y₀ + j·δ : j < len}` and a coordinate `c₀` with `δ c₀ ≠ 0`, there is a
fibre point `u₀` minimising the `c₀`-coordinate, and a fibre point sits at `c₀`-distance
`j·|δ c₀|` above it exactly when `j < len`. -/
private theorem exists_min_index {δ : Fin q → ℤ} {c₀ : Fin q} (he : δ c₀ ≠ 0)
    {y₀ : Fin q → ℕ} {len : ℕ} {P : (Fin q → ℕ) → Prop}
    (hiff : ∀ y : Fin q → ℕ,
      P y ↔ ∃ j : ℕ, j < len ∧ ∀ c, (y c : ℤ) = (y₀ c : ℤ) + j * δ c)
    (hreal : ∀ j : ℕ, j < len → ∃ y : Fin q → ℕ, ∀ c, (y c : ℤ) = (y₀ c : ℤ) + j * δ c)
    (hlen : 0 < len) :
    ∃ u₀ : Fin q → ℕ, P u₀ ∧ (∀ w, P w → u₀ c₀ ≤ w c₀) ∧
      ∀ j : ℕ, (∃ y, P y ∧ (y c₀ : ℤ) = (u₀ c₀ : ℤ) + ((δ c₀).natAbs : ℤ) * j) ↔ j < len := by
  rcases lt_or_gt_of_ne he with hneg | hpos
  · -- `δ c₀ < 0`: the minimum sits at the far end `len - 1`, and index `j` is at `len-1-j`.
    have hD : ((δ c₀).natAbs : ℤ) = -δ c₀ := by omega
    obtain ⟨u₀, hu₀⟩ := hreal (len - 1) (by omega)
    have hu₀mem : P u₀ := (hiff u₀).2 ⟨len - 1, by omega, hu₀⟩
    have hmin : ∀ w, P w → u₀ c₀ ≤ w c₀ := by
      intro w hw
      obtain ⟨i, hi, hws⟩ := (hiff w).1 hw
      have hle : (i : ℤ) ≤ ((len - 1 : ℕ) : ℤ) := by omega
      have := mul_le_mul_of_nonpos_right hle hneg.le
      have e1 := hu₀ c₀
      have e2 := hws c₀
      have : ((u₀ c₀ : ℕ) : ℤ) ≤ ((w c₀ : ℕ) : ℤ) := by omega
      exact_mod_cast this
    refine ⟨u₀, hu₀mem, hmin, fun j => ⟨?_, ?_⟩⟩
    · rintro ⟨y, hy, hyc⟩
      obtain ⟨i, hi, hys⟩ := (hiff y).1 hy
      have e1 := hu₀ c₀
      have e2 := hys c₀
      have key : (i : ℤ) * δ c₀ = (((len - 1 : ℕ) : ℤ) - j) * δ c₀ := by
        rw [hD] at hyc; ring_nf; ring_nf at hyc e1 e2 ⊢; linarith
      have := mul_right_cancel₀ he key
      omega
    · intro hj
      obtain ⟨y, hy⟩ := hreal (len - 1 - j) (by omega)
      refine ⟨y, (hiff y).2 ⟨len - 1 - j, by omega, hy⟩, ?_⟩
      have e1 := hu₀ c₀
      have e2 := hy c₀
      have hcast : ((len - 1 - j : ℕ) : ℤ) = ((len - 1 : ℕ) : ℤ) - (j : ℤ) := by omega
      rw [hD, e2, e1, hcast]
      ring
  · -- `δ c₀ > 0`: the minimum sits at the near end `0`, and index `j` is at `j`.
    have hD : ((δ c₀).natAbs : ℤ) = δ c₀ := by omega
    obtain ⟨u₀, hu₀⟩ := hreal 0 hlen
    have hu₀mem : P u₀ := (hiff u₀).2 ⟨0, hlen, hu₀⟩
    have hmin : ∀ w, P w → u₀ c₀ ≤ w c₀ := by
      intro w hw
      obtain ⟨i, hi, hws⟩ := (hiff w).1 hw
      have := mul_nonneg (Int.natCast_nonneg i) hpos.le
      have e1 := hu₀ c₀
      have e2 := hws c₀
      have : ((u₀ c₀ : ℕ) : ℤ) ≤ ((w c₀ : ℕ) : ℤ) := by
        rw [e1, e2]; simp; linarith
      exact_mod_cast this
    refine ⟨u₀, hu₀mem, hmin, fun j => ⟨?_, ?_⟩⟩
    · rintro ⟨y, hy, hyc⟩
      obtain ⟨i, hi, hys⟩ := (hiff y).1 hy
      have e1 := hu₀ c₀
      have e2 := hys c₀
      have key : (i : ℤ) * δ c₀ = (j : ℤ) * δ c₀ := by
        rw [hD] at hyc; ring_nf; ring_nf at hyc e1 e2 ⊢; linarith
      have := mul_right_cancel₀ he key
      omega
    · intro hj
      obtain ⟨y, hy⟩ := hreal j hj
      refine ⟨y, (hiff y).2 ⟨j, hj, hy⟩, ?_⟩
      have e1 := hu₀ c₀
      have e2 := hy c₀
      rw [hD, e2, e1]
      ring

end Core

/-! ## The two index sets -/

section IndexSets

/-- The index set cut out by the `c₀`-offset from the fibrewise minimum: a parameter `x` and
an index `j` are related when some fibre point sits `j·D` above the `c₀`-minimum of the
fibre. -/
private theorem isSemilinearSet_minIndexSet {p q : ℕ} {S : Set (Fin p ⊕ Fin q → ℕ)}
    (hS : IsSemilinearSet S) (c₀ : Fin q) (D : ℕ) :
    IsSemilinearSet {w : Fin p ⊕ Fin 1 → ℕ | ∃ y u : Fin q → ℕ,
      Sum.elim (w ∘ Sum.inl) y ∈ S ∧
      (Sum.elim (w ∘ Sum.inl) u ∈ S ∧
        ∀ v : Fin q → ℕ, Sum.elim (w ∘ Sum.inl) v ∈ S → u c₀ ≤ v c₀) ∧
      y c₀ = u c₀ + D * w (Sum.inr 0)} := by
  classical
  set Smin : Set (Fin p ⊕ Fin q → ℕ) := {g : Fin p ⊕ Fin q → ℕ | g ∈ S ∧
    ∀ v : Fin q → ℕ, Sum.elim (g ∘ Sum.inl) v ∈ S → g (Sum.inr c₀) ≤ v c₀} with hSmin
  have hSminSL : IsSemilinearSet Smin := SemilinearMinMax.isSemilinearSet_minCoord c₀ hS
  have hSminMem : ∀ (x : Fin p → ℕ) (u : Fin q → ℕ), Sum.elim x u ∈ Smin ↔
      (Sum.elim x u ∈ S ∧ ∀ v : Fin q → ℕ, Sum.elim x v ∈ S → u c₀ ≤ v c₀) := by
    intro x u
    rw [hSmin]
    simp [Sum.elim_comp_inl]
  rw [← presburger.definable_iff_isSemilinearSet (A := (∅ : Set ℕ))]
  set f₁ : Fin p ⊕ Fin q → (Fin p ⊕ Fin 1) ⊕ (Fin q ⊕ Fin q) :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun c => Sum.inr (Sum.inl c)) with hf₁
  set f₂ : Fin p ⊕ Fin q → (Fin p ⊕ Fin 1) ⊕ (Fin q ⊕ Fin q) :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun c => Sum.inr (Sum.inr c)) with hf₂
  have hc₁ : ∀ (w : Fin p ⊕ Fin 1 → ℕ) (z : Fin q ⊕ Fin q → ℕ),
      (Sum.elim w z) ∘ f₁ = Sum.elim (w ∘ Sum.inl) (z ∘ Sum.inl) := by
    intro w z; funext v; cases v <;> rfl
  have hc₂ : ∀ (w : Fin p ⊕ Fin 1 → ℕ) (z : Fin q ⊕ Fin q → ℕ),
      (Sum.elim w z) ∘ f₂ = Sum.elim (w ∘ Sum.inl) (z ∘ Sum.inr) := by
    intro w z; funext v; cases v <;> rfl
  have h1 := (hS.definable (A := (∅ : Set ℕ))).preimage_comp f₁
  have h2 := (hSminSL.definable (A := (∅ : Set ℕ))).preimage_comp f₂
  have h3 : (∅ : Set ℕ).Definable presburger
      {g : (Fin p ⊕ Fin 1) ⊕ (Fin q ⊕ Fin q) → ℕ |
        g (Sum.inr (Sum.inl c₀)) = g (Sum.inr (Sum.inr c₀)) + D * g (Sum.inl (Sum.inr 0))} :=
    definable_eq_add_mul _ _ _ D
  have h4 := ((h1.inter h2).inter h3).exists_of_finite (β := Fin q ⊕ Fin q)
  convert h4 using 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, hc₁, hc₂,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨y, u, hy, hu, heq⟩
    refine ⟨Sum.elim y u, ⟨⟨by simpa using hy, ?_⟩, by simpa using heq⟩⟩
    simpa using (hSminMem (w ∘ Sum.inl) u).2 hu
  · rintro ⟨z, ⟨hz1, hz2⟩, hz3⟩
    refine ⟨z ∘ Sum.inl, z ∘ Sum.inr, by simpa using hz1, ?_, by simpa using hz3⟩
    simpa using (hSminMem (w ∘ Sum.inl) (z ∘ Sum.inr)).1 hz2

/-- The degenerate index set used when the progression direction vanishes: the fibre has at
most one point, so only the index `0` occurs, and only over a nonempty fibre. -/
private theorem isSemilinearSet_zeroIndexSet {p q : ℕ} {S : Set (Fin p ⊕ Fin q → ℕ)}
    (hS : IsSemilinearSet S) :
    IsSemilinearSet {w : Fin p ⊕ Fin 1 → ℕ |
      w (Sum.inr 0) = 0 ∧ ∃ y : Fin q → ℕ, Sum.elim (w ∘ Sum.inl) y ∈ S} := by
  classical
  rw [← presburger.definable_iff_isSemilinearSet (A := (∅ : Set ℕ))]
  set f : Fin p ⊕ Fin q → (Fin p ⊕ Fin 1) ⊕ Fin q :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun c => Sum.inr c) with hf
  have hc : ∀ (w : Fin p ⊕ Fin 1 → ℕ) (y : Fin q → ℕ),
      (Sum.elim w y) ∘ f = Sum.elim (w ∘ Sum.inl) y := by
    intro w y; funext v; cases v <;> rfl
  have h1 : (∅ : Set ℕ).Definable presburger
      {w : Fin p ⊕ Fin 1 → ℕ | w (Sum.inr 0) = 0} := definable_coord_const _ 0
  have h2 := ((hS.definable (A := (∅ : Set ℕ))).preimage_comp f).exists_of_finite (β := Fin q)
  convert h1.inter h2 using 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, hc]

end IndexSets

/-! ## The count graph of a proper linear piece -/

section CountPiece

/-- **The count graph of a proper linear piece is semilinear.**

Let `S ⊆ ℕ^p × ℕ^q` be a proper linear set whose parameter-fibres are finite and of size at
most `C · (‖x‖_∞ + 1)`.  Then the graph of the fibre count, packed as `Fin (p+1) → ℕ` with
the parameters on `Fin.castSucc` and the count on `Fin.last p`, is semilinear. -/
theorem isSemilinearSet_properPiece_countGraph {p q : ℕ} {S : Set (Fin p ⊕ Fin q → ℕ)}
    (hS : IsProperLinearSet S)
    (hfin : ∀ x : Fin p → ℕ, Set.Finite {y : Fin q → ℕ | Sum.elim x y ∈ S})
    (C : ℕ)
    (hbd : ∀ x : Fin p → ℕ,
      Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ S} ≤ C * (Finset.univ.sup x + 1)) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ |
      Nat.card {y : Fin q → ℕ | Sum.elim (fun i => z i.castSucc) y ∈ S} = z (Fin.last p)} := by
  classical
  have hSsl : IsSemilinearSet S := hS.isLinearSet.isSemilinearSet
  obtain ⟨δ, hprog⟩ := KernelDichotomy.properLinear_fibre_progression hS hfin (C := C) hbd
  by_cases hδ : ∃ c, δ c ≠ 0
  · obtain ⟨c₀, hc₀⟩ := hδ
    refine isSemilinearSet_countGraph_of_indexSet
      (isSemilinearSet_minIndexSet hSsl c₀ (δ c₀).natAbs)
      (N := fun x => Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ S}) ?_
    intro x j
    obtain ⟨y₀, len, hiff, hreal, hcard⟩ := hprog x
    have hpar : (Sum.elim x (fun _ : Fin 1 => j)) ∘ Sum.inl = x := Sum.elim_comp_inl _ _
    simp only [Set.mem_ofPred_eq, hpar, Sum.elim_inr, hcard]
    rcases Nat.eq_zero_or_pos len with hlen | hlen
    · subst hlen
      constructor
      · rintro ⟨y, u, hy, -, -⟩
        obtain ⟨i, hi, -⟩ := (hiff y).1 hy
        omega
      · omega
    · obtain ⟨u₀, hP₀, hmin₀, hkey⟩ :=
        exists_min_index (P := fun y => Sum.elim x y ∈ S) hc₀ hiff hreal hlen
      constructor
      · rintro ⟨y, u, hy, ⟨hu, humin⟩, hyu⟩
        have huu : u c₀ = u₀ c₀ := le_antisymm (humin u₀ hP₀) (hmin₀ u hu)
        refine (hkey j).1 ⟨y, hy, ?_⟩
        rw [huu] at hyu
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hyu
      · intro hj
        obtain ⟨y, hy, hyc⟩ := (hkey j).2 hj
        exact ⟨y, u₀, hy, ⟨hP₀, hmin₀⟩, by exact_mod_cast hyc⟩
  · simp only [ne_eq, not_exists, not_not] at hδ
    refine isSemilinearSet_countGraph_of_indexSet (isSemilinearSet_zeroIndexSet hSsl)
      (N := fun x => Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ S}) ?_
    intro x j
    obtain ⟨y₀, len, hiff, hreal, hcard⟩ := hprog x
    have hpar : (Sum.elim x (fun _ : Fin 1 => j)) ∘ Sum.inl = x := Sum.elim_comp_inl _ _
    simp only [Set.mem_ofPred_eq, hpar, Sum.elim_inr]
    by_cases hne : ∃ y : Fin q → ℕ, Sum.elim x y ∈ S
    · have hlen : 0 < len := by
        obtain ⟨y, hy⟩ := hne
        obtain ⟨i, hi, -⟩ := (hiff y).1 hy
        omega
      have hsingle : {y : Fin q → ℕ | Sum.elim x y ∈ S} = {y₀} := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · intro hy
          obtain ⟨i, -, hys⟩ := (hiff y).1 hy
          funext c
          have := hys c
          rw [hδ c] at this
          exact_mod_cast this
        · rintro rfl
          exact (hiff _).2 ⟨0, hlen, fun c => by simp⟩
      rw [hsingle] at hcard
      have h1 : Nat.card ({y₀} : Set (Fin q → ℕ)) = 1 := by simp
      rw [hsingle, h1]
      simp only [hne, and_true]
      omega
    · have hempty : {y : Fin q → ℕ | Sum.elim x y ∈ S} = ∅ := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hy
        exact hne ⟨y, hy⟩
      rw [hempty]
      simp only [hne, and_false, Nat.card_eq_fintype_card]
      simp

/-- **The axiom-shaped packaging.**  `lem:presburger-counting` for a relation whose graph is
a *proper* linear set: with finite parameter-fibres of size at most `C · (‖x‖_∞ + 1)`, the
count graph is semilinear. -/
theorem count_graph_properLinear {p q : ℕ} (R : (Fin p → ℕ) → (Fin q → ℕ) → Prop)
    (hR : IsProperLinearSet {w : Fin p ⊕ Fin q → ℕ | R (w ∘ Sum.inl) (w ∘ Sum.inr)})
    (hfin : ∀ x : Fin p → ℕ, Set.Finite {y : Fin q → ℕ | R x y})
    (C : ℕ)
    (hbd : ∀ x : Fin p → ℕ,
      Nat.card {y : Fin q → ℕ | R x y} ≤ C * (Finset.univ.sup x + 1)) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ |
      Nat.card {y : Fin q → ℕ | R (fun i => z i.castSucc) y} = z (Fin.last p)} := by
  have heq : ∀ x : Fin p → ℕ,
      {y : Fin q → ℕ | Sum.elim x y ∈ {w : Fin p ⊕ Fin q → ℕ | R (w ∘ Sum.inl) (w ∘ Sum.inr)}}
        = {y : Fin q → ℕ | R x y} := by
    intro x
    ext y
    have h1 : (Sum.elim x y) ∘ Sum.inl = x := funext fun _ => rfl
    have h2 : (Sum.elim x y) ∘ Sum.inr = y := funext fun _ => rfl
    simp only [Set.mem_ofPred_eq, h1, h2]
  have h := isSemilinearSet_properPiece_countGraph hR
    (fun x => by rw [heq x]; exact hfin x) C (fun x => by rw [heq x]; exact hbd x)
  have hgraph : {z : Fin (p + 1) → ℕ |
      Nat.card {y : Fin q → ℕ | R (fun i => z i.castSucc) y} = z (Fin.last p)}
      = {z : Fin (p + 1) → ℕ | Nat.card {y : Fin q → ℕ |
        Sum.elim (fun i => z i.castSucc) y ∈
          {w : Fin p ⊕ Fin q → ℕ | R (w ∘ Sum.inl) (w ∘ Sum.inr)}} = z (Fin.last p)} := by
    ext z
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, heq]
  rw [hgraph]
  exact h

end CountPiece

/-! ## Reducing an intersection to a one-dimensional count

Intersecting a progression fibre with an arbitrary set `W` leaves a set counted by the
indices it meets: the affine map `j ↦ y₀ + j·δ` is injective as soon as `δ ≠ 0`, so the
`q`-dimensional count becomes a count of natural numbers.
-/

section Intersection

/-- The `j`-th point of the arithmetic progression with base `y₀` and direction `δ`,
truncated to `ℕ` coordinatewise.  The truncation is inert on the indices the progression
actually realises. -/
def progPoint {q : ℕ} (y₀ : Fin q → ℕ) (δ : Fin q → ℤ) (j : ℕ) : Fin q → ℕ :=
  fun c => ((y₀ c : ℤ) + j * δ c).toNat

/-- On a realised index the truncation in `progPoint` does nothing. -/
theorem progPoint_cast {q : ℕ} {y₀ : Fin q → ℕ} {δ : Fin q → ℤ} {j : ℕ}
    (h : ∃ y : Fin q → ℕ, ∀ c, (y c : ℤ) = (y₀ c : ℤ) + j * δ c) (c : Fin q) :
    ((progPoint y₀ δ j c : ℕ) : ℤ) = (y₀ c : ℤ) + j * δ c := by
  obtain ⟨y, hy⟩ := h
  refine Int.toNat_of_nonneg ?_
  rw [← hy c]
  positivity

@[simp] theorem progPoint_zero {q : ℕ} (y₀ : Fin q → ℕ) (δ : Fin q → ℤ) :
    progPoint y₀ δ 0 = y₀ := by
  funext c
  simp [progPoint]

/-- **Counting an intersection by indices.**  If the fibre of `S` over `x` is the
progression `{y₀ + j·δ : j < len}` and `δ` is nonzero, then intersecting the fibre with any
set `W` is counted by the indices whose progression point lies in `W`; the bijection is
`j ↦ y₀ + j·δ`. -/
theorem card_inter_eq_card_indices {p q : ℕ} {S W : Set (Fin p ⊕ Fin q → ℕ)}
    {δ : Fin q → ℤ} {c₀ : Fin q} (hc₀ : δ c₀ ≠ 0)
    {x : Fin p → ℕ} {y₀ : Fin q → ℕ} {len : ℕ}
    (hiff : ∀ y : Fin q → ℕ,
      Sum.elim x y ∈ S ↔ ∃ j : ℕ, j < len ∧ ∀ c, (y c : ℤ) = (y₀ c : ℤ) + j * δ c)
    (hreal : ∀ j : ℕ, j < len → ∃ y : Fin q → ℕ, ∀ c, (y c : ℤ) = (y₀ c : ℤ) + j * δ c) :
    Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ S ∧ Sum.elim x y ∈ W}
      = Nat.card {j : ℕ | j < len ∧ Sum.elim x (progPoint y₀ δ j) ∈ W} := by
  classical
  refine (Nat.card_congr (Equiv.ofBijective
    (fun j : {j : ℕ | j < len ∧ Sum.elim x (progPoint y₀ δ j) ∈ W} =>
      (⟨progPoint y₀ δ j.1, ?_, j.2.2⟩ :
        {y : Fin q → ℕ | Sum.elim x y ∈ S ∧ Sum.elim x y ∈ W})) ⟨?_, ?_⟩)).symm
  · exact (hiff _).2 ⟨j.1, j.2.1, fun c => progPoint_cast (hreal j.1 j.2.1) c⟩
  · rintro ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ h
    have hp : progPoint y₀ δ j₁ = progPoint y₀ δ j₂ := congrArg Subtype.val h
    have e₁ := progPoint_cast (hreal j₁ hj₁.1) c₀
    have e₂ := progPoint_cast (hreal j₂ hj₂.1) c₀
    rw [hp, e₂] at e₁
    have : (j₁ : ℤ) * δ c₀ = (j₂ : ℤ) * δ c₀ := by linarith
    have := mul_right_cancel₀ hc₀ this
    exact Subtype.ext (by exact_mod_cast this)
  · rintro ⟨y, hyS, hyW⟩
    obtain ⟨j, hjlt, hjs⟩ := (hiff y).1 hyS
    have hpy : progPoint y₀ δ j = y := by
      funext c
      have e := progPoint_cast (hreal j hjlt) c
      rw [← hjs c] at e
      exact_mod_cast e
    exact ⟨⟨j, hjlt, by rw [hpy]; exact hyW⟩, Subtype.ext hpy⟩

/-- Semilinear sets of `ℕ`-tuples over a finite index type are closed under intersection. -/
theorem isSemilinearSet_inter {γ : Type} [Finite γ] {S W : Set (γ → ℕ)}
    (hS : IsSemilinearSet S) (hW : IsSemilinearSet W) : IsSemilinearSet (S ∩ W) := by
  rw [← presburger.definable_iff_isSemilinearSet (A := (∅ : Set ℕ))]
  exact hS.definable.inter hW.definable

/-- The generic shape of an index set: a parameter `x` and an index `j` are related when the
fibre of `S` over `x` carries a point `y` of `W` whose `a`-coordinate exceeds the
`b`-coordinate of a selected fibre point `u` by `D · j`.  The two coordinates `a`, `b` range
over the disjoint union of the `y`- and `u`-copies of the fibre index, so either order can
be expressed. -/
private theorem isSemilinearSet_selIndexSet {p q : ℕ} {S Sel W : Set (Fin p ⊕ Fin q → ℕ)}
    (hS : IsSemilinearSet S) (hSel : IsSemilinearSet Sel) (hW : IsSemilinearSet W)
    (D : ℕ) (a b : Fin q ⊕ Fin q) :
    IsSemilinearSet {w : Fin p ⊕ Fin 1 → ℕ | ∃ y u : Fin q → ℕ,
      Sum.elim (w ∘ Sum.inl) y ∈ S ∧ Sum.elim (w ∘ Sum.inl) y ∈ W ∧
      Sum.elim (w ∘ Sum.inl) u ∈ Sel ∧
      Sum.elim y u a = Sum.elim y u b + D * w (Sum.inr 0)} := by
  classical
  rw [← presburger.definable_iff_isSemilinearSet (A := (∅ : Set ℕ))]
  set f₁ : Fin p ⊕ Fin q → (Fin p ⊕ Fin 1) ⊕ (Fin q ⊕ Fin q) :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun c => Sum.inr (Sum.inl c)) with hf₁
  set f₂ : Fin p ⊕ Fin q → (Fin p ⊕ Fin 1) ⊕ (Fin q ⊕ Fin q) :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun c => Sum.inr (Sum.inr c)) with hf₂
  have hc₁ : ∀ (w : Fin p ⊕ Fin 1 → ℕ) (z : Fin q ⊕ Fin q → ℕ),
      (Sum.elim w z) ∘ f₁ = Sum.elim (w ∘ Sum.inl) (z ∘ Sum.inl) := by
    intro w z; funext v; cases v <;> rfl
  have hc₂ : ∀ (w : Fin p ⊕ Fin 1 → ℕ) (z : Fin q ⊕ Fin q → ℕ),
      (Sum.elim w z) ∘ f₂ = Sum.elim (w ∘ Sum.inl) (z ∘ Sum.inr) := by
    intro w z; funext v; cases v <;> rfl
  have h1 := (hS.definable (A := (∅ : Set ℕ))).preimage_comp f₁
  have h1W := (hW.definable (A := (∅ : Set ℕ))).preimage_comp f₁
  have h2 := (hSel.definable (A := (∅ : Set ℕ))).preimage_comp f₂
  have h3 : (∅ : Set ℕ).Definable presburger
      {g : (Fin p ⊕ Fin 1) ⊕ (Fin q ⊕ Fin q) → ℕ |
        g (Sum.inr a) = g (Sum.inr b) + D * g (Sum.inl (Sum.inr 0))} :=
    definable_eq_add_mul _ _ _ D
  have h4 := (((h1.inter h1W).inter h2).inter h3).exists_of_finite (β := Fin q ⊕ Fin q)
  convert h4 using 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, hc₁, hc₂,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨y, u, hy, hyW, hu, heq⟩
    exact ⟨Sum.elim y u, ⟨⟨⟨by simpa using hy, by simpa using hyW⟩, by simpa using hu⟩,
      by simpa using heq⟩⟩
  · rintro ⟨z, ⟨⟨hz1, hz1W⟩, hz2⟩, hz3⟩
    refine ⟨z ∘ Sum.inl, z ∘ Sum.inr, by simpa using hz1, by simpa using hz1W,
      by simpa using hz2, ?_⟩
    rw [Sum.elim_comp_inl_inr]
    simpa using hz3

/-- **The generic index set is the progression index set.**  Under the hypotheses pinning
the selected point `u` to the base `y₀ x` of the progression and matching the coordinate
equation with the progression step, the generic index set of
`isSemilinearSet_selIndexSet` is exactly `{(x, j) | j < len x ∧ y₀ x + j·δ ∈ W}`. -/
private theorem indexSet_eq {p q : ℕ} {S W Sel : Set (Fin p ⊕ Fin q → ℕ)}
    {δ : Fin q → ℤ} {c₀ : Fin q} (hc₀ : δ c₀ ≠ 0) (D : ℕ) (a b : Fin q ⊕ Fin q)
    {y₀ : (Fin p → ℕ) → (Fin q → ℕ)} {len : (Fin p → ℕ) → ℕ}
    (hiff : ∀ (x : Fin p → ℕ) (y : Fin q → ℕ),
      Sum.elim x y ∈ S ↔ ∃ j : ℕ, j < len x ∧ ∀ c, (y c : ℤ) = (y₀ x c : ℤ) + j * δ c)
    (hreal : ∀ (x : Fin p → ℕ) (j : ℕ), j < len x →
      ∃ y : Fin q → ℕ, ∀ c, (y c : ℤ) = (y₀ x c : ℤ) + j * δ c)
    (hbase : ∀ x : Fin p → ℕ, 0 < len x → Sum.elim x (y₀ x) ∈ Sel)
    (hpin : ∀ (x : Fin p → ℕ) (u : Fin q → ℕ), Sum.elim x u ∈ Sel → u c₀ = y₀ x c₀)
    (heq : ∀ (y u : Fin q → ℕ) (j : ℕ),
      Sum.elim y u a = Sum.elim y u b + D * j ↔ (y c₀ : ℤ) = (u c₀ : ℤ) + j * δ c₀) :
    {w : Fin p ⊕ Fin 1 → ℕ | ∃ y u : Fin q → ℕ,
      Sum.elim (w ∘ Sum.inl) y ∈ S ∧ Sum.elim (w ∘ Sum.inl) y ∈ W ∧
      Sum.elim (w ∘ Sum.inl) u ∈ Sel ∧
      Sum.elim y u a = Sum.elim y u b + D * w (Sum.inr 0)}
      = {w : Fin p ⊕ Fin 1 → ℕ | w (Sum.inr 0) < len (w ∘ Sum.inl) ∧
        Sum.elim (w ∘ Sum.inl) (progPoint (y₀ (w ∘ Sum.inl)) δ (w (Sum.inr 0))) ∈ W} := by
  ext w
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, u, hyS, hyW, huSel, hE⟩
    obtain ⟨i, hilt, his⟩ := (hiff (w ∘ Sum.inl) y).1 hyS
    have hE' := (heq y u (w (Sum.inr 0))).1 hE
    rw [hpin (w ∘ Sum.inl) u huSel] at hE'
    have hmul : (i : ℤ) * δ c₀ = ((w (Sum.inr 0) : ℕ) : ℤ) * δ c₀ := by
      have := his c₀
      linarith
    have hij : i = w (Sum.inr 0) := by exact_mod_cast mul_right_cancel₀ hc₀ hmul
    subst hij
    refine ⟨hilt, ?_⟩
    have hpy : progPoint (y₀ (w ∘ Sum.inl)) δ (w (Sum.inr 0)) = y := by
      funext c
      have e := progPoint_cast (hreal (w ∘ Sum.inl) (w (Sum.inr 0)) hilt) c
      rw [← his c] at e
      exact_mod_cast e
    rw [hpy]
    exact hyW
  · rintro ⟨hjlt, hWmem⟩
    refine ⟨progPoint (y₀ (w ∘ Sum.inl)) δ (w (Sum.inr 0)), y₀ (w ∘ Sum.inl), ?_, hWmem,
      hbase _ (by omega), ?_⟩
    · exact (hiff _ _).2 ⟨w (Sum.inr 0), hjlt,
        fun c => progPoint_cast (hreal _ _ hjlt) c⟩
    · refine (heq _ _ (w (Sum.inr 0))).2 ?_
      rw [progPoint_cast (hreal _ _ hjlt) c₀]

/-- **The index set of an intersection is semilinear.**  Let `S ⊆ ℕ^p × ℕ^q` have
parameter-fibres described by the progression `{y₀ x + j·δ : j < len x}` with a fixed
nonzero direction `δ`, and let `W` be semilinear.  Then
`{(x, j) | j < len x ∧ y₀ x + j·δ ∈ W}` is a semilinear subset of `ℕ^p × ℕ`. -/
theorem isSemilinearSet_indexSet_inter {p q : ℕ} {S W : Set (Fin p ⊕ Fin q → ℕ)}
    (hS : IsSemilinearSet S) (hW : IsSemilinearSet W)
    {δ : Fin q → ℤ} {c₀ : Fin q} (hc₀ : δ c₀ ≠ 0)
    {y₀ : (Fin p → ℕ) → (Fin q → ℕ)} {len : (Fin p → ℕ) → ℕ}
    (hiff : ∀ (x : Fin p → ℕ) (y : Fin q → ℕ),
      Sum.elim x y ∈ S ↔ ∃ j : ℕ, j < len x ∧ ∀ c, (y c : ℤ) = (y₀ x c : ℤ) + j * δ c)
    (hreal : ∀ (x : Fin p → ℕ) (j : ℕ), j < len x →
      ∃ y : Fin q → ℕ, ∀ c, (y c : ℤ) = (y₀ x c : ℤ) + j * δ c) :
    IsSemilinearSet {w : Fin p ⊕ Fin 1 → ℕ | w (Sum.inr 0) < len (w ∘ Sum.inl) ∧
      Sum.elim (w ∘ Sum.inl) (progPoint (y₀ (w ∘ Sum.inl)) δ (w (Sum.inr 0))) ∈ W} := by
  classical
  have hy₀S : ∀ x : Fin p → ℕ, 0 < len x → Sum.elim x (y₀ x) ∈ S := fun x hx =>
    (hiff x (y₀ x)).2 ⟨0, hx, fun c => by simp⟩
  rcases lt_or_gt_of_ne hc₀ with hneg | hpos
  · -- `δ c₀ < 0`: the base point maximises the `c₀`-coordinate.
    obtain ⟨D, hD⟩ : ∃ D : ℕ, (D : ℤ) = -δ c₀ := ⟨(δ c₀).natAbs, by omega⟩
    set Sel : Set (Fin p ⊕ Fin q → ℕ) := {g : Fin p ⊕ Fin q → ℕ | g ∈ S ∧
      ∀ v : Fin q → ℕ, Sum.elim (g ∘ Sum.inl) v ∈ S → v c₀ ≤ g (Sum.inr c₀)} with hSeldef
    have hSelSL : IsSemilinearSet Sel := SemilinearMinMax.isSemilinearSet_maxCoord c₀ hS
    have hSelMem : ∀ (x : Fin p → ℕ) (u : Fin q → ℕ), Sum.elim x u ∈ Sel ↔
        (Sum.elim x u ∈ S ∧ ∀ v : Fin q → ℕ, Sum.elim x v ∈ S → v c₀ ≤ u c₀) := by
      intro x u; rw [hSeldef]; simp [Sum.elim_comp_inl]
    have hbase : ∀ x : Fin p → ℕ, 0 < len x → Sum.elim x (y₀ x) ∈ Sel := by
      intro x hx
      refine (hSelMem x (y₀ x)).2 ⟨hy₀S x hx, fun v hv => ?_⟩
      obtain ⟨i, -, his⟩ := (hiff x v).1 hv
      have hle : (i : ℤ) * δ c₀ ≤ (i : ℤ) * 0 :=
        mul_le_mul_of_nonneg_left hneg.le (Int.natCast_nonneg i)
      have e := his c₀
      have : ((v c₀ : ℕ) : ℤ) ≤ ((y₀ x c₀ : ℕ) : ℤ) := by simp at hle; linarith
      exact_mod_cast this
    have hpin : ∀ (x : Fin p → ℕ) (u : Fin q → ℕ), Sum.elim x u ∈ Sel → u c₀ = y₀ x c₀ := by
      intro x u hu
      obtain ⟨huS, humax⟩ := (hSelMem x u).1 hu
      obtain ⟨i, hi, -⟩ := (hiff x u).1 huS
      have hx : 0 < len x := by omega
      have h1 : u c₀ ≤ y₀ x c₀ := ((hSelMem x (y₀ x)).1 (hbase x hx)).2 u huS
      have h2 : y₀ x c₀ ≤ u c₀ := humax (y₀ x) (hy₀S x hx)
      omega
    have heq : ∀ (y u : Fin q → ℕ) (j : ℕ),
        Sum.elim y u (Sum.inr c₀) = Sum.elim y u (Sum.inl c₀) + D * j ↔
          (y c₀ : ℤ) = (u c₀ : ℤ) + j * δ c₀ := by
      intro y u j
      simp only [Sum.elim_inl, Sum.elim_inr]
      constructor
      · intro h
        have h' : ((u c₀ : ℕ) : ℤ) = ((y c₀ + D * j : ℕ) : ℤ) := by exact_mod_cast h
        push_cast at h'
        rw [hD] at h'
        linarith
      · intro h
        have h' : ((u c₀ : ℕ) : ℤ) = ((y c₀ + D * j : ℕ) : ℤ) := by
          push_cast; rw [hD]; linarith
        exact_mod_cast h'
    rw [← indexSet_eq (S := S) (W := W) (Sel := Sel) hc₀ D (Sum.inr c₀) (Sum.inl c₀)
      hiff hreal hbase hpin heq]
    exact isSemilinearSet_selIndexSet hS hSelSL hW D _ _
  · -- `δ c₀ > 0`: the base point minimises the `c₀`-coordinate.
    obtain ⟨D, hD⟩ : ∃ D : ℕ, (D : ℤ) = δ c₀ := ⟨(δ c₀).natAbs, by omega⟩
    set Sel : Set (Fin p ⊕ Fin q → ℕ) := {g : Fin p ⊕ Fin q → ℕ | g ∈ S ∧
      ∀ v : Fin q → ℕ, Sum.elim (g ∘ Sum.inl) v ∈ S → g (Sum.inr c₀) ≤ v c₀} with hSeldef
    have hSelSL : IsSemilinearSet Sel := SemilinearMinMax.isSemilinearSet_minCoord c₀ hS
    have hSelMem : ∀ (x : Fin p → ℕ) (u : Fin q → ℕ), Sum.elim x u ∈ Sel ↔
        (Sum.elim x u ∈ S ∧ ∀ v : Fin q → ℕ, Sum.elim x v ∈ S → u c₀ ≤ v c₀) := by
      intro x u; rw [hSeldef]; simp [Sum.elim_comp_inl]
    have hbase : ∀ x : Fin p → ℕ, 0 < len x → Sum.elim x (y₀ x) ∈ Sel := by
      intro x hx
      refine (hSelMem x (y₀ x)).2 ⟨hy₀S x hx, fun v hv => ?_⟩
      obtain ⟨i, -, his⟩ := (hiff x v).1 hv
      have hle : 0 ≤ (i : ℤ) * δ c₀ := mul_nonneg (Int.natCast_nonneg i) hpos.le
      have e := his c₀
      have : ((y₀ x c₀ : ℕ) : ℤ) ≤ ((v c₀ : ℕ) : ℤ) := by linarith
      exact_mod_cast this
    have hpin : ∀ (x : Fin p → ℕ) (u : Fin q → ℕ), Sum.elim x u ∈ Sel → u c₀ = y₀ x c₀ := by
      intro x u hu
      obtain ⟨huS, humin⟩ := (hSelMem x u).1 hu
      obtain ⟨i, hi, -⟩ := (hiff x u).1 huS
      have hx : 0 < len x := by omega
      have h1 : y₀ x c₀ ≤ u c₀ := ((hSelMem x (y₀ x)).1 (hbase x hx)).2 u huS
      have h2 : u c₀ ≤ y₀ x c₀ := humin (y₀ x) (hy₀S x hx)
      omega
    have heq : ∀ (y u : Fin q → ℕ) (j : ℕ),
        Sum.elim y u (Sum.inl c₀) = Sum.elim y u (Sum.inr c₀) + D * j ↔
          (y c₀ : ℤ) = (u c₀ : ℤ) + j * δ c₀ := by
      intro y u j
      simp only [Sum.elim_inl, Sum.elim_inr]
      constructor
      · intro h
        have h' : ((y c₀ : ℕ) : ℤ) = ((u c₀ + D * j : ℕ) : ℤ) := by exact_mod_cast h
        push_cast at h'
        rw [hD] at h'
        linarith
      · intro h
        have h' : ((y c₀ : ℕ) : ℤ) = ((u c₀ + D * j : ℕ) : ℤ) := by
          push_cast; rw [hD]; linarith
        exact_mod_cast h'
    rw [← indexSet_eq (S := S) (W := W) (Sel := Sel) hc₀ D (Sum.inl c₀) (Sum.inr c₀)
      hiff hreal hbase hpin heq]
    exact isSemilinearSet_selIndexSet hS hSelSL hW D _ _

/-- **Intersecting a proper linear piece is a one-dimensional count.**

For a proper linear `S ⊆ ℕ^p × ℕ^q` with finite, linearly bounded parameter-fibres and any
semilinear `W`, there is a semilinear `V ⊆ ℕ^p × ℕ` whose fibre over `x` has the same number
of elements as `S_x ∩ W_x`.  This replaces a `q`-dimensional fibre count by a count of
natural numbers, uniformly in the parameter. -/
theorem exists_indexSet_inter {p q : ℕ} {S W : Set (Fin p ⊕ Fin q → ℕ)}
    (hS : IsProperLinearSet S) (hW : IsSemilinearSet W)
    (hfin : ∀ x : Fin p → ℕ, Set.Finite {y : Fin q → ℕ | Sum.elim x y ∈ S})
    (C : ℕ)
    (hbd : ∀ x : Fin p → ℕ,
      Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ S} ≤ C * (Finset.univ.sup x + 1)) :
    ∃ V : Set (Fin p ⊕ Fin 1 → ℕ), IsSemilinearSet V ∧
      ∀ x : Fin p → ℕ,
        Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ S ∧ Sum.elim x y ∈ W}
          = Nat.card {j : ℕ | Sum.elim x (fun _ => j) ∈ V} := by
  classical
  have hSsl : IsSemilinearSet S := hS.isLinearSet.isSemilinearSet
  obtain ⟨δ, hprog⟩ := KernelDichotomy.properLinear_fibre_progression hS hfin (C := C) hbd
  choose y₀ len hiff hreal hcard using hprog
  by_cases hδ : ∃ c, δ c ≠ 0
  · obtain ⟨c₀, hc₀⟩ := hδ
    refine ⟨_, isSemilinearSet_indexSet_inter hSsl hW hc₀ hiff hreal, fun x => ?_⟩
    have hset : {j : ℕ | Sum.elim x (fun _ : Fin 1 => j) ∈
        {w : Fin p ⊕ Fin 1 → ℕ | w (Sum.inr 0) < len (w ∘ Sum.inl) ∧
          Sum.elim (w ∘ Sum.inl) (progPoint (y₀ (w ∘ Sum.inl)) δ (w (Sum.inr 0))) ∈ W}}
        = {j : ℕ | j < len x ∧ Sum.elim x (progPoint (y₀ x) δ j) ∈ W} := by
      ext j
      simp [Sum.elim_comp_inl]
    rw [hset]
    exact card_inter_eq_card_indices hc₀ (hiff x) (hreal x)
  · simp only [ne_eq, not_exists, not_not] at hδ
    set V : Set (Fin p ⊕ Fin 1 → ℕ) := {w : Fin p ⊕ Fin 1 → ℕ | w (Sum.inr 0) = 0 ∧
      ∃ y : Fin q → ℕ, Sum.elim (w ∘ Sum.inl) y ∈ S ∩ W} with hVdef
    refine ⟨V, isSemilinearSet_zeroIndexSet (isSemilinearSet_inter hSsl hW), fun x => ?_⟩
    have hV : ∀ j : ℕ, Sum.elim x (fun _ : Fin 1 => j) ∈ V ↔
        (j = 0 ∧ ∃ y : Fin q → ℕ, Sum.elim x y ∈ S ∧ Sum.elim x y ∈ W) := by
      intro j
      rw [hVdef]
      simp [Sum.elim_comp_inl]
    have hall : ∀ y : Fin q → ℕ, Sum.elim x y ∈ S → y = y₀ x := by
      intro y hy
      obtain ⟨i, -, his⟩ := (hiff x y).1 hy
      funext c
      have hc := his c
      rw [hδ c] at hc
      exact_mod_cast hc
    by_cases hne : ∃ y : Fin q → ℕ, Sum.elim x y ∈ S ∧ Sum.elim x y ∈ W
    · obtain ⟨y1, hy1S, hy1W⟩ := hne
      have hL : {y : Fin q → ℕ | Sum.elim x y ∈ S ∧ Sum.elim x y ∈ W} = {y1} := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hyS, -⟩
          rw [hall y hyS, ← hall y1 hy1S]
        · rintro rfl
          exact ⟨hy1S, hy1W⟩
      have hR : {j : ℕ | Sum.elim x (fun _ : Fin 1 => j) ∈ V} = {0} := by
        ext j
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, hV j]
        exact ⟨fun h => h.1, fun h => ⟨h, y1, hy1S, hy1W⟩⟩
      rw [hL, hR]
      simp
    · have hL : {y : Fin q → ℕ | Sum.elim x y ∈ S ∧ Sum.elim x y ∈ W} = ∅ := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hne ⟨y, h⟩
      have hR : {j : ℕ | Sum.elim x (fun _ : Fin 1 => j) ∈ V} = ∅ := by
        ext j
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, hV j]
        exact fun h => hne h.2
      rw [hL, hR]
      simp

end Intersection

end ProperPieceCount
