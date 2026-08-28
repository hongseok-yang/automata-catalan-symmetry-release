/-
# Presburger-definable extremal selection in semilinear sets

Semilinear sets are closed under the *extremal selection* operations that turn a
semilinear relation into a semilinear (partial) function: inside each fibre of a
semilinear set, pick the element minimising a designated coordinate, or the
lexicographically least element.

The proofs go through Mathlib's Ginsburg–Spanier bridge
`FirstOrder.Language.presburger.definable_iff_isSemilinearSet`.  The selection conditions
are first-order over `(ℕ, 0, 1, +)`, so they are assembled from the `Set.Definable`
combinators (`inter`, `union`, `compl`, `preimage_comp`, `forall_of_finite`) and
transported back to `IsSemilinearSet`.

## Main results

* `isSemilinearSet_fibre_forall`: the workhorse.  For semilinear `S ⊆ ℕ^ι × ℕ^κ` and a
  Presburger-definable comparison `P` between a point and a challenger from the same
  fibre, the set of `(x, v) ∈ S` beating every challenger is semilinear.
* `isSemilinearSet_minCoord` / `isSemilinearSet_maxCoord`: fibrewise minimisation and
  maximisation of one designated coordinate.
* `isSemilinearSet_minGraph`, `isSemilinearSet_minGraph_sum`,
  `isSemilinearSet_leastGraph`: the least-witness graph of a semilinear relation, in the
  `Fin (p+1)`, `Fin p ⊕ Fin 1` and relational packagings.  `minGraph_unique` shows the
  first is a function graph.
* `isSemilinearSet_lexArgmin`: lexicographic argmin selection, single-valued by
  `lexArgmin_unique`.

All statements are unconditional; no counting input is used.
-/
import Mathlib

namespace SemilinearMinMax

open Set FirstOrder Language

/-! ## Atoms: coordinate comparisons are definable -/

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

/-- The order set `{w | w 0 ≤ w 1}` on two coordinates is semilinear: it is the projection
of the linear equation `w 1 = w 0 + y`. -/
theorem isSemilinearSet_le2 : IsSemilinearSet {w : Fin 2 → ℕ | w 0 ≤ w 1} := by
  have hbase : IsSemilinearSet
      {z : Fin 2 ⊕ Fin 1 → ℕ | (z ∘ Sum.inl) 1 = (z ∘ Sum.inl) 0 + (z ∘ Sum.inr) 0} := by
    have := isSemilinearSet_forms_eq (γ := Fin 2 ⊕ Fin 1)
      (Sum.elim ![0, 1] ![0]) (Sum.elim ![1, 0] ![1])
    convert this using 1
    ext z
    simp [Fintype.sum_sum_type, Fin.sum_univ_two]
  have hproj := IsSemilinearSet.proj'
    (p := fun (x : Fin 2 → ℕ) (y : Fin 1 → ℕ) => x 1 = x 0 + y 0) hbase
  convert hproj using 1
  ext w
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h; exact ⟨fun _ => w 1 - w 0, by show w 1 = w 0 + (w 1 - w 0); omega⟩
  · rintro ⟨y, hy⟩; omega

/-- Comparison of two coordinates is Presburger-definable. -/
theorem definable_coord_le {γ : Type} [Finite γ] (p q : γ) :
    A.Definable presburger {v : γ → ℕ | v p ≤ v q} := by
  have h := (isSemilinearSet_le2.definable (A := A)).preimage_comp (![p, q] : Fin 2 → γ)
  convert h using 1
  ext v
  simp

/-- Equality of two coordinates is Presburger-definable. -/
theorem definable_coord_eq {γ : Type} [Finite γ] (p q : γ) :
    A.Definable presburger {v : γ → ℕ | v p = v q} := by
  have h := (definable_coord_le (A := A) p q).inter (definable_coord_le (A := A) q p)
  convert h using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  omega

end Atoms

/-! ## The selection workhorse

A selection condition compares the candidate `u : ι ⊕ κ → ℕ` with a challenger
`w : κ → ℕ` drawn from the same fibre.  Both live in the index type `(ι ⊕ κ) ⊕ κ`: the
candidate on `Sum.inl`, the challenger on `Sum.inr`. -/

section Workhorse

/-- **Fibrewise universal comparison preserves semilinearity.**

Let `S ⊆ ℕ^ι × ℕ^κ` be semilinear (coordinates packed as `ι ⊕ κ → ℕ`) and let `P` be a
Presburger-definable condition on candidate-plus-challenger tuples.  Then the set of
`u ∈ S` satisfying `P` against every challenger `w` in the same fibre is semilinear. -/
theorem isSemilinearSet_fibre_forall {ι κ : Type} [Finite ι] [Finite κ]
    {S : Set (ι ⊕ κ → ℕ)} (hS : IsSemilinearSet S)
    {P : Set ((ι ⊕ κ) ⊕ κ → ℕ)} (hP : (∅ : Set ℕ).Definable presburger P) :
    IsSemilinearSet {u : ι ⊕ κ → ℕ | u ∈ S ∧
      ∀ w : κ → ℕ, Sum.elim (u ∘ Sum.inl) w ∈ S → Sum.elim u w ∈ P} := by
  classical
  rw [← presburger.definable_iff_isSemilinearSet (A := (∅ : Set ℕ))]
  have hSd : (∅ : Set ℕ).Definable presburger S := hS.definable
  -- "the challenger lies in the same fibre", as a condition on `(ι ⊕ κ) ⊕ κ`
  have h2 := hSd.preimage_comp (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr :
    ι ⊕ κ → (ι ⊕ κ) ⊕ κ)
  have h4 := (h2.compl.union hP).forall_of_finite (β := κ)
  have h5 := hSd.inter h4
  convert h5 using 1
  ext u
  have hcomp : ∀ w : κ → ℕ, (Sum.elim u w) ∘ (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr :
      ι ⊕ κ → (ι ⊕ κ) ⊕ κ) = Sum.elim (u ∘ Sum.inl) w := by
    intro w; funext x; cases x <;> rfl
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
    Set.mem_preimage]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h w
    by_cases hw : Sum.elim (u ∘ Sum.inl) w ∈ S
    · exact Or.inr (h w hw)
    · exact Or.inl (by rw [hcomp w]; exact hw)
  · intro h w hw
    rcases h w with hc | hc
    · exact absurd (by rw [hcomp w]; exact hw) hc
    · exact hc

end Workhorse

/-! ## Minimising or maximising a designated coordinate over each fibre -/

section MinMaxCoord

/-- **Fibrewise coordinate minimisation preserves semilinearity.**

For semilinear `S ⊆ ℕ^ι × ℕ^κ` and a designated fibre coordinate `c : κ`, the set of
pairs `(x, v) ∈ S` whose `c`-coordinate is least over the fibre `S_x` is semilinear. -/
theorem isSemilinearSet_minCoord {ι κ : Type} [Finite ι] [Finite κ] (c : κ)
    {S : Set (ι ⊕ κ → ℕ)} (hS : IsSemilinearSet S) :
    IsSemilinearSet {u : ι ⊕ κ → ℕ | u ∈ S ∧
      ∀ w : κ → ℕ, Sum.elim (u ∘ Sum.inl) w ∈ S → u (Sum.inr c) ≤ w c} := by
  have hP : (∅ : Set ℕ).Definable presburger
      {g : (ι ⊕ κ) ⊕ κ → ℕ | g (Sum.inl (Sum.inr c)) ≤ g (Sum.inr c)} :=
    definable_coord_le _ _
  have h := isSemilinearSet_fibre_forall hS hP
  convert h using 1
  ext u
  refine and_congr_right fun _ => ?_
  exact forall_congr' fun w => by simp

/-- **Fibrewise coordinate maximisation preserves semilinearity.**  The mirror image of
`isSemilinearSet_minCoord`. -/
theorem isSemilinearSet_maxCoord {ι κ : Type} [Finite ι] [Finite κ] (c : κ)
    {S : Set (ι ⊕ κ → ℕ)} (hS : IsSemilinearSet S) :
    IsSemilinearSet {u : ι ⊕ κ → ℕ | u ∈ S ∧
      ∀ w : κ → ℕ, Sum.elim (u ∘ Sum.inl) w ∈ S → w c ≤ u (Sum.inr c)} := by
  have hP : (∅ : Set ℕ).Definable presburger
      {g : (ι ⊕ κ) ⊕ κ → ℕ | g (Sum.inr c) ≤ g (Sum.inl (Sum.inr c))} :=
    definable_coord_le _ _
  have h := isSemilinearSet_fibre_forall hS hP
  convert h using 1
  ext u
  refine and_congr_right fun _ => ?_
  exact forall_congr' fun w => by simp

/-- **Min graph, `Fin p ⊕ Fin 1` packaging.**  The `κ = Fin 1` instance of
`isSemilinearSet_minCoord`: for semilinear `S ⊆ ℕ^p × ℕ`, the set of `(x, m)` with `m`
the least value such that `(x, m) ∈ S` is semilinear. -/
theorem isSemilinearSet_minGraph_sum {p : ℕ} {S : Set (Fin p ⊕ Fin 1 → ℕ)}
    (hS : IsSemilinearSet S) :
    IsSemilinearSet {u : Fin p ⊕ Fin 1 → ℕ | u ∈ S ∧
      ∀ m : ℕ, Sum.elim (u ∘ Sum.inl) (fun _ => m) ∈ S → u (Sum.inr 0) ≤ m} := by
  have h := isSemilinearSet_minCoord (ι := Fin p) (κ := Fin 1) 0 hS
  convert h using 1
  ext u
  refine and_congr_right fun _ => ?_
  constructor
  · intro hmin w hw
    have hw' : Sum.elim (u ∘ Sum.inl) (fun _ => w 0) ∈ S := by
      have hfun : (fun _ : Fin 1 => w 0) = w := by funext i; fin_cases i; rfl
      rwa [hfun]
    exact hmin (w 0) hw'
  · intro hmin m hm
    exact hmin (fun _ => m) hm

end MinMaxCoord

/-! ## The `Fin (p+1)` packaging: least value of the last coordinate -/

section MinGraph

/-- **Min graph, `Fin (p+1)` packaging.**  For semilinear `S ⊆ ℕ^(p+1)`, the set of `z ∈ S`
whose last coordinate is the least value that keeps the point in `S` is semilinear. -/
theorem isSemilinearSet_minGraph {p : ℕ} {S : Set (Fin (p + 1) → ℕ)} (hS : IsSemilinearSet S) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ | z ∈ S ∧
      ∀ m : ℕ, Function.update z (Fin.last p) m ∈ S → z (Fin.last p) ≤ m} := by
  classical
  rw [← presburger.definable_iff_isSemilinearSet (A := (∅ : Set ℕ))]
  have hSd : (∅ : Set ℕ).Definable presburger S := hS.definable
  set f₂ : Fin (p + 1) → Fin (p + 1) ⊕ Fin 1 :=
    fun i => if i = Fin.last p then Sum.inr 0 else Sum.inl i with hf₂
  have hcomp : ∀ (z : Fin (p + 1) → ℕ) (u : Fin 1 → ℕ),
      (Sum.elim z u) ∘ f₂ = Function.update z (Fin.last p) (u 0) := by
    intro z u
    funext i
    by_cases hi : i = Fin.last p
    · subst hi; simp [hf₂, Function.update_self]
    · simp [hf₂, hi]
  have h2 := hSd.preimage_comp f₂
  have h3 : (∅ : Set ℕ).Definable presburger
      {g : Fin (p + 1) ⊕ Fin 1 → ℕ | g (Sum.inl (Fin.last p)) ≤ g (Sum.inr 0)} :=
    definable_coord_le _ _
  have h4 := (h2.compl.union h3).forall_of_finite (β := Fin 1)
  have h5 := hSd.inter h4
  convert h5 using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
    Set.mem_preimage]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h u
    by_cases hu : Function.update z (Fin.last p) (u 0) ∈ S
    · exact Or.inr (by simpa using h (u 0) hu)
    · exact Or.inl (by rw [hcomp z u]; exact hu)
  · intro h m
    have hu := h (fun _ => m)
    rw [hcomp z (fun _ => m)] at hu
    intro hm
    rcases hu with hc | hc
    · exact absurd hm hc
    · simpa using hc

/-- The min graph is single-valued: two of its points agreeing off the last coordinate
are equal. -/
theorem minGraph_unique {p : ℕ} {S : Set (Fin (p + 1) → ℕ)} {z z' : Fin (p + 1) → ℕ}
    (hz : z ∈ S ∧ ∀ m : ℕ, Function.update z (Fin.last p) m ∈ S → z (Fin.last p) ≤ m)
    (hz' : z' ∈ S ∧ ∀ m : ℕ, Function.update z' (Fin.last p) m ∈ S → z' (Fin.last p) ≤ m)
    (hagree : ∀ i : Fin p, z i.castSucc = z' i.castSucc) : z = z' := by
  classical
  have hoff : ∀ i : Fin (p + 1), i ≠ Fin.last p → z i = z' i := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hi
    exact hagree j
  have e1 : Function.update z' (Fin.last p) (z (Fin.last p)) = z := by
    funext i
    by_cases hi : i = Fin.last p
    · subst hi; simp
    · rw [Function.update_of_ne hi, hoff i hi]
  have e2 : Function.update z (Fin.last p) (z' (Fin.last p)) = z' := by
    funext i
    by_cases hi : i = Fin.last p
    · subst hi; simp
    · rw [Function.update_of_ne hi, hoff i hi]
  have h1 : z' (Fin.last p) ≤ z (Fin.last p) := hz'.2 _ (by rw [e1]; exact hz.1)
  have h2 : z (Fin.last p) ≤ z' (Fin.last p) := hz.2 _ (by rw [e2]; exact hz'.1)
  funext i
  by_cases hi : i = Fin.last p
  · subst hi; omega
  · exact hoff i hi

/-- **Least-witness graph of a semilinear relation.**  If the graph of
`R : ℕ^p → ℕ → Prop` is semilinear in the `Fin (p+1)` layout (parameters on
`Fin.castSucc`, witness on `Fin.last`), then so is the set of `z` whose last coordinate is
the least witness for its parameters. -/
theorem isSemilinearSet_leastGraph {p : ℕ} (R : (Fin p → ℕ) → ℕ → Prop)
    (hR : IsSemilinearSet {z : Fin (p + 1) → ℕ | R (fun i => z i.castSucc) (z (Fin.last p))}) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ |
      IsLeast {m : ℕ | R (fun i => z i.castSucc) m} (z (Fin.last p))} := by
  classical
  have h := isSemilinearSet_minGraph hR
  convert h using 1
  ext z
  have hup : ∀ m : ℕ, (Function.update z (Fin.last p) m ∈
      {z : Fin (p + 1) → ℕ | R (fun i => z i.castSucc) (z (Fin.last p))})
      ↔ R (fun i => z i.castSucc) m := by
    intro m
    have hpar : (fun i : Fin p => Function.update z (Fin.last p) m i.castSucc)
        = fun i : Fin p => z i.castSucc := by
      funext i
      exact Function.update_of_ne (Fin.castSucc_lt_last i).ne _ _
    simp only [Set.mem_ofPred_eq, hpar, Function.update_self]
  constructor
  · rintro ⟨hmem, hlb⟩
    exact ⟨hmem, fun m hm => hlb ((hup m).mp hm)⟩
  · rintro ⟨hmem, hlb⟩
    exact ⟨hmem, fun m hm => hlb m ((hup m).mpr hm)⟩

end MinGraph

/-! ## Lexicographic argmin -/

section Lex

variable {A : Set ℕ}

/-- Strict lexicographic order on tuples: `v` precedes `w` at the first differing
coordinate. -/
def LexLt {q : ℕ} (v w : Fin q → ℕ) : Prop :=
  ∃ j : Fin q, (∀ i : Fin q, i < j → v i = w i) ∧ v j < w j

/-- Distinct tuples are lexicographically comparable. -/
theorem lexLt_or_of_ne {q : ℕ} {v w : Fin q → ℕ} (h : v ≠ w) : LexLt v w ∨ LexLt w v := by
  classical
  have hne : {i : Fin q | v i ≠ w i}.toFinset.Nonempty := by
    by_contra hc
    apply h
    funext i
    by_contra hi
    exact hc ⟨i, by simpa using hi⟩
  set j := {i : Fin q | v i ≠ w i}.toFinset.min' hne with hjdef
  have hjmem : v j ≠ w j := by
    have := Finset.min'_mem _ hne
    simpa [hjdef] using this
  have hjlt : ∀ i : Fin q, i < j → v i = w i := by
    intro i hi
    by_contra hc
    have hle : j ≤ i := Finset.min'_le _ i (by simpa using hc)
    exact absurd hi (not_lt.mpr hle)
  rcases lt_or_gt_of_ne hjmem with hc | hc
  · exact Or.inl ⟨j, hjlt, hc⟩
  · exact Or.inr ⟨j, fun i hi => (hjlt i hi).symm, hc⟩

/-- "The tuple read at positions `b` is not lexicographically below the tuple read at
positions `a`" is Presburger-definable. -/
theorem definable_notLexLt {γ : Type} [Finite γ] {q : ℕ} (a b : Fin q → γ) :
    A.Definable presburger
      {g : γ → ℕ | ∀ j : Fin q, (∀ i : Fin q, i < j → g (a i) = g (b i)) → g (b j) ≤ g (a j)} := by
  classical
  have hbase : ∀ j : Fin q, A.Definable presburger
      {g : γ → ℕ | (∀ i : Fin q, i < j → g (a i) = g (b i)) → g (b j) ≤ g (a j)} := by
    intro j
    have h1 : ∀ i : Fin q, A.Definable presburger
        {g : γ → ℕ | i < j → g (a i) = g (b i)} := by
      intro i
      by_cases hij : i < j
      · have hset : {g : γ → ℕ | i < j → g (a i) = g (b i)}
            = {g : γ → ℕ | g (a i) = g (b i)} := by ext g; simp [hij]
        rw [hset]; exact definable_coord_eq _ _
      · have hset : {g : γ → ℕ | i < j → g (a i) = g (b i)} = Set.univ := by ext g; simp [hij]
        rw [hset]; exact Set.definable_univ
    have h2 := Set.definable_iInter_of_finite h1
    have h3 : A.Definable presburger {g : γ → ℕ | g (b j) ≤ g (a j)} := definable_coord_le _ _
    convert h2.compl.union h3 using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_iInter]
    tauto
  have h := Set.definable_iInter_of_finite hbase
  convert h using 1
  ext g
  simp [Set.mem_iInter]

/-- **Fibrewise lexicographic argmin preserves semilinearity.**

For semilinear `S ⊆ ℕ^ι × ℕ^q`, the set of pairs `(x, v) ∈ S` with `v` the
lexicographically least element of the fibre `S_x` is semilinear. -/
theorem isSemilinearSet_lexArgmin {ι : Type} [Finite ι] {q : ℕ}
    {S : Set (ι ⊕ Fin q → ℕ)} (hS : IsSemilinearSet S) :
    IsSemilinearSet {u : ι ⊕ Fin q → ℕ | u ∈ S ∧
      ∀ w : Fin q → ℕ, Sum.elim (u ∘ Sum.inl) w ∈ S → ¬ LexLt w (u ∘ Sum.inr)} := by
  classical
  have hP := definable_notLexLt (A := (∅ : Set ℕ)) (γ := (ι ⊕ Fin q) ⊕ Fin q)
    (fun i : Fin q => (Sum.inr i : (ι ⊕ Fin q) ⊕ Fin q))
    (fun i : Fin q => (Sum.inl (Sum.inr i) : (ι ⊕ Fin q) ⊕ Fin q))
  have h := isSemilinearSet_fibre_forall hS hP
  convert h using 1
  ext u
  refine and_congr_right fun _ => ?_
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  simp only [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr, LexLt, Function.comp_apply,
    not_exists, not_and, not_lt]

/-- The lexicographic argmin selection is single-valued on each fibre. -/
theorem lexArgmin_unique {ι : Type} {q : ℕ} {S : Set (ι ⊕ Fin q → ℕ)} {u u' : ι ⊕ Fin q → ℕ}
    (hu : u ∈ S ∧ ∀ w : Fin q → ℕ, Sum.elim (u ∘ Sum.inl) w ∈ S → ¬ LexLt w (u ∘ Sum.inr))
    (hu' : u' ∈ S ∧ ∀ w : Fin q → ℕ, Sum.elim (u' ∘ Sum.inl) w ∈ S → ¬ LexLt w (u' ∘ Sum.inr))
    (hagree : u ∘ Sum.inl = u' ∘ Sum.inl) : u = u' := by
  have hue : Sum.elim (u ∘ Sum.inl) (u ∘ Sum.inr) = u := by funext x; cases x <;> rfl
  have hu'e : Sum.elim (u' ∘ Sum.inl) (u' ∘ Sum.inr) = u' := by funext x; cases x <;> rfl
  have hcore : u ∘ Sum.inr = u' ∘ Sum.inr := by
    by_contra hne
    rcases lexLt_or_of_ne hne with h | h
    · exact hu'.2 (u ∘ Sum.inr) (by rw [← hagree, hue]; exact hu.1) h
    · exact hu.2 (u' ∘ Sum.inr) (by rw [hagree, hu'e]; exact hu'.1) h
  funext x
  cases x with
  | inl i => exact congrFun hagree i
  | inr j => exact congrFun hcore j

end Lex

end SemilinearMinMax
