/-
# Bounded parametric Presburger counting in arbitrary fibre dimension

The one-dimensional case (`CountBaseCase.isSemilinearSet_countGraph_dim_one`) is lifted here
to fibres of any dimension, proving `lem:presburger-counting` outright.

The reduction has three moves.  A semilinear set is a finite union of *proper* linear pieces,
so the count of a fibre is determined by the counts of the fibres of the finite intersections
of pieces (`isSemilinearSet_countGraph_biUnion`, the `ℕ^q` analogue of the base-case engine:
it needs only the two-set identity `|B ∪ C| + |B ∩ C| = |B| + |C|` and the closure of
semilinear graphs under `+` and `-`).  Each such intersection is contained in one proper piece
`L`, whose fibres the kernel dichotomy presents as arithmetic progressions
`{y₀(x) + j·δ : j < len(x)}` with a direction `δ` independent of `x`.  When `δ ≠ 0` the map
`j ↦ y₀(x) + j·δ` is injective, so the count of the intersection equals the count of a set of
*indices* `j` — a one-dimensional problem, solved by the base case.  When `δ = 0` every fibre
of `L` has at most one point and the count is `0` or `1` according to a semilinear condition.

## Main results

* `isSemilinearSet_interCountGraph`: the count graph of `S ∩ W` for a proper linear `S` with
  bounded fibres and a semilinear `W`.
* `isSemilinearSet_countGraph_biUnion`: intersections to unions, for `ℕ^q` fibres.
* `isSemilinearSet_countGraph_general`: the count graph of an arbitrary semilinear set with
  finite, linearly bounded fibres.
* `count_graph_semilinear_proved`: the same statement in the relational packaging of
  `lem:presburger-counting`, which `PresburgerCounting.count_graph_semilinear` re-exports.

All statements are unconditional; nothing is admitted.
-/
import RequestProject.KernelDichotomy
import RequestProject.SemilinearGraphArith
import RequestProject.ProperPieceCount
import RequestProject.CountBaseCase

namespace CountGeneral

open Set FirstOrder Language

/-! ## Fibres of a subset of `ℕ^p × ℕ^q` -/

/-- The parameter-fibre of `A ⊆ ℕ^p × ℕ^q` over `x`, read as a set of `q`-tuples. -/
def qfib {p q : ℕ} (A : Set (Fin p ⊕ Fin q → ℕ)) (x : Fin p → ℕ) : Set (Fin q → ℕ) :=
  {y : Fin q → ℕ | Sum.elim x y ∈ A}

@[simp] theorem mem_qfib {p q : ℕ} {A : Set (Fin p ⊕ Fin q → ℕ)} {x : Fin p → ℕ}
    {y : Fin q → ℕ} : y ∈ qfib A x ↔ Sum.elim x y ∈ A := Iff.rfl

theorem qfib_mono {p q : ℕ} {A B : Set (Fin p ⊕ Fin q → ℕ)} (h : A ⊆ B) (x : Fin p → ℕ) :
    qfib A x ⊆ qfib B x := fun _ hy => h hy

/-- The fibre count is the cardinality of the fibre. -/
theorem card_qfib {p q : ℕ} (A : Set (Fin p ⊕ Fin q → ℕ)) (x : Fin p → ℕ) :
    Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ A} = (qfib A x).ncard := rfl

theorem finite_qfib_biUnion {p q : ℕ} {ι : Type*} {A : ι → Set (Fin p ⊕ Fin q → ℕ)}
    (s : Finset ι) (hfin : ∀ (i : ι) (x : Fin p → ℕ), (qfib (A i) x).Finite) (x : Fin p → ℕ) :
    (qfib (⋃ i ∈ s, A i) x).Finite := by
  have h : qfib (⋃ i ∈ s, A i) x = ⋃ i ∈ (s : Set ι), qfib (A i) x := by
    ext y; simp [qfib]
  rw [h]
  exact Set.Finite.biUnion s.finite_toSet (fun i _ => hfin i x)

/-! ## The degenerate index set

When the progression direction vanishes the fibre carries at most one point, so the only
index that can occur is `0`, and it occurs exactly over a nonempty fibre.
-/

/-- `{(x, j) | j = 0 ∧ the fibre of `A` over `x` is nonempty}` is semilinear. -/
private theorem isSemilinearSet_zeroIndexSet {p q : ℕ} {A : Set (Fin p ⊕ Fin q → ℕ)}
    (hA : IsSemilinearSet A) :
    IsSemilinearSet {w : Fin p ⊕ Fin 1 → ℕ |
      w (Sum.inr 0) = 0 ∧ ∃ y : Fin q → ℕ, Sum.elim (w ∘ Sum.inl) y ∈ A} := by
  classical
  rw [← presburger.definable_iff_isSemilinearSet (A := (∅ : Set ℕ))]
  set f : Fin p ⊕ Fin q → (Fin p ⊕ Fin 1) ⊕ Fin q :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun c => Sum.inr c) with hf
  have hc : ∀ (w : Fin p ⊕ Fin 1 → ℕ) (y : Fin q → ℕ),
      (Sum.elim w y) ∘ f = Sum.elim (w ∘ Sum.inl) y := by
    intro w y; funext v; cases v <;> rfl
  have h1 : (∅ : Set ℕ).Definable presburger
      {w : Fin p ⊕ Fin 1 → ℕ | w (Sum.inr 0) = 0} :=
    ProperPieceCount.definable_coord_const _ 0
  have h2 := ((hA.definable (A := (∅ : Set ℕ))).preimage_comp f).exists_of_finite (β := Fin q)
  convert h1.inter h2 using 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, hc]

/-! ## Reducing an intersection with a proper piece to one dimension -/

/-- **The one-dimensional replacement of a fibre count, with finite fibres.**

For a proper linear `S ⊆ ℕ^p × ℕ^q` with finite, linearly bounded parameter-fibres and any
semilinear `W`, there is a semilinear `V ⊆ ℕ^p × ℕ` whose fibres are finite and carry as many
elements as `S_x ∩ W_x`.  This is `ProperPieceCount.exists_indexSet_inter` strengthened by the
finiteness clause, which the base case consumes. -/
theorem exists_indexSet_inter_finite {p q : ℕ} {S W : Set (Fin p ⊕ Fin q → ℕ)}
    (hS : IsProperLinearSet S) (hW : IsSemilinearSet W)
    (hfin : ∀ x : Fin p → ℕ, Set.Finite {y : Fin q → ℕ | Sum.elim x y ∈ S})
    (C : ℕ)
    (hbd : ∀ x : Fin p → ℕ,
      Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ S} ≤ C * (Finset.univ.sup x + 1)) :
    ∃ V : Set (Fin p ⊕ Fin 1 → ℕ), IsSemilinearSet V ∧
      (∀ x : Fin p → ℕ, Set.Finite {j : ℕ | Sum.elim x (fun _ => j) ∈ V}) ∧
      ∀ x : Fin p → ℕ,
        Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ S ∧ Sum.elim x y ∈ W}
          = Nat.card {j : ℕ | Sum.elim x (fun _ => j) ∈ V} := by
  classical
  have hSsl : IsSemilinearSet S := hS.isLinearSet.isSemilinearSet
  obtain ⟨δ, hprog⟩ := KernelDichotomy.properLinear_fibre_progression hS hfin (C := C) hbd
  choose y₀ len hiff hreal hcard using hprog
  by_cases hδ : ∃ c, δ c ≠ 0
  · obtain ⟨c₀, hc₀⟩ := hδ
    have hset : ∀ x : Fin p → ℕ,
        {j : ℕ | Sum.elim x (fun _ : Fin 1 => j) ∈
          {w : Fin p ⊕ Fin 1 → ℕ | w (Sum.inr 0) < len (w ∘ Sum.inl) ∧
            Sum.elim (w ∘ Sum.inl)
              (ProperPieceCount.progPoint (y₀ (w ∘ Sum.inl)) δ (w (Sum.inr 0))) ∈ W}}
          = {j : ℕ | j < len x ∧ Sum.elim x (ProperPieceCount.progPoint (y₀ x) δ j) ∈ W} := by
      intro x
      ext j
      simp [Sum.elim_comp_inl]
    refine ⟨_, ProperPieceCount.isSemilinearSet_indexSet_inter hSsl hW hc₀ hiff hreal,
      fun x => ?_, fun x => ?_⟩
    · rw [hset x]
      exact (Set.finite_lt_nat (len x)).subset fun j hj => hj.1
    · rw [hset x]
      exact ProperPieceCount.card_inter_eq_card_indices hc₀ (hiff x) (hreal x)
  · simp only [ne_eq, not_exists, not_not] at hδ
    set V : Set (Fin p ⊕ Fin 1 → ℕ) := {w : Fin p ⊕ Fin 1 → ℕ | w (Sum.inr 0) = 0 ∧
      ∃ y : Fin q → ℕ, Sum.elim (w ∘ Sum.inl) y ∈ S ∩ W} with hVdef
    have hV : ∀ (x : Fin p → ℕ) (j : ℕ), Sum.elim x (fun _ : Fin 1 => j) ∈ V ↔
        (j = 0 ∧ ∃ y : Fin q → ℕ, Sum.elim x y ∈ S ∧ Sum.elim x y ∈ W) := by
      intro x j
      rw [hVdef]
      simp [Sum.elim_comp_inl]
    refine ⟨V, isSemilinearSet_zeroIndexSet
      (ProperPieceCount.isSemilinearSet_inter hSsl hW), fun x => ?_, fun x => ?_⟩
    · refine (Set.finite_singleton 0).subset fun j hj => ?_
      exact (hV x j).1 hj |>.1
    · have hall : ∀ y : Fin q → ℕ, Sum.elim x y ∈ S → y = y₀ x := by
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
          simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, hV x j]
          exact ⟨fun h => h.1, fun h => ⟨h, y1, hy1S, hy1W⟩⟩
        rw [hL, hR]
        simp
      · have hL : {y : Fin q → ℕ | Sum.elim x y ∈ S ∧ Sum.elim x y ∈ W} = ∅ := by
          ext y
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hne ⟨y, h⟩
        have hR : {j : ℕ | Sum.elim x (fun _ : Fin 1 => j) ∈ V} = ∅ := by
          ext j
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, hV x j]
          exact fun h => hne h.2
        rw [hL, hR]
        simp

/-- **The count graph of an intersection with a proper piece.**

For a proper linear `S ⊆ ℕ^p × ℕ^q` with finite parameter-fibres of size at most
`C · (‖x‖_∞ + 1)` and any semilinear `W`, the graph of `x ↦ |S_x ∩ W_x|` is semilinear. -/
theorem isSemilinearSet_interCountGraph {p q : ℕ} {S W : Set (Fin p ⊕ Fin q → ℕ)}
    (hS : IsProperLinearSet S) (hW : IsSemilinearSet W)
    (hfin : ∀ x : Fin p → ℕ, Set.Finite {y : Fin q → ℕ | Sum.elim x y ∈ S})
    (C : ℕ)
    (hbd : ∀ x : Fin p → ℕ,
      Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ S} ≤ C * (Finset.univ.sup x + 1)) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ |
      Nat.card {y : Fin q → ℕ | Sum.elim (fun i => z i.castSucc) y ∈ S ∧
        Sum.elim (fun i => z i.castSucc) y ∈ W} = z (Fin.last p)} := by
  obtain ⟨V, hV, hVfin, hVcard⟩ := exists_indexSet_inter_finite hS hW hfin C hbd
  have hVbd : ∀ x : Fin p → ℕ,
      Nat.card {n : ℕ | Sum.elim x (fun _ => n) ∈ V} ≤ C * (Finset.univ.sup x + 1) := by
    intro x
    refine le_trans (le_of_eq (hVcard x).symm) (le_trans ?_ (hbd x))
    exact Set.ncard_le_ncard (fun y hy => hy.1) (hfin x)
  have h := CountBaseCase.isSemilinearSet_countGraph_nat hV hVfin C hVbd
  have hgraph : {z : Fin (p + 1) → ℕ |
      Nat.card {y : Fin q → ℕ | Sum.elim (fun i => z i.castSucc) y ∈ S ∧
        Sum.elim (fun i => z i.castSucc) y ∈ W} = z (Fin.last p)}
      = {z : Fin (p + 1) → ℕ |
        Nat.card {n : ℕ | Sum.elim (fun i => z i.castSucc) (fun _ => n) ∈ V}
          = z (Fin.last p)} := by
    ext z
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hVcard]
  rw [hgraph]
  exact h

/-! ## From intersections to unions -/

/-- **From intersections to unions, in fibre dimension `q`.**  If every nonempty finite
intersection of the family `A` has a semilinear count graph, so does every finite union.  The
induction rests on the two-set identity `|B ∪ C| + |B ∩ C| = |B| + |C|` applied to `B = A a`
and `C = ⋃_{i ∈ s} A i`; the correction term `A a ∩ ⋃_{i ∈ s} A i = ⋃_{i ∈ s} (A a ∩ A i)` is
a shorter union of the same kind. -/
theorem isSemilinearSet_countGraph_biUnion {p q : ℕ} {ι : Type} [DecidableEq ι]
    (s : Finset ι) :
    ∀ A : ι → Set (Fin p ⊕ Fin q → ℕ),
      (∀ (i : ι) (x : Fin p → ℕ), (qfib (A i) x).Finite) →
      (∀ T : Finset ι, T.Nonempty → IsSemilinearSet {z : Fin (p + 1) → ℕ |
        (qfib (⋂ i ∈ T, A i) (fun i => z i.castSucc)).ncard = z (Fin.last p)}) →
      IsSemilinearSet {z : Fin (p + 1) → ℕ |
        (qfib (⋃ i ∈ s, A i) (fun i => z i.castSucc)).ncard = z (Fin.last p)} := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro A _ _
    convert SemilinearGraphArith.isSemilinearSet_graph_const (p := p) 0 using 1
    ext z
    simp [qfib]
  | @insert a s' ha ih =>
    intro A hfin hgraph
    have hA : IsSemilinearSet {z : Fin (p + 1) → ℕ |
        (qfib (A a) (fun i => z i.castSucc)).ncard = z (Fin.last p)} := by
      have h := hgraph {a} (Finset.singleton_nonempty a)
      have hset : (⋂ i ∈ ({a} : Finset ι), A i) = A a := by ext w; simp
      rwa [hset] at h
    have hU' := ih A hfin hgraph
    have hInt : IsSemilinearSet {z : Fin (p + 1) → ℕ |
        (qfib (⋃ i ∈ s', A a ∩ A i) (fun i => z i.castSucc)).ncard = z (Fin.last p)} := by
      refine ih (fun i => A a ∩ A i) (fun i x => (hfin i x).subset fun y hy => hy.2) ?_
      intro T hT
      have h := hgraph (insert a T) (Finset.insert_nonempty a T)
      have hset : (⋂ i ∈ T, A a ∩ A i) = ⋂ i ∈ insert a T, A i := by
        ext w
        simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_insert]
        constructor
        · intro hw i hi
          rcases hi with rfl | hi
          · obtain ⟨j, hj⟩ := hT
            exact (hw j hj).1
          · exact (hw i hi).2
        · intro hw i hi
          exact ⟨hw a (Or.inl rfl), hw i (Or.inr hi)⟩
      rw [hset]
      exact h
    have hUeq : ∀ x : Fin p → ℕ,
        (qfib (⋃ i ∈ insert a s', A i) x).ncard + (qfib (⋃ i ∈ s', A a ∩ A i) x).ncard
          = (qfib (A a) x).ncard + (qfib (⋃ i ∈ s', A i) x).ncard := by
      intro x
      have e1 : qfib (⋃ i ∈ insert a s', A i) x = qfib (A a) x ∪ qfib (⋃ i ∈ s', A i) x := by
        ext y
        simp only [qfib, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_union, Finset.mem_insert,
          exists_prop]
        constructor
        · rintro ⟨i, hi | hi, hy⟩
          · exact Or.inl (hi ▸ hy)
          · exact Or.inr ⟨i, hi, hy⟩
        · rintro (hy | ⟨i, hi, hy⟩)
          · exact ⟨a, Or.inl rfl, hy⟩
          · exact ⟨i, Or.inr hi, hy⟩
      have e2 : qfib (⋃ i ∈ s', A a ∩ A i) x = qfib (A a) x ∩ qfib (⋃ i ∈ s', A i) x := by
        ext y
        simp only [qfib, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
        constructor
        · rintro ⟨i, hi, hy1, hy2⟩
          exact ⟨hy1, i, hi, hy2⟩
        · rintro ⟨hy1, i, hi, hy2⟩
          exact ⟨i, hi, hy1, hy2⟩
      rw [e1, e2]
      exact Set.ncard_union_add_ncard_inter _ _ (hfin a x) (finite_qfib_biUnion s' hfin x)
    exact SemilinearGraphArith.isSemilinearSet_graph_sub
      (f₁ := fun x => (qfib (A a) x).ncard + (qfib (⋃ i ∈ s', A i) x).ncard)
      (f₂ := fun x => (qfib (⋃ i ∈ s', A a ∩ A i) x).ncard)
      (g := fun x => (qfib (⋃ i ∈ insert a s', A i) x).ncard)
      (SemilinearGraphArith.isSemilinearSet_graph_add
        (f₁ := fun x => (qfib (A a) x).ncard)
        (f₂ := fun x => (qfib (⋃ i ∈ s', A i) x).ncard) hA hU')
      hInt hUeq

/-! ## The general counting theorem -/

/-- **`lem:presburger-counting`.**  For a semilinear `S ⊆ ℕ^p × ℕ^q` whose parameter-fibres are
finite and of size at most `C · (‖x‖_∞ + 1)`, the count graph, packed as `Fin (p+1) → ℕ` with
the parameters on `Fin.castSucc` and the count on `Fin.last p`, is semilinear. -/
theorem isSemilinearSet_countGraph_general {p q : ℕ} {S : Set (Fin p ⊕ Fin q → ℕ)}
    (hS : IsSemilinearSet S)
    (hfin : ∀ x : Fin p → ℕ, Set.Finite {y : Fin q → ℕ | Sum.elim x y ∈ S})
    (C : ℕ)
    (hbd : ∀ x : Fin p → ℕ,
      Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ S} ≤ C * (Finset.univ.sup x + 1)) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ |
      Nat.card {y : Fin q → ℕ | Sum.elim (fun i => z i.castSucc) y ∈ S} = z (Fin.last p)} := by
  classical
  have hfinS : ∀ x : Fin p → ℕ, (qfib S x).Finite := hfin
  -- decompose into proper linear pieces
  obtain ⟨𝒮, h𝒮, hSeq⟩ := isProperSemilinearSet_iff.1 hS.isProperSemilinearSet
  set ι : Type := {t : Set (Fin p ⊕ Fin q → ℕ) // t ∈ 𝒮} with hι
  set L : ι → Set (Fin p ⊕ Fin q → ℕ) := fun i => (i : Set (Fin p ⊕ Fin q → ℕ)) with hL
  have hSU : S = ⋃ i ∈ (Finset.univ : Finset ι), L i := by
    rw [hSeq]
    ext w
    constructor
    · rintro ⟨t, ht, hwt⟩
      exact Set.mem_iUnion₂.2 ⟨⟨t, Finset.mem_coe.1 ht⟩, Finset.mem_univ _, hwt⟩
    · intro hw
      obtain ⟨i, -, hwi⟩ := Set.mem_iUnion₂.1 hw
      exact ⟨(i : Set (Fin p ⊕ Fin q → ℕ)), Finset.mem_coe.2 i.2, hwi⟩
  have hLsub : ∀ i : ι, L i ⊆ S := by
    intro i w hw
    rw [hSU]
    exact Set.mem_biUnion (Finset.mem_univ i) hw
  have hLprop : ∀ i : ι, IsProperLinearSet (L i) := fun i => h𝒮 (L i) i.2
  have hLsl : ∀ i : ι, IsSemilinearSet (L i) := fun i => (hLprop i).isLinearSet.isSemilinearSet
  have hLfin : ∀ (i : ι) (x : Fin p → ℕ), Set.Finite {y : Fin q → ℕ | Sum.elim x y ∈ L i} :=
    fun i x => (hfin x).subset (fun y hy => hLsub i hy)
  have hLbd : ∀ (i : ι) (x : Fin p → ℕ),
      Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ L i} ≤ C * (Finset.univ.sup x + 1) := by
    intro i x
    calc Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ L i}
        = (qfib (L i) x).ncard := card_qfib _ _
      _ ≤ (qfib S x).ncard := Set.ncard_le_ncard (qfib_mono (hLsub i) x) (hfinS x)
      _ = Nat.card {y : Fin q → ℕ | Sum.elim x y ∈ S} := (card_qfib _ _).symm
      _ ≤ C * (Finset.univ.sup x + 1) := hbd x
  -- every nonempty intersection of pieces has a semilinear count graph
  have hInt : ∀ T : Finset ι, T.Nonempty → IsSemilinearSet {z : Fin (p + 1) → ℕ |
      (qfib (⋂ i ∈ T, L i) (fun i => z i.castSucc)).ncard = z (Fin.last p)} := by
    intro T hT
    obtain ⟨i₀, hi₀⟩ := hT
    have hWsl : IsSemilinearSet (⋂ i ∈ T, L i) :=
      CountBaseCase.isSemilinearSet_biInter_finset T hLsl
    have h := isSemilinearSet_interCountGraph (hLprop i₀) hWsl (hLfin i₀) C (hLbd i₀)
    have hsete : ∀ x : Fin p → ℕ,
        {y : Fin q → ℕ | Sum.elim x y ∈ L i₀ ∧ Sum.elim x y ∈ ⋂ i ∈ T, L i}
          = qfib (⋂ i ∈ T, L i) x := by
      intro x
      ext y
      simp only [Set.mem_ofPred_eq, mem_qfib]
      exact ⟨fun hy => hy.2, fun hy => ⟨Set.mem_iInter₂.1 hy i₀ hi₀, hy⟩⟩
    have hconv : {z : Fin (p + 1) → ℕ |
        (qfib (⋂ i ∈ T, L i) (fun i => z i.castSucc)).ncard = z (Fin.last p)}
        = {z : Fin (p + 1) → ℕ |
          Nat.card {y : Fin q → ℕ | Sum.elim (fun i => z i.castSucc) y ∈ L i₀ ∧
            Sum.elim (fun i => z i.castSucc) y ∈ ⋂ i ∈ T, L i} = z (Fin.last p)} := by
      ext z
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hsete]
      rfl
    rw [hconv]
    exact h
  have hU := isSemilinearSet_countGraph_biUnion (Finset.univ : Finset ι) L
    (fun i x => (hLfin i x)) hInt
  have hconv : {z : Fin (p + 1) → ℕ |
      Nat.card {y : Fin q → ℕ | Sum.elim (fun i => z i.castSucc) y ∈ S} = z (Fin.last p)}
      = {z : Fin (p + 1) → ℕ |
        (qfib (⋃ i ∈ (Finset.univ : Finset ι), L i) (fun i => z i.castSucc)).ncard
          = z (Fin.last p)} := by
    rw [← hSU]
    rfl
  rw [hconv]
  exact hU

/-- **`lem:presburger-counting`, relational packaging.**  For a relation `R ⊆ ℕ^p × ℕ^q` with
semilinear graph, finite fibres and a linear fibre bound, the count graph is semilinear.  This
is the statement re-exported as `PresburgerCounting.count_graph_semilinear`. -/
theorem count_graph_semilinear_proved {p q : ℕ}
    (R : (Fin p → ℕ) → (Fin q → ℕ) → Prop)
    (hR : IsSemilinearSet {w : Fin p ⊕ Fin q → ℕ | R (w ∘ Sum.inl) (w ∘ Sum.inr)})
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
  have h := isSemilinearSet_countGraph_general hR
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

end CountGeneral
