/-
# Counting MSO-definable positions along a block-linear slice

The bridge from MSO-definability to the *counting* layer: for a block-linear two-parameter
word family `F` and an MSO-definable relation `R` on (word, position tuple), the number of
positions of `F.eval mS n` satisfying `R` at a given parameter tuple has a semilinear graph
as a two-parameter slice family.

Three ingredients meet here.

* `SliceSemilinearN.BlockLinearWord2.length_eval` — the slice word's length is an explicit
  ℕ-affine function of `(mS, n)`, hence bounded by `lenBound · (mS + n + 1)`
  (`BlockLinearWord2.length_eval_le`).  This is what makes the counted fibres — subsets of
  the slice's positions — obey the *linear* bound that
  `PresburgerCounting.count_graph_semilinear` requires.
* `SliceSemilinearN.msoDefinableRel2_semilinear_general` makes the position/parameter
  relation a semilinear family.
* `PresburgerCounting.count_graph_semilinear` (a theorem) turns a semilinear family with
  linearly bounded finite fibres into a semilinear count graph.

`count_last_semilinear` is the packaging step: it counts the LAST atom coordinate of a
two-parameter semilinear family, keeping the other atom coordinates as parameters, and
returns the count graph in the same `Fin (k+1)` layout (parameters on `Fin.castSucc`, the
count on `Fin.last`).  `msoCount_semilinear` is its MSO instance, and
`detAuto_state_letter_count_semilinear` / `rankSource_state_letter_count_semilinear` are the
`(state before, letter)` position counts that a prefix rank decomposes into;
`prefixRank_eq_sum_counts` is that decomposition — `RankSource.prefixRank` is the fixed
`ω`-weighted ℤ-combination of those counts.

The state predicate enters through the **theorem** `SliceMSO.detAuto_state_mso` (the
automaton ⇒ MSO half of Büchi–Elgot–Trakhtenbrot), not through the `buchi` axiom;
`count_last_semilinear` and `prefixRank_eq_sum_counts` are axiom-clean, and the MSO counts
admit only `msoDefinableRel2_semilinear_general`.
-/
import RequestProject.SliceSemilinear2
import RequestProject.PresburgerCounting
import RequestProject.SemilinearGraphArith
import RequestProject.SliceMSO
import RequestProject.SliceFasGates

namespace SliceSemilinearN

/-! ## The length of a block-linear slice is affine in the two parameters -/

/-- The flattening of `m` copies of `b` has length `m · |b|`. -/
theorem length_flatten_replicate {α : Type*} (m : ℕ) (b : List α) :
    ((List.replicate m b).flatten).length = m * b.length := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; ring

/-- **The slice length is ℕ-affine in `(mS, n)`**: block `(b, a_mS, a_n, c)` contributes
`(a_mS·mS + a_n·n + c)·|b|` letters. -/
theorem BlockLinearWord2.length_eval {Alpha : Type*} (F : BlockLinearWord2 Alpha) (mS n : ℕ) :
    (F.eval mS n).length
      = (F.blocks.map (fun x => (x.2.1 * mS + x.2.2.1 * n + x.2.2.2) * x.1.length)).sum := by
  unfold BlockLinearWord2.eval
  rw [List.length_flatten, List.map_map]
  refine congrArg List.sum (List.map_congr_left ?_)
  rintro ⟨b, aMS, aN, c⟩ _
  exact length_flatten_replicate _ b

/-- The constant of the linear length bound: the sum over blocks of
`(a_mS + a_n + c)·|b|`. -/
def BlockLinearWord2.lenBound {Alpha : Type*} (F : BlockLinearWord2 Alpha) : ℕ :=
  (F.blocks.map (fun x => (x.2.1 + x.2.2.1 + x.2.2.2) * x.1.length)).sum

/-- **The slice length obeys a linear bound in `mS + n`.**  This is the hypothesis shape of
`PresburgerCounting.count_graph_semilinear`: a fibre of positions of `F.eval mS n` has at
most `lenBound · (mS + n + 1)` elements. -/
theorem BlockLinearWord2.length_eval_le {Alpha : Type*} (F : BlockLinearWord2 Alpha)
    (mS n : ℕ) : (F.eval mS n).length ≤ F.lenBound * (mS + n + 1) := by
  rw [F.length_eval mS n, BlockLinearWord2.lenBound, ← List.sum_map_mul_right]
  refine List.sum_le_sum ?_
  rintro ⟨b, aMS, aN, c⟩ _
  simp only
  have hkey : aMS * mS + aN * n + c ≤ (aMS + aN + c) * (mS + n + 1) := by
    nlinarith [Nat.zero_le aMS, Nat.zero_le aN, Nat.zero_le c, Nat.zero_le mS, Nat.zero_le n]
  calc (aMS * mS + aN * n + c) * b.length
      ≤ ((aMS + aN + c) * (mS + n + 1)) * b.length := Nat.mul_le_mul_right _ hkey
    _ = (aMS + aN + c) * b.length * (mS + n + 1) := by ring

end SliceSemilinearN

/-- A rank source read as a deterministic acceptor (the accepting set is irrelevant: only
the run is used). -/
def RankSource.toDetAuto {Alpha : Type*} {d : ℕ} (A : RankSource Alpha d) :
    SliceMSO.DetAuto Alpha where
  Q := A.Q
  fintypeQ := A.fintypeQ
  q0 := A.q0
  δ := A.δ
  accept := fun _ => True

@[simp] theorem RankSource.toDetAuto_stateBefore {Alpha : Type*} {d : ℕ}
    (A : RankSource Alpha d) (w : List Alpha) (i : ℕ) :
    A.toDetAuto.stateBefore w i = A.stateBefore w i := rfl

namespace SliceMSOCount

open SliceSemilinearN MSO

/-! ## Counting the last atom coordinate of a two-parameter semilinear family

`PresburgerCounting.count_graph_semilinear` is stated with `p` parameter coordinates and `q`
fibre coordinates, packed as `Fin p ⊕ Fin q`.  A two-parameter slice family
`Φ : ℕ → ℕ → (Fin (k+1) → ℕ) → Prop` whose LAST atom coordinate is the one to be counted is
its `p = k + 2`, `q = 1` instance: `(mS, n)` and the first `k` atom coordinates are
parameters, the last atom coordinate is the fibre.  `countSel` is the reindexing between the
two packings. -/

/-- Reindexing `Fin (k+3)` (the packed `(mS, n, params, position)` tuple) as
`Fin (k+2) ⊕ Fin 1` (parameters, then the counted position). -/
private def countSel (k : ℕ) : Fin (k + 3) → (Fin (k + 2) ⊕ Fin 1) := fun j =>
  if h : (j : ℕ) < k + 2 then Sum.inl ⟨j, h⟩ else Sum.inr 0

private theorem countSel_zero (k : ℕ) : countSel k 0 = Sum.inl 0 := rfl

private theorem countSel_one (k : ℕ) : countSel k 1 = Sum.inl 1 := rfl

private theorem countSel_cast (k : ℕ) (t : Fin k) :
    countSel k (t.castSucc.succ.succ) = Sum.inl t.succ.succ := by
  unfold countSel
  have hv : ((t.castSucc.succ.succ : Fin (k + 3)) : ℕ) = t + 2 := by simp [Fin.val_succ]
  rw [dif_pos (by rw [hv]; omega)]
  congr 1

private theorem countSel_last (k : ℕ) :
    countSel k ((Fin.last k).succ.succ) = Sum.inr 0 := by
  unfold countSel
  have hv : (((Fin.last k).succ.succ : Fin (k + 3)) : ℕ) = k + 2 := by simp
  rw [dif_neg (by rw [hv]; omega)]

private theorem snoc_countSel {k : ℕ} (u : (Fin (k + 2) ⊕ Fin 1) → ℕ) :
    (fun i : Fin (k + 1) => u (countSel k i.succ.succ))
      = @Fin.snoc k (fun _ => ℕ) (fun t : Fin k => u (Sum.inl t.succ.succ)) (u (Sum.inr 0)) := by
  funext i
  induction i using Fin.lastCases with
  | last => rw [countSel_last, Fin.snoc_last]
  | cast t => rw [countSel_cast, Fin.snoc_castSucc]

private theorem cs_zero (k : ℕ) : ((0 : Fin (k + 2)).castSucc : Fin (k + 3)) = 0 := rfl

private theorem cs_one (k : ℕ) : ((1 : Fin (k + 2)).castSucc : Fin (k + 3)) = 1 := by
  apply Fin.ext; simp

private theorem cs_succ (k : ℕ) (t : Fin k) :
    ((t.succ.succ : Fin (k + 2)).castSucc : Fin (k + 3)) = t.castSucc.succ.succ := by
  apply Fin.ext; simp [Fin.val_succ]

private theorem cs_last (k : ℕ) :
    (Fin.last (k + 2) : Fin (k + 3)) = (Fin.last k).succ.succ := by
  apply Fin.ext; simp

/-- A `Fin 1`-indexed fibre has the same cardinality as the corresponding ℕ-indexed one. -/
private theorem natCard_fin1 (P : ℕ → Prop) :
    Nat.card {y : Fin 1 → ℕ | P (y 0)} = Nat.card {i : ℕ | P i} :=
  Nat.card_congr (Equiv.subtypeEquiv (Equiv.funUnique (Fin 1) ℕ) (fun _ => Iff.rfl))

/-- Under the linear bound on the counted coordinate, a fibre sits inside a finite range. -/
private theorem fibre_subset {k : ℕ} (Φ : ℕ → ℕ → (Fin (k + 1) → ℕ) → Prop) (C : ℕ)
    (hbd : ∀ mS n v, Φ mS n v → v (Fin.last k) < C * (mS + n + 1))
    (x : Fin (k + 2) → ℕ) :
    {y : Fin 1 → ℕ | Φ (x 0) (x 1)
        (@Fin.snoc k (fun _ => ℕ) (fun t : Fin k => x t.succ.succ) (y 0))}
      ⊆ ↑((Finset.range (C * (x 0 + x 1 + 1))).image
          (fun m => (fun _ => m : Fin 1 → ℕ))) := by
  intro y hy
  have h := hbd _ _ _ hy
  rw [Fin.snoc_last] at h
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]
  exact ⟨y 0, h, by funext i; congr 1; omega⟩

/-- **Counting the last atom coordinate.**  For a two-parameter semilinear family
`Φ : ℕ → ℕ → (Fin (k+1) → ℕ) → Prop` whose last atom coordinate is bounded by
`C · (mS + n + 1)` on the family, the map sending `(mS, n)` and the first `k` atom
coordinates to the number of values of the last coordinate in the family has a semilinear
graph: the graph is again an `IsSliceFamilySemilinear2` family in the same `Fin (k+1)`
layout, with the parameters on `Fin.castSucc` and the count on `Fin.last`.

This is the `p = k + 2`, `q = 1` instance of `PresburgerCounting.count_graph_semilinear`
(`lem:presburger-counting`); the bound is traded for the sup-norm form at the cost of a
factor `2` in the constant. -/
theorem count_last_semilinear {k : ℕ} {Φ : ℕ → ℕ → (Fin (k + 1) → ℕ) → Prop}
    (hΦ : IsSliceFamilySemilinear2 Φ) (C : ℕ)
    (hbd : ∀ mS n v, Φ mS n v → v (Fin.last k) < C * (mS + n + 1)) :
    IsSliceFamilySemilinear2 (fun mS n (v : Fin (k + 1) → ℕ) =>
      Nat.card {i : ℕ |
        Φ mS n (@Fin.snoc k (fun _ => ℕ) (fun t : Fin k => v t.castSucc) i)}
        = v (Fin.last k)) := by
  classical
  set R : (Fin (k + 2) → ℕ) → (Fin 1 → ℕ) → Prop := fun x y =>
    Φ (x 0) (x 1) (@Fin.snoc k (fun _ => ℕ) (fun t : Fin k => x t.succ.succ) (y 0)) with hRdef
  have hset : {w : (Fin (k + 2) ⊕ Fin 1) → ℕ | R (w ∘ Sum.inl) (w ∘ Sum.inr)}
      = {u : (Fin (k + 2) ⊕ Fin 1) → ℕ | (fun j => u (countSel k j)) ∈ familyGraph2 Φ} := by
    ext u
    simp only [familyGraph2, Set.mem_ofPred_eq, hRdef]
    rw [countSel_zero, countSel_one, snoc_countSel]
    exact Iff.rfl
  have hRsl : IsSemilinearSet {w : (Fin (k + 2) ⊕ Fin 1) → ℕ |
      R (w ∘ Sum.inl) (w ∘ Sum.inr)} := by
    rw [hset]
    exact SemilinearGraphArith.isSemilinearSet_comap (countSel k)
      (isSemilinearNd_to_mathlib (k + 1 + 2) _ hΦ)
  have hsub : ∀ x : Fin (k + 2) → ℕ, {y : Fin 1 → ℕ | R x y}
      ⊆ ↑((Finset.range (C * (x 0 + x 1 + 1))).image
          (fun m => (fun _ => m : Fin 1 → ℕ))) := fun x => fibre_subset Φ C hbd x
  have hfin : ∀ x : Fin (k + 2) → ℕ, Set.Finite {y : Fin 1 → ℕ | R x y} :=
    fun x => Set.Finite.subset (Finset.finite_toSet _) (hsub x)
  have hbd2 : ∀ x : Fin (k + 2) → ℕ,
      Nat.card {y : Fin 1 → ℕ | R x y} ≤ (2 * C) * (Finset.univ.sup x + 1) := by
    intro x
    have h0 : x 0 ≤ Finset.univ.sup x := Finset.le_sup (Finset.mem_univ (0 : Fin (k + 2)))
    have h1 : x 1 ≤ Finset.univ.sup x := Finset.le_sup (Finset.mem_univ (1 : Fin (k + 2)))
    have hcard : Nat.card {y : Fin 1 → ℕ | R x y} ≤ C * (x 0 + x 1 + 1) := by
      rw [Nat.card_coe_set_eq]
      calc {y : Fin 1 → ℕ | R x y}.ncard
          ≤ (↑((Finset.range (C * (x 0 + x 1 + 1))).image
              (fun m => (fun _ => m : Fin 1 → ℕ))) : Set (Fin 1 → ℕ)).ncard :=
            Set.ncard_le_ncard (hsub x) (Finset.finite_toSet _)
        _ = ((Finset.range (C * (x 0 + x 1 + 1))).image
              (fun m => (fun _ => m : Fin 1 → ℕ))).card := Set.ncard_coe_finset _
        _ ≤ (Finset.range (C * (x 0 + x 1 + 1))).card := Finset.card_image_le
        _ = C * (x 0 + x 1 + 1) := Finset.card_range _
    calc Nat.card {y : Fin 1 → ℕ | R x y} ≤ C * (x 0 + x 1 + 1) := hcard
      _ ≤ C * (2 * (Finset.univ.sup x + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * C * (Finset.univ.sup x + 1) := by ring
  have hcount := PresburgerCounting.count_graph_semilinear R hRsl hfin (2 * C) hbd2
  refine mathlib_to_isSemilinearNd (k + 1 + 2) _ ?_
  have hgraph : (familyGraph2 (fun mS n (v : Fin (k + 1) → ℕ) =>
        Nat.card {i : ℕ |
          Φ mS n (@Fin.snoc k (fun _ => ℕ) (fun t : Fin k => v t.castSucc) i)}
          = v (Fin.last k)))
      = {z : Fin (k + 2 + 1) → ℕ |
          Nat.card {y : Fin 1 → ℕ | R (fun i => z i.castSucc) y} = z (Fin.last (k + 2))} := by
    ext z
    simp only [familyGraph2, Set.mem_ofPred_eq, hRdef, cs_zero, cs_one, cs_succ, cs_last]
    rw [natCard_fin1 (fun a => Φ (z 0) (z 1)
      (@Fin.snoc k (fun _ => ℕ) (fun t : Fin k => z t.castSucc.succ.succ) a))]
  rw [hgraph]
  exact hcount

/-! ## MSO helpers

The `MSODefinableRel` closure lemmas this file uses.  `mso_and` and `mso_congr` are the
standard pair (also derived, `private`, in `WRPBoundedRank.lean` and `WRPClosures.lean`);
`mso_inRange` is the guard "position `i` lies inside the word", expressible because the
first-order quantifier of `MSO.Formula.Sat` ranges exactly over the valid positions. -/

/-- `MSODefinableRel` transfers along a pointwise iff. -/
private theorem mso_congr {Alpha : Type*} {k : ℕ} {R S : List Alpha → (Fin k → ℕ) → Prop}
    (h : ∀ w ī, R w ī ↔ S w ī) (hR : MSODefinableRel k R) : MSODefinableRel k S := by
  obtain ⟨φ, hφ⟩ := hR
  exact ⟨φ, fun w ī => (h w ī).symm.trans (hφ w ī)⟩

/-- Conjunction of two `MSODefinableRel`s at the same arity. -/
private theorem mso_and {Alpha : Type*} {k : ℕ} {R S : List Alpha → (Fin k → ℕ) → Prop}
    (hR : MSODefinableRel k R) (hS : MSODefinableRel k S) :
    MSODefinableRel k (fun w ī => R w ī ∧ S w ī) := by
  obtain ⟨φ, hφ⟩ := hR
  obtain ⟨ψ, hψ⟩ := hS
  exact ⟨Formula.and φ ψ, fun w ρ => by rw [Formula.sat_and, ← hφ, ← hψ]⟩

/-- The guard "the position at variable `i` lies inside the word": `∃ x. x = x_i`, whose
quantifier ranges over the valid positions. -/
private def inRangeF {Alpha : Type*} {m : ℕ} (i : Fin m) : Formula Alpha m 0 :=
  .exFO (Formula.eqPos 0 i.succ)

/-- Membership of a free position variable in the word is MSO-definable. -/
private theorem mso_inRange {Alpha : Type*} {m : ℕ} (i : Fin m) :
    MSODefinableRel m (fun (w : List Alpha) (ρ : Fin m → ℕ) => ρ i < w.length) := by
  refine ⟨inRangeF i, fun w ρ => ?_⟩
  rw [inRangeF, Formula.sat_exFO]
  constructor
  · intro h
    exact ⟨ρ i, h, by rw [Formula.sat_eqPos]; simp⟩
  · rintro ⟨p, hp, hsat⟩
    rw [Formula.sat_eqPos] at hsat
    simp only [Fin.cons_zero, Fin.cons_succ] at hsat
    omega

/-- The order on two free position variables is MSO-definable. -/
private theorem mso_lt {Alpha : Type*} {m : ℕ} (i j : Fin m) :
    MSODefinableRel m (fun (_ : List Alpha) (ρ : Fin m → ℕ) => ρ i < ρ j) :=
  ⟨Formula.lt i j, fun _ _ => Iff.rfl⟩

/-- The letter at a free position variable is MSO-definable. -/
private theorem mso_labelEq {Alpha : Type*} {m : ℕ} (i : Fin m) (a : Alpha) :
    MSODefinableRel m (fun (w : List Alpha) (ρ : Fin m → ℕ) => w[ρ i]? = some a) :=
  ⟨Formula.labelEq i a, fun _ _ => Iff.rfl⟩

/-- Reindexing the free position variables of an MSO-definable relation, along an arbitrary
(not necessarily injective) map, via `SliceFasGates.relabelFO`. -/
private theorem mso_relabel {Alpha : Type*} {k m : ℕ} (g : Fin k → Fin m)
    {R : List Alpha → (Fin k → ℕ) → Prop} (hR : MSODefinableRel k R) :
    MSODefinableRel m (fun w ī => R w (fun t => ī (g t))) := by
  obtain ⟨φ, hφ⟩ := hR
  exact ⟨SliceFasGates.relabelFO g φ, fun w ρ => by
    rw [SliceFasGates.sat_relabelFO]; exact hφ w (fun t => ρ (g t))⟩

/-! ## The MSO position count -/

/-- **Counting MSO-definable positions along a block-linear slice.**  For a block-linear
two-parameter word family `F` over a finite alphabet and an MSO-definable relation `R` on
(word, `(k+1)`-tuple of positions), the number of positions `i` of `F.eval mS n` for which
`R` holds at `(params, i)` has a semilinear graph as a two-parameter slice family: the graph
is `IsSliceFamilySemilinear2` in the `Fin (k+1)` layout carrying the `k` parameters on
`Fin.castSucc` and the count on `Fin.last`.

The relation is guarded by `i < |F.eval mS n|` — a guard that is itself MSO-definable
(`mso_inRange`) — so the counted fibres are sets of positions of the slice word, whose
length is affine in `(mS, n)` (`BlockLinearWord2.length_eval_le`).  That is exactly the
linear fibre bound of `count_last_semilinear`. -/
theorem msoCount_semilinear {Alpha : Type*} [Fintype Alpha] {k : ℕ}
    (F : BlockLinearWord2 Alpha)
    {R : List Alpha → (Fin (k + 1) → ℕ) → Prop} (hR : MSODefinableRel (k + 1) R) :
    IsSliceFamilySemilinear2 (fun mS n (v : Fin (k + 1) → ℕ) =>
      Nat.card {i : ℕ | i < (F.eval mS n).length ∧
          R (F.eval mS n) (@Fin.snoc k (fun _ => ℕ) (fun t : Fin k => v t.castSucc) i)}
        = v (Fin.last k)) := by
  classical
  have hR' : MSODefinableRel (k + 1) (fun (w : List Alpha) (v : Fin (k + 1) → ℕ) =>
      v (Fin.last k) < w.length ∧ R w v) := mso_and (mso_inRange (Fin.last k)) hR
  have hΦ : IsSliceFamilySemilinear2 (fun mS n (v : Fin (k + 1) → ℕ) =>
      v (Fin.last k) < (F.eval mS n).length ∧ R (F.eval mS n) v) :=
    msoDefinableRel2_semilinear_general F hR'
  have hbd : ∀ mS n (v : Fin (k + 1) → ℕ),
      (v (Fin.last k) < (F.eval mS n).length ∧ R (F.eval mS n) v) →
        v (Fin.last k) < F.lenBound * (mS + n + 1) :=
    fun mS n v hv => lt_of_lt_of_le hv.1 (F.length_eval_le mS n)
  have hcount := count_last_semilinear hΦ F.lenBound hbd
  refine isSemilinearNd_congr ?_ hcount
  ext z
  simp only [familyGraph2, Set.mem_ofPred_eq]
  have hsets : {i : ℕ |
        (@Fin.snoc k (fun _ => ℕ) (fun t : Fin k => z t.castSucc.succ.succ) i) (Fin.last k)
            < (F.eval (z 0) (z 1)).length
          ∧ R (F.eval (z 0) (z 1))
              (@Fin.snoc k (fun _ => ℕ) (fun t : Fin k => z t.castSucc.succ.succ) i)}
      = {i : ℕ | i < (F.eval (z 0) (z 1)).length
          ∧ R (F.eval (z 0) (z 1))
              (@Fin.snoc k (fun _ => ℕ) (fun t : Fin k => z t.castSucc.succ.succ) i)} := by
    ext i
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Fin.snoc_last]
  rw [hsets]

/-! ## The `(state before, letter)` position counts

The counts a prefix rank decomposes into: grouping the positions of a word by the pair
(source state just before the position, letter at the position) turns
`RankSource.prefixRank` into a fixed ℤ-combination of the counts below. -/

/-- **The `(state, letter)` position count along a block-linear slice is semilinear.**  For a
deterministic acceptor `M` over a finite alphabet, a state `q` and a letter `a`, the number
of positions `i < j` of `F.eval mS n` at which `M` is in state `q` and reads `a` has a
semilinear graph in `(mS, n, j)`: the family sends `(mS, n)` and `v 0 = j` to the count at
`v 1`.

The state predicate is MSO-definable by `SliceMSO.detAuto_state_mso` (the *proved*
automaton ⇒ MSO half of Büchi–Elgot–Trakhtenbrot), the letter predicate by
`MSO.Formula.labelEq` and the bound `i < j` by `MSO.Formula.lt`; `msoCount_semilinear`
counts the conjunction. -/
theorem detAuto_state_letter_count_semilinear {Alpha : Type*} [Fintype Alpha]
    (F : BlockLinearWord2 Alpha) (M : SliceMSO.DetAuto Alpha) (q : M.Q) (a : Alpha) :
    IsSliceFamilySemilinear2 (fun mS n (v : Fin 2 → ℕ) =>
      Nat.card {i : ℕ | i < v 0 ∧ M.stateBefore (F.eval mS n) i = q
          ∧ (F.eval mS n)[i]? = some a} = v 1) := by
  classical
  have hstate : MSODefinableRel 2 (fun (w : List Alpha) (u : Fin 2 → ℕ) =>
      M.stateBefore w (u (Fin.last 1)) = q) :=
    mso_relabel (fun _ : Fin 1 => Fin.last 1) (SliceMSO.detAuto_state_mso M q)
  have hR : MSODefinableRel 2 (fun (w : List Alpha) (u : Fin 2 → ℕ) =>
      u (Fin.last 1) < u 0 ∧ M.stateBefore w (u (Fin.last 1)) = q
        ∧ w[u (Fin.last 1)]? = some a) :=
    mso_and (mso_lt (Fin.last 1) 0) (mso_and hstate (mso_labelEq (Fin.last 1) a))
  have hcount := msoCount_semilinear (k := 1) F hR
  refine isSemilinearNd_congr ?_ hcount
  ext z
  simp only [familyGraph2, Set.mem_ofPred_eq]
  have hz0 : (0 : Fin 2) = Fin.castSucc (0 : Fin 1) := rfl
  have hsets : ∀ (w : List Alpha) (p : Fin 1 → ℕ),
      {i : ℕ | i < w.length ∧
          ((@Fin.snoc 1 (fun _ => ℕ) p i) (Fin.last 1) < (@Fin.snoc 1 (fun _ => ℕ) p i) 0
            ∧ M.stateBefore w ((@Fin.snoc 1 (fun _ => ℕ) p i) (Fin.last 1)) = q
            ∧ w[(@Fin.snoc 1 (fun _ => ℕ) p i) (Fin.last 1)]? = some a)}
        = {i : ℕ | i < p 0 ∧ M.stateBefore w i = q ∧ w[i]? = some a} := by
    intro w p
    ext i
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Fin.snoc_last, hz0, Fin.snoc_castSucc]
    constructor
    · rintro ⟨-, hlt, hst, hlab⟩
      exact ⟨hlt, hst, hlab⟩
    · rintro ⟨hlt, hst, hlab⟩
      refine ⟨?_, hlt, hst, hlab⟩
      obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hlab
      exact hi
  rw [hsets]
  rfl

/-- **The `(state, letter)` prefix count of a rank source is semilinear.**  The
`RankSource` form of `detAuto_state_letter_count_semilinear`: for a source `A`, a state `q`
and a letter `a`, the number of positions `i < j` of `F.eval mS n` with
`A.stateBefore … i = q` and letter `a` has a semilinear graph in `(mS, n, j)`.  These are
the counts that `RankSource.prefixRank` is the fixed ℤ-combination of, when the positions
below `j` are grouped by their `(state, letter)` pair. -/
theorem rankSource_state_letter_count_semilinear {Alpha : Type*} [Fintype Alpha] {d : ℕ}
    (F : BlockLinearWord2 Alpha) (A : RankSource Alpha d) (q : A.Q) (a : Alpha) :
    IsSliceFamilySemilinear2 (fun mS n (v : Fin 2 → ℕ) =>
      Nat.card {i : ℕ | i < v 0 ∧ A.stateBefore (F.eval mS n) i = q
          ∧ (F.eval mS n)[i]? = some a} = v 1) :=
  detAuto_state_letter_count_semilinear F A.toDetAuto q a

/-! ## A prefix rank is a fixed ℤ-combination of the `(state, letter)` counts

The identity that makes the counts above the right ones: grouping the positions below `j` by
their `(state just before, letter)` pair turns `RankSource.prefixRank` into a fixed
ℤ-combination — coefficients `A.ω q a c`, independent of the word and of `j` — of the counts
whose graphs `rankSource_state_letter_count_semilinear` proves semilinear. -/

/-- A `< j`-guarded set-fibre cardinality as a `Finset.filter` count. -/
theorem natCard_lt_and (j : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Nat.card {i : ℕ | i < j ∧ P i} = ((Finset.range j).filter P).card := by
  classical
  have hset : {i : ℕ | i < j ∧ P i} = ↑((Finset.range j).filter P) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- **The prefix-rank regrouping.**  `ρ_A^w(j)` is the `ω`-weighted sum of the
`(state, letter)` position counts below `j`. -/
theorem prefixRank_eq_sum_counts {Alpha : Type*} [Fintype Alpha] {d : ℕ}
    (A : RankSource Alpha d) [Fintype A.Q] (w : List Alpha) (j : ℕ) (c : Fin d) :
    A.prefixRank w j c
      = ∑ q : A.Q, ∑ a : Alpha, A.ω q a c *
          (Nat.card {i : ℕ | i < j ∧ A.stateBefore w i = q ∧ w[i]? = some a} : ℤ) := by
  classical
  have hcard : ∀ (q : A.Q) (a : Alpha),
      A.ω q a c * (Nat.card {i : ℕ | i < j ∧ A.stateBefore w i = q ∧ w[i]? = some a} : ℤ)
        = ∑ i ∈ Finset.range j,
            (if A.stateBefore w i = q ∧ w[i]? = some a then A.ω q a c else 0) := by
    intro q a
    rw [natCard_lt_and j (fun i => A.stateBefore w i = q ∧ w[i]? = some a),
      Finset.card_filter]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split <;> simp
  have hpt : ∀ i : ℕ, (w[i]?).elim 0 (fun a => A.ω (A.stateBefore w i) a c)
      = ∑ q : A.Q, ∑ a : Alpha,
          (if A.stateBefore w i = q ∧ w[i]? = some a then A.ω q a c else 0) := by
    intro i
    rw [Finset.sum_eq_single (A.stateBefore w i)]
    · cases w[i]? with
      | none => simp
      | some a0 =>
          rw [Finset.sum_eq_single a0]
          · simp
          · intro a _ hne; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ a0) h
    · intro q _ hne
      refine Finset.sum_eq_zero (fun a _ => ?_)
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact hne h1.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  calc A.prefixRank w j c
      = ∑ i ∈ Finset.range j, (w[i]?).elim 0 (fun a => A.ω (A.stateBefore w i) a c) := rfl
    _ = ∑ i ∈ Finset.range j, ∑ q : A.Q, ∑ a : Alpha,
          (if A.stateBefore w i = q ∧ w[i]? = some a then A.ω q a c else 0) :=
        Finset.sum_congr rfl (fun i _ => hpt i)
    _ = ∑ q : A.Q, ∑ i ∈ Finset.range j, ∑ a : Alpha,
          (if A.stateBefore w i = q ∧ w[i]? = some a then A.ω q a c else 0) := Finset.sum_comm
    _ = ∑ q : A.Q, ∑ a : Alpha, ∑ i ∈ Finset.range j,
          (if A.stateBefore w i = q ∧ w[i]? = some a then A.ω q a c else 0) :=
        Finset.sum_congr rfl (fun q _ => Finset.sum_comm)
    _ = ∑ q : A.Q, ∑ a : Alpha, A.ω q a c *
          (Nat.card {i : ℕ | i < j ∧ A.stateBefore w i = q ∧ w[i]? = some a} : ℤ) :=
        Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun a _ => (hcard q a).symm))

end SliceMSOCount
