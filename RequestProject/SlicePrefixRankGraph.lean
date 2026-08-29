/-
# The value graph of a prefix rank along a block-linear slice

For a block-linear two-parameter word family `F : BlockLinearWord2 Alpha` and a rank source
`A : RankSource Alpha d`, the `ℤ^d`-valued function

    (mS, n, j) ↦ ρ_A^{F.eval mS n}(j) = A.prefixRank (F.eval mS n) j

has a semilinear value graph (`SliceSemilinearN.IsSliceValueSemilinear2`): the packed
relation `A.prefixRank (F.eval mS n) j = decodeZ v` over `(mS, n, j, v)` is
`IsSliceFamilySemilinear2` (`prefixRank_value_semilinear`, `prefixRank_graph_semilinear`, and the
queried-coordinate forms `prefixRank_at_semilinear` / `coeff_prefixRank_at_semilinear`).

The prefix rank is the composition of the two halves supplied upstream:

* `SliceMSOCount.prefixRank_eq_sum_counts` regroups it as the `ω`-weighted sum, over the
  **fixed** finite index set `A.Q × Alpha`, of the `(state, letter)` position counts below
  `j`, so the number of summands does not depend on `(mS, n, j)`;
* `SliceMSOCount.rankSource_state_letter_count_semilinear` gives each count a semilinear
  count graph, and `SliceSemilinearN.isSliceValueSemilinear2_natCoeffSum` assembles the
  finite signed combination.

`IsSliceValueSemilinear2.comap` reindexes the atom coordinates of a value graph along an
arbitrary map, so the position may be read from any coordinate `π` of a `k`-tuple — the
form `Summand.eval` queries it in (`prefixRank_at_semilinear`,
`coeff_prefixRank_at_semilinear`).  `RequestProject.RankTermGraph` assembles from these the
value graph of a whole regular rank term.

The single admission behind these results is
`SliceSemilinearN.msoDefinableRel2_semilinear_general`; the automaton ⇒ MSO ingredient is
the theorem `SliceMSO.detAuto_state_mso`, not `SliceMSO.buchi`.
-/
import RequestProject.SliceMSOCount
import RequestProject.SliceGraphArithZ

namespace SliceSemilinearN

open scoped BigOperators

/-! ## Reindexing the atom coordinates of a value graph

The `ℤ`-valued companion of `IsSliceFamilySemilinear2.comap`: a value graph may be read
through an arbitrary (not necessarily injective) coordinate selection, the `decodeZ` value
block being carried along unchanged. -/

/-- **Reindexing of a value graph.**  Reading a `ℤ^d`-valued slice function with a
semilinear value graph through any `sel : Fin m → Fin K` again yields a semilinear value
graph.  The selection acts only on the `m` atom coordinates; the `d + d` `decodeZ`
coordinates keep their position at the end of the tuple. -/
theorem IsSliceValueSemilinear2.comap {m K d : ℕ} (sel : Fin m → Fin K)
    {f : ℕ → ℕ → (Fin m → ℕ) → (Fin d → ℤ)} (hf : IsSliceValueSemilinear2 f) :
    IsSliceValueSemilinear2 (fun mS n (ī : Fin K → ℕ) => f mS n (fun t => ī (sel t))) := by
  have h := IsSliceFamilySemilinear2.comap
    (Fin.append (fun t : Fin m => Fin.castAdd (d + d) (sel t))
      (fun c : Fin (d + d) => Fin.natAdd K c)) hf
  refine isSemilinearNd_congr ?_ h
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]

end SliceSemilinearN

namespace SliceMSOCount

open SliceSemilinearN

/-! ## The prefix-rank value graph -/

/-- **The value graph of a prefix rank along a block-linear slice is semilinear.**  For a
block-linear two-parameter word family `F` over a finite alphabet and a rank source `A`,
the function `(mS, n, j) ↦ ρ_A^{F.eval mS n}(j)` has a semilinear value graph.

The position `j` is the single atom coordinate `p 0`; the value is carried by the trailing
`d + d` `decodeZ` coordinates.

Proof: `prefixRank_eq_sum_counts` writes the prefix rank as
`∑_{(q,a) ∈ A.Q × Alpha} ω(q,a,c) · #{i < j : stateBefore … i = q ∧ letter i = a}`, a sum
over a *fixed* finite index set, so the number of summands is independent of `(mS, n, j)`.
Each count has a semilinear count graph by
`rankSource_state_letter_count_semilinear`, and `isSliceValueSemilinear2_natCoeffSum`
assembles the finite signed combination. -/
theorem prefixRank_value_semilinear {Alpha : Type*} [Fintype Alpha] {d : ℕ}
    (F : BlockLinearWord2 Alpha) (A : RankSource Alpha d) :
    IsSliceValueSemilinear2
      (fun mS n (p : Fin 1 → ℕ) => A.prefixRank (F.eval mS n) (p 0)) := by
  classical
  have := A.fintypeQ
  refine IsSliceValueSemilinear2.congr (fun mS n p => ?_)
    (isSliceValueSemilinear2_natCoeffSum (Finset.univ : Finset (A.Q × Alpha))
      (fun x c => A.ω x.1 x.2 c)
      (fun x mS n (p : Fin 1 → ℕ) => Nat.card {i : ℕ |
        i < p 0 ∧ A.stateBefore (F.eval mS n) i = x.1 ∧ (F.eval mS n)[i]? = some x.2})
      (fun x _ => rankSource_state_letter_count_semilinear F A x.1 x.2))
  funext c
  rw [prefixRank_eq_sum_counts A (F.eval mS n) (p 0) c, Fintype.sum_prod_type]

/-- **The unpacked prefix-rank graph.**  `prefixRank_value_semilinear` written out as the
`IsSliceFamilySemilinear2` statement in the `Fin (1 + (d + d))` layout: the position at the
single atom coordinate, the `decodeZ`-encoded rank vector in the trailing block.  This is
the `k = 1` instance of the layout of `regularRankTerm_graph_semilinear`. -/
theorem prefixRank_graph_semilinear {Alpha : Type*} [Fintype Alpha] {d : ℕ}
    (F : BlockLinearWord2 Alpha) (A : RankSource Alpha d) :
    IsSliceFamilySemilinear2 (fun mS n (jv : Fin (1 + (d + d)) → ℕ) =>
      A.prefixRank (F.eval mS n) (jv (Fin.castAdd (d + d) 0))
        = decodeZ (fun c => jv (Fin.natAdd 1 c))) :=
  prefixRank_value_semilinear F A

/-- **The prefix rank at a selected coordinate.**  The form a `Summand` queries: the
position is read from coordinate `π` of a `k`-tuple, the remaining atom coordinates being
free.  This is `prefixRank_value_semilinear` reindexed along `fun _ : Fin 1 => π`. -/
theorem prefixRank_at_semilinear {Alpha : Type*} [Fintype Alpha] {d k : ℕ}
    (F : BlockLinearWord2 Alpha) (A : RankSource Alpha d) (π : Fin k) :
    IsSliceValueSemilinear2
      (fun mS n (ī : Fin k → ℕ) => A.prefixRank (F.eval mS n) (ī π)) :=
  IsSliceValueSemilinear2.comap (fun _ : Fin 1 => π) (prefixRank_value_semilinear F A)

/-- **An integer multiple of a prefix rank at a selected coordinate.**  The first half of
`Summand.eval`: `c_t · ρ_{A}(x_π)`. -/
theorem coeff_prefixRank_at_semilinear {Alpha : Type*} [Fintype Alpha] {d k : ℕ}
    (F : BlockLinearWord2 Alpha) (A : RankSource Alpha d) (coeff : ℤ) (π : Fin k) :
    IsSliceValueSemilinear2
      (fun mS n (ī : Fin k → ℕ) => fun c => coeff * A.prefixRank (F.eval mS n) (ī π) c) :=
  (prefixRank_at_semilinear F A π).smul coeff

end SliceMSOCount
