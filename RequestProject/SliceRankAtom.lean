/-
# Ranks are prefix-determined (foundation for the `fas` rank-sort)

The rank of an atom at position `p` reads the word only up to `p`: `prefixRank` sums
over `j < p`, `stateBefore` folds `w.take p`, and the local correction `β` queries
`w[p]`.  Hence the rank depends only on `w.take (p+1)`.

On the slice this means an atom at loop-index `j` has a rank **independent of `n`**
(once `n` is large enough to contain it) — the rank is a function of `j` alone.
That is what lets the moving `≺`-threshold of `fas` be analysed as a comparison of
affine-in-`j` rank vectors (feeding `SliceOrder`).

All proved from `WRP` + Mathlib; axiom-clean.
-/
import RequestProject.WRP
import RequestProject.SliceWords
import RequestProject.SliceRank

open WRP Step

namespace SliceRankAtom

variable {Alpha : Type*} {d : ℕ}

/-- `stateBefore` at `j` depends only on the length-`i` prefix, for `j ≤ i`. -/
theorem stateBefore_prefix_stable (A : RankSource Alpha d) (w w' : List Alpha) (i j : ℕ)
    (h : w.take i = w'.take i) (hj : j ≤ i) : A.stateBefore w j = A.stateBefore w' j := by
  have hwj : w.take j = w'.take j := by
    have e1 : (w.take i).take j = w.take j := by rw [List.take_take, Nat.min_eq_left hj]
    have e2 : (w'.take i).take j = w'.take j := by rw [List.take_take, Nat.min_eq_left hj]
    rw [← e1, ← e2, h]
  unfold RankSource.stateBefore
  rw [hwj]

/-- `prefixRank` at `i` depends only on the length-`i` prefix. -/
theorem prefixRank_prefix_stable (A : RankSource Alpha d) (w w' : List Alpha) (i : ℕ)
    (h : w.take i = w'.take i) : A.prefixRank w i = A.prefixRank w' i := by
  funext c
  unfold RankSource.prefixRank
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have hget : w[j]? = w'[j]? := by
    have hh : (w.take i)[j]? = (w'.take i)[j]? := by rw [h]
    rwa [List.getElem?_take_of_lt hj, List.getElem?_take_of_lt hj] at hh
  rw [hget, stateBefore_prefix_stable A w w' i j h (le_of_lt hj)]

/-- A summand's value at the constant tuple `· ↦ p` depends only on `w.take (p+1)`. -/
theorem summand_eval_const_prefix_stable {k : ℕ} (s : Summand Alpha d k) (w w' : List Alpha)
    (p : ℕ) (h : w.take (p + 1) = w'.take (p + 1)) :
    s.eval w (fun _ => p) = s.eval w' (fun _ => p) := by
  have hp : w.take p = w'.take p := by
    have e1 : (w.take (p + 1)).take p = w.take p := by rw [List.take_take]; congr 1; omega
    have e2 : (w'.take (p + 1)).take p = w'.take p := by rw [List.take_take]; congr 1; omega
    rw [← e1, ← e2, h]
  have hget : w[p]? = w'[p]? := by
    have hh : (w.take (p + 1))[p]? = (w'.take (p + 1))[p]? := by rw [h]
    rwa [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)] at hh
  unfold Summand.eval
  funext c
  rw [prefixRank_prefix_stable s.A w w' p hp, stateBefore_prefix_stable s.A w w' p p hp (le_refl p),
    hget]

/-- A regular rank term's value at the constant tuple `· ↦ p` depends only on
`w.take (p+1)`. -/
theorem rankTerm_eval_const_prefix_stable {k : ℕ} (κ : RankTerm Alpha d k) (w w' : List Alpha)
    (p : ℕ) (h : w.take (p + 1) = w'.take (p + 1)) :
    κ.eval w (fun _ => p) = κ.eval w' (fun _ => p) := by
  unfold RankTerm.eval
  funext c
  refine congrArg (κ.c0 c + ·) ?_
  refine congrArg List.sum (List.map_congr_left (fun s _ => ?_))
  rw [summand_eval_const_prefix_stable s w w' p h]

/-- **The rank of an atom at position `p` is prefix-determined.**  If `w` and `w'`
agree up to position `p`, the rank of copy `c` at the constant tuple `· ↦ p` is the
same. -/
theorem rank_const_prefix_stable {Gamma : Type*} (P : WRP.Presentation Alpha Gamma)
    (c : Fin P.toPoly.K) (w w' : List Alpha) (p : ℕ) (h : w.take (p + 1) = w'.take (p + 1)) :
    P.rank c w (fun _ => p) = P.rank c w' (fun _ => p) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  rw [hκ w, hκ w', rankTerm_eval_const_prefix_stable κ w w' p h]

/-- **Slice block-atom prefix-rank reduces to the one-loop family.**  The prefix-rank
of a source `A` at the `U`-position `1+2j` of `W_n` equals its prefix-rank at the end
of `U(UD)^j` — the quantity `SliceRank.prefixRank_pre_blocks_affineOnResidues` shows
is affine on residue classes of `j`. -/
theorem prefixRank_slice_blockU (A : RankSource Step d) (n j : ℕ) (h : j ≤ n) :
    A.prefixRank (wrappedFlat n) (1 + 2 * j) =
      A.prefixRank ([U] ++ (List.replicate j [U, D]).flatten)
        (([U] ++ (List.replicate j [U, D]).flatten).length) := by
  have hlen : ([U] ++ (List.replicate j [U, D]).flatten).length = 1 + 2 * j := by
    rw [List.length_append, SliceWords.length_flatten_replicate]
    simp only [List.length_cons, List.length_nil]; ring
  have htake : (wrappedFlat n).take (1 + 2 * j) =
      ([U] ++ (List.replicate j [U, D]).flatten).take (1 + 2 * j) := by
    rw [SliceWords.wrappedFlat_take j n h, List.take_of_length_le hlen.le]
  rw [prefixRank_prefix_stable A _ _ (1 + 2 * j) htake, hlen]

end SliceRankAtom
