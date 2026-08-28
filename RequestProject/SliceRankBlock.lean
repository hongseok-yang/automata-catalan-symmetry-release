/-
# The WRP rank of a slice block-atom is `RankAffine` in its loop-index (fas piece (a))

Assembles `RankTerm.eval` on the slice.  At the constant tuple `· ↦ 1+2j` (the
`U`-position of loop-block `j`) every summand reads position `1+2j`, so:

  * its prefix-rank reduces to the one-loop family (`prefixRank_slice_blockU`),
    which is `RankAffine` (`prefixRank_blockU_rankAffine`);
  * its bounded `β` correction is `s.β (blockState^[j] q₁) U`, a bounded function of
    a finite-state iterate, hence `RankAffine` (`rankAffine_of_iterate`).

Summing over the finitely many summands (`listSum`) and adding the constant `c₀`
gives that the whole rank term — and hence `P.rank c` — is `RankAffine` in `j`.
Works for **any** arity (the constant tuple makes `ī s.π = 1+2j` regardless of
`s.π`).  Axiom-clean.
-/
import RequestProject.SliceRankAffine
import RequestProject.SliceCountSlice

open WRP Step

namespace SliceRankAtom

variable {d : ℕ}

/-- `stateBefore` at the block-`j` `U`-position is the `j`-fold one-block iterate. -/
theorem stateBefore_block (A : RankSource Step d) (n j : ℕ) (h : j ≤ n) :
    A.stateBefore (wrappedFlat n) (1 + 2 * j) =
      (fun q => List.foldl A.δ q [U, D])^[j] (A.δ A.q0 U) := by
  unfold RankSource.stateBefore
  rw [SliceWords.wrappedFlat_take j n h, List.foldl_append, SliceMSO.foldl_replicate_flatten]
  rfl

/-- A summand at the block-`j` `U`-position, reduced to the affine prefix-rank plus
the bounded `β` iterate. -/
theorem summand_block_eq {k : ℕ} (s : Summand Step d k) (j : ℕ) :
    s.eval (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j) =
      s.coeff • (s.A.prefixRank ([U] ++ (List.replicate j [U, D]).flatten)
          (([U] ++ (List.replicate j [U, D]).flatten).length))
        + s.β ((fun q => List.foldl s.A.δ q [U, D])^[j] (s.A.δ s.A.q0 U)) U := by
  have hget : (wrappedFlat (j + 1))[1 + 2 * j]? = some U := by
    rw [List.getElem?_eq_getElem (by rw [length_wrappedFlat]; omega),
      SliceCount.wrappedFlat_getElem_U (j + 1) j (by omega) (by rw [length_wrappedFlat]; omega)]
  unfold Summand.eval
  rw [prefixRank_slice_blockU s.A (j + 1) j (by omega), stateBefore_block s.A (j + 1) j (by omega)]
  funext c
  rw [hget]
  simp [smul_eq_mul]

/-- Each summand is `RankAffine` in `j`. -/
theorem summand_block_rankAffine {k : ℕ} (s : Summand Step d k) :
    RankAffine (fun j => s.eval (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j)) := by
  have := s.A.fintypeQ
  refine RankAffine.congr (fun j => (summand_block_eq s j).symm) ?_
  exact (RankAffine.smul s.coeff (prefixRank_blockU_rankAffine s.A)).add
    (rankAffine_of_iterate (fun q => List.foldl s.A.δ q [U, D]) (s.A.δ s.A.q0 U)
      (fun q => s.β q U))

/-- A regular rank term at the block-`j` `U`-position is `RankAffine` in `j`. -/
theorem rankTerm_block_rankAffine {k : ℕ} (κ : RankTerm Step d k) :
    RankAffine (fun j => κ.eval (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j)) := by
  refine RankAffine.congr (fun j => ?_)
    ((RankAffine.const κ.c0).add (RankAffine.listSum κ.summands
      (fun s j => s.eval (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j))
      (fun s _ => summand_block_rankAffine s)))
  unfold RankTerm.eval
  funext c
  have key : (κ.summands.map (fun s => s.eval (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j))).sum c =
      (κ.summands.map (fun s => s.eval (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j) c)).sum := by
    induction κ.summands with
    | nil => rfl
    | cons s t ih => simp only [List.map_cons, List.sum_cons, Pi.add_apply, ih]
  rw [Pi.add_apply, key]

/-- **The WRP rank of a slice block-`U`-atom is `RankAffine` in its loop-index** —
`fas` piece (a).  (Independent of arity; ranks are prefix-determined.) -/
theorem rank_block_rankAffine {Gamma : Type*} (P : WRP.Presentation Step Gamma)
    (c : Fin P.toPoly.K) :
    RankAffine (fun j => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j)) := by
  obtain ⟨κ, hκ⟩ := P.rankReg c
  exact RankAffine.congr (fun j => (hκ _ _).symm) (rankTerm_block_rankAffine κ)

end SliceRankAtom
