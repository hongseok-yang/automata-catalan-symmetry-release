/-
# The value graph of a regular rank term on a block-linear slice

`SliceSemilinearN.regularRankTerm_value2_graph_semilinear`: a regular rank term `f` read
along a block-linear two-parameter word family `F` has a semilinear value graph — the set
of `(mS, n, ī, v)` with `f (F.eval mS n) ī = decodeZ v`, the `k` atom coordinates first and
the `d + d` value coordinates last, is `IsSliceFamilySemilinear2`.  Its bundled `= g` form
`regularRankTerm_eq_value2_semilinear` follows.

`IsRegularRankTerm f` exhibits `f` as `RankTerm.eval κ`, and

    RankTerm.eval κ w ī c = κ.c0 c + ∑_{s ∈ κ.summands} Summand.eval s w ī c,
    Summand.eval s w ī c  = s.coeff * ρ_{s.A}^w (ī s.π) c
                              + (w[ī s.π]?).elim 0 (fun a => s.β (s.A.stateBefore w (ī s.π)) a),

a sum over a list of summands fixed by `κ`.  The `ℤ`-valued closure operations of
`SliceGraphArithZ` — constants, pointwise sums, integer multiples — therefore reduce the
whole term to two atoms:

* the prefix rank at a selected coordinate, `SliceMSOCount.coeff_prefixRank_at_semilinear`;
* the bounded local correction `β`, handled here by `summandBeta_value_semilinear`.

The correction takes finitely many values: one per pair `(q, a)` of the fixed finite set
`s.A.Q × Alpha`, and `0` when `ī s.π` runs off the end of the word.  Its cells are
MSO-definable in the free position variables — "the source state just before position
`ī π` is `q`" is `SliceMSO.detAuto_state_mso` relabelled to the coordinate `π`, "the letter
there is `a`" is `MSO.Formula.labelEq`, and the off-the-end cell is the complement of the
in-range guard `∃ x, x = x_π` — so `isSliceValueSemilinear2_of_cases` glues the cover of a
locally constant value.

`isSliceValueSemilinear2_blockLinear_iff` identifies the packaged value graph with the
`Fin (k + (d + d))` layout of the statement, and `regularRankTerm_eq_value2_semilinear`
intersects that graph with the value graph of a slice-const-semilinear target `g`, sharing
the value block, and projects the block away with `decodeZ_surjective`.

The single admission behind the file is
`SliceSemilinearN.msoDefinableRel2_semilinear_general`; the automaton ⇒ MSO ingredient is
the theorem `SliceMSO.detAuto_state_mso`, not `SliceMSO.buchi`, and the counting layer
underneath is the theorem `PresburgerCounting.count_graph_semilinear`.
-/
import RequestProject.SlicePrefixRankGraph

namespace SliceMSOCount

open SliceSemilinearN MSO

/-! ## MSO helpers for the bounded correction

The `MSODefinableRel` closure lemmas the correction cell needs.  They repeat the standard
pair `mso_and`/`mso_relabel` and the in-range guard `mso_inRange`, whose quantifier ranges
exactly over the valid positions of the word. -/

/-- Conjunction of two `MSODefinableRel`s at the same arity. -/
private theorem mso_and {Alpha : Type*} {k : ℕ} {R S : List Alpha → (Fin k → ℕ) → Prop}
    (hR : MSODefinableRel k R) (hS : MSODefinableRel k S) :
    MSODefinableRel k (fun w ī => R w ī ∧ S w ī) := by
  obtain ⟨φ, hφ⟩ := hR
  obtain ⟨ψ, hψ⟩ := hS
  exact ⟨Formula.and φ ψ, fun w ρ => by rw [Formula.sat_and, ← hφ, ← hψ]⟩

/-- Membership of a free position variable in the word is MSO-definable: `∃ x. x = x_i`,
whose first-order quantifier ranges over the valid positions. -/
private theorem mso_inRange {Alpha : Type*} {m : ℕ} (i : Fin m) :
    MSODefinableRel m (fun (w : List Alpha) (ρ : Fin m → ℕ) => ρ i < w.length) := by
  refine ⟨.exFO (Formula.eqPos 0 i.succ), fun w ρ => ?_⟩
  rw [Formula.sat_exFO]
  constructor
  · intro h
    exact ⟨ρ i, h, by rw [Formula.sat_eqPos]; simp⟩
  · rintro ⟨p, hp, hsat⟩
    rw [Formula.sat_eqPos] at hsat
    simp only [Fin.cons_zero, Fin.cons_succ] at hsat
    omega

/-- The letter at a free position variable is MSO-definable. -/
private theorem mso_labelEq {Alpha : Type*} {m : ℕ} (i : Fin m) (a : Alpha) :
    MSODefinableRel m (fun (w : List Alpha) (ρ : Fin m → ℕ) => w[ρ i]? = some a) :=
  ⟨Formula.labelEq i a, fun _ _ => Iff.rfl⟩

/-- Reindexing the free position variables of an MSO-definable relation, along an
arbitrary (not necessarily injective) map, via `SliceFasGates.relabelFO`. -/
private theorem mso_relabel {Alpha : Type*} {k m : ℕ} (g : Fin k → Fin m)
    {R : List Alpha → (Fin k → ℕ) → Prop} (hR : MSODefinableRel k R) :
    MSODefinableRel m (fun w ī => R w (fun t => ī (g t))) := by
  obtain ⟨φ, hφ⟩ := hR
  exact ⟨SliceFasGates.relabelFO g φ, fun w ρ => by
    rw [SliceFasGates.sat_relabelFO]; exact hφ w (fun t => ρ (g t))⟩

/-! ## The bounded local correction

The second half of `Summand.eval`: the table `β` evaluated at the source state just before,
and the letter at, the queried position.  It takes finitely many values — one per
`(state, letter)` pair, plus `0` off the end of the word — each on an MSO-definable cell,
so `isSliceValueSemilinear2_of_cases` assembles it. -/

/-- **The bounded correction of a summand has a semilinear value graph.**  The value at
`(mS, n, ī)` is `β(q, a)` where `q` is the source state just before position `ī π` of
`F.eval mS n` and `a` the letter there, and `0` when `ī π` lies off the end of the word.

The cover is indexed by `Option (A.Q × Alpha)`: the cell `some (q, a)` is the
MSO-definable conjunction "state `q` before `ī π`" (`SliceMSO.detAuto_state_mso`) and
"letter `a` at `ī π`" (`MSO.Formula.labelEq`); the cell `none` is the complement of the
in-range guard.  On each cell the correction is constant. -/
theorem summandBeta_value_semilinear {Alpha : Type*} [Fintype Alpha] {d k : ℕ}
    (F : BlockLinearWord2 Alpha) (s : Summand Alpha d k) :
    IsSliceValueSemilinear2 (fun mS n (ī : Fin k → ℕ) =>
      ((F.eval mS n)[ī s.π]?).elim (0 : Fin d → ℤ)
        (fun a => s.β (s.A.stateBefore (F.eval mS n) (ī s.π)) a)) := by
  classical
  have := s.A.fintypeQ
  refine isSliceValueSemilinear2_of_cases (ι := Option (s.A.Q × Alpha))
    (fun i mS n (ī : Fin k → ℕ) => i.elim (¬ (ī s.π < (F.eval mS n).length))
      (fun x => s.A.stateBefore (F.eval mS n) (ī s.π) = x.1
        ∧ (F.eval mS n)[ī s.π]? = some x.2))
    (fun i _ _ (_ : Fin k → ℕ) => i.elim (0 : Fin d → ℤ) (fun x => s.β x.1 x.2))
    _ ?_ ?_ ?_ ?_
  · rintro (_ | x)
    · exact IsSliceFamilySemilinear2.not
        (msoDefinableRel2_semilinear_general F (mso_inRange s.π))
    · have hR : MSODefinableRel k (fun (w : List Alpha) (ī : Fin k → ℕ) =>
          s.A.stateBefore w (ī s.π) = x.1 ∧ w[ī s.π]? = some x.2) :=
        mso_and (mso_relabel (fun _ : Fin 1 => s.π)
          (SliceMSO.detAuto_state_mso s.A.toDetAuto x.1)) (mso_labelEq s.π x.2)
      exact msoDefinableRel2_semilinear_general F hR
  · rintro (_ | x)
    · exact isSliceValueSemilinear2_const _
    · exact isSliceValueSemilinear2_const _
  · intro mS n ī
    by_cases h : ī s.π < (F.eval mS n).length
    · exact ⟨some (s.A.stateBefore (F.eval mS n) (ī s.π), (F.eval mS n)[ī s.π]'h),
        rfl, List.getElem?_eq_getElem h⟩
    · exact ⟨none, h⟩
  · rintro (_ | x) mS n ī hPi
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hPi)]
      rfl
    · obtain ⟨h1, h2⟩ := hPi
      rw [h2, h1]
      rfl

/-! ## Summands and rank terms -/

/-- **A summand's value graph is semilinear.**  `Summand.eval` is the sum of the scaled
prefix rank at the queried coordinate (`coeff_prefixRank_at_semilinear`) and the bounded
correction (`summandBeta_value_semilinear`). -/
theorem summand_value_semilinear {Alpha : Type*} [Fintype Alpha] {d k : ℕ}
    (F : BlockLinearWord2 Alpha) (s : Summand Alpha d k) :
    IsSliceValueSemilinear2 (fun mS n (ī : Fin k → ℕ) => s.eval (F.eval mS n) ī) :=
  IsSliceValueSemilinear2.congr (fun _ _ _ => rfl)
    ((coeff_prefixRank_at_semilinear F s.A s.coeff s.π).add
      (summandBeta_value_semilinear F s))

/-- The pointwise sum over a list of summands has a semilinear value graph. -/
private theorem summandsSum_value_semilinear {Alpha : Type*} [Fintype Alpha] {d k : ℕ}
    (F : BlockLinearWord2 Alpha) :
    ∀ L : List (Summand Alpha d k),
      IsSliceValueSemilinear2 (fun mS n (ī : Fin k → ℕ) =>
        fun c => (L.map (fun s => s.eval (F.eval mS n) ī c)).sum)
  | [] => by
      refine IsSliceValueSemilinear2.congr (fun mS n ī => ?_) isSliceValueSemilinear2_zero
      funext c; simp
  | s :: L => by
      refine IsSliceValueSemilinear2.congr (fun mS n ī => ?_)
        ((summand_value_semilinear F s).add (summandsSum_value_semilinear F L))
      funext c; simp

/-- **A rank term's value graph is semilinear.**  `RankTerm.eval` is its constant plus the
sum over its (fixed, finite) list of summands. -/
theorem rankTerm_value_semilinear {Alpha : Type*} [Fintype Alpha] {d k : ℕ}
    (F : BlockLinearWord2 Alpha) (κ : RankTerm Alpha d k) :
    IsSliceValueSemilinear2 (fun mS n (ī : Fin k → ℕ) => κ.eval (F.eval mS n) ī) :=
  IsSliceValueSemilinear2.congr (fun _ _ _ => rfl)
    ((isSliceValueSemilinear2_const (k := k) κ.c0).add
      (summandsSum_value_semilinear F κ.summands))

/-- **The value graph of a regular rank term along a block-linear slice is semilinear.**
A regular rank term is the evaluation of some `RankTerm`, whose value graph is semilinear
by `rankTerm_value_semilinear`, and `isSliceValueSemilinear2_blockLinear_iff` identifies
the packaged value graph with the unpacked `Fin (k + (d + d))` statement.  This is the
form `SliceSemilinearN.regularRankTerm_value2_graph_semilinear` exports. -/
theorem regularRankTerm_graph_semilinear {Alpha : Type*} [Fintype Alpha] {d k : ℕ}
    (F : BlockLinearWord2 Alpha)
    {f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)} (hf : IsRegularRankTerm f) :
    IsSliceFamilySemilinear2
      (fun mS n (iv : Fin (k + (d + d)) → ℕ) =>
        f (F.eval mS n) (fun t => iv (Fin.castAdd (d + d) t))
          = decodeZ (fun c => iv (Fin.natAdd k c))) := by
  obtain ⟨κ, hκ⟩ := hf
  exact (isSliceValueSemilinear2_blockLinear_iff F f).mp
    (IsSliceValueSemilinear2.congr (fun mS n ī => (hκ (F.eval mS n) ī).symm)
      (rankTerm_value_semilinear F κ))

end SliceMSOCount

namespace SliceSemilinearN

/-- **A regular rank term has a semilinear VALUE GRAPH on a block-linear slice.**  A
`IsRegularRankTerm` `f` read along a block-linear two-parameter word family `F` has a
semilinear value graph — the set of `(mS, n, ī, v)` with the rank value
`f (F.eval mS n) ī` decoded by `v : Fin (d+d) → ℕ` (the `ī` coordinates first, the `v`
value coordinates last).  Project-agnostic: it mentions only `IsRegularRankTerm`,
`BlockLinearWord2`, `decodeZ`, and `IsSliceFamilySemilinear2`, no specific presentation or
slice.  Both hypotheses are load-bearing: `[Fintype Alpha]` (automaton step) and the
block-linear shape of `F` (regularity of the slice).  This is strictly stronger than the
bundled `= g` form (`regularRankTerm_eq_value2_semilinear` below), which it derives:
exposing the value as free coordinates lets a *second* atom's rank be a free variable,
after which `lexLt`/`=` of two ranks are first-order.

Proof: `SliceMSOCount.regularRankTerm_graph_semilinear`.  A rank term is a fixed finite
signed combination of prefix ranks and bounded local corrections; a prefix rank is the
`ω`-weighted sum of the counts of the MSO-definable `(state, letter)` positions below the
queried one, which are semilinear by `PresburgerCounting.count_graph_semilinear`; and a
correction is constant on each cell of a finite MSO-definable cover. -/
theorem regularRankTerm_value2_graph_semilinear {Alpha : Type*} [Fintype Alpha] {d k : ℕ}
    (F : BlockLinearWord2 Alpha)
    {f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)} (hf : IsRegularRankTerm f) :
    IsSliceFamilySemilinear2
      (fun mS n (iv : Fin (k + (d + d)) → ℕ) =>
        f (F.eval mS n) (fun t => iv (Fin.castAdd (d + d) t))
          = decodeZ (fun c => iv (Fin.natAdd k c))) :=
  SliceMSOCount.regularRankTerm_graph_semilinear F hf

/-- **A regular rank term equals a slice-semilinear target: semilinear.**  The bundled
`= g` corollary of `regularRankTerm_value2_graph_semilinear`: intersect `f`'s value graph
with `g`'s value graph (sharing the value block) and existentially project the value, using
`decodeZ_surjective` to pick the common split. -/
theorem regularRankTerm_eq_value2_semilinear {Alpha : Type*} [Fintype Alpha] {d k : ℕ}
    (F : BlockLinearWord2 Alpha)
    {f : List Alpha → (Fin k → ℕ) → (Fin d → ℤ)} (hf : IsRegularRankTerm f)
    {g : ℕ → ℕ → (Fin d → ℤ)} (hg : IsSliceConstSemilinear2 g) :
    IsSliceFamilySemilinear2 (fun mS n ī => f (F.eval mS n) ī = g mS n) := by
  have hf2 := regularRankTerm_value2_graph_semilinear F hf
  have hgw : IsSliceFamilySemilinear2
      (fun mS n (iv : Fin (k + (d + d)) → ℕ) =>
        g mS n = decodeZ (fun c => iv (Fin.natAdd k c))) :=
    IsSliceFamilySemilinear2.weaken_natAdd (j := k) hg
  have hex := IsSliceFamilySemilinear2.exists_extra_tuple (k := k) (m := d + d) (hf2.and hgw)
  refine isSemilinearNd_congr ?_ hex
  ext w
  simp only [familyGraph2, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]
  constructor
  · rintro ⟨bb, hA, hB⟩
    rw [hA, hB]
  · intro hAB
    obtain ⟨bb, hbb⟩ := decodeZ_surjective (g (w 0) (w 1))
    exact ⟨bb, by rw [hAB, hbb], hbb.symm⟩

end SliceSemilinearN
