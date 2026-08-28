/-
# The counting input: `lem:presburger-counting`

This file states the counting fact the development's counting layer rests on, in Mathlib
vocabulary only (`IsSemilinearSet`, `Nat.card`, `Set.Finite`), so that it can be compared
with the literature without decoding any project abstraction.  It is a theorem, proved in
`RequestProject/CountGeneral.lean` and re-exported here under the name the rest of the
development uses; the project-side counting statements are derived from it.

Also provided here: the coordinate-reindexing transport `isSemilinearSet_comp` and the
`p = 2` repackaging `count_graph_two_param`, which puts the theorem into the `Fin (k+2)` /
`Fin 3` coordinate shape the two-parameter development uses.
-/
import Mathlib
import RequestProject.CountGeneral

namespace PresburgerCounting

open Set

/-! ## Reindexing transport -/

/-- Semilinearity transports along a bijective reindexing of coordinates: if `S ⊆ ℕ^ι` is
semilinear and `e : ι ≃ κ`, then the set of `w : κ → ℕ` whose `e`-pullback lies in `S` is
semilinear.  This is `IsSemilinearSet.image` for the linear map `LinearMap.funLeft` of the
inverse reindexing. -/
theorem isSemilinearSet_comp {ι κ : Type*} (e : ι ≃ κ) {S : Set (ι → ℕ)}
    (hS : IsSemilinearSet S) :
    IsSemilinearSet {w : κ → ℕ | (fun i => w (e i)) ∈ S} := by
  have himg : (LinearMap.funLeft ℕ ℕ e.symm) '' S
      = {w : κ → ℕ | (fun i => w (e i)) ∈ S} := by
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
    · intro hw
      exact ⟨fun i => w (e i), hw, by funext j; simp⟩
  rw [← himg]
  exact hS.image _

/-! ## The counting theorem -/

/-- **`lem:presburger-counting`** — bounded parametric Presburger counting.

Let `A ⊆ ℕ^p × ℕ^q` be semilinear (equivalently, Presburger-definable: Ginsburg–Spanier),
write `A_x = {y | (x, y) ∈ A}` for its fibres, and suppose every fibre is finite and
`|A_x| ≤ C · (‖x‖_∞ + 1)` for one constant `C` independent of `x`.  Then the count graph
`{(x, |A_x|)} ⊆ ℕ^(p+1)` is semilinear.

Here `‖x‖_∞` is `Finset.univ.sup x`, the fibre index tuple is packed as `Fin p ⊕ Fin q → ℕ`
(matching `IsSemilinearSet.proj`), and the count graph is packed as `Fin (p+1) → ℕ` with the
parameters on `Fin.castSucc` and the count on `Fin.last p`.  The paper states the lemma for
`p, q ≥ 1`; it is stated here for all `p q : ℕ`.  Both degenerate cases are elementary, so
dropping those hypotheses costs nothing: for `p = 0` there is a single fibre, whose count
is one number, and the graph is a singleton; for `q = 0` the count is `0` or `1` according
to the semilinear condition `R x 0`, and semilinear sets are closed under complement.
The paper's joint `r`-tuple form is not transcribed; the development uses only the
single-count case.

The proof is elementary and self-contained; it is assembled in
`RequestProject/CountGeneral.lean` from `ProperLinearRep`, `SemilinearMinMax`,
`KernelDichotomy`, `SemilinearGraphArith`, `ProperPieceCount` and `CountBaseCase`, and this
declaration re-exports `CountGeneral.count_graph_semilinear_proved`.  Three ingredients carry
it.  First, decomposition into *proper* linear pieces, whose periods are linearly independent,
so that the points of a piece are in bijection with their coefficient tuples.  Second, a
kernel dichotomy: two linearly independent integer vectors in the kernel of the parameter map
would place quadratically many coefficient tuples over one parameter value, which the linear
bound forbids, so the kernel is cyclic and every fibre of a piece is an arithmetic progression
whose direction is fixed once and for all, independent of the parameter.  Third, the counts of
the pieces are combined by inclusion–exclusion over those progressions — carried out through
the two-set identity `|B ∪ C| + |B ∩ C| = |B| + |C|`, so that a union reduces to shorter
unions of intersections — after which a single intersection is counted by its progression
indices, a one-dimensional problem settled by splitting into residue classes of a common
period and counting each class as an interval with definable endpoints.

No Ehrhart theory, quasi-polynomiality, or parametric Presburger counting theorem is used;
Mathlib's Ginsburg–Spanier bridge `presburger.definable_iff_isSemilinearSet` supplies the
first-order closure properties, and nothing else external is needed.  The linear bound is what
makes the statement true, and it enters exactly once, in the kernel dichotomy.  Without it the
statement fails — e.g. the semilinear family `A_x = {y : Fin 2 → ℕ | y 0 < x 0 ∧ y 1 < x 0}`
has `|A_x| = (x 0)^2`, whose graph is not semilinear. -/
theorem count_graph_semilinear {p q : ℕ}
    (R : (Fin p → ℕ) → (Fin q → ℕ) → Prop)
    (hR : IsSemilinearSet {w : Fin p ⊕ Fin q → ℕ | R (w ∘ Sum.inl) (w ∘ Sum.inr)})
    (hfin : ∀ x : Fin p → ℕ, Set.Finite {y : Fin q → ℕ | R x y})
    (C : ℕ)
    (hbd : ∀ x : Fin p → ℕ,
      Nat.card {y : Fin q → ℕ | R x y} ≤ C * (Finset.univ.sup x + 1)) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ |
      Nat.card {y : Fin q → ℕ | R (fun i => z i.castSucc) y} = z (Fin.last p)} :=
  CountGeneral.count_graph_semilinear_proved R hR hfin C hbd

/-! ## The two-parameter repackaging -/

/-- Split `Fin (k+2)` into the two leading parameter coordinates and the `k` trailing atom
coordinates. -/
def finSplit2 (k : ℕ) : Fin (k + 2) ≃ (Fin 2 ⊕ Fin k) :=
  (finCongr (Nat.add_comm k 2)).trans finSumFinEquiv.symm

@[simp] theorem finSplit2_zero (k : ℕ) : finSplit2 k 0 = Sum.inl 0 := by
  rw [finSplit2, Equiv.trans_apply, Equiv.symm_apply_eq]
  apply Fin.ext
  simp

@[simp] theorem finSplit2_one (k : ℕ) : finSplit2 k 1 = Sum.inl 1 := by
  rw [finSplit2, Equiv.trans_apply, Equiv.symm_apply_eq]
  apply Fin.ext
  simp

@[simp] theorem finSplit2_succ_succ (k : ℕ) (i : Fin k) :
    finSplit2 k i.succ.succ = Sum.inr i := by
  rw [finSplit2, Equiv.trans_apply, Equiv.symm_apply_eq]
  apply Fin.ext
  simp [Fin.val_succ]
  omega

/-- **`lem:presburger-counting` at `p = 2`, in `Fin`-coordinates.**  For a semilinear
two-parameter family `Φ : ℕ → ℕ → (Fin k → ℕ) → Prop` (presented by its packed
`Fin (k+2)`-graph) with finite fibres of size `≤ C · (m + n + 1)`, the count graph
`{(m, n, #fibre)} ⊆ ℕ³` is semilinear.

The bound is reconciled with the axiom's sup-norm form by `m + n + 1 ≤ 2 · (max m n + 1)`,
which costs a factor `2` in the constant. -/
theorem count_graph_two_param {k : ℕ} (Φ : ℕ → ℕ → (Fin k → ℕ) → Prop)
    (hΦ : IsSemilinearSet {v : Fin (k + 2) → ℕ | Φ (v 0) (v 1) (fun i => v i.succ.succ)})
    (hfin : ∀ m n, Set.Finite {ī : Fin k → ℕ | Φ m n ī})
    (C : ℕ) (hbd : ∀ m n, Nat.card {ī : Fin k → ℕ | Φ m n ī} ≤ C * (m + n + 1)) :
    IsSemilinearSet {v : Fin 3 → ℕ | Nat.card {ī : Fin k → ℕ | Φ (v 0) (v 1) ī} = v 2} := by
  have hR : IsSemilinearSet {w : Fin 2 ⊕ Fin k → ℕ |
      (fun (x : Fin 2 → ℕ) (ī : Fin k → ℕ) => Φ (x 0) (x 1) ī)
        (w ∘ Sum.inl) (w ∘ Sum.inr)} := by
    have h := isSemilinearSet_comp (finSplit2 k) hΦ
    simp only [Set.mem_ofPred_eq, finSplit2_zero, finSplit2_one, finSplit2_succ_succ] at h
    exact h
  have hbd' : ∀ x : Fin 2 → ℕ,
      Nat.card {ī : Fin k → ℕ | Φ (x 0) (x 1) ī} ≤ 2 * C * (Finset.univ.sup x + 1) := by
    intro x
    have h0 : x 0 ≤ Finset.univ.sup x := Finset.le_sup (Finset.mem_univ (0 : Fin 2))
    have h1 : x 1 ≤ Finset.univ.sup x := Finset.le_sup (Finset.mem_univ (1 : Fin 2))
    calc Nat.card {ī : Fin k → ℕ | Φ (x 0) (x 1) ī}
        ≤ C * (x 0 + x 1 + 1) := hbd (x 0) (x 1)
      _ ≤ C * (2 * (Finset.univ.sup x + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * C * (Finset.univ.sup x + 1) := by ring
  exact count_graph_semilinear
    (fun (x : Fin 2 → ℕ) (ī : Fin k → ℕ) => Φ (x 0) (x 1) ī) hR
    (fun x => hfin (x 0) (x 1)) (2 * C) hbd'

end PresburgerCounting
