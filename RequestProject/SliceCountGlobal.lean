/-
# Global-bound counting for two-parameter slice families

`lem:presburger-counting` (transcribed as `PresburgerCounting.count_graph_semilinear`)
applied to a two-parameter slice atom-family `Φ : ℕ → ℕ → (Fin k → ℕ) → Prop`.  Two
consequences are packaged here, both under the **global** linear fibre bound
`#fibre_{mS,n} ≤ C · (mS + n + 1)`:

* `SliceSemilinearN.sliceFamilyCount2_graph_semilinear` — the joint count graph
  `{(mS, n, #fibre_{mS,n})} ⊆ ℕ³` is semilinear;
* `SliceSemilinearN.isSliceFamilySemilinear2_count_global` — every row
  `n ↦ #fibre_{mS,n}` is eventually affine on the residue classes of ONE period `p0`,
  uniform in the row `mS`.

The second follows from the first with no further counting input, by
`semilinearGraph3_affineOnResiduesAt_uniform`.

The file sits below both `CopiedTieSemilinear2` (which discharges
`CopiedD4.TieCountAffineBudgeted`) and `TwoParamSemilinearity` (which needs the graph
form), so that a single counting input serves both towers.
-/
import RequestProject.SliceSemilinear2
import RequestProject.PresburgerCounting
import RequestProject.SemilinearGraphAffine

namespace SliceSemilinearN

/-- **Joint count graph of a two-parameter slice family.**  For a semilinear family
with finite fibres obeying the global linear bound `≤ C · (mS + n + 1)`, the graph
`{(mS, n, #fibre_{mS,n})} ⊆ ℕ³` is semilinear.

This is the `p = 2`, `q = k` instance of `PresburgerCounting.count_graph_semilinear`
(`lem:presburger-counting`).  The derivation is bookkeeping: the packed family graph
`familyGraph2 Φ ⊆ ℕ^(k+2)` is carried to Mathlib's `IsSemilinearSet` by
`isSemilinearNd_to_mathlib`, the counting input is applied through
`PresburgerCounting.count_graph_two_param` (which reindexes `Fin (k+2)` as
`Fin 2 ⊕ Fin k` and trades the sup-norm bound for the `mS + n + 1` bound at the cost of
a factor `2` in the constant), and the resulting `ℕ³` count graph is carried back by
`mathlib_to_isSemilinearNd`. -/
theorem sliceFamilyCount2_graph_semilinear {k : ℕ}
    {Φ : ℕ → ℕ → (Fin k → ℕ) → Prop} (hΦ : IsSliceFamilySemilinear2 Φ)
    (hfin : ∀ mS n, Set.Finite {ī : Fin k → ℕ | Φ mS n ī})
    (C : ℕ) (hbd : ∀ mS n, Nat.card {ī : Fin k → ℕ | Φ mS n ī} ≤ C * (mS + n + 1)) :
    IsSemilinearNd 3
      {v : Fin 3 → ℕ | Nat.card {ī : Fin k → ℕ | Φ (v 0) (v 1) ī} = v 2} :=
  mathlib_to_isSemilinearNd 3 _
    (PresburgerCounting.count_graph_two_param Φ
      (isSemilinearNd_to_mathlib (k + 2) _ hΦ) hfin C hbd)

/-- **Row-uniform affinity of the count, from the global bound.**  For a semilinear
two-parameter family with finite fibres whose cardinality obeys the *global* linear
bound `≤ C · (mS + n + 1)`, there is one period `p0`, uniform in the row `mS`, on whose
residue classes every row `n ↦ #fibre_{mS,n}` is eventually affine.

`sliceFamilyCount2_graph_semilinear` supplies the joint `ℕ³` count graph, and
`semilinearGraph3_affineOnResiduesAt_uniform` reads a row-uniform period off any
semilinear function graph in `ℕ³` with no bound hypotheses. -/
theorem isSliceFamilySemilinear2_count_global {k : ℕ}
    {Φ : ℕ → ℕ → (Fin k → ℕ) → Prop} (hΦ : IsSliceFamilySemilinear2 Φ)
    (hfin : ∀ mS n, Set.Finite {ī : Fin k → ℕ | Φ mS n ī})
    (C : ℕ) (hbd : ∀ mS n, Nat.card {ī : Fin k → ℕ | Φ mS n ī} ≤ C * (mS + n + 1)) :
    ∃ p0 : ℕ, 1 ≤ p0 ∧ ∀ mS : ℕ,
      SlicePeriodStar.AffineOnResiduesAt p0
        (fun n => Nat.card {ī : Fin k → ℕ | Φ mS n ī}) :=
  semilinearGraph3_affineOnResiduesAt_uniform _
    (sliceFamilyCount2_graph_semilinear hΦ hfin C hbd)

end SliceSemilinearN
