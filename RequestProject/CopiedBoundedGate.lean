/-
# The bounded-cell gate variant (§9 mS-direction, the fibred-fold ONE-DFA piece)

The unbounded fibred full gate builds its DFA from a formula whose cellClause `andList`s range over
`regionTuplesF B/Bh (arity c') mS`, which GROWS with `mS` — so the DFA differs per `mS` and cannot be a
single folded `GdfaF` object.  This file builds the variant whose cellClause `andList`s range over a
FIXED, mS-FREE cell set `boundedTuplesF` (the only cells with non-empty selector emitters: `core` plus
shallow `prefIdx q < q_U` / `sufIdx l < q_D`).  Because the formula is mS-free, the resulting `Mdfa` is
ONE object usable for EVERY `mS` in the class — folding becomes `rfl`.

The deep cells (in `regionTuplesF mS \ boundedTuplesF`) are dropped: their selector emitters are empty
(`hS₁b`/`hF₁b`/… hypotheses, supplied by the selector's emptiness conclusions), so in the BACKWARD
direction a `cfgCellGAFL` witness cell — whose `cfgPosL` premise forces some emitter non-empty — is
necessarily a bounded cell.  In the FORWARD direction the bounded cells are valid at every `mS > max q_U q_D`.
-/
import RequestProject.CopiedDeepRunGate
import RequestProject.CopiedTieGateF

namespace CopiedBoundedGate

open CopiedCells

/-- The bounded (mS-free) descriptor set: all `core` cells plus shallow `prefIdx q < q_U` / `sufIdx l < q_D`. -/
def boundedSpecFs (B q_U q_D : ℕ) : Finset (RegionSpecF B) :=
  (Finset.univ.image RegionSpecF.core)
    ∪ ((Finset.range q_U).image RegionSpecF.prefIdx)
    ∪ ((Finset.range q_D).image RegionSpecF.sufIdx)

theorem mem_boundedSpecFs {B : ℕ} (q_U q_D : ℕ) (r : RegionSpecF B) :
    r ∈ boundedSpecFs B q_U q_D ↔
      (match r with
        | .core _ => True
        | .prefIdx q => q < q_U
        | .sufIdx l => l < q_D) := by
  unfold boundedSpecFs
  rcases r with r | q | l <;>
    simp [Finset.mem_union, Finset.mem_image]

/-- The bounded tuple enumeration (mS-free; NOT a `Fintype` instance). -/
def boundedTuplesF (B k q_U q_D : ℕ) : Finset (Fin k → RegionSpecF B) :=
  Fintype.piFinset (fun _ => boundedSpecFs B q_U q_D)

theorem mem_boundedTuplesF {B k : ℕ} (q_U q_D : ℕ) (r : Fin k → RegionSpecF B) :
    r ∈ boundedTuplesF B k q_U q_D ↔
      ∀ i, (match r i with
        | .core _ => True
        | .prefIdx q => q < q_U
        | .sufIdx l => l < q_D) := by
  unfold boundedTuplesF
  rw [Fintype.mem_piFinset]
  exact forall_congr' (fun i => mem_boundedSpecFs q_U q_D (r i))

/-- Every bounded cell is `valid` at any `mS > max q_U q_D`. -/
theorem boundedTuplesF_valid {B k : ℕ} (q_U q_D mS : ℕ) (hqU : q_U < mS) (hqD : q_D < mS)
    (rs : Fin k → RegionSpecF B) (hrs : rs ∈ boundedTuplesF B k q_U q_D) :
    ∀ i, (rs i).valid mS := by
  intro i
  have hi := (mem_boundedTuplesF q_U q_D rs).mp hrs i
  rcases hrsi : rs i with r | q | l
  · simp only [RegionSpecF.valid]
  · simp only [hrsi] at hi; simp only [RegionSpecF.valid]; omega
  · simp only [hrsi] at hi; simp only [RegionSpecF.valid]; omega

end CopiedBoundedGate
