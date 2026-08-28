/-
# EP-in-mS folding of the deep-achieving offset sets (§9 mS-direction, step 2 of the direct bridge)

The direct `hbr` bridge conjoins `deepSufOrdClauseAt k` over the from-end offsets `k` whose deep cell
achieves `d*`, and `sufOrdClauseAt r` over the tying residue classes `r`.  For
`tie_count_fibred_of_gate` the gate must be a FOLDED family `GdfaF (mS % qM) (n % pG)`, so these index
sets must be CONSTANT on each mS-residue-class past a threshold.  This file folds the DEEP-offset
achieving sets `deepAchSuf` / `deepAchPre` via `CopiedTie2b.range_filter_EP_mS` + the deep-cell atom
EP `CopiedTie2b.rankEqDstarC_atom_EP_mS`.  (The shallow / run-tying-class folds reuse
`CopiedTie2b.rankEq_iff_on_mS_class` directly — the genuinely new pieces here are the DEEP ones.)
-/
import RequestProject.CopiedTie2b

namespace CopiedAchSetFold

open WRP Step CopiedTie2b CopiedCells CopiedDstar CopiedSetupMS SliceOrder CopiedAffineAt

/-- **`tyingSuf` folds in mS.**  The set of suffix pc-residue-classes `r ∈ [0, pcF)` that tie `d*`
(rank of the shallow representative `sufIdx (Ts+r)` = `d*`) is constant on each mS-residue-class —
`range_filter_EP_mS` over the shallow `rankEq_iff_on_mS_class`. -/
theorem tyingSuf_fold (P : WRP.Presentation Step Step) (c' : Fin P.toPoly.K)
    {B : ℕ} (hB : 1 ≤ B) (t n : ℕ) (hwin : t + B ≤ n) (Ts pcF : ℕ)
    (pstar : ℕ) (hpstar : 1 ≤ pstar) (dstarC : ℕ → Fin P.d → ℤ)
    (hdstarCaff : ∀ i, AffineOnResiduesAtZ pstar (fun mS => dstarC mS i)) :
    ∃ q m0, 1 ≤ q ∧ ∀ mS mS', m0 ≤ mS → m0 ≤ mS' → mS % q = mS' % q →
      (Finset.range pcF).filter (fun r =>
          P.rank c' (copiedSlice mS n)
            (cellTupleF (fun _ => (RegionSpecF.sufIdx (Ts + r) : RegionSpecF B)) mS t n) = dstarC mS)
        = (Finset.range pcF).filter (fun r =>
          P.rank c' (copiedSlice mS' n)
            (cellTupleF (fun _ => (RegionSpecF.sufIdx (Ts + r) : RegionSpecF B)) mS' t n) = dstarC mS') := by
  have key : ∀ r : ℕ, ∃ (q m₀ : ℕ), 1 ≤ q ∧ ∀ mS mS', m₀ ≤ mS → m₀ ≤ mS' → mS % q = mS' % q →
      ((P.rank c' (copiedSlice mS n)
            (cellTupleF (fun _ => (RegionSpecF.sufIdx (Ts + r) : RegionSpecF B)) mS t n) = dstarC mS) ↔
       (P.rank c' (copiedSlice mS' n)
            (cellTupleF (fun _ => (RegionSpecF.sufIdx (Ts + r) : RegionSpecF B)) mS' t n) = dstarC mS')) := by
    intro r
    exact rankEq_iff_on_mS_class P c' hB (fun _ => (RegionSpecF.sufIdx (Ts + r) : RegionSpecF B))
      t n hwin pstar hpstar dstarC hdstarCaff
  choose qs m0s hq htrans using key
  obtain ⟨q, m0, hq1, hfold⟩ := range_filter_EP_mS pcF
    (fun r mS => P.rank c' (copiedSlice mS n)
      (cellTupleF (fun _ => (RegionSpecF.sufIdx (Ts + r) : RegionSpecF B)) mS t n) = dstarC mS)
    qs m0s hq htrans
  refine ⟨q, m0, hq1, fun mS mS' hm hm' hmod => ?_⟩
  convert hfold mS mS' hm hm' hmod using 2

end CopiedAchSetFold
