/-
# The §7 slice-domain periodicity lemma

`domain_slice_EP`: the domain bit of a polyregular presentation is eventually periodic along the
wrapped-flat slice `W_n`.  It is the one statement the arity-1 `fas`-count assembly left behind for
the general-arity tower, which consumes it in `SliceFasAssemblyGA` and `SliceFasCountGA`.

The file sits above the whole arity-1 slice tower in the import order, which is why the lemma lives
here rather than in `SliceFasCount`.
-/
import RequestProject.SliceAffineSelect
import RequestProject.SliceFasSelector
import RequestProject.SliceFasTie
import RequestProject.SliceProfileDischarge
import RequestProject.SliceProfile

namespace SliceFasAssembly

open Step SliceMSO
open scoped Classical

/-- The slice domain bit of a polyregular presentation is eventually periodic in `n`
(`domainDef` + `mso_slice_eventuallyPeriodic`). -/
theorem domain_slice_EP (Q : Polyreg.Presentation Step Step) :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ n, m ≤ n →
      (Q.domain (wrappedFlat (n + p)) ↔ Q.domain (wrappedFlat n)) := by
  obtain ⟨φ, hφ⟩ := Q.domainDef
  obtain ⟨m, p, hp, hper⟩ := SliceMSO.mso_slice_eventuallyPeriodic φ [U] [U, D] [D]
  refine ⟨m, p, hp, fun n hn => ?_⟩
  rw [hφ, hφ]
  exact hper n hn

end SliceFasAssembly
