/-
# The fibred sentence gates (§9 tower, Stage F — uniform EP gates)

The wrapped chain gated its case splits on per-slice MSO-sentence
periodicities (`Dpresent_eventuallyPeriodic`, domain-EP) — pointwise calls
whose periods would be `mS`-dependent on the copied slice.  The fibred route
replaces them by ONE `mso_slice_EP_uniform` call per sentence: the copied
slice is `pre ++ loop^n ++ suf` with `pre := U^mS`, `loop := UD`,
`suf := D^mS`, and the uniform engine's threshold and period are independent
of `(pre, suf)` — hence of `mS`.

* `copiedSlice_eq_blocks` — the canonical pre/loop/suf form of the copied
  slice (the single bridge every uniform-EP application uses);
* `Dpresent_EP_fibred` — D-presence on the copied slice is EP in `n` with
  `(m, p)` BEFORE `mS`;
* `domain_EP_fibred` — same for the presentation's domain sentence.
-/
import RequestProject.SliceSelect
import RequestProject.SlicePeriodStar
import RequestProject.CopiedRank

namespace CopiedGates

open WRP Step CopiedRank

/-- **The canonical block form of the copied slice**:
`U^mS (UD)^n D^mS` as `pre ++ loop^n ++ suf`. -/
theorem copiedSlice_eq_blocks (mS n : ℕ) (hm : 1 ≤ mS) :
    copiedSlice mS n
      = List.replicate mS U ++ (List.replicate n [U, D]).flatten
          ++ List.replicate mS D := by
  rw [CopiedMark.copiedSlice_eq_wrap mS n hm, wrappedFlat]
  have hU : List.replicate (mS - 1) U ++ [U] = List.replicate mS U := by
    rw [show ([U] : List Step) = List.replicate 1 U from rfl,
      List.replicate_append_replicate]
    congr 1
    omega
  have hD : ([D] : List Step) ++ List.replicate (mS - 1) D
      = List.replicate mS D := by
    rw [show ([D] : List Step) = List.replicate 1 D from rfl,
      List.replicate_append_replicate]
    congr 1
    omega
  rw [← hU, ← hD]
  simp only [List.append_assoc]

/-- **The fibred D-present gate**: existence of a selected `D`-atom on the
copied slice is eventually periodic in `n`, with threshold and period BEFORE
`mS` (one uniform-EP call on the exists-sentence). -/
theorem Dpresent_EP_fibred (P : WRP.Presentation Step Step) :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ mS, 1 ≤ mS → ∀ n, m ≤ n →
      ((∃ a : P.toPoly.Atom,
          P.toPoly.selectedAtom (copiedSlice mS (n + p)) a ∧
          P.toPoly.labelOf (copiedSlice mS (n + p)) a = D) ↔
       (∃ a : P.toPoly.Atom,
          P.toPoly.selectedAtom (copiedSlice mS n) a ∧
          P.toPoly.labelOf (copiedSlice mS n) a = D)) := by
  obtain ⟨mv, pv, hpv, hper⟩ := SlicePeriodStar.mso_slice_EP_uniform
    (SliceSelect.existsSentence P.toPoly D) [U, D]
  refine ⟨mv, pv, hpv, fun mS hm n hn => ?_⟩
  rw [← SliceSelect.sat_existsSentence P.toPoly D (copiedSlice mS (n + pv)),
    ← SliceSelect.sat_existsSentence P.toPoly D (copiedSlice mS n),
    copiedSlice_eq_blocks mS (n + pv) hm, copiedSlice_eq_blocks mS n hm]
  exact hper (List.replicate mS U) (List.replicate mS D) n hn

/-- **The fibred domain gate**: membership of the copied slice in the
presentation's domain is eventually periodic in `n`, with threshold and
period BEFORE `mS`. -/
theorem domain_EP_fibred (P : WRP.Presentation Step Step) :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ mS, 1 ≤ mS → ∀ n, m ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + p))
        ↔ P.toPoly.domain (copiedSlice mS n)) := by
  obtain ⟨φ, hφ⟩ := P.toPoly.domainDef
  obtain ⟨mv, pv, hpv, hper⟩ := SlicePeriodStar.mso_slice_EP_uniform φ [U, D]
  refine ⟨mv, pv, hpv, fun mS hm n hn => ?_⟩
  rw [hφ, hφ, copiedSlice_eq_blocks mS (n + pv) hm,
    copiedSlice_eq_blocks mS n hm]
  exact hper (List.replicate mS U) (List.replicate mS D) n hn

end CopiedGates
