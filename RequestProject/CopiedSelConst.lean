/-
# Selection-constancy on a residue class (§9 d4a, gap G2 — the slice wrapper)

Gate acceptance (= `selectedAtom ∧ label = D`, via the marked DFA `Mc`) is constant on each residue
class of the homogeneous `D^mS` suffix run — and of the `U^mS` prefix run — of `copiedSlice mS n`.
This is what makes the per-class uniformity of `CopiedSelUniform` provable: a run atom achieving `d*`
forces its whole class to achieve `d*` only because the class endpoint is SELECTED, which is exactly
this constancy.

The two wrappers `selRun_suf_update_shift` / `selRun_pre_update_shift` are stated over
distinguished-coordinate update tuples at ARBITRARY arity, so they apply directly to the
arity-`(arity c)` D-selector gate with no `MarkedN (arity c) → MarkedN 1` coercion.
-/import RequestProject.CopiedSufRunGate
import RequestProject.CopiedDstarCMS

namespace CopiedSelConst

open WRP Step MSOMarkN SliceMSO

/-! ## (4a-1) Selection-constancy at the slice — the keystone connecting G2 to per-class uniformity -/

/-- Selection-constancy for one moving suffix coordinate in arbitrary arity.
This is the selector-facing wrapper around
`CopiedDstarCMS.accepts_copiedSlice_suf_shift`: if two tuples differ only by
sliding coordinate `j0` inside a clear final-`D` sub-window, and the unmarked
`D` transition is periodic across that slide, then the selected-`D` predicate is
unchanged. -/
theorem selRun_suf_update_shift
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hM : ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        (M.accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (mS n : ℕ) (hm1 : 1 ≤ mS)
    (ī ī' : Fin (P.toPoly.arity c) → ℕ) (j0 : Fin (P.toPoly.arity c))
    (s e a a' κ T pc : ℕ)
    (hper : ∀ κ b, T ≤ b →
      (fun q => M.δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun q => M.δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hval : ∀ i, ī i < (copiedSlice mS n).length)
    (hval' : ∀ i, ī' i < (copiedSlice mS n).length)
    (hsame : ∀ i, i ≠ j0 → ī i = ī' i)
    (hse : s ≤ e) (heL : e ≤ mS - 1)
    (hsa : s ≤ a) (hae : a < e) (hsa' : s ≤ a') (hae' : a' < e)
    (hj0 : ī j0 = mS + 2 * n + 1 + a)
    (hj0' : ī' j0 = mS + 2 * n + 1 + a')
    (hclear : ∀ i, i ≠ j0 →
      ī i < mS + 2 * n + 1 + s ∨ mS + 2 * n + 1 + e ≤ ī i)
    (hgapA : T ≤ a - s) (hgapA' : T ≤ a' - s)
    (hgapR : T ≤ e - 1 - a) (hgapR' : T ≤ e - 1 - a')
    (hshift : a' = a + pc * κ ∨ a = a' + pc * κ) :
    (P.toPoly.sel c (copiedSlice mS n) ī
        ∧ P.toPoly.label c (copiedSlice mS n) ī = D)
      ↔ (P.toPoly.sel c (copiedSlice mS n) ī'
        ∧ P.toPoly.label c (copiedSlice mS n) ī' = D) := by
  rw [← hM (copiedSlice mS n) ī hval, ← hM (copiedSlice mS n) ī' hval']
  exact CopiedDstarCMS.accepts_copiedSlice_suf_shift M mS n hm1 ī ī' j0 s e a a' κ T pc
    hper hsame hse heL hsa hae hsa' hae' hj0 hj0' hclear hgapA hgapA' hgapR hgapR'
    hshift

/-- Prefix twin of `selRun_suf_update_shift`: one moving coordinate slides
inside a clear initial-`U` sub-window, preserving the selected-`D` predicate. -/
theorem selRun_pre_update_shift
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hM : ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        (M.accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (mS n : ℕ) (hm1 : 1 ≤ mS)
    (ī ī' : Fin (P.toPoly.arity c) → ℕ) (j0 : Fin (P.toPoly.arity c))
    (s e a a' κ T pc : ℕ)
    (hper : ∀ κ b, T ≤ b →
      (fun q => M.δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun q => M.δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b])
    (hval : ∀ i, ī i < (copiedSlice mS n).length)
    (hval' : ∀ i, ī' i < (copiedSlice mS n).length)
    (hsame : ∀ i, i ≠ j0 → ī i = ī' i)
    (hse : s ≤ e) (heL : e ≤ mS - 1)
    (hsa : s ≤ a) (hae : a < e) (hsa' : s ≤ a') (hae' : a' < e)
    (hj0 : ī j0 = a) (hj0' : ī' j0 = a')
    (hclear : ∀ i, i ≠ j0 → ī i < s ∨ e ≤ ī i)
    (hgapA : T ≤ a - s) (hgapA' : T ≤ a' - s)
    (hgapR : T ≤ e - 1 - a) (hgapR' : T ≤ e - 1 - a')
    (hshift : a' = a + pc * κ ∨ a = a' + pc * κ) :
    (P.toPoly.sel c (copiedSlice mS n) ī
        ∧ P.toPoly.label c (copiedSlice mS n) ī = D)
      ↔ (P.toPoly.sel c (copiedSlice mS n) ī'
        ∧ P.toPoly.label c (copiedSlice mS n) ī' = D) := by
  rw [← hM (copiedSlice mS n) ī hval, ← hM (copiedSlice mS n) ī' hval']
  exact CopiedDstarCMS.accepts_copiedSlice_pref_shift M mS n hm1 ī ī' j0 s e a a' κ T pc
    hper hsame hse heL hsa hae hsa' hae' hj0 hj0' hclear hgapA hgapA' hgapR hgapR'
    hshift

end CopiedSelConst
