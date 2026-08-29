/-
# The d*-rank bridge: the class-boundary domination lemma

`selBvec_le_member`: the selected-restricted per-class lex boundary of `SliceDstar` dominates every
member of its class.  It is the `sel`-restricted specialisation of
`SliceDstar.selBvec_lex_is_lex_min`, extracted as a standalone lemma so that the bulk leaves of the
`d*`-existence proofs do not re-elaborate the heavy proof inline.

Rests on the textbook Büchi axiom (via the selectedness gates).
-/import RequestProject.SliceDstar
import RequestProject.SliceFasBridges
import RequestProject.SliceFasGates
import RequestProject.SliceRankRegions

namespace SliceDstarBridge

open WRP SliceDstar SliceBoundaryMinCore
open scoped Classical

/-- **The class boundary lex-dominates every member**, extracted as a standalone lemma so the
`d*`-existence bulk leaves do not re-elaborate the heavy proof inline.  The boundary vector with
`firstSel = 0`, `lastSel = numReps - 1` lex-dominates `F (m+r+p·kd)` for every `kd < numReps`. -/
theorem selBvec_le_member {d : ℕ} (F : ℕ → Fin d → ℤ) {m p : ℕ} (P : Fin d → ℤ) (takeLast : Bool)
    (hrec : ∀ (i : Fin d) (r k : ℕ), F (m + r + p * k) i = F (m + r) i + k * P i)
    (hflag : takeLast = true ↔ WRP.lexLt P (fun _ => 0))
    (r N kd : ℕ) (hkd : kd < numReps m p r N) :
    ¬ WRP.lexLt (F (m + r + p * kd))
      (selBvecVal F m r P takeLast 0 (numReps m p r N - 1)) :=
  (selBvec_lex_is_lex_min F P takeLast (fun _ => True) hrec hflag r N 0 (numReps m p r N - 1)
    ⟨by omega, trivial, fun k hk => (by omega : False).elim⟩
    ⟨by omega, trivial, fun k h1 h2 => (by omega : False).elim⟩).1 kd hkd trivial

/-- Every member of a `ℤ`-list is `≤` its `foldr max 0`. -/
theorem le_foldr_max {x : ℤ} : ∀ {l : List ℤ}, x ∈ l → x ≤ l.foldr max 0 := by
  intro l hx
  induction l with
  | nil => exact absurd hx (by simp)
  | cons a l ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact le_max_left _ _
      · exact le_trans (ih hx') (le_max_right _ _)

end SliceDstarBridge
