/-
# Examples and Computations

Formalization of the concrete examples in the paper
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang.
-/
import RequestProject.DyckPath

open Step

/-! ## Example 2.4 (`def:zeta`, paper.tex) -/

/-- **`def:zeta` (paper.tex).**
The path `P = UUDDUD ∈ D_3` has U-positions 0, 1, 4 at heights 0, 1, 0,
so `a(P) = (0, 1, 0)`. -/
theorem areaSeq_UUDDUD : areaSeq [U, U, D, D, U, D] = [0, 1, 0] := by native_decide

/-- **`def:zeta` (paper.tex).**
`area(UUDDUD) = 1`. -/
theorem area_UUDDUD : area [U, U, D, D, U, D] = 1 := by native_decide

/-- **`def:zeta` (paper.tex).**
`dinv(UUDDUD) = 2`, with dinv pairs `(1,3)` giving `0 - 0 = 0`
and `(2,3)` giving `1 - 0 = 1`. -/
theorem dinv_UUDDUD : dinv [U, U, D, D, U, D] = 2 := by native_decide

/-- **`def:zeta` (paper.tex).**
`UUDDUD` is a Dyck path. -/
theorem isDyckPath_UUDDUD : IsDyckPath [U, U, D, D, U, D] := by
  unfold IsDyckPath
  refine ⟨?_, ?_⟩
  · intro k hk; simp only [List.length] at hk; interval_cases k <;> simp [height]
  · simp [height]

/-! ## Example 2.6 (`sec:dyck`, paper.tex) -/

/-- **`sec:dyck` (paper.tex).**
`ζ(UUDDUD) = UUDUDD`. The area sequence `(0,1,0)` yields: at rank 0, entries
equal to 0 at positions 1,3 give `UU`; at rank 1, entries equal to 0 give D's
and the entry equal to 1 gives a U; at rank 2, the entry equal to 1 gives D. -/
theorem zetaMap_UUDDUD : zetaMap [U, U, D, D, U, D] = [U, U, D, U, D, D] := by native_decide

/-- **`sec:dyck` (paper.tex).**
`area(ζ(UUDDUD)) = 2 = dinv(UUDDUD)`, verifying that the zeta map sends
dinv to area. -/
theorem area_zetaMap_UUDDUD : area (zetaMap [U, U, D, D, U, D]) = 2 := by native_decide

/-! ## Example 8.8 (`sec:narayana-sweep`, paper.tex): Narayana sweep on UUUDDD -/

/-- **`sec:narayana-sweep` (paper.tex).**
The Narayana sweep `H(UUUDDD) = UDUDUD`. The mountain with two double rises
and no valley is sent to the zigzag with `val = 2` and `dr = 0`.
Uses right-to-left ties as specified in the paper's definition of H. -/
theorem heightSweep_UUUDDD :
    heightSweep [U, U, U, D, D, D] = [U, D, U, D, U, D] := by native_decide

/-- **`sec:narayana-sweep` (paper.tex).**
`UUUDDD` has 0 valleys and 2 double rises. -/
theorem valleys_UUUDDD : valleys [U, U, U, D, D, D] = 0 := by native_decide
theorem doubleRises_UUUDDD : doubleRises [U, U, U, D, D, D] = 2 := by native_decide

/-- **`sec:narayana-sweep` (paper.tex).**
`UDUDUD` has 2 valleys and 0 double rises, confirming the swap. -/
theorem valleys_UDUDUD : valleys [U, D, U, D, U, D] = 2 := by native_decide
theorem doubleRises_UDUDUD : doubleRises [U, D, U, D, U, D] = 0 := by native_decide
