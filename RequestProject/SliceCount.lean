/-
# Counting MSO-satisfying positions on the slice (selection-counting, part 2)

Connects the marked recogniser of `MSOMark` (part 1) to the convolution kernels of
`SliceGatedConv` (part 3).

This file is the forward–backward bridge.  For a deterministic automaton `M` over
`Step × Bool`, reading the single-mark word `markAt w p` factors into

  * a **forward** unmarked run `fwd w p` over the prefix `w.take p`, then the marked
    transition on `(w[p], true)`, then
  * a **backward** unmarked run, captured by the *type* `tau w (p+1)` — whether,
    from a given state, reading the unmarked suffix `w.drop (p+1)` accepts.

So `M.accepts (markAt w p) ↔ tau w (p+1) (M.δ (fwd w p) (w[p], true))`.  The forward
state is a left automaton iterate and the backward type a right automaton iterate;
on the slice both are eventually periodic, and the position count becomes a
convolution handled by `SliceGatedConv`.
-/
import RequestProject.MSOMark

open MSOMark SliceMSO

namespace SliceCount

/-- The "unmarked" embedding `Step → Step × Bool`. -/
def unmark (a : Step) : Step × Bool := (a, false)

/-- `markAt w p` is the unmarked prefix, the single marked letter, then the
unmarked suffix. -/
theorem markAt_decomp (w : List Step) (p : ℕ) (hp : p < w.length) :
    markAt w p = (w.take p).map unmark ++ (w[p], true) :: (w.drop (p + 1)).map unmark := by
  have hAlen : ((w.take p).map unmark).length = p := by
    rw [List.length_map, List.length_take, Nat.min_eq_left (le_of_lt hp)]
  apply List.ext_getElem?
  intro n
  rcases lt_or_ge n w.length with hn | hn
  · rw [markAt_getElem? w p n hn]
    rcases lt_trichotomy n p with hlt | heq | hgt
    · -- `n < p`: inside the unmarked prefix
      rw [List.getElem?_append_left (by omega), List.getElem?_map,
        List.getElem?_take_of_lt hlt, List.getElem?_eq_getElem (by omega)]
      simp [unmark, Nat.ne_of_lt hlt]
    · -- `n = p`: the marked letter
      subst heq
      rw [List.getElem?_append_right (by omega), hAlen, Nat.sub_self, List.getElem?_cons_zero]
      simp
    · -- `n > p`: inside the unmarked suffix
      rw [List.getElem?_append_right (by omega), hAlen]
      rw [show n - p = (n - p - 1) + 1 from by omega, List.getElem?_cons_succ,
        List.getElem?_map, List.getElem?_drop, List.getElem?_eq_getElem (by omega)]
      have : p + 1 + (n - p - 1) = n := by omega
      simp [unmark, this, Nat.ne_of_gt hgt]
  · rw [List.getElem?_eq_none (by rw [markAt_length]; exact hn),
      List.getElem?_eq_none (by
        rw [List.length_append, hAlen, List.length_cons, List.length_map, List.length_drop]
        omega)]

variable (M : DetAuto (Step × Bool))

/-- Forward (unmarked) transition. -/
def fStep (q : M.Q) (a : Step) : M.Q := M.δ q (a, false)

/-- Forward state after reading the unmarked prefix `w.take p`. -/
def fwd (w : List Step) (p : ℕ) : M.Q := List.foldl (fStep M) M.q0 (w.take p)

/-- Backward type at `j`: from `q`, does reading the unmarked suffix `w.drop j`
accept? -/
def tau (w : List Step) (j : ℕ) (q : M.Q) : Prop :=
  M.accept (List.foldl (fStep M) q (w.drop j))

/-- Folding `M.δ` over an unmarked word is the forward run. -/
theorem foldl_fStep_eq (q : M.Q) (l : List Step) :
    List.foldl M.δ q (l.map unmark) = List.foldl (fStep M) q l := by
  rw [List.foldl_map]; rfl

/-- **Forward–backward acceptance.**  `M` accepts the single-mark word `markAt w p`
iff the backward type after the marked position accepts the marked transition out
of the forward state. -/
theorem accepts_markAt (w : List Step) (p : ℕ) (hp : p < w.length) :
    M.accepts (markAt w p) ↔ tau M w (p + 1) (M.δ (fwd M w p) (w[p], true)) := by
  unfold DetAuto.accepts
  rw [markAt_decomp w p hp, List.foldl_append, List.foldl_cons, foldl_fStep_eq, foldl_fStep_eq]
  rfl

end SliceCount
