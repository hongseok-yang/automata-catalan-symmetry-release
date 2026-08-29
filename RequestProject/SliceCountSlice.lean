/-
# Block-iterate facts for the slice selection count

The automaton-side foundation of the slice-specific count reduction.  For a
deterministic automaton `M` over `Step × Bool`, the forward unmarked run `fwd`
reaches the start of loop-block `j` of `W_n` in state `bF^[j] q_pre`, where
`bF q = foldl fStep q [U,D]` is the one-block transition and `q_pre = fStep q0 U`.
The forward state iterate `bF^[j] q_pre` and the iterate *function* `bF^[m]` are
both eventually periodic (`M.Q`, hence `M.Q → M.Q`, is finite), which is what feeds
the convolution.  All axiom-clean.
-/
import RequestProject.SliceCount
import RequestProject.SliceWords
import RequestProject.SliceMSO
import RequestProject.SliceAutomata
import RequestProject.SliceAffine
import RequestProject.WrappedFlat

open SliceMSO Step
open scoped Classical

namespace SliceCount

variable (M : DetAuto (Step × Bool))

/-- The one-block (`UD`) forward transition. -/
def bF (q : M.Q) : M.Q := List.foldl (fStep M) q [U, D]

/-- The forward state after the slice's leading `U`. -/
def qpre : M.Q := fStep M M.q0 U

/-- **Forward state at a block boundary.**  The unmarked forward run reaches the
start of loop-block `j` of `W_n` in state `bF^[j] q_pre`. -/
theorem fwd_blockStart (n j : ℕ) (h : j ≤ n) :
    fwd M (wrappedFlat n) (1 + 2 * j) = (bF M)^[j] (qpre M) := by
  unfold fwd
  rw [SliceWords.wrappedFlat_take j n h, List.foldl_append,
    show List.foldl (fStep M) M.q0 [U] = qpre M from rfl, foldl_replicate_flatten]
  rfl

/-- The forward state iterate `bF^[j] q_pre` is eventually periodic in `j`. -/
theorem bF_iterate_eventuallyPeriodic :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ j, m ≤ j → (bF M)^[j + p] (qpre M) = (bF M)^[j] (qpre M) := by
  have := M.fintypeQ
  exact SliceAutomata.iterate_eventuallyPeriodic (bF M) (qpre M)

/-- The iterate *function* `bF^[m]` is eventually periodic in `m` (`M.Q → M.Q` is
finite). -/
theorem bF_func_iterate_eventuallyPeriodic :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ j, m ≤ j → (bF M)^[j + p] = (bF M)^[j] := by
  have := M.fintypeQ
  obtain ⟨m, p, hp, hper⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic (fun g : M.Q → M.Q => bF M ∘ g) id
  have key : ∀ k, (fun g : M.Q → M.Q => bF M ∘ g)^[k] id = (bF M)^[k] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, ← Function.iterate_succ']
  exact ⟨m, p, hp, fun j hj => by rw [← key, ← key]; exact hper j hj⟩

/-- The slice suffix at a loop-block, exposing the block's `U`, `D` and the rest. -/
theorem wrappedFlat_drop_block (n j : ℕ) (h : j < n) :
    (wrappedFlat n).drop (1 + 2 * j) =
      U :: D :: ((List.replicate (n - 1 - j) [U, D]).flatten ++ [D]) := by
  rw [SliceWords.wrappedFlat_drop j n (le_of_lt h), show n - j = (n - 1 - j) + 1 from by omega,
    List.replicate_succ, List.flatten_cons]
  rfl

theorem wrappedFlat_getElem_U (n j : ℕ) (h : j < n) (hb : 1 + 2 * j < (wrappedFlat n).length) :
    (wrappedFlat n)[1 + 2 * j] = U := by
  have hd := @List.getElem?_drop _ (wrappedFlat n) (1 + 2 * j) 0
  rw [wrappedFlat_drop_block n j h, Nat.add_zero, List.getElem?_eq_getElem hb] at hd
  simpa using hd.symm

theorem wrappedFlat_getElem_D (n j : ℕ) (h : j < n)
    (hb : 1 + 2 * j + 1 < (wrappedFlat n).length) : (wrappedFlat n)[1 + 2 * j + 1] = D := by
  have hd := @List.getElem?_drop _ (wrappedFlat n) (1 + 2 * j) 1
  rw [wrappedFlat_drop_block n j h, List.getElem?_eq_getElem hb] at hd
  simpa using hd.symm

/-- Backward type just after the block's `U` (at its `D`). -/
theorem tau_blockU (n j : ℕ) (h : j < n) (q : M.Q) :
    tau M (wrappedFlat n) (1 + 2 * j + 1) q =
      M.accept (fStep M ((bF M)^[n - 1 - j] (fStep M q D)) D) := by
  unfold tau
  rw [show 1 + 2 * j + 1 = (1 + 2 * j) + 1 from rfl, ← List.drop_drop, wrappedFlat_drop_block n j h,
    List.drop_one, List.tail_cons, List.foldl_cons, List.foldl_append, foldl_replicate_flatten]
  rfl

theorem wrappedFlat_getElem_zero (n : ℕ) (hb : 0 < (wrappedFlat n).length) :
    (wrappedFlat n)[0] = U := by
  have h0 : (wrappedFlat n)[0]? = some U := by unfold wrappedFlat; rfl
  rw [List.getElem?_eq_getElem hb] at h0
  exact Option.some.inj h0

theorem wrappedFlat_getElem_last (n : ℕ) (hb : 2 * n + 1 < (wrappedFlat n).length) :
    (wrappedFlat n)[2 * n + 1] = D := by
  have hd := @List.getElem?_drop _ (wrappedFlat n) (1 + 2 * n) 0
  rw [SliceWords.wrappedFlat_drop n n (le_refl n), Nat.sub_self, Nat.add_zero,
    show 1 + 2 * n = 2 * n + 1 from by ring, List.getElem?_eq_getElem hb] at hd
  simpa using hd.symm

end SliceCount
