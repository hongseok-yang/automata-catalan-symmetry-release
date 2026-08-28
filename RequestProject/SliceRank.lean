/-
# Prefix-ranks of a rank source on the slice are affine on residue classes

This connects the abstract automata core (`SliceAutomata.affineOnResidues_of_blockIterate`)
to the *actual* `RankSource.prefixRank` evaluated on the wrapped-flat slice
`W_n = U(UD)^n D`.  We introduce a fold-based rank accumulator `rankStep`, prove
it computes `prefixRank`, and split a run over `pre ++ (UD)^n` into one block per
loop iteration.  The conclusion (`prefixRank_pre_blocks_affineOnResidues`) is the
paper's `lem:one-loop-rank-affine` for the concrete model: the rank accumulated reading
`pre ++ (loop)^n` is, beyond a threshold and on each residue class of `n`, affine
in `n`.

For the wrapped-flat slice `W_n = U(UD)^n D`, take `pre = [U]` and `loop = [U,D]`:
the prefix-ranks at the loop boundaries are then affine on residue classes of `n`,
which is the rank ingredient the slice-profile theorem `wrp_slice_profile_affine` needs.
This file fully proves that ingredient (axiom-clean); what the axiom still bundles
is the MSO-selection ⇒ Presburger step and the bounded counting of `fas`/`tailU`.
-/
import RequestProject.WRP
import RequestProject.SliceAutomata

namespace SliceRank

open WRP

variable {Alpha : Type*} {d : ℕ} (A : RankSource Alpha d)

/-- One-step rank accumulator: advance the state and add the transition weight. -/
def rankStep (qacc : A.Q × (Fin d → ℤ)) (a : Alpha) : A.Q × (Fin d → ℤ) :=
  (A.δ qacc.1 a, qacc.2 + A.ω qacc.1 a)

/-- The state component of a `rankStep` fold is just the automaton run. -/
theorem rankStep_fst (q : A.Q) (acc : Fin d → ℤ) (w : List Alpha) :
    (List.foldl (rankStep A) (q, acc) w).1 = List.foldl A.δ q w := by
  induction w generalizing q acc with
  | nil => rfl
  | cons a w ih => simp only [List.foldl_cons, rankStep, ih]

/-- The rank component is additive in the starting accumulator. -/
theorem rankStep_snd_add (q : A.Q) (acc : Fin d → ℤ) (w : List Alpha) :
    (List.foldl (rankStep A) (q, acc) w).2 = acc + (List.foldl (rankStep A) (q, 0) w).2 := by
  induction w generalizing q acc with
  | nil => simp
  | cons a w ih =>
      simp only [List.foldl_cons, rankStep]
      rw [ih (A.δ q a) (acc + A.ω q a), ih (A.δ q a) (0 + A.ω q a)]
      abel

/-- The `rankStep` fold computes `prefixRank` over the whole word. -/
theorem foldl_rankStep_snd (q : A.Q) (acc : Fin d → ℤ) (w : List Alpha) :
    (List.foldl (rankStep A) (q, acc) w).2 =
      acc + ∑ j ∈ Finset.range w.length,
        (w[j]?).elim 0 (fun a => A.ω (List.foldl A.δ q (w.take j)) a) := by
  induction w generalizing q acc with
  | nil => simp
  | cons a w ih =>
      rw [List.foldl_cons]
      show (List.foldl (rankStep A) (A.δ q a, acc + A.ω q a) w).2 = _
      rw [ih, List.length_cons, Finset.sum_range_succ']
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.take_succ_cons,
        List.take_zero, List.foldl_cons, List.foldl_nil, Option.elim_some]
      abel

/-- `prefixRank A w |w| = (rankStep-fold over w).2`, starting from `(q₀, 0)`. -/
theorem prefixRank_eq_foldl (w : List Alpha) :
    A.prefixRank w w.length = (List.foldl (rankStep A) (A.q0, 0) w).2 := by
  rw [foldl_rankStep_snd, zero_add]
  funext c
  simp only [RankSource.prefixRank, RankSource.stateBefore, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  cases w[j]? <;> simp

/-- The state after one `loop` block, as a function of the starting state. -/
def blockStep (loop : List Alpha) (q : A.Q) : A.Q := List.foldl A.δ q loop

/-- The rank accumulated reading one `loop` block from state `q`. -/
def blockWeight (loop : List Alpha) (q : A.Q) : Fin d → ℤ :=
  (List.foldl (rankStep A) (q, 0) loop).2

/-- Reading `n` copies of `loop` accumulates `Σ_{i<n} blockWeight(blockStep^[i] q)`. -/
theorem foldl_rankStep_replicate_snd (loop : List Alpha) (q : A.Q) (acc : Fin d → ℤ) :
    ∀ n, (List.foldl (rankStep A) (q, acc) (List.replicate n loop).flatten).2 =
      acc + ∑ i ∈ Finset.range n, blockWeight A loop ((blockStep A loop)^[i] q) := by
  intro n
  induction n generalizing q acc with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, List.foldl_append]
      rw [show (List.foldl (rankStep A) (q, acc) loop)
            = (blockStep A loop q, acc + blockWeight A loop q) from ?_]
      · rw [ih, Finset.sum_range_succ', Function.iterate_zero, id]
        simp only [Function.iterate_succ_apply]
        abel
      · refine Prod.ext ?_ ?_
        · exact rankStep_fst A q acc loop
        · simp only [blockWeight]; exact rankStep_snd_add A q acc loop

/-- **Paper `lem:one-loop-rank-affine` for the concrete model.**  The total prefix-rank of the rank
source `A` reading `pre ++ loop^n` is, beyond a threshold `m` and on each residue
class of `n` mod a period `p`, affine in the loop count `n`. -/
theorem prefixRank_pre_blocks_affineOnResidues (pre loop : List Alpha) :
    ∃ (m p : ℕ) (P : Fin d → ℤ), 1 ≤ p ∧ ∀ k r : ℕ,
      A.prefixRank (pre ++ (List.replicate (m + p * k + r) loop).flatten)
        (pre ++ (List.replicate (m + p * k + r) loop).flatten).length =
      A.prefixRank (pre ++ (List.replicate (m + r) loop).flatten)
        (pre ++ (List.replicate (m + r) loop).flatten).length + k • P := by
  have : Fintype A.Q := A.fintypeQ
  -- abbreviate the per-block start state and the constant rank from the prefix
  set q₁ : A.Q := List.foldl A.δ A.q0 pre with hq₁
  set c : Fin d → ℤ := (List.foldl (rankStep A) (A.q0, 0) pre).2 with hc
  -- the total rank reading `pre ++ loop^n` equals `c + Σ_{i<n} blockWeight(blockStep^[i] q₁)`
  have hrank : ∀ n, A.prefixRank (pre ++ (List.replicate n loop).flatten)
      (pre ++ (List.replicate n loop).flatten).length =
      c + ∑ i ∈ Finset.range n, blockWeight A loop ((blockStep A loop)^[i] q₁) := by
    intro n
    rw [prefixRank_eq_foldl, List.foldl_append, foldl_rankStep_replicate_snd]
    rw [show (List.foldl (rankStep A) (A.q0, 0) pre).1 = q₁ from rankStep_fst A A.q0 0 pre]
  obtain ⟨m, p, P, hp, haff⟩ :=
    SliceAutomata.affineOnResidues_of_blockIterate (blockStep A loop) q₁ (blockWeight A loop)
  refine ⟨m, p, P, hp, fun k r => ?_⟩
  rw [hrank, hrank, haff k r]
  abel

end SliceRank
