/-
# Period-star layer (§9 tower, Stage C): function-level eventual periodicity

The pinned-period discipline of the fibred route.
The one-parameter tower extracts its periods POINTWISE — at a start state that
moves with the prefix (`detAuto_slice_eventuallyPeriodic` runs from
`foldl δ q0 pre`).  On the copied slice the prefix is `U^{m}`, so pointwise
extraction would make periods `m`-dependent and silently destroy the
load-bearing quantifier order of `RowAffine`.  The fix: extract eventual
periodicity at the FUNCTION level (`Q → Q` is finite), where it is uniform in
the start state, hence in `pre`/`suf`, hence in the slice parameter.

* `detAuto_loop_func_EP` — the loop-fold iterates are eventually periodic AS
  FUNCTIONS;
* `detAuto_slice_EP_uniform` / `mso_slice_EP_uniform` — acceptance on
  `pre ++ loop^n ++ suf` is eventually periodic in `n` with threshold and
  period UNIFORM in `pre` and `suf`;
* `affineOnResidues_of_blockIterate_func` — the rank twin: threshold and
  period hoisted BEFORE the start state (slopes may depend on it);
* `AffineOnResiduesAt` — affineness at a PINNED period, with the
  divisor-to-multiple transfer.
-/
import RequestProject.SliceMarkN

open SliceMSO

namespace SlicePeriodStar

/-- The loop-fold map of an acceptor. -/
def loopFold {Alpha : Type*} (M : DetAuto Alpha) (loop : List Alpha) :
    M.Q → M.Q := fun q => loop.foldl M.δ q

/-- **Function-level loop periodicity**: uniform in the start state. -/
theorem detAuto_loop_func_EP {Alpha : Type*} (M : DetAuto Alpha)
    (loop : List Alpha) :
    ∃ mv pv : ℕ, 1 ≤ pv ∧ ∀ g, mv ≤ g →
      (loopFold M loop)^[g + pv] = (loopFold M loop)^[g] := by
  have := M.fintypeQ
  obtain ⟨mv, pv, hpv, hper⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic
      (fun g : M.Q → M.Q => loopFold M loop ∘ g) id
  have key : ∀ k, (fun g : M.Q → M.Q => loopFold M loop ∘ g)^[k] id
      = (loopFold M loop)^[k] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, ← Function.iterate_succ']
  exact ⟨mv, pv, hpv, fun g hg => by rw [← key, ← key]; exact hper g hg⟩

/-- **Uniform slice periodicity**: threshold and period independent of the
prefix and suffix. -/
theorem detAuto_slice_EP_uniform {Alpha : Type*} (M : DetAuto Alpha)
    (loop : List Alpha) :
    ∃ mv pv : ℕ, 1 ≤ pv ∧ ∀ (pre suf : List Alpha) (n : ℕ), mv ≤ n →
      (M.accepts (pre ++ (List.replicate (n + pv) loop).flatten ++ suf) ↔
       M.accepts (pre ++ (List.replicate n loop).flatten ++ suf)) := by
  obtain ⟨mv, pv, hpv, hper⟩ := detAuto_loop_func_EP M loop
  refine ⟨mv, pv, hpv, fun pre suf n hn => ?_⟩
  simp only [DetAuto.accepts, List.foldl_append, foldl_replicate_flatten]
  rw [show (fun q => List.foldl M.δ q loop)^[n + pv]
      = (fun q => List.foldl M.δ q loop)^[n] from hper n hn]

/-- **Uniform MSO slice periodicity**: one Büchi call, then prefix/suffix
uniformity for free. -/
theorem mso_slice_EP_uniform {Alpha : Type*} [Fintype Alpha]
    (φ : MSO.Sentence Alpha) (loop : List Alpha) :
    ∃ mv pv : ℕ, 1 ≤ pv ∧ ∀ (pre suf : List Alpha) (n : ℕ), mv ≤ n →
      (φ.Sat (pre ++ (List.replicate (n + pv) loop).flatten ++ suf)
          Fin.elim0 Fin.elim0 ↔
       φ.Sat (pre ++ (List.replicate n loop).flatten ++ suf)
          Fin.elim0 Fin.elim0) := by
  obtain ⟨M, hM⟩ := SliceMSO.buchi φ
  obtain ⟨mv, pv, hpv, hper⟩ := detAuto_slice_EP_uniform M loop
  exact ⟨mv, pv, hpv, fun pre suf n hn => by
    rw [← hM, ← hM]; exact hper pre suf n hn⟩

/-- **The rank twin**: threshold and period hoisted BEFORE the start state. -/
theorem affineOnResidues_of_blockIterate_func {Q : Type*} [Finite Q]
    {M : Type*} [AddCommMonoid M] (blockStep : Q → Q) (w : Q → M) :
    ∃ (m p : ℕ), 1 ≤ p ∧ ∀ q₀ : Q, ∃ P : M,
      ∀ k r : ℕ, (∑ i ∈ Finset.range (m + p * k + r), w (blockStep^[i] q₀)) =
        (∑ i ∈ Finset.range (m + r), w (blockStep^[i] q₀)) + k • P := by
  obtain ⟨m, p, hp, hper⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic
      (fun g : Q → Q => blockStep ∘ g) id
  have key : ∀ k, (fun g : Q → Q => blockStep ∘ g)^[k] id = blockStep^[k] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, ← Function.iterate_succ']
  refine ⟨m, p, hp, fun q₀ => ?_⟩
  set g : ℕ → M := fun i => w (blockStep^[i] q₀) with hg
  have hgper : ∀ i, m ≤ i → g (i + p) = g i := by
    intro i hi
    show w (blockStep^[i + p] q₀) = w (blockStep^[i] q₀)
    have hfun : blockStep^[i + p] = blockStep^[i] := by
      rw [← key, ← key]
      exact hper i hi
    rw [hfun]
  exact ⟨∑ i ∈ Finset.Ico m (m + p), g i,
    SliceAutomata.recurrence_affineOnResidues
      (fun n => ∑ i ∈ Finset.range n, g i) m p _
      (SliceAutomata.partialSum_recurrence' g m p hgper)⟩

/-- **Affineness at a pinned period** — the discipline that keeps the period
existential OUTSIDE the slice-parameter quantifier. -/
def AffineOnResiduesAt (p : ℕ) (f : ℕ → ℕ) : Prop :=
  ∃ m, ∀ j, j < p → ∃ b s : ℕ, ∀ k, f (m + j + p * k) = b + k * s

/-- Pinned affineness transfers to any multiple of the period. -/
theorem AffineOnResiduesAt.of_dvd {p p' : ℕ} {f : ℕ → ℕ} (hp : 1 ≤ p)
    (hdvd : p ∣ p') (hp' : 1 ≤ p') (h : AffineOnResiduesAt p f) :
    AffineOnResiduesAt p' f := by
  obtain ⟨d, rfl⟩ := hdvd
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun j' hj' => ?_⟩
  obtain ⟨b, s, hbs⟩ := hm (j' % p) (Nat.mod_lt _ (by omega))
  refine ⟨b + (j' / p) * s, d * s, fun k => ?_⟩
  have harg : m + j' + p * d * k = m + j' % p + p * (j' / p + d * k) := by
    have hdm := Nat.div_add_mod j' p
    have hexp : p * (j' / p + d * k) = p * (j' / p) + p * (d * k) := by ring
    have hexp2 : p * d * k = p * (d * k) := by ring
    omega
  rw [harg, hbs (j' / p + d * k)]
  ring

end SlicePeriodStar
