/-
# `ℤ^d`-valued affine-on-residues (recurrence form) for the WRP rank

For the `fas` rank-sort we need the rank of a slice atom — a `ℤ^d` vector — to be
affine on residue classes of its loop-index `j`.  This file fixes the recurrence
form `F(j+p) = F(j) + P` (for `j ≥ m`) used by `SliceOrder.lexLt_eventuallyPeriodic`,
and proves it closed under the operations `RankTerm.eval` is built from: constants,
`ℤ`-scaling, addition, and eventual periodicity (the bounded `β` corrections).

All axiom-clean.
-/
import RequestProject.SliceRankAtom

open Step

namespace SliceRankAtom

/-- A `ℤ^d`-valued sequence is **affine on residues** when, beyond a threshold, one
period adds a fixed vector: `F(j+p) = F(j) + P`. -/
def RankAffine {d : ℕ} (F : ℕ → Fin d → ℤ) : Prop :=
  ∃ (m p : ℕ) (P : Fin d → ℤ), 1 ≤ p ∧ ∀ j, m ≤ j → F (j + p) = F j + P

/-- Iterating the period: `F(j + p·k) = F(j) + k·P`. -/
theorem RankAffine.iterate {d : ℕ} {F : ℕ → Fin d → ℤ} {m p : ℕ} {P : Fin d → ℤ}
    (h : ∀ j, m ≤ j → F (j + p) = F j + P) : ∀ j k, m ≤ j → F (j + p * k) = F j + k • P := by
  intro j k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hj
      rw [Nat.mul_succ, ← Nat.add_assoc, h _ (by omega), ih hj, succ_nsmul]
      abel

theorem RankAffine.const {d : ℕ} (v : Fin d → ℤ) : RankAffine (fun _ => v) :=
  ⟨0, 1, 0, le_refl 1, fun _ _ => by simp⟩

theorem RankAffine.add {d : ℕ} {F G : ℕ → Fin d → ℤ} (hF : RankAffine F) (hG : RankAffine G) :
    RankAffine (fun j => F j + G j) := by
  obtain ⟨mF, pF, PF, hpF, hF⟩ := hF
  obtain ⟨mG, pG, PG, hpG, hG⟩ := hG
  refine ⟨max mF mG, pF * pG, pG • PF + pF • PG, Nat.one_le_iff_ne_zero.mpr (by positivity),
    fun j hj => ?_⟩
  have eF : F (j + pF * pG) = F j + pG • PF := RankAffine.iterate hF j pG (by omega)
  have eG : G (j + pF * pG) = G j + pF • PG := by
    have := RankAffine.iterate hG j pF (by omega); rwa [Nat.mul_comm pG pF] at this
  show F (j + pF * pG) + G (j + pF * pG) = (F j + G j) + (pG • PF + pF • PG)
  rw [eF, eG]; abel

theorem RankAffine.smul {d : ℕ} (c : ℤ) {F : ℕ → Fin d → ℤ} (hF : RankAffine F) :
    RankAffine (fun j => c • F j) := by
  obtain ⟨m, p, P, hp, hF⟩ := hF
  exact ⟨m, p, c • P, hp, fun j hj => by show c • F (j + p) = c • F j + c • P; rw [hF j hj, smul_add]⟩

theorem RankAffine.of_eventuallyPeriodic {d : ℕ} {F : ℕ → Fin d → ℤ} {m p : ℕ} (hp : 1 ≤ p)
    (h : ∀ j, m ≤ j → F (j + p) = F j) : RankAffine F :=
  ⟨m, p, 0, hp, fun j hj => by rw [h j hj]; simp⟩

theorem RankAffine.congr {d : ℕ} {F G : ℕ → Fin d → ℤ} (h : ∀ j, F j = G j)
    (hF : RankAffine F) : RankAffine G := by
  obtain ⟨m, p, P, hp, hF⟩ := hF
  exact ⟨m, p, P, hp, fun j hj => by rw [← h, ← h]; exact hF j hj⟩

/-- The `pre_blocks` shape `S(m+p·k+r) = S(m+r) + k·P` implies the recurrence form. -/
theorem rankAffine_of_pre_blocks {d : ℕ} {S : ℕ → Fin d → ℤ} {m p : ℕ} {P : Fin d → ℤ}
    (hp : 1 ≤ p) (h : ∀ k r, S (m + p * k + r) = S (m + r) + k • P) : RankAffine S := by
  refine ⟨m, p, P, hp, fun j hj => ?_⟩
  obtain ⟨k, r, -, hjeq⟩ : ∃ k r, r < p ∧ j = m + p * k + r := by
    refine ⟨(j - m) / p, (j - m) % p, Nat.mod_lt _ hp, ?_⟩
    have := Nat.div_add_mod (j - m) p; omega
  have e1 : S j = S (m + r) + k • P := by rw [hjeq]; exact h k r
  have e2 : S (j + p) = S (m + r) + (k + 1) • P := by
    rw [show j + p = m + p * (k + 1) + r from by rw [Nat.mul_succ]; omega]; exact h (k + 1) r
  rw [e1, e2, succ_nsmul]; abel

/-- Finite sums of `RankAffine` sequences are `RankAffine`. -/
theorem RankAffine.listSum {d : ℕ} {ι : Type*} (l : List ι) (F : ι → ℕ → Fin d → ℤ) :
    (∀ i ∈ l, RankAffine (F i)) → RankAffine (fun j => (l.map (fun i => F i j)).sum) := by
  induction l with
  | nil => intro _; simpa using RankAffine.const (0 : Fin d → ℤ)
  | cons a l ih =>
      intro h
      have ha := h a (List.mem_cons.mpr (Or.inl rfl))
      have ih' := ih (fun i hi => h i (List.mem_cons.mpr (Or.inr hi)))
      exact RankAffine.congr (fun j => by simp [List.sum_cons]) (ha.add ih')

/-- A bounded function of a finite-state iterate is `RankAffine` (eventually
periodic) — this is the shape of the bounded `β` corrections. -/
theorem rankAffine_of_iterate {d : ℕ} {Q : Type*} [Finite Q] (f : Q → Q) (q0 : Q)
    (g : Q → (Fin d → ℤ)) : RankAffine (fun j => g (f^[j] q0)) := by
  obtain ⟨m, p, hp, hper⟩ := SliceAutomata.iterate_eventuallyPeriodic f q0
  exact RankAffine.of_eventuallyPeriodic hp (fun j hj => by rw [hper j hj])

/-- **A slice block-atom's rank-source prefix-rank is `RankAffine` in its
loop-index.**  (Paper `lem:one-loop-rank-affine` for the one-loop family, in recurrence form.) -/
theorem prefixRank_blockU_rankAffine {d : ℕ} (A : RankSource Step d) :
    RankAffine (fun j => A.prefixRank ([U] ++ (List.replicate j [U, D]).flatten)
      (([U] ++ (List.replicate j [U, D]).flatten).length)) := by
  obtain ⟨m, p, P, hp, haff⟩ := SliceRank.prefixRank_pre_blocks_affineOnResidues A [U] [U, D]
  exact rankAffine_of_pre_blocks hp haff

end SliceRankAtom
