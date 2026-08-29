/-
# Vector lex-min selector: `AffineOnResiduesZ` is closed under EP-gated selection

The `d*`-rank threshold is the coordinatewise lexicographic minimum of finitely many
`RankAffine`/`AffineOnResiduesZ` rank-vector families.  The combinatorial core
("the lex-min is `AffineOnResiduesZ` per coordinate") rests on a single new closure
property:

> **EP-gated selector.**  If `Pr` is eventually periodic with period `p` and `A, B`
> are `AffineOnResiduesZ`, then `n ↦ if Pr n then A n else B n` is `AffineOnResiduesZ`.

This is the inductive STEP of the finite lex-min fold: an eventually-periodic argmin
tournament (each pairwise `lexLt` comparison is `EventuallyPeriodic` by
`SliceOrder.lexLt_eventuallyPeriodic`, per residue) selects, on each residue class of
`n`, a FIXED winning family; that selection is exactly an EP-gated ite.

Supporting lemmas (round-trip between the residue form and a single-step recurrence):
* `AffineOnResiduesZ.toStep` / `affineOnResiduesZ_of_step` — residue-keyed single-step
  recurrence ⇄ `AffineOnResiduesZ`;
* `affineOnResiduesZ_of_step_gen` — `n`-keyed `P`-periodic single-step recurrence form;
* `affineOnResiduesZ_ite_of_EP` — the EP-gated selector (the new closure property);
* `lexMin2_coord_affineOnResiduesZ` — the two-element vector lex-min coordinate (the
  fold step), taking the comparison's eventual-periodicity as the hypothesis the
  per-residue `lexLt_eventuallyPeriodic` application supplies.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
import RequestProject.SliceBoundaryMinCore
import RequestProject.SliceOrder

namespace SliceVectorLexMin

open SliceThreshold SliceOrder

/-- **Single-step additive form of `AffineOnResiduesZ`.** -/
theorem AffineOnResiduesZ.toStep {F : ℕ → ℤ} (hF : AffineOnResiduesZ F) :
    ∃ (m p : ℕ) (σ : ℕ → ℤ), 1 ≤ p ∧ ∀ n, m ≤ n → F (n + p) = F n + σ ((n - m) % p) := by
  obtain ⟨m, p, s, hp, hrec⟩ := hF
  refine ⟨m, p, s, hp, fun n hn => ?_⟩
  set r := (n - m) % p with hr
  set k := (n - m) / p with hk
  have hrp : r < p := Nat.mod_lt _ hp
  have hdm := Nat.div_add_mod (n - m) p
  have hnform : n = m + r + p * k := by rw [hr, hk]; omega
  have h1 : F (n + p) = F (m + r) + ((k : ℤ) + 1) * s r := by
    rw [show n + p = m + r + p * (k + 1) from by rw [hnform]; ring, hrec r (k + 1)]
    push_cast; ring
  have h2 : F n = F (m + r) + (k : ℤ) * s r := by rw [hnform, hrec r k]
  rw [h1, h2]; ring

/-- **`AffineOnResiduesZ` from a residue-keyed single-step recurrence.** -/
theorem affineOnResiduesZ_of_step {F : ℕ → ℤ} {m p : ℕ} (σ : ℕ → ℤ) (hp : 1 ≤ p)
    (h : ∀ n, m ≤ n → F (n + p) = F n + σ ((n - m) % p)) : AffineOnResiduesZ F := by
  refine ⟨m, p, fun r => σ (r % p), hp, fun r k => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : F (m + r + p * k + p) = F (m + r + p * k) + σ ((m + r + p * k - m) % p) :=
        h (m + r + p * k) (by omega)
      have hmod : (m + r + p * k - m) % p = r % p := by
        rw [show m + r + p * k - m = r + p * k from by omega, Nat.add_mul_mod_self_left]
      rw [hmod] at hstep
      rw [show m + r + p * (k + 1) = m + r + p * k + p from by ring, hstep, ih]
      push_cast; ring

/-- **`AffineOnResiduesZ` from an `n`-keyed `P`-periodic single-step recurrence.**  If
`F (n + P) = F n + σ n` for `n ≥ m`, and the step `σ` is `P`-periodic beyond `m`
(`σ (n + P) = σ n`), then `F` is `AffineOnResiduesZ`.  (Reduces to the residue-keyed
form by `τ a := σ (m + a)`, valid because `σ` is `P`-periodic.) -/
theorem affineOnResiduesZ_of_step_gen {F : ℕ → ℤ} {m P : ℕ} (σ : ℕ → ℤ) (hP : 1 ≤ P)
    (hper : ∀ n, m ≤ n → σ (n + P) = σ n)
    (h : ∀ n, m ≤ n → F (n + P) = F n + σ n) : AffineOnResiduesZ F := by
  -- σ is determined by its residue: σ n = σ (m + (n - m) % P) for n ≥ m.
  have hσres : ∀ n, m ≤ n → σ n = σ (m + (n - m) % P) := by
    intro n hn
    -- n = m + (n-m)%P + P * ((n-m)/P); iterate hper backwards
    set a := (n - m) % P with ha
    set k := (n - m) / P with hk
    have hnform : n = m + a + P * k := by
      have := Nat.div_add_mod (n - m) P; rw [ha, hk]; omega
    -- prove σ (m + a + P*k) = σ (m + a) by induction on k
    have key : ∀ k, σ (m + a + P * k) = σ (m + a) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [show m + a + P * (k + 1) = (m + a + P * k) + P from by ring,
            hper (m + a + P * k) (by omega), ih]
    rw [hnform, key k]
  refine affineOnResiduesZ_of_step (m := m) (p := P) (fun a => σ (m + a)) hP (fun n hn => ?_)
  rw [h n hn, hσres n hn]

/-- **The EP-gated selector is `AffineOnResiduesZ`.**  If `Pr` is eventually periodic
with period `p` and `A`, `B` are `AffineOnResiduesZ`, then `n ↦ if Pr n then A n else
B n` is `AffineOnResiduesZ`.  This is the finite-family argmin SELECTOR lifting the
scalar boundary-min to the vector lex-min: an eventually-periodic tournament of
`lexLt` comparisons picks, per residue class of `n`, a FIXED winning family — exactly
an EP-gated ite.

Mechanism: convert `A`, `B` to single-step form (`toStep`), telescope each to the
COMMON period `P = p · pA · pB` (the rebased step is the `q`-fold sum, manifestly
`P`-periodic in `n`); beyond `M`, `Pr` is constant on each residue class mod `P`
(since `P` is a multiple of `p`), so the ite agrees with a single fixed branch along
each class and satisfies an `n`-keyed `P`-periodic single-step recurrence; close via
`affineOnResiduesZ_of_step_gen`. -/
theorem affineOnResiduesZ_ite_of_EP {Pr : ℕ → Prop} [DecidablePred Pr] {p : ℕ}
    (hp : 1 ≤ p) (hEP : EventuallyPeriodic Pr p)
    {A B : ℕ → ℤ} (hA : AffineOnResiduesZ A) (hB : AffineOnResiduesZ B) :
    AffineOnResiduesZ (fun n => if Pr n then A n else B n) := by
  classical
  obtain ⟨mA, pA, σA, hpA, hAstep⟩ := AffineOnResiduesZ.toStep hA
  obtain ⟨mB, pB, σB, hpB, hBstep⟩ := AffineOnResiduesZ.toStep hB
  obtain ⟨mP, hmP⟩ := hEP
  set M : ℕ := max (max mA mB) mP with hMdef
  set P : ℕ := p * (pA * pB) with hPdef
  have hP1 : 1 ≤ P := by
    have hpos : 0 < p * (pA * pB) := by positivity
    omega
  -- A telescoped to period P: F(n+P) = F n + (Σ_{i<P/pA} σA ((n+pA*i-mA)%pA))
  have hPdvdA : pA ∣ P := by rw [hPdef]; exact Dvd.dvd.mul_left (dvd_mul_right pA pB) p
  have hPdvdB : pB ∣ P := by rw [hPdef]; exact Dvd.dvd.mul_left (dvd_mul_left pB pA) p
  obtain ⟨qA, hqA⟩ := hPdvdA
  obtain ⟨qB, hqB⟩ := hPdvdB
  -- the n-keyed rebased steps
  set τA : ℕ → ℤ := fun n => (Finset.range qA).sum (fun i => σA ((n + pA * i - mA) % pA)) with hτA
  set τB : ℕ → ℤ := fun n => (Finset.range qB).sum (fun i => σB ((n + pB * i - mB) % pB)) with hτB
  -- telescoping (n-keyed) for A and B
  have telescope :
      ∀ (G : ℕ → ℤ) (mG pG : ℕ) (σG : ℕ → ℤ),
        (∀ n, mG ≤ n → G (n + pG) = G n + σG ((n - mG) % pG)) →
        ∀ (q : ℕ) n, mG ≤ n →
          G (n + pG * q) = G n + (Finset.range q).sum (fun i => σG ((n + pG * i - mG) % pG)) := by
    intro G mG pG σG hG q
    induction q with
    | zero => intro n _; simp
    | succ q ih =>
        intro n hn
        have hstep : G (n + pG * q + pG) = G (n + pG * q) + σG ((n + pG * q - mG) % pG) :=
          hG (n + pG * q) (by omega)
        rw [show n + pG * (q + 1) = n + pG * q + pG from by ring, hstep, ih n hn,
          Finset.sum_range_succ]
        ring
  have hA' : ∀ n, M ≤ n → A (n + P) = A n + τA n := by
    intro n hn
    have := telescope A mA pA σA hAstep qA n (by omega)
    rw [hqA]; exact this
  have hB' : ∀ n, M ≤ n → B (n + P) = B n + τB n := by
    intro n hn
    have := telescope B mB pB σB hBstep qB n (by omega)
    rw [hqB]; exact this
  -- τA, τB are P-periodic in n (each summand `(n + pA*i - mA) % pA` is pA-periodic, pA ∣ P)
  have hmAM : mA ≤ M := le_trans (le_trans (le_max_left mA mB) (le_max_left _ mP)) (le_refl M)
  have hmBM : mB ≤ M := le_trans (le_trans (le_max_right mA mB) (le_max_left _ mP)) (le_refl M)
  have hτAper : ∀ n, M ≤ n → τA (n + P) = τA n := by
    intro n hn
    rw [hτA]; apply Finset.sum_congr rfl; intro i _
    congr 1
    have heq : n + P + pA * i - mA = (n + pA * i - mA) + qA * pA := by
      have hmn : mA ≤ n := le_trans hmAM hn
      have : P = qA * pA := by rw [hqA]; ring
      rw [this]; omega
    rw [heq, Nat.add_mul_mod_self_right]
  have hτBper : ∀ n, M ≤ n → τB (n + P) = τB n := by
    intro n hn
    rw [hτB]; apply Finset.sum_congr rfl; intro i _
    congr 1
    have heq : n + P + pB * i - mB = (n + pB * i - mB) + qB * pB := by
      have hmn : mB ≤ n := le_trans hmBM hn
      have : P = qB * pB := by rw [hqB]; ring
      rw [this]; omega
    rw [heq, Nat.add_mul_mod_self_right]
  -- EP-constancy mod P
  have hPriter : ∀ t n, mP ≤ n → (Pr (n + p * t) ↔ Pr n) := by
    intro t
    induction t with
    | zero => intro n _; simp
    | succ t iht =>
        intro n hn
        have hstep : Pr (n + p * t + p) ↔ Pr (n + p * t) := hmP (n + p * t) (by omega)
        rw [show n + p * (t + 1) = n + p * t + p from by ring, hstep]
        exact iht n hn
  have hPrconst : ∀ n, M ≤ n → (Pr (n + P) ↔ Pr n) := by
    intro n hn; rw [hPdef]; exact hPriter (pA * pB) n (by omega)
  -- close via the n-keyed general step lemma
  refine affineOnResiduesZ_of_step_gen
    (m := M) (P := P) (σ := fun n => if Pr n then τA n else τB n) hP1 (fun n hn => ?_) (fun n hn => ?_)
  · -- step is P-periodic: branches and predicate both P-periodic beyond M
    by_cases hPr : Pr n
    · have hPrP : Pr (n + P) := (hPrconst n hn).mpr hPr
      simp only [if_pos hPr, if_pos hPrP]; exact hτAper n hn
    · have hPrP : ¬ Pr (n + P) := fun h => hPr ((hPrconst n hn).mp h)
      simp only [if_neg hPr, if_neg hPrP]; exact hτBper n hn
  · -- the recurrence
    by_cases hPr : Pr n
    · have hPrP : Pr (n + P) := (hPrconst n hn).mpr hPr
      simp only [if_pos hPr, if_pos hPrP]; exact hA' n hn
    · have hPrP : ¬ Pr (n + P) := fun h => hPr ((hPrconst n hn).mp h)
      simp only [if_neg hPr, if_neg hPrP]; exact hB' n hn

/-! ## Capstone: the two-element vector lexLt-min has `AffineOnResiduesZ` coordinates

Given two vector families `U, V : ℕ → Fin d → ℤ` whose every coordinate is
`AffineOnResiduesZ`, and the (eventually-periodic) comparison predicate
`fun n => WRP.lexLt (U n) (V n)`, the per-coordinate LEX-MIN
`fun n => if lexLt (U n) (V n) then U n i else V n i` is `AffineOnResiduesZ`.
This is the inductive STEP of the finite lex-min fold the `d*`-rank needs: folding it
over the finite family of (copy,region,residue) boundary vectors (each comparison EP
by `SliceOrder.lexLt_eventuallyPeriodic`, per residue) yields each coordinate of
`d*`-rank as `AffineOnResiduesZ`.

We take the comparison's eventual-periodicity as a hypothesis (it is exactly what the
per-residue `lexLt_eventuallyPeriodic` application supplies in the assembly). -/
open Classical in
theorem lexMin2_coord_affineOnResiduesZ {d : ℕ} (U V : ℕ → Fin d → ℤ) {p : ℕ}
    (hp : 1 ≤ p)
    (hEP : EventuallyPeriodic (fun n => WRP.lexLt (U n) (V n)) p)
    (hU : ∀ i : Fin d, AffineOnResiduesZ (fun n => U n i))
    (hV : ∀ i : Fin d, AffineOnResiduesZ (fun n => V n i))
    (i : Fin d) :
    AffineOnResiduesZ
      (fun n => if WRP.lexLt (U n) (V n) then U n i else V n i) :=
  affineOnResiduesZ_ite_of_EP hp hEP (hU i) (hV i)

end SliceVectorLexMin
