/-
# Order stabilisation: comparisons of affine-on-residues integer sequences are
  eventually periodic

This is the order-theoretic core behind the *rank-sort* half of the slice analysis
(paper §7): the mechanism by which "the WRP rank order is eventually periodic in
`n`" feeds the Presburger-definability of the `≺`-comparisons on the one-loop
slice.  Concretely, if `S : ℕ → ℤ` satisfies the period-`p` recurrence
`S(n+p) = S(n) + P` for all `n ≥ m₀` — the form produced by
`SliceAutomata.recurrence_affineOnResidues` and `SliceRank.prefixRank_*` for actual
rank sources — then the sign predicate `0 ≤ S n` is **eventually periodic** with
period `p`.

Closure of eventual periodicity under Boolean combinations and finite quantifiers
then lifts this to the lexicographic comparison `WRP.lexLt (F n) (G n)` of two
coordinatewise-affine `ℤ^d` vectors — exactly the comparison the rank-then-`χ`
order performs when deciding which selected atom precedes another on the slice.
This is the new lemma the rank-sorted-output modelling needs (the "`lexLt` of
affine-on-residues vectors is eventually periodic" fact).

Everything here is proved from Mathlib + `SliceAutomata` only — no new axioms.
-/
import RequestProject.SliceAutomata
import RequestProject.WRP

namespace SliceOrder

open SliceAutomata

/-- A predicate on `ℕ` is *eventually periodic* with period `p` if, beyond some
threshold, shifting the argument by `p` preserves its truth value. -/
def EventuallyPeriodic (Pr : ℕ → Prop) (p : ℕ) : Prop :=
  ∃ m, ∀ n, m ≤ n → (Pr (n + p) ↔ Pr n)

namespace EventuallyPeriodic

/-- Eventual periodicity transports along a pointwise logical equivalence. -/
theorem congr {Pr Qr : ℕ → Prop} {p : ℕ} (h : ∀ n, Pr n ↔ Qr n)
    (hP : EventuallyPeriodic Pr p) : EventuallyPeriodic Qr p := by
  obtain ⟨m, hm⟩ := hP
  exact ⟨m, fun n hn => by rw [← h, ← h]; exact hm n hn⟩

theorem and {Pr Qr : ℕ → Prop} {p : ℕ} (hP : EventuallyPeriodic Pr p)
    (hQ : EventuallyPeriodic Qr p) : EventuallyPeriodic (fun n => Pr n ∧ Qr n) p := by
  obtain ⟨a, ha⟩ := hP; obtain ⟨b, hb⟩ := hQ
  exact ⟨max a b, fun n hn =>
    and_congr (ha n (le_trans (le_max_left a b) hn)) (hb n (le_trans (le_max_right a b) hn))⟩

theorem or {Pr Qr : ℕ → Prop} {p : ℕ} (hP : EventuallyPeriodic Pr p)
    (hQ : EventuallyPeriodic Qr p) : EventuallyPeriodic (fun n => Pr n ∨ Qr n) p := by
  obtain ⟨a, ha⟩ := hP; obtain ⟨b, hb⟩ := hQ
  exact ⟨max a b, fun n hn =>
    or_congr (ha n (le_trans (le_max_left a b) hn)) (hb n (le_trans (le_max_right a b) hn))⟩

/-- An eventually-true predicate is eventually periodic (with any period). -/
theorem of_eventually_true {Pr : ℕ → Prop} {p : ℕ} (h : ∃ m, ∀ n, m ≤ n → Pr n) :
    EventuallyPeriodic Pr p := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, fun n hn => iff_of_true (hm (n + p) (by omega)) (hm n hn)⟩

/-- An eventually-false predicate is eventually periodic (with any period). -/
theorem of_eventually_false {Pr : ℕ → Prop} {p : ℕ} (h : ∃ m, ∀ n, m ≤ n → ¬ Pr n) :
    EventuallyPeriodic Pr p := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, fun n hn => iff_of_false (hm (n + p) (by omega)) (hm n hn)⟩

/-- A finite disjunction of eventually-periodic predicates (common period) is
eventually periodic. -/
theorem finset_or {ι : Type*} (s : Finset ι) (Pr : ι → ℕ → Prop) (p : ℕ)
    (h : ∀ i ∈ s, EventuallyPeriodic (Pr i) p) :
    EventuallyPeriodic (fun n => ∃ i ∈ s, Pr i n) p := by
  classical
  induction s using Finset.induction with
  | empty => exact of_eventually_false ⟨0, fun n _ => by simp⟩
  | insert a s ha ih =>
      have ha' : EventuallyPeriodic (Pr a) p := h a (Finset.mem_insert_self a s)
      have ih' : EventuallyPeriodic (fun n => ∃ i ∈ s, Pr i n) p :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      refine (ha'.or ih').congr (fun n => ?_)
      constructor
      · rintro (hpa | ⟨i, hi, hpi⟩)
        · exact ⟨a, Finset.mem_insert_self _ _, hpa⟩
        · exact ⟨i, Finset.mem_insert_of_mem hi, hpi⟩
      · rintro ⟨i, hi, hpi⟩
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact Or.inl hpi
        · exact Or.inr ⟨i, hi', hpi⟩

/-- A finite conjunction of eventually-periodic predicates (common period) is
eventually periodic. -/
theorem finset_and {ι : Type*} (s : Finset ι) (Pr : ι → ℕ → Prop) (p : ℕ)
    (h : ∀ i ∈ s, EventuallyPeriodic (Pr i) p) :
    EventuallyPeriodic (fun n => ∀ i ∈ s, Pr i n) p := by
  classical
  induction s using Finset.induction with
  | empty => exact of_eventually_true ⟨0, fun n _ => by simp⟩
  | insert a s ha ih =>
      have ha' : EventuallyPeriodic (Pr a) p := h a (Finset.mem_insert_self a s)
      have ih' : EventuallyPeriodic (fun n => ∀ i ∈ s, Pr i n) p :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      refine (ha'.and ih').congr (fun n => ?_)
      constructor
      · rintro ⟨hpa, hps⟩ i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact hpa
        · exact hps i hi'
      · intro hall
        exact ⟨hall a (Finset.mem_insert_self _ _),
          fun i hi => hall i (Finset.mem_insert_of_mem hi)⟩

end EventuallyPeriodic

/-- If `S(n+p) = S(n) + P` beyond `m₀` and `P > 0`, then `S` is eventually `≥ 0`:
the genuine threshold computation (one period adds `P ≥ 1`, so after `≥ |S(m₀+r)|`
periods the value is non-negative on every residue class `r`). -/
theorem affineOnResidues_eventually_nonneg (S : ℕ → ℤ) (m₀ p : ℕ) (hp : 1 ≤ p) (P : ℤ)
    (hP : 0 < P) (hrec : ∀ n, m₀ ≤ n → S (n + p) = S n + P) :
    ∃ m', ∀ n, m' ≤ n → 0 ≤ S n := by
  classical
  set K : ℕ := (Finset.range p).sup (fun r => (- S (m₀ + r)).toNat) with hKdef
  refine ⟨m₀ + p * K + p, fun n hn => ?_⟩
  obtain ⟨k, r, hrp, hnr⟩ : ∃ k r, r < p ∧ n = m₀ + p * k + r := by
    refine ⟨(n - m₀) / p, (n - m₀) % p, Nat.mod_lt _ hp, ?_⟩
    have := Nat.div_add_mod (n - m₀) p
    omega
  have hKk : K < k := by
    have h1 : p * K < p * k := by omega
    exact Nat.lt_of_mul_lt_mul_left h1
  have heq := recurrence_affineOnResidues S m₀ p P hrec k r
  rw [hnr, heq, nsmul_eq_mul]
  have hb : (- S (m₀ + r)).toNat ≤ K := by
    rw [hKdef]
    exact Finset.le_sup (f := fun r => (- S (m₀ + r)).toNat) (Finset.mem_range.mpr hrp)
  have hbk : - S (m₀ + r) ≤ (k : ℤ) := Int.toNat_le.mp (le_trans hb (le_of_lt hKk))
  have hP1 : (1 : ℤ) ≤ P := by omega
  nlinarith [mul_le_mul_of_nonneg_left hP1 (Int.natCast_nonneg k), hbk]

/-- **The sign of an affine-on-residues `ℤ`-sequence is eventually periodic.**  If
`S(n+p) = S(n) + P` beyond `m₀`, the truth value of `0 ≤ S n` is periodic in `n`
with period `p` beyond some threshold (constant `true` if `P > 0`, constant `false`
if `P < 0`, literally periodic if `P = 0`). -/
theorem eventuallyPeriodic_nonneg (S : ℕ → ℤ) (m₀ p : ℕ) (hp : 1 ≤ p) (P : ℤ)
    (hrec : ∀ n, m₀ ≤ n → S (n + p) = S n + P) :
    EventuallyPeriodic (fun n => 0 ≤ S n) p := by
  rcases lt_trichotomy P 0 with hneg | hzero | hpos
  · -- `P < 0`: eventually `S n < 0`, so the predicate is eventually false.
    apply EventuallyPeriodic.of_eventually_false
    obtain ⟨m', hm'⟩ := affineOnResidues_eventually_nonneg (fun n => -1 - S n) m₀ p hp (-P)
      (by linarith) (fun n hn => by rw [hrec n hn]; ring)
    exact ⟨m', fun n hn => by intro h; have := hm' n hn; linarith⟩
  · -- `P = 0`: literally periodic.
    subst hzero
    exact ⟨m₀, fun n hn => by show 0 ≤ S (n + p) ↔ 0 ≤ S n; rw [hrec n hn]; simp⟩
  · -- `P > 0`: eventually `0 ≤ S n`, so the predicate is eventually true.
    apply EventuallyPeriodic.of_eventually_true
    exact affineOnResidues_eventually_nonneg S m₀ p hp P hpos hrec

/-- The strict positivity predicate `0 < S n` is eventually periodic. -/
theorem eventuallyPeriodic_pos (S : ℕ → ℤ) (m₀ p : ℕ) (hp : 1 ≤ p) (P : ℤ)
    (hrec : ∀ n, m₀ ≤ n → S (n + p) = S n + P) :
    EventuallyPeriodic (fun n => 0 < S n) p := by
  have h := eventuallyPeriodic_nonneg (fun n => S n - 1) m₀ p hp P
    (fun n hn => by rw [hrec n hn]; ring)
  exact h.congr (fun n => by omega)

/-- The equality predicate `S n = 0` is eventually periodic. -/
theorem eventuallyPeriodic_eqZero (S : ℕ → ℤ) (m₀ p : ℕ) (hp : 1 ≤ p) (P : ℤ)
    (hrec : ∀ n, m₀ ≤ n → S (n + p) = S n + P) :
    EventuallyPeriodic (fun n => S n = 0) p := by
  have h1 := eventuallyPeriodic_nonneg S m₀ p hp P hrec
  have h2 := eventuallyPeriodic_nonneg (fun n => - S n) m₀ p hp (-P)
    (fun n hn => by rw [hrec n hn]; ring)
  exact (h1.and h2).congr (fun n => by omega)

/-- Comparison of two affine-on-residues sequences: `f n < g n` is eventually
periodic. -/
theorem eventuallyPeriodic_lt (f g : ℕ → ℤ) (m₀ p : ℕ) (hp : 1 ≤ p) (Pf Pg : ℤ)
    (hf : ∀ n, m₀ ≤ n → f (n + p) = f n + Pf) (hg : ∀ n, m₀ ≤ n → g (n + p) = g n + Pg) :
    EventuallyPeriodic (fun n => f n < g n) p := by
  have h := eventuallyPeriodic_pos (fun n => g n - f n) m₀ p hp (Pg - Pf)
    (fun n hn => by rw [hf n hn, hg n hn]; ring)
  exact h.congr (fun n => by omega)

/-- Coordinatewise equality of two affine-on-residues sequences: `f n = g n` is
eventually periodic. -/
theorem eventuallyPeriodic_eq (f g : ℕ → ℤ) (m₀ p : ℕ) (hp : 1 ≤ p) (Pf Pg : ℤ)
    (hf : ∀ n, m₀ ≤ n → f (n + p) = f n + Pf) (hg : ∀ n, m₀ ≤ n → g (n + p) = g n + Pg) :
    EventuallyPeriodic (fun n => f n = g n) p := by
  have h := eventuallyPeriodic_eqZero (fun n => f n - g n) m₀ p hp (Pf - Pg)
    (fun n hn => by rw [hf n hn, hg n hn]; ring)
  exact h.congr (fun n => by omega)

/-- **`lexLt` of two coordinatewise-affine `ℤ^d` vectors is eventually periodic.**
This is the rank-order stabilisation the WRP slice analysis needs: each rank
coordinate `F n i` is affine on residue classes of `n` (paper `lem:one-loop-rank-affine`, proved in
`SliceRank`), and the lexicographic comparison of two such vectors — the way the
WRP order `≺` decides precedence on the slice — is therefore an eventually periodic
predicate in `n`. -/
theorem lexLt_eventuallyPeriodic {d : ℕ} (F G : ℕ → Fin d → ℤ) (m₀ p : ℕ) (hp : 1 ≤ p)
    (Pf Pg : Fin d → ℤ)
    (hF : ∀ (i : Fin d) n, m₀ ≤ n → F (n + p) i = F n i + Pf i)
    (hG : ∀ (i : Fin d) n, m₀ ≤ n → G (n + p) i = G n i + Pg i) :
    EventuallyPeriodic (fun n => WRP.lexLt (F n) (G n)) p := by
  classical
  have hreify : ∀ n, WRP.lexLt (F n) (G n) ↔
      ∃ i ∈ (Finset.univ : Finset (Fin d)),
        (∀ j ∈ (Finset.univ.filter (fun j => j < i)), F n j = G n j) ∧ F n i < G n i := by
    intro n
    unfold WRP.lexLt
    constructor
    · rintro ⟨i, hlt, hlti⟩
      exact ⟨i, Finset.mem_univ i, fun j hj => hlt j (Finset.mem_filter.mp hj).2, hlti⟩
    · rintro ⟨i, _, hlt, hlti⟩
      exact ⟨i, fun j hj => hlt j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩), hlti⟩
  refine (EventuallyPeriodic.finset_or (Finset.univ : Finset (Fin d))
    (fun i n => (∀ j ∈ (Finset.univ.filter (fun j => j < i)), F n j = G n j) ∧ F n i < G n i)
    p (fun i _ => ?_)).congr (fun n => (hreify n).symm)
  refine EventuallyPeriodic.and ?_ ?_
  · exact EventuallyPeriodic.finset_and _ (fun j n => F n j = G n j) p
      (fun j _ => eventuallyPeriodic_eq (fun n => F n j) (fun n => G n j) m₀ p hp (Pf j) (Pg j)
        (fun n hn => hF j n hn) (fun n hn => hG j n hn))
  · exact eventuallyPeriodic_lt (fun n => F n i) (fun n => G n i) m₀ p hp (Pf i) (Pg i)
      (fun n hn => hF i n hn) (fun n hn => hG i n hn)

end SliceOrder
