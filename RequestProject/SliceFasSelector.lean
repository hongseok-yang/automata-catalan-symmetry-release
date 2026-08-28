/-
# The §7 `fas` TIE-count assembly (arity-1): the equal-rank position selector (route step L5)

This file builds towards `eqRankD_position_selector`: the per-`n%p0`-class finite data
`(S, Front, Back)` such that, on every `D`-present slice past a threshold, a selected
`D`-atom has rank equal to the `d*`-rank exactly when its position satisfies the L4
`cfgPos` cell condition (`SliceFasGates.cfgPos`).

The present section provides the generic eventually-periodic machinery the selector
rests on:

* `const_on_class` / `iff_on_class` — a `P`-periodic-beyond-`m₀` function (resp.
  predicate) is constant along each residue class (the transport that lets the
  per-class data sets be *defined* at a class representative);
* `slope_periodic` — the per-residue slope of an `AffineOnResiduesZ` witness is
  automatically periodic;
* `affineOnResiduesZ_eq_EP` — equality of two `AffineOnResiduesZ` functions is an
  eventually periodic predicate (per class of the common period, the difference is an
  arithmetic progression: zero increment ⇒ constant truth, nonzero increment ⇒ at most
  one sporadic zero, absorbed by the threshold);
* `affineOnResiduesZ_vec_eq_EP` — the vector (`Fin d`) version, for rank vectors.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`): pure arithmetic.
-/
import RequestProject.SliceDstarBridge

namespace SliceFasSelector

open WRP Step SliceOrder SliceThreshold SliceAffine SliceDstar SliceLexOrder SliceCount
  SliceMSO MSOMark SliceRankAtom
open scoped Classical

/-! ## The position-cell taxonomy of a slice word -/

/-- Every position of `W_n` (`|W_n| = 2(n+1)`) is the pre position `0`, a block-`U`
position `1+2j` (`j < n`), a block-`D` position `1+2j+1` (`j < n`), or the suffix
position `1+2n`. -/
theorem position_cases (n q : ℕ) (hq : q < 2 * (n + 1)) :
    q = 0 ∨ (∃ j, j < n ∧ q = 1 + 2 * j) ∨ (∃ j, j < n ∧ q = 1 + 2 * j + 1)
      ∨ q = 1 + 2 * n := by
  rcases Nat.even_or_odd q with ⟨t, ht⟩ | ⟨t, ht⟩
  · rcases Nat.eq_zero_or_pos t with rfl | hpos
    · left; omega
    · right; right; left; exact ⟨t - 1, by omega, by omega⟩
  · by_cases hsuf : t = n
    · right; right; right; omega
    · right; left; exact ⟨t, by omega, by omega⟩

/-! ## Residue-class transport for eventually periodic data -/

/-- A function that is `P`-periodic beyond `m₀` is constant along each residue class
beyond `m₀`. -/
theorem const_on_class {α : Type*} {f : ℕ → α} {P m₀ : ℕ} (_hP : 1 ≤ P)
    (h : ∀ n, m₀ ≤ n → f (n + P) = f n) {n n' : ℕ} (hn : m₀ ≤ n) (hn' : m₀ ≤ n')
    (hmod : n % P = n' % P) : f n = f n' := by
  have step : ∀ a, m₀ ≤ a → ∀ k, f (a + P * k) = f a := by
    intro a ha k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.mul_succ, ← Nat.add_assoc, h (a + P * k) (by omega), ih]
  rcases Nat.le_total n n' with hle | hle
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).mp hmod
    rw [show n' = n + P * k from by omega, step n hn k]
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    rw [show n = n' + P * k from by omega, step n' hn' k]

/-- A predicate that is `P`-eventually-periodic with threshold `m₀` has constant truth
value along each residue class beyond `m₀` (transport to a class representative). -/
theorem iff_on_class {Pr : ℕ → Prop} {P m₀ : ℕ} (_hP : 1 ≤ P)
    (h : ∀ n, m₀ ≤ n → (Pr (n + P) ↔ Pr n)) {n n' : ℕ} (hn : m₀ ≤ n) (hn' : m₀ ≤ n')
    (hmod : n % P = n' % P) : Pr n ↔ Pr n' := by
  have step : ∀ a, m₀ ≤ a → ∀ k, (Pr (a + P * k) ↔ Pr a) := by
    intro a ha k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.mul_succ, ← Nat.add_assoc]
        exact (h (a + P * k) (by omega)).trans ih
  rcases Nat.le_total n n' with hle | hle
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).mp hmod
    rw [show n' = n + P * k from by omega]
    exact (step n hn k).symm
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    rw [show n = n' + P * k from by omega]
    exact step n' hn' k

/-! ## Bulk-window iterate equality along a residue class -/

/-- **Forward- and backward-iterate equality** for two block indices of the same
`p`-residue class inside the bulk window `[m, n - m)` — the prerequisite pair of
`selBU_eq_of_iter`/`selBD_eq_of_iter`, i.e. the all-or-nothing selectedness of a bulk
class. -/
theorem iter_eq_of_class (M : DetAuto (Step × Bool)) {m p : ℕ} (hp : 1 ≤ p)
    (hfwd : ∀ j, m ≤ j → (bF M)^[j + p] (qpre M) = (bF M)^[j] (qpre M))
    (hbwd : ∀ j, m ≤ j → (bF M)^[j + p] = (bF M)^[j])
    {n j j' : ℕ} (hjm : m ≤ j) (hj'm : m ≤ j') (hjw : j + m < n) (hj'w : j' + m < n)
    (hmod : j % p = j' % p) :
    (bF M)^[j] (qpre M) = (bF M)^[j'] (qpre M)
    ∧ (bF M)^[n - 1 - j] = (bF M)^[n - 1 - j'] := by
  constructor
  · exact const_on_class (f := fun i => (bF M)^[i] (qpre M)) hp hfwd hjm hj'm hmod
  · rcases Nat.le_total j j' with hle | hle
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).mp hmod
      rw [show n - 1 - j = (n - 1 - j') + p * k from by omega]
      exact fn_period_mul (fun i => (bF M)^[i]) hbwd (n - 1 - j') k (by omega)
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      rw [show n - 1 - j' = (n - 1 - j) + p * k from by omega]
      exact (fn_period_mul (fun i => (bF M)^[i]) hbwd (n - 1 - j) k (by omega)).symm

/-! ## Equality of affine-on-residues functions is eventually periodic -/

/-- The per-residue slope of an `AffineOnResiduesZ` witness is automatically
`p`-periodic. -/
theorem slope_periodic {F : ℕ → ℤ} {m p : ℕ} {s : ℕ → ℤ}
    (h : ∀ r k : ℕ, F (m + r + p * k) = F (m + r) + k * s r) (r : ℕ) :
    s (r + p) = s r := by
  have h2 : F (m + r + p * 2) = F (m + r) + (2 : ℕ) * s r := h r 2
  have h1 : F (m + (r + p) + p * 1) = F (m + (r + p)) + (1 : ℕ) * s (r + p) := h (r + p) 1
  have h0 : F (m + r + p * 1) = F (m + r) + (1 : ℕ) * s r := h r 1
  have e1 : m + (r + p) + p * 1 = m + r + p * 2 := by ring
  have e0 : m + (r + p) = m + r + p * 1 := by ring
  rw [e1, e0, h0] at h1
  rw [h1] at h2
  push_cast at h2
  linarith

/-- **The difference of two `AffineOnResiduesZ` functions is, along each residue class
of a common period, an arithmetic progression**: there are a period `P ≥ 1`, a
threshold `m₀`, and a per-point increment `D` — constant along classes beyond `m₀` —
with `(F−G)(n + P·k) = (F−G)(n) + k·D n`.  The shared core of the equality- and
order-comparison EP lemmas below. -/
theorem diff_AP {F G : ℕ → ℤ} (hF : AffineOnResiduesZ F) (hG : AffineOnResiduesZ G) :
    ∃ (P m₀ : ℕ) (D : ℕ → ℤ), 1 ≤ P ∧
      (∀ n, m₀ ≤ n → D (n + P) = D n) ∧
      (∀ n, m₀ ≤ n → ∀ k : ℕ,
        F (n + P * k) - G (n + P * k) = (F n - G n) + (k : ℤ) * D n) := by
  obtain ⟨mf, pf, sf, hpf, hf⟩ := hF
  obtain ⟨mg, pg, sg, hpg, hg⟩ := hG
  set P : ℕ := pf * pg with hPdef
  have hP : 1 ≤ P := Nat.mul_pos hpf hpg
  obtain ⟨m₀, hm₀f, hm₀g⟩ : ∃ m₀ : ℕ, mf ≤ m₀ ∧ mg ≤ m₀ :=
    ⟨mf + mg, Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  -- the one-period increment of `F - G`
  set D : ℕ → ℤ := fun n => (pg : ℤ) * sf (n - mf) - (pf : ℤ) * sg (n - mg) with hDdef
  have hDeval : ∀ x, D x = (pg : ℤ) * sf (x - mf) - (pf : ℤ) * sg (x - mg) :=
    fun x => rfl
  have hstepF : ∀ n, mf ≤ n → F (n + P) = F n + (pg : ℤ) * sf (n - mf) := by
    intro n hn
    have h := hf (n - mf) pg
    rw [show mf + (n - mf) + pf * pg = n + P from by rw [hPdef]; omega,
      show mf + (n - mf) = n from by omega] at h
    exact h
  have hstepG : ∀ n, mg ≤ n → G (n + P) = G n + (pf : ℤ) * sg (n - mg) := by
    intro n hn
    have h := hg (n - mg) pf
    rw [show mg + (n - mg) + pg * pf = n + P from by
        rw [hPdef, Nat.mul_comm pf pg]; omega,
      show mg + (n - mg) = n from by omega] at h
    exact h
  -- `D` is `P`-periodic beyond `m₀`
  have hDper : ∀ n, m₀ ≤ n → D (n + P) = D n := by
    intro n hn
    have hsfrec : ∀ a k, sf (a + pf * k) = sf a := by
      intro a k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Nat.mul_succ, ← Nat.add_assoc, slope_periodic hf, ih]
    have hsgrec : ∀ a k, sg (a + pg * k) = sg a := by
      intro a k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Nat.mul_succ, ← Nat.add_assoc, slope_periodic hg, ih]
    have hsf : sf (n + P - mf) = sf (n - mf) := by
      rw [show n + P - mf = n - mf + pf * pg from by rw [hPdef]; omega, hsfrec]
    have hsg : sg (n + P - mg) = sg (n - mg) := by
      rw [show n + P - mg = n - mg + pg * pf from by
        rw [hPdef, Nat.mul_comm pf pg]; omega, hsgrec]
    rw [hDeval, hDeval, hsf, hsg]
  -- `D` is constant along each class beyond `m₀`
  have hDiter : ∀ a, m₀ ≤ a → ∀ k, D (a + P * k) = D a := by
    intro a ha k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.mul_succ, ← Nat.add_assoc, hDper (a + P * k) (by omega), ih]
  -- iterating the increment along a class
  have hiter : ∀ n, m₀ ≤ n → ∀ k : ℕ,
      F (n + P * k) - G (n + P * k) = (F n - G n) + (k : ℤ) * D n := by
    intro n hn k
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : F (n + P * k + P) - G (n + P * k + P)
            = (F (n + P * k) - G (n + P * k)) + D (n + P * k) := by
          rw [hstepF (n + P * k) (by omega), hstepG (n + P * k) (by omega),
            hDeval]
          ring
        rw [Nat.mul_succ, ← Nat.add_assoc, hk', ih, hDiter n hn k]
        push_cast
        ring
  exact ⟨P, m₀, D, hP, hDper, hiter⟩

/-- **Equality of two `AffineOnResiduesZ` functions is eventually periodic.**  On each
residue class of the common period the difference is an arithmetic progression; a zero
increment makes the equality truth-constant along the class, a nonzero increment allows
at most one sporadic zero, absorbed by the threshold. -/
theorem affineOnResiduesZ_eq_EP {F G : ℕ → ℤ}
    (hF : AffineOnResiduesZ F) (hG : AffineOnResiduesZ G) :
    ∃ p : ℕ, 1 ≤ p ∧ EventuallyPeriodic (fun n => F n = G n) p := by
  obtain ⟨P, m₀, D, hP, hDper, hiter⟩ := diff_AP hF hG
  -- per-class threshold past the (at most one) sporadic zero on nonzero-increment classes
  have hMρ : ∀ ρ : ℕ, ∃ Mρ : ℕ, ∀ n, Mρ ≤ n → m₀ ≤ n → n % P = ρ →
      (D n = 0 ∨ (F n ≠ G n ∧ F (n + P) ≠ G (n + P))) := by
    intro ρ
    by_cases hz : ∃ z, m₀ ≤ z ∧ z % P = ρ ∧ D z ≠ 0 ∧ F z = G z
    · obtain ⟨z, hzm, hzρ, hzD, hzeq⟩ := hz
      refine ⟨z + 1, fun n hn hnm hρ => ?_⟩
      by_cases hDn : D n = 0
      · exact Or.inl hDn
      · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (show z ≤ n by omega)).mp
          (hzρ.trans hρ.symm)
        have hkpos : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with rfl | h1
          · omega
          · exact h1
        have hzn : n = z + P * k := by omega
        have hval : F n - G n = (F z - G z) + (k : ℤ) * D z := by
          rw [hzn]; exact hiter z hzm k
        have hval' : F (n + P) - G (n + P) = (F z - G z) + ((k : ℤ) + 1) * D z := by
          rw [hzn, show z + P * k + P = z + P * (k + 1) from by ring]
          have := hiter z hzm (k + 1)
          push_cast at this
          exact this
        rw [hzeq] at hval hval'
        refine Or.inr ⟨?_, ?_⟩
        · intro hcon
          rw [hcon] at hval
          have hkD : (k : ℤ) * D z = 0 := by linarith
          rcases mul_eq_zero.mp hkD with h | h
          · exact (Nat.cast_ne_zero.mpr (by omega : k ≠ 0)) h
          · exact hzD h
        · intro hcon
          rw [hcon] at hval'
          have hkD : ((k : ℤ) + 1) * D z = 0 := by linarith
          rcases mul_eq_zero.mp hkD with h | h
          · have : (0 : ℤ) < (k : ℤ) + 1 := by positivity
            omega
          · exact hzD h
    · push Not at hz
      refine ⟨0, fun n _ hnm hρ => ?_⟩
      by_cases hDn : D n = 0
      · exact Or.inl hDn
      · refine Or.inr ⟨hz n hnm hρ hDn, ?_⟩
        have hDn' : D (n + P) ≠ 0 := by rw [hDper n hnm]; exact hDn
        exact hz (n + P) (by omega) (by rw [Nat.add_mod_right]; exact hρ) hDn'
  choose Mρ hMρspec using hMρ
  refine ⟨P, hP, (Finset.range P).sup Mρ + m₀, fun n hn => ?_⟩
  have hρlt : n % P < P := Nat.mod_lt _ hP
  have hMle : Mρ (n % P) ≤ n := by
    have := Finset.le_sup (f := Mρ) (Finset.mem_range.mpr hρlt)
    omega
  have hm₀n : m₀ ≤ n := by
    have := Finset.le_sup (f := Mρ) (Finset.mem_range.mpr hρlt)
    omega
  rcases hMρspec (n % P) n hMle hm₀n rfl with hD0 | ⟨hne, hne'⟩
  · -- zero local increment: `F - G` is constant across the period step
    have h1 := hiter n hm₀n 1
    rw [Nat.mul_one, hD0] at h1
    simp only [mul_zero, add_zero, Nat.cast_one] at h1
    exact ⟨fun h => by omega, fun h => by omega⟩
  · exact iff_of_false hne' hne

/-- **Vector version**: equality of two rank-vector functions whose coordinates are all
`AffineOnResiduesZ` is eventually periodic. -/
theorem affineOnResiduesZ_vec_eq_EP {d : ℕ} {F G : ℕ → Fin d → ℤ}
    (hF : ∀ i, AffineOnResiduesZ (fun n => F n i))
    (hG : ∀ i, AffineOnResiduesZ (fun n => G n i)) :
    ∃ p : ℕ, 1 ≤ p ∧ EventuallyPeriodic (fun n => F n = G n) p := by
  have hcoord : ∀ i : Fin d, ∃ p : ℕ, 1 ≤ p ∧
      EventuallyPeriodic (fun n => F n i = G n i) p :=
    fun i => affineOnResiduesZ_eq_EP (hF i) (hG i)
  choose pc hpc hEPc using hcoord
  set P : ℕ := ∏ i : Fin d, pc i with hPdef
  have hP : 1 ≤ P := by
    rw [hPdef]
    exact Finset.prod_pos (f := pc) (fun i _ => by have := hpc i; omega)
  have hdvd : ∀ i : Fin d, pc i ∣ P := fun i =>
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨P, hP, ?_⟩
  have hconj : EventuallyPeriodic (fun n => ∀ i ∈ (Finset.univ : Finset (Fin d)),
      F n i = G n i) P :=
    EventuallyPeriodic.finset_and (Finset.univ : Finset (Fin d))
      (fun i n => F n i = G n i) P (fun i _ => EP_of_dvd (hEPc i) (hdvd i))
  exact hconj.congr (fun n => by
    constructor
    · intro h
      funext i
      exact h i (Finset.mem_univ i)
    · intro h i _
      rw [h])

/-- **Strict comparison of two `AffineOnResiduesZ` functions is eventually periodic.**
On each residue class the difference is an arithmetic progression; a zero increment
keeps the sign constant, a nonzero increment crosses zero at most once, and the
threshold is set past that single crossing. -/
theorem affineOnResiduesZ_lt_EP {F G : ℕ → ℤ}
    (hF : AffineOnResiduesZ F) (hG : AffineOnResiduesZ G) :
    ∃ p : ℕ, 1 ≤ p ∧ EventuallyPeriodic (fun n => F n < G n) p := by
  obtain ⟨P, m₀, D, hP, hDper, hiter⟩ := diff_AP hF hG
  -- per-class threshold past the (at most one) sign crossing
  have hMρ : ∀ ρ : ℕ, ∃ Mρ : ℕ, ∀ n, Mρ ≤ n → m₀ ≤ n → n % P = ρ →
      (F (n + P) - G (n + P) < 0 ↔ F n - G n < 0) := by
    intro ρ
    by_cases hz : ∃ z, m₀ ≤ z ∧ z % P = ρ ∧
        ¬ (F (z + P) - G (z + P) < 0 ↔ F z - G z < 0)
    · obtain ⟨z, hzm, hzρ, hzflip⟩ := hz
      have hHz1 : F (z + P) - G (z + P) = (F z - G z) + D z := by
        have h := hiter z hzm 1
        rw [Nat.mul_one] at h
        push_cast at h
        linarith
      refine ⟨z + 1, fun n hn hnm hρ => ?_⟩
      obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (show z ≤ n by omega)).mp
        (hzρ.trans hρ.symm)
      have hkpos : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h1
        · omega
        · exact h1
      have hzn : n = z + P * k := by omega
      have hHn : F n - G n = (F z - G z) + (k : ℤ) * D z := by
        rw [hzn]; exact hiter z hzm k
      have hHn' : F (n + P) - G (n + P) = (F z - G z) + ((k : ℤ) + 1) * D z := by
        rw [hzn, show z + P * k + P = z + P * (k + 1) from by ring]
        have h := hiter z hzm (k + 1)
        push_cast at h
        exact h
      rcases lt_trichotomy (D z) 0 with hD | hD | hD
      · -- decreasing chain: the flip forces `H z ≥ 0 > H (z+P)`; past it both negative
        have hcase : ¬ (F z - G z < 0) ∧ F (z + P) - G (z + P) < 0 := by
          by_contra hcon
          apply hzflip
          constructor
          · intro h'
            by_contra hzneg
            exact hcon ⟨hzneg, h'⟩
          · intro h'
            rw [hHz1]; linarith
        have h1 : (k : ℤ) * D z ≤ 1 * D z :=
          mul_le_mul_of_nonpos_right (by exact_mod_cast hkpos) (le_of_lt hD)
        have hk1 : ((k : ℤ) + 1) * D z ≤ 1 * D z :=
          mul_le_mul_of_nonpos_right (by omega) (le_of_lt hD)
        rw [hHz1] at hcase
        have hHneg : F n - G n < 0 := by rw [hHn]; linarith [hcase.2]
        have hHneg' : F (n + P) - G (n + P) < 0 := by rw [hHn']; linarith [hcase.2]
        exact iff_of_true hHneg' hHneg
      · -- zero increment contradicts the flip
        exfalso
        apply hzflip
        rw [hHz1, hD, add_zero]
      · -- increasing chain: the flip forces `H z < 0 ≤ H (z+P)`; past it both nonneg
        have hcase : F z - G z < 0 ∧ ¬ (F (z + P) - G (z + P) < 0) := by
          by_contra hcon
          apply hzflip
          constructor
          · intro h'
            rw [hHz1] at h'; linarith
          · intro h'
            by_contra hpos
            exact hcon ⟨h', hpos⟩
        have h1 : 1 * D z ≤ (k : ℤ) * D z :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hkpos) (le_of_lt hD)
        have hk1 : 1 * D z ≤ ((k : ℤ) + 1) * D z :=
          mul_le_mul_of_nonneg_right (by omega) (le_of_lt hD)
        rw [hHz1] at hcase
        have hHpos : ¬ (F n - G n < 0) := by
          rw [hHn]
          have := hcase.2
          push Not at this ⊢
          linarith
        have hHpos' : ¬ (F (n + P) - G (n + P) < 0) := by
          rw [hHn']
          have := hcase.2
          push Not at this ⊢
          linarith
        exact iff_of_false hHpos' hHpos
    · push Not at hz
      exact ⟨0, fun n _ hnm hρ => hz n hnm hρ⟩
  choose Mρ hMρspec using hMρ
  refine ⟨P, hP, (Finset.range P).sup Mρ + m₀, fun n hn => ?_⟩
  have hρlt : n % P < P := Nat.mod_lt _ hP
  have hMle : Mρ (n % P) ≤ n := by
    have := Finset.le_sup (f := Mρ) (Finset.mem_range.mpr hρlt)
    omega
  have hm₀n : m₀ ≤ n := by
    have := Finset.le_sup (f := Mρ) (Finset.mem_range.mpr hρlt)
    omega
  have h := hMρspec (n % P) n hMle hm₀n rfl
  constructor
  · intro h'
    have : F (n + P) - G (n + P) < 0 := by omega
    have := h.mp this
    omega
  · intro h'
    have : F n - G n < 0 := by omega
    have := h.mpr this
    omega

/-- **Lexicographic comparison of two `AffineOnResiduesZ` rank-vector families is
eventually periodic** — the per-residue-slope replacement for
`SliceOrder.lexLt_eventuallyPeriodic` (which needs a single global slope and so does
not apply to `dstarRank`/`dstarC`-shaped thresholds). -/
theorem affineOnResiduesZ_lexLt_EP {d : ℕ} {F G : ℕ → Fin d → ℤ}
    (hF : ∀ i, AffineOnResiduesZ (fun n => F n i))
    (hG : ∀ i, AffineOnResiduesZ (fun n => G n i)) :
    ∃ p : ℕ, 1 ≤ p ∧ EventuallyPeriodic (fun n => WRP.lexLt (F n) (G n)) p := by
  classical
  choose pe hpe hEPe using fun i : Fin d => affineOnResiduesZ_eq_EP (hF i) (hG i)
  choose pl hpl hEPl using fun i : Fin d => affineOnResiduesZ_lt_EP (hF i) (hG i)
  set P : ℕ := (∏ i : Fin d, pe i) * (∏ i : Fin d, pl i) with hPdef
  have hP : 1 ≤ P := by
    rw [hPdef]
    exact Nat.mul_pos (Finset.prod_pos (f := pe) (fun i _ => by have := hpe i; omega))
      (Finset.prod_pos (f := pl) (fun i _ => by have := hpl i; omega))
  have hdvde : ∀ i : Fin d, pe i ∣ P := fun i => by
    rw [hPdef]
    exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).mul_right _
  have hdvdl : ∀ i : Fin d, pl i ∣ P := fun i => by
    rw [hPdef]
    exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).mul_left _
  refine ⟨P, hP, ?_⟩
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
    P (fun i _ => ?_)).congr (fun n => (hreify n).symm)
  refine EventuallyPeriodic.and ?_ (EP_of_dvd (hEPl i) (hdvdl i))
  exact EventuallyPeriodic.finset_and _ (fun j n => F n j = G n j) P
    (fun j _ => EP_of_dvd (hEPe j) (hdvde j))

/-! ## Chain-step lexicographic comparisons -/

/-- Adding a **positive multiple of the slope** moves lex-DOWN exactly when the slope
is lex-negative: `x + c·s ≺ x ↔ s ≺ 0` (for `c > 0`).  The Case-A chain-forcing step. -/
theorem lexLt_add_pos_smul_left {d : ℕ} (x s : Fin d → ℤ) (c : ℤ) (hc : 0 < c) :
    WRP.lexLt (fun i => x i + c * s i) x ↔ WRP.lexLt s (fun _ => 0) := by
  constructor
  · rintro ⟨i, hpre, hlt⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · have h := hpre j hj
      have hcs : c * s j = 0 := by
        have : x j + c * s j = x j := h
        omega
      show s j = 0
      rcases mul_eq_zero.mp hcs with h' | h'
      · exact absurd h' (by omega)
      · exact h'
    · have h : x i + c * s i < x i := hlt
      show s i < 0
      by_contra hge
      push Not at hge
      have := mul_nonneg (le_of_lt hc) hge
      omega
  · rintro ⟨i, hpre, hlt⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · have h : s j = 0 := hpre j hj
      show x j + c * s j = x j
      rw [h]; ring
    · have h : s i < 0 := hlt
      show x i + c * s i < x i
      have := mul_neg_of_pos_of_neg hc h
      omega

/-- Adding a **positive multiple of the slope** moves lex-UP exactly when the slope is
lex-positive: `x ≺ x + c·s ↔ 0 ≺ s` (for `c > 0`). -/
theorem lexLt_add_pos_smul_right {d : ℕ} (x s : Fin d → ℤ) (c : ℤ) (hc : 0 < c) :
    WRP.lexLt x (fun i => x i + c * s i) ↔ WRP.lexLt (fun _ => 0) s := by
  constructor
  · rintro ⟨i, hpre, hlt⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · have h : x j = x j + c * s j := hpre j hj
      have hcs : c * s j = 0 := by omega
      show (0 : ℤ) = s j
      rcases mul_eq_zero.mp hcs with h' | h'
      · exact absurd h' (by omega)
      · exact h'.symm
    · have h : x i < x i + c * s i := hlt
      show (0 : ℤ) < s i
      by_contra hle
      push Not at hle
      have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) hle
      omega
  · rintro ⟨i, hpre, hlt⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · have h : (0 : ℤ) = s j := hpre j hj
      show x j = x j + c * s j
      rw [← h]; ring
    · have h : (0 : ℤ) < s i := hlt
      show x i < x i + c * s i
      have := mul_pos hc h
      omega

/-- **An interior chain member never attains the chain minimum**: for `1 ≤ k < klast`
and a nonzero slope `s`, either the first member (`R`) or the last member
(`R + klast·s`) lex-precedes the `k`-th member.  The Case-A forcing core. -/
theorem chain_min_endpoint {d : ℕ} (R s : Fin d → ℤ) (k klast : ℕ)
    (hk1 : 1 ≤ k) (hklt : k < klast) (hs : ¬ s = fun _ => 0) :
    WRP.lexLt R (fun i => R i + (k : ℤ) * s i)
    ∨ WRP.lexLt (fun i => R i + (klast : ℤ) * s i) (fun i => R i + (k : ℤ) * s i) := by
  rcases SliceLexOrder.lexLt_trichot s (fun _ => 0) with hneg | hzero | hpos
  · -- decreasing slope: the last member precedes the interior one
    right
    have h := (lexLt_add_pos_smul_left (fun i => R i + (k : ℤ) * s i) s
      ((klast : ℤ) - (k : ℤ)) (by omega)).mpr hneg
    have hrew : (fun i => (R i + (k : ℤ) * s i) + ((klast : ℤ) - (k : ℤ)) * s i)
        = fun i => R i + (klast : ℤ) * s i := by
      funext i; ring
    rwa [hrew] at h
  · exact absurd hzero hs
  · -- increasing slope: the first member precedes the interior one
    left
    exact (lexLt_add_pos_smul_right R s (k : ℤ) (by exact_mod_cast hk1)).mpr hpos

/-- Odd positions reduce mod `2p` blockwise: `(1+2a) % 2p = 1 + 2(a % p)`. -/
theorem odd_mod_two_mul (a p : ℕ) (hp : 1 ≤ p) :
    (1 + 2 * a) % (2 * p) = 1 + 2 * (a % p) := by
  conv_lhs => rw [show 1 + 2 * a = 1 + 2 * (a % p) + (a / p) * (2 * p) from by
    conv_lhs => rw [← Nat.mod_add_div a p]
    ring]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by have := Nat.mod_lt a hp; omega)]

/-- Even positions reduce mod `2p` blockwise: `(2a) % 2p = 2(a % p)`. -/
theorem even_mod_two_mul (a p : ℕ) :
    (2 * a) % (2 * p) = 2 * (a % p) :=
  Nat.mul_mod_mul_left 2 a p

/-! ## The `d*`-rank lex-minimality interface -/

/-- **No selected `D`-atom's rank lex-precedes the `d*`-rank** (the standalone
extraction of `dstarC_exists`'s inline `hDRle`).  The minimality input to the Case-A
chain forcing. -/
theorem dstarRank_lex_min (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity : ∀ c, P.toPoly.arity c = 1) (n : ℕ)
    (hD : ∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧
      P.toPoly.labelOf (wrappedFlat n) a = D)
    (b : P.toPoly.Atom) (hbsel : P.toPoly.selectedAtom (wrappedFlat n) b)
    (hbD : P.toPoly.labelOf (wrappedFlat n) b = D) :
    ¬ WRP.lexLt (P.rankOf (wrappedFlat n) b) (dstarRank P hV harity n) := by
  obtain ⟨dstar, hdsel, hdD, hdmin, hdrank⟩ := dstarRank_spec P hV harity n hD
  rw [hdrank]
  rcases hdmin b hbsel hbD with rfl | hord
  · exact SliceLexOrder.lexLt_irrefl _
  · simp only [WRP.Presentation.wrpOrd] at hord
    rcases hord with hlt | ⟨heqr, _⟩
    · exact fun hcon => SliceLexOrder.lexLt_irrefl _
        (SliceLexOrder.lexLt_trans _ _ _ hlt hcon)
    · rw [heqr]
      exact SliceLexOrder.lexLt_irrefl _

/-! ## The equal-rank position selector (route step L5)

The per-`n % p0`-class finite data `(S, Front, Back)`: on every `D`-present slice past
the threshold `N1`, a selected `D`-atom has rank equal to `dstarRank n` exactly when its
position satisfies the L4 `cfgPos` cell condition for the data of its class.  The data
is *defined* by evaluating each cell's rank-equality at a class representative
`rep κ := N1·p0 + κ`; correctness transports along the class via `iff_on_class`, with
the per-cell equality predicates eventually periodic by `affineOnResiduesZ_vec_eq_EP`
against the affine `dstarRank` (`dstarRank_affineOnResiduesZ`). -/

set_option maxHeartbeats 1600000 in
/-- **The equal-rank position selector** (route step L5).  Produces `M := 2p`,
`mthr := 1+2m`, a common period `p0` (a multiple of `p`), a threshold `N1`, and
per-class, per-copy finite data `(S, Front, Back)` such that on `D`-present slices
`n ≥ N1`, a selected `D`-atom `b` satisfies `rankOf b = dstarRank n` if and only if its
position lies in the `cfgPos` cells of class `n % p0`.  Base `+ SliceMSO.buchi` (via
`dstar_setup`/`dstarRank_affineOnResiduesZ`). -/
theorem eqRankD_position_selector (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity : ∀ c, P.toPoly.arity c = 1) :
    ∃ (M mthr p0 N1 : ℕ) (S Front Back : ℕ → Fin P.toPoly.K → Finset ℕ),
      1 ≤ p0 ∧
      (∀ κ c', ∀ r ∈ S κ c', r < M) ∧
      ∀ n, N1 ≤ n →
        (∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧
          P.toPoly.labelOf (wrappedFlat n) a = D) →
        ∀ b, P.toPoly.selectedAtom (wrappedFlat n) b →
          P.toPoly.labelOf (wrappedFlat n) b = D →
          (P.rankOf (wrappedFlat n) b = dstarRank P hV harity n ↔
            SliceFasGates.cfgPos M mthr (S (n % p0) b.1) (Front (n % p0) b.1)
              (Back (n % p0) b.1) (wrappedFlat n).length
              (b.2 (SliceBridge.z P.toPoly harity b.1))) := by
  classical
  obtain ⟨m, p, Mc, PU, PB, PS, PP, hp, hMc, hfwd, hbwd, hRUrec, hRBrec, hRSrec, hRPrec⟩ :=
    SliceDstarBridge.dstar_setup P harity
  set RU : Fin P.toPoly.K → ℕ → Fin P.d → ℤ :=
    fun c j => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j) with hRUdef
  set RB : Fin P.toPoly.K → ℕ → Fin P.d → ℤ :=
    fun c j => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1) with hRBdef
  set RS : Fin P.toPoly.K → ℕ → Fin P.d → ℤ :=
    fun c n => P.rank c (wrappedFlat n) (fun _ => 1 + 2 * n) with hRSdef
  set RP : Fin P.toPoly.K → ℕ → Fin P.d → ℤ :=
    fun c n => P.rank c (wrappedFlat n) (fun _ => 0) with hRPdef
  have hRU : ∀ c, RankAffine (RU c) := fun c => rank_block_rankAffine P c
  have hRB : ∀ c, RankAffine (RB c) := fun c => rank_blockD_rankAffine P c
  have hRS : ∀ c, RankAffine (RS c) := fun c => rank_suf_rankAffine P c
  have hRP : ∀ c, RankAffine (RP c) := fun c => rank_pre_rankAffine P c
  have hRUrec' : ∀ c'' x, m ≤ x → RU c'' (x + p) = RU c'' x + PU c'' :=
    fun c'' x hx => hRUrec c'' x hx
  have hRBrec' : ∀ c'' x, m ≤ x → RB c'' (x + p) = RB c'' x + PB c'' :=
    fun c'' x hx => hRBrec c'' x hx
  set DR : ℕ → Fin P.d → ℤ := fun n => dstarRank P hV harity n with hDRdef
  have hDRaff : ∀ i, AffineOnResiduesZ (fun n => DR n i) :=
    SliceDstarBridge.dstarRank_affineOnResiduesZ P hV harity
  -- the per-cell equality-vs-`DR` predicates are eventually periodic
  choose pFU hpFU hFUrec using fun (c' : Fin P.toPoly.K) (j : ℕ) =>
    affineOnResiduesZ_vec_eq_EP (F := fun _ => RU c' j) (G := DR)
      (fun i => AffineOnResiduesZ.const (RU c' j i)) hDRaff
  choose pFD hpFD hFDrec using fun (c' : Fin P.toPoly.K) (j : ℕ) =>
    affineOnResiduesZ_vec_eq_EP (F := fun _ => RB c' j) (G := DR)
      (fun i => AffineOnResiduesZ.const (RB c' j i)) hDRaff
  choose pBU hpBU hBUrec using fun (c' : Fin P.toPoly.K) (l : ℕ) =>
    affineOnResiduesZ_vec_eq_EP (F := fun n => RU c' (n - 1 - l)) (G := DR)
      (fun i => SliceFasBridges.rankAffine_back_coord (hRU c') l i) hDRaff
  choose pBD hpBD hBDrec using fun (c' : Fin P.toPoly.K) (l : ℕ) =>
    affineOnResiduesZ_vec_eq_EP (F := fun n => RB c' (n - 1 - l)) (G := DR)
      (fun i => SliceFasBridges.rankAffine_back_coord (hRB c') l i) hDRaff
  choose pPre hpPre hPrerec using fun (c' : Fin P.toPoly.K) =>
    affineOnResiduesZ_vec_eq_EP (F := fun n => RP c' n) (G := DR)
      (fun i => SliceFasBridges.rankAffine_coord_affineOnResiduesZ (hRP c') i) hDRaff
  choose pSuf hpSuf hSufrec using fun (c' : Fin P.toPoly.K) =>
    affineOnResiduesZ_vec_eq_EP (F := fun n => RS c' n) (G := DR)
      (fun i => SliceFasBridges.rankAffine_coord_affineOnResiduesZ (hRS c') i) hDRaff
  -- extract the raw EP thresholds
  choose NFU hNFU using fun c' j => hFUrec c' j
  choose NFD hNFD using fun c' j => hFDrec c' j
  choose NBU hNBU using fun c' l => hBUrec c' l
  choose NBD hNBD using fun c' l => hBDrec c' l
  choose NPre hNPre using fun c' => hPrerec c'
  choose NSuf hNSuf using fun c' => hSufrec c'
  -- the common period
  set Q : Fin P.toPoly.K → ℕ := fun c' =>
    (pPre c' * pSuf c')
    * ((Finset.range (m + p)).prod (fun j => pFU c' j * pFD c' j))
    * ((Finset.range (m + p)).prod (fun l => pBU c' l * pBD c' l)) with hQdef
  set p0 : ℕ := p * Finset.univ.prod Q with hp0def
  have hQpos : ∀ c', 1 ≤ Q c' := by
    intro c'
    rw [hQdef]
    refine Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hpPre c') (hpSuf c')) ?_) ?_
    · exact Finset.prod_pos (fun j _ => Nat.mul_pos (hpFU c' j) (hpFD c' j))
    · exact Finset.prod_pos (fun l _ => Nat.mul_pos (hpBU c' l) (hpBD c' l))
  have hp0 : 1 ≤ p0 := by
    rw [hp0def]
    exact Nat.mul_pos hp (Finset.prod_pos (f := Q) (fun c' _ => hQpos c'))
  have hQdvd : ∀ c', Q c' ∣ p0 := by
    intro c'
    rw [hp0def]
    exact (Finset.dvd_prod_of_mem Q (Finset.mem_univ c')).mul_left p
  have hpdvd : p ∣ p0 := by rw [hp0def]; exact dvd_mul_right p _
  have hFUdvd : ∀ c' j, j < m + p → pFU c' j ∣ p0 := by
    intro c' j hj
    refine dvd_trans (dvd_trans (dvd_trans ⟨pFD c' j, rfl⟩
      (Finset.dvd_prod_of_mem (fun j => pFU c' j * pFD c' j)
        (Finset.mem_range.mpr hj))) ⟨(pPre c' * pSuf c')
          * ((Finset.range (m + p)).prod (fun l => pBU c' l * pBD c' l)), ?_⟩)
      (hQdvd c')
    rw [hQdef]; ring
  have hFDdvd : ∀ c' j, j < m + p → pFD c' j ∣ p0 := by
    intro c' j hj
    refine dvd_trans (dvd_trans (dvd_trans ⟨pFU c' j, by ring⟩
      (Finset.dvd_prod_of_mem (fun j => pFU c' j * pFD c' j)
        (Finset.mem_range.mpr hj))) ⟨(pPre c' * pSuf c')
          * ((Finset.range (m + p)).prod (fun l => pBU c' l * pBD c' l)), ?_⟩)
      (hQdvd c')
    rw [hQdef]; ring
  have hBUdvd : ∀ c' l, l < m + p → pBU c' l ∣ p0 := by
    intro c' l hl
    refine dvd_trans (dvd_trans (dvd_trans ⟨pBD c' l, rfl⟩
      (Finset.dvd_prod_of_mem (fun l => pBU c' l * pBD c' l)
        (Finset.mem_range.mpr hl))) ⟨(pPre c' * pSuf c')
          * ((Finset.range (m + p)).prod (fun j => pFU c' j * pFD c' j)), ?_⟩)
      (hQdvd c')
    rw [hQdef]; ring
  have hBDdvd : ∀ c' l, l < m + p → pBD c' l ∣ p0 := by
    intro c' l hl
    refine dvd_trans (dvd_trans (dvd_trans ⟨pBU c' l, by ring⟩
      (Finset.dvd_prod_of_mem (fun l => pBU c' l * pBD c' l)
        (Finset.mem_range.mpr hl))) ⟨(pPre c' * pSuf c')
          * ((Finset.range (m + p)).prod (fun j => pFU c' j * pFD c' j)), ?_⟩)
      (hQdvd c')
    rw [hQdef]; ring
  have hPredvd : ∀ c', pPre c' ∣ p0 := by
    intro c'
    refine dvd_trans (⟨pSuf c'
      * ((Finset.range (m + p)).prod (fun j => pFU c' j * pFD c' j))
      * ((Finset.range (m + p)).prod (fun l => pBU c' l * pBD c' l)), ?_⟩ :
        pPre c' ∣ Q c') (hQdvd c')
    rw [hQdef]; ring
  have hSufdvd : ∀ c', pSuf c' ∣ p0 := by
    intro c'
    refine dvd_trans (⟨pPre c'
      * ((Finset.range (m + p)).prod (fun j => pFU c' j * pFD c' j))
      * ((Finset.range (m + p)).prod (fun l => pBU c' l * pBD c' l)), ?_⟩ :
        pSuf c' ∣ Q c') (hQdvd c')
    rw [hQdef]; ring
  -- the threshold
  set NA : ℕ := Finset.univ.sup (fun c' : Fin P.toPoly.K => NPre c' ⊔ NSuf c') with hNAdef
  set NB : ℕ := Finset.univ.sup (fun c' : Fin P.toPoly.K =>
    (Finset.range (m + p)).sup (fun j => NFU c' j ⊔ NFD c' j)) with hNBdef
  set NC : ℕ := Finset.univ.sup (fun c' : Fin P.toPoly.K =>
    (Finset.range (m + p)).sup (fun l => NBU c' l ⊔ NBD c' l)) with hNCdef
  set N1 : ℕ := (4 * m + 4 * p + 8) + NA + NB + NC with hN1def
  have hN1geo : 4 * m + 4 * p + 8 ≤ N1 := by rw [hN1def]; omega
  have hNPreLe : ∀ c', NPre c' ≤ N1 := by
    intro c'
    have h1 : NPre c' ⊔ NSuf c' ≤ NA := by
      rw [hNAdef]
      exact Finset.le_sup (f := fun c' : Fin P.toPoly.K => NPre c' ⊔ NSuf c')
        (Finset.mem_univ c')
    rw [hN1def]; omega
  have hNSufLe : ∀ c', NSuf c' ≤ N1 := by
    intro c'
    have h1 : NPre c' ⊔ NSuf c' ≤ NA := by
      rw [hNAdef]
      exact Finset.le_sup (f := fun c' : Fin P.toPoly.K => NPre c' ⊔ NSuf c')
        (Finset.mem_univ c')
    rw [hN1def]; omega
  have hNFULe : ∀ c' j, j < m + p → NFU c' j ≤ N1 := by
    intro c' j hj
    have h1 : NFU c' j ⊔ NFD c' j
        ≤ (Finset.range (m + p)).sup (fun j => NFU c' j ⊔ NFD c' j) :=
      Finset.le_sup (f := fun j => NFU c' j ⊔ NFD c' j) (Finset.mem_range.mpr hj)
    have h2 : (Finset.range (m + p)).sup (fun j => NFU c' j ⊔ NFD c' j) ≤ NB := by
      rw [hNBdef]
      exact Finset.le_sup (f := fun c' : Fin P.toPoly.K =>
        (Finset.range (m + p)).sup (fun j => NFU c' j ⊔ NFD c' j)) (Finset.mem_univ c')
    rw [hN1def]; omega
  have hNFDLe : ∀ c' j, j < m + p → NFD c' j ≤ N1 := by
    intro c' j hj
    have h1 : NFU c' j ⊔ NFD c' j
        ≤ (Finset.range (m + p)).sup (fun j => NFU c' j ⊔ NFD c' j) :=
      Finset.le_sup (f := fun j => NFU c' j ⊔ NFD c' j) (Finset.mem_range.mpr hj)
    have h2 : (Finset.range (m + p)).sup (fun j => NFU c' j ⊔ NFD c' j) ≤ NB := by
      rw [hNBdef]
      exact Finset.le_sup (f := fun c' : Fin P.toPoly.K =>
        (Finset.range (m + p)).sup (fun j => NFU c' j ⊔ NFD c' j)) (Finset.mem_univ c')
    rw [hN1def]; omega
  have hNBULe : ∀ c' l, l < m + p → NBU c' l ≤ N1 := by
    intro c' l hl
    have h1 : NBU c' l ⊔ NBD c' l
        ≤ (Finset.range (m + p)).sup (fun l => NBU c' l ⊔ NBD c' l) :=
      Finset.le_sup (f := fun l => NBU c' l ⊔ NBD c' l) (Finset.mem_range.mpr hl)
    have h2 : (Finset.range (m + p)).sup (fun l => NBU c' l ⊔ NBD c' l) ≤ NC := by
      rw [hNCdef]
      exact Finset.le_sup (f := fun c' : Fin P.toPoly.K =>
        (Finset.range (m + p)).sup (fun l => NBU c' l ⊔ NBD c' l)) (Finset.mem_univ c')
    rw [hN1def]; omega
  have hNBDLe : ∀ c' l, l < m + p → NBD c' l ≤ N1 := by
    intro c' l hl
    have h1 : NBU c' l ⊔ NBD c' l
        ≤ (Finset.range (m + p)).sup (fun l => NBU c' l ⊔ NBD c' l) :=
      Finset.le_sup (f := fun l => NBU c' l ⊔ NBD c' l) (Finset.mem_range.mpr hl)
    have h2 : (Finset.range (m + p)).sup (fun l => NBU c' l ⊔ NBD c' l) ≤ NC := by
      rw [hNCdef]
      exact Finset.le_sup (f := fun c' : Fin P.toPoly.K =>
        (Finset.range (m + p)).sup (fun l => NBU c' l ⊔ NBD c' l)) (Finset.mem_univ c')
    rw [hN1def]; omega
  -- the class representative and the data
  set rep : ℕ → ℕ := fun κ => N1 * p0 + κ with hrepdef
  set Front : ℕ → Fin P.toPoly.K → Finset ℕ := fun κ c' =>
    ((Finset.range (m + p)).filter (fun j => RU c' j = DR (rep κ))).image (fun j => 1 + 2 * j)
    ∪ ((Finset.range (m + p)).filter (fun j => RB c' j = DR (rep κ))).image
        (fun j => 1 + 2 * j + 1)
    ∪ (if RP c' (rep κ) = DR (rep κ) then {0} else ∅) with hFrontdef
  set Back : ℕ → Fin P.toPoly.K → Finset ℕ := fun κ c' =>
    ((Finset.range (m + p)).filter (fun l => RU c' (rep κ - 1 - l) = DR (rep κ))).image
        (fun l => 2 * l + 2)
    ∪ ((Finset.range (m + p)).filter (fun l => RB c' (rep κ - 1 - l) = DR (rep κ))).image
        (fun l => 2 * l + 1)
    ∪ (if RS c' (rep κ) = DR (rep κ) then {0} else ∅) with hBackdef
  set S : ℕ → Fin P.toPoly.K → Finset ℕ := fun κ c' =>
    ((Finset.range p).filter (fun r =>
        PU c' = (fun _ => 0) ∧ RU c' (m + r) = DR (rep κ))).image
      (fun r => (1 + 2 * (m + r)) % (2 * p))
    ∪ ((Finset.range p).filter (fun r =>
        PB c' = (fun _ => 0) ∧ RB c' (m + r) = DR (rep κ))).image
      (fun r => (1 + 2 * (m + r) + 1) % (2 * p)) with hSdef
  have hp2 : 0 < 2 * p := by omega
  have hSbound : ∀ κ c', ∀ r ∈ S κ c', r < 2 * p := by
    intro κ c' r hr
    rw [hSdef] at hr
    rcases Finset.mem_union.mp hr with h | h <;>
      · obtain ⟨r', _, rfl⟩ := Finset.mem_image.mp h
        exact Nat.mod_lt _ hp2
  refine ⟨2 * p, 1 + 2 * m, p0, N1, S, Front, Back, hp0, hSbound, ?_⟩
  intro n hn hD b hbsel hbD
  -- collapse the arity-1 atom
  set c' : Fin P.toPoly.K := b.1 with hc'def
  set q : ℕ := b.2 (SliceBridge.z P.toPoly harity b.1) with hqdef
  have hbeq : b = ⟨c', fun _ => q⟩ := SliceBridge.atom_eq P.toPoly harity b
  rw [hbeq] at hbsel hbD
  have hqlt : q < (wrappedFlat n).length := hbsel.1 (SliceBridge.z P.toPoly harity c')
  have hq2 : q < 2 * (n + 1) := by rwa [length_wrappedFlat] at hqlt
  have hlen : (wrappedFlat n).length = 2 * (n + 1) := length_wrappedFlat n
  -- the class facts
  set κ : ℕ := n % p0 with hκdef
  have hκlt : κ < p0 := Nat.mod_lt _ hp0
  have hrepmod : rep κ % p0 = κ := by
    rw [hrepdef]
    simp only []
    rw [Nat.mul_comm, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hκlt
  have hrepN1 : N1 ≤ rep κ := by
    rw [hrepdef]
    simp only []
    have : N1 ≤ N1 * p0 := Nat.le_mul_of_pos_right N1 hp0
    omega
  have hmodeq : ∀ qf : ℕ, qf ∣ p0 → n % qf = rep κ % qf := by
    intro qf hdvd
    have h1 : n % p0 = rep κ % p0 := by rw [hrepmod, hκdef]
    exact Nat.ModEq.of_dvd hdvd h1
  -- the per-family truth transport between `n` and the representative
  have htransFU : ∀ j, j < m + p → ((RU c' j = DR n) ↔ (RU c' j = DR (rep κ))) := by
    intro j hj
    exact iff_on_class (Pr := fun x => RU c' j = DR x) (hpFU c' j) (hNFU c' j)
      (le_trans (hNFULe c' j hj) hn) (le_trans (hNFULe c' j hj) hrepN1)
      (hmodeq _ (hFUdvd c' j hj))
  have htransFD : ∀ j, j < m + p → ((RB c' j = DR n) ↔ (RB c' j = DR (rep κ))) := by
    intro j hj
    exact iff_on_class (Pr := fun x => RB c' j = DR x) (hpFD c' j) (hNFD c' j)
      (le_trans (hNFDLe c' j hj) hn) (le_trans (hNFDLe c' j hj) hrepN1)
      (hmodeq _ (hFDdvd c' j hj))
  have htransBU : ∀ l, l < m + p →
      ((RU c' (n - 1 - l) = DR n) ↔ (RU c' (rep κ - 1 - l) = DR (rep κ))) := by
    intro l hl
    exact iff_on_class (Pr := fun x => RU c' (x - 1 - l) = DR x) (hpBU c' l) (hNBU c' l)
      (le_trans (hNBULe c' l hl) hn) (le_trans (hNBULe c' l hl) hrepN1)
      (hmodeq _ (hBUdvd c' l hl))
  have htransBD : ∀ l, l < m + p →
      ((RB c' (n - 1 - l) = DR n) ↔ (RB c' (rep κ - 1 - l) = DR (rep κ))) := by
    intro l hl
    exact iff_on_class (Pr := fun x => RB c' (x - 1 - l) = DR x) (hpBD c' l) (hNBD c' l)
      (le_trans (hNBDLe c' l hl) hn) (le_trans (hNBDLe c' l hl) hrepN1)
      (hmodeq _ (hBDdvd c' l hl))
  have htransPre : ((RP c' n = DR n) ↔ (RP c' (rep κ) = DR (rep κ))) :=
    iff_on_class (Pr := fun x => RP c' x = DR x) (hpPre c') (hNPre c') (le_trans (hNPreLe c') hn)
      (le_trans (hNPreLe c') hrepN1) (hmodeq _ (hPredvd c'))
  have htransSuf : ((RS c' n = DR n) ↔ (RS c' (rep κ) = DR (rep κ))) :=
    iff_on_class (Pr := fun x => RS c' x = DR x) (hpSuf c') (hNSuf c') (le_trans (hNSufLe c') hn)
      (le_trans (hNSufLe c') hrepN1) (hmodeq _ (hSufdvd c'))
  -- the rank of `b` in terms of the region families
  have hrankb : P.rankOf (wrappedFlat n) (⟨c', fun _ => q⟩ : P.toPoly.Atom)
      = P.rank c' (wrappedFlat n) (fun _ => q) := rfl
  have hrankmU : ∀ j'', j'' < n →
      P.rank c' (wrappedFlat n) (fun _ => 1 + 2 * j'') = RU c' j'' :=
    fun j'' h => (rank_block_prefix_invariant P c' n j'' h).1
  have hrankmD : ∀ j'', j'' < n →
      P.rank c' (wrappedFlat n) (fun _ => 1 + 2 * j'' + 1) = RB c' j'' :=
    fun j'' h => (rank_block_prefix_invariant P c' n j'' h).2
  rw [hbeq]
  simp only [SliceFasGates.cfgPos]
  constructor
  · -- (→) rank-equality at `n` places the position in a cell
    intro hrank
    have hrank' : P.rank c' (wrappedFlat n) (fun _ => q) = DR n := hrank
    rcases position_cases n q hq2 with hq0 | ⟨j, hjn, hqU⟩ | ⟨j, hjn, hqD⟩ | hqsuf
    · -- pre: `q = 0`, the rank is `RP c' n`; the `Front` if-piece fires
      have hr : RP c' n = DR n := by
        have h1 := hrank'
        rw [hq0] at h1
        exact h1
      refine Or.inr (Or.inl ?_)
      rw [hFrontdef]
      simp only []
      refine Finset.mem_union_right _ ?_
      rw [if_pos (htransPre.mp hr), hq0]
      exact Finset.mem_singleton_self 0
    · -- blockU: `q = 1+2j`
      have hrj : RU c' j = DR n := by
        have h1 := hrank'
        rw [hqU, hrankmU j hjn] at h1
        exact h1
      by_cases hjf : j < m + p
      · -- transient front or Case-A first member: the Front U-piece fires
        refine Or.inr (Or.inl ?_)
        rw [hFrontdef]
        simp only []
        refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hjf, (htransFU j hjf).mp hrj⟩, hqU.symm⟩
      · by_cases hjb : n - 1 - j < m + p
        · -- transient back or Case-A last member: the Back U-piece fires
          refine Or.inr (Or.inr ⟨2 * (n - 1 - j) + 2, ?_, by rw [hlen]; omega⟩)
          rw [hBackdef]
          simp only []
          refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          refine Finset.mem_image.mpr ⟨n - 1 - j, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hjb, ?_⟩, rfl⟩
          have hj' : n - 1 - (n - 1 - j) = j := by omega
          exact (htransBU (n - 1 - j) hjb).mp (by rw [hj']; exact hrj)
        · -- deep bulk
          push Not at hjf hjb
          set r : ℕ := (j - m) % p with hrdef
          have hrp : r < p := by rw [hrdef]; exact Nat.mod_lt _ hp
          set kk : ℕ := (j - m) / p with hkkdef
          have hjeq : j = m + r + p * kk := by
            rw [hrdef, hkkdef]
            have := Nat.mod_add_div (j - m) p
            omega
          have hkk1 : 1 ≤ kk := by
            rw [hkkdef]
            exact (Nat.one_le_div_iff hp).mpr (by omega)
          have hchain : ∀ t : ℕ,
              RU c' (m + r + p * t) = fun i => RU c' (m + r) i + (t : ℤ) * PU c' i := by
            intro t
            have hit := RankAffine.iterate (fun x hx => hRUrec' c' x hx) (m + r) t (by omega)
            funext i
            have h := congrFun hit i
            rwa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at h
          by_cases hcol : PU c' = (fun _ => 0)
          · -- collinear class: the bulk residue fires
            refine Or.inl ⟨by omega, by rw [hlen]; omega, ?_⟩
            have hjmodp : j % p = (m + r) % p := by
              rw [hjeq]
              exact Nat.add_mul_mod_self_left (m + r) p kk
            have hqmod : q % (2 * p) = (1 + 2 * (m + r)) % (2 * p) := by
              rw [hqU, odd_mod_two_mul j p hp, odd_mod_two_mul (m + r) p hp, hjmodp]
            rw [hqmod, hSdef]
            simp only []
            refine Finset.mem_union_left _ ?_
            refine Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr hrp, hcol, ?_⟩, rfl⟩
            have h0 : RU c' (m + r) = DR n := by
              have h1 := hchain kk
              rw [hcol] at h1
              have h2 : RU c' (m + r + p * kk) = RU c' (m + r) := by
                rw [h1]; funext i; simp
              rw [← hjeq] at h2
              rw [← h2]
              exact hrj
            exact (htransFU (m + r) (by omega)).mp h0
          · -- Case-A interior member: impossible
            exfalso
            set tl : ℕ := (n - m - 1 - (m + r)) / p with htldef
            set jl : ℕ := m + r + p * tl with hjldef
            have hjlw : jl ≤ n - m - 1 ∧ n - m - 1 < jl + p := by
              have h1 := Nat.mod_add_div (n - m - 1 - (m + r)) p
              have h2 := Nat.mod_lt (n - m - 1 - (m + r)) hp
              constructor
              · rw [hjldef, htldef]; omega
              · rw [hjldef, htldef]; omega
            have hkktl : kk < tl := by
              have h1 : j < jl := by omega
              rw [hjeq, hjldef] at h1
              exact Nat.lt_of_mul_lt_mul_left (a := p) (by omega)
            have hmem_selD : ∀ j'', m ≤ j'' → j'' + m < n → j'' % p = j % p →
                P.toPoly.selectedAtom (wrappedFlat n) ⟨c', fun _ => 1 + 2 * j''⟩ ∧
                P.toPoly.labelOf (wrappedFlat n) ⟨c', fun _ => 1 + 2 * j''⟩ = D := by
              intro j'' hj''m hj''w hj''mod
              obtain ⟨hf, hb⟩ := iter_eq_of_class (Mc c') hp (hfwd c') (hbwd c')
                hj''m (by omega : m ≤ j) hj''w (by omega : j + m < n) hj''mod
              have hacc_j : (Mc c').accepts (markAt (wrappedFlat n) (1 + 2 * j)) := by
                refine (hMc c' n (1 + 2 * j) (by rw [hlen]; omega)).mp ?_
                rw [← hqU]
                exact ⟨hbsel, hbD⟩
              have hacc : (Mc c').accepts (markAt (wrappedFlat n) (1 + 2 * j'')) := by
                rw [selBU_eq_of_iter (Mc c') n j'' j (by omega) hjn hf hb]
                exact hacc_j
              exact (hMc c' n (1 + 2 * j'') (by rw [hlen]; omega)).mpr hacc
            have hrankb' : DR n = fun i => RU c' (m + r) i + (kk : ℤ) * PU c' i := by
              rw [← hrj, hjeq]
              exact hchain kk
            rcases chain_min_endpoint (RU c' (m + r)) (PU c') kk tl hkk1 hkktl hcol
              with hfirst | hlast
            · -- the first member lex-precedes `d*` — contradiction with minimality
              have hsel0 := hmem_selD (m + r) (by omega) (by omega)
                (by rw [hjeq]; exact (Nat.add_mul_mod_self_left (m + r) p kk).symm)
              refine dstarRank_lex_min P hV harity n hD _ hsel0.1 hsel0.2 ?_
              have hr0 : P.rankOf (wrappedFlat n)
                  (⟨c', fun _ => 1 + 2 * (m + r)⟩ : P.toPoly.Atom) = RU c' (m + r) :=
                hrankmU (m + r) (by omega)
              rw [hr0]
              show WRP.lexLt (RU c' (m + r)) (DR n)
              rw [hrankb']
              exact hfirst
            · -- the last member lex-precedes `d*` — contradiction with minimality
              have hseltl := hmem_selD jl (by omega) (by omega)
                (by rw [hjldef, hjeq]
                    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left])
              refine dstarRank_lex_min P hV harity n hD _ hseltl.1 hseltl.2 ?_
              have hrl : P.rankOf (wrappedFlat n)
                  (⟨c', fun _ => 1 + 2 * jl⟩ : P.toPoly.Atom) = RU c' jl :=
                hrankmU jl (by omega)
              rw [hrl]
              have hjl_chain : RU c' jl = fun i => RU c' (m + r) i + (tl : ℤ) * PU c' i := by
                rw [hjldef]
                exact hchain tl
              rw [hjl_chain]
              show WRP.lexLt (fun i => RU c' (m + r) i + (tl : ℤ) * PU c' i) (DR n)
              rw [hrankb']
              exact hlast
    · -- blockD: `q = 1+2j+1` (the mirror of the blockU arm with `RB`/`PB`)
      have hrj : RB c' j = DR n := by
        have h1 := hrank'
        rw [hqD, hrankmD j hjn] at h1
        exact h1
      by_cases hjf : j < m + p
      · refine Or.inr (Or.inl ?_)
        rw [hFrontdef]
        simp only []
        refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hjf, (htransFD j hjf).mp hrj⟩, hqD.symm⟩
      · by_cases hjb : n - 1 - j < m + p
        · refine Or.inr (Or.inr ⟨2 * (n - 1 - j) + 1, ?_, by rw [hlen]; omega⟩)
          rw [hBackdef]
          simp only []
          refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          refine Finset.mem_image.mpr ⟨n - 1 - j, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hjb, ?_⟩, rfl⟩
          have hj' : n - 1 - (n - 1 - j) = j := by omega
          exact (htransBD (n - 1 - j) hjb).mp (by rw [hj']; exact hrj)
        · push Not at hjf hjb
          set r : ℕ := (j - m) % p with hrdef
          have hrp : r < p := by rw [hrdef]; exact Nat.mod_lt _ hp
          set kk : ℕ := (j - m) / p with hkkdef
          have hjeq : j = m + r + p * kk := by
            rw [hrdef, hkkdef]
            have := Nat.mod_add_div (j - m) p
            omega
          have hkk1 : 1 ≤ kk := by
            rw [hkkdef]
            exact (Nat.one_le_div_iff hp).mpr (by omega)
          have hchain : ∀ t : ℕ,
              RB c' (m + r + p * t) = fun i => RB c' (m + r) i + (t : ℤ) * PB c' i := by
            intro t
            have hit := RankAffine.iterate (fun x hx => hRBrec' c' x hx) (m + r) t (by omega)
            funext i
            have h := congrFun hit i
            rwa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at h
          by_cases hcol : PB c' = (fun _ => 0)
          · refine Or.inl ⟨by omega, by rw [hlen]; omega, ?_⟩
            have hjmodp : j % p = (m + r) % p := by
              rw [hjeq]
              exact Nat.add_mul_mod_self_left (m + r) p kk
            have hqmod : q % (2 * p) = (1 + 2 * (m + r) + 1) % (2 * p) := by
              rw [hqD, show 1 + 2 * j + 1 = 2 * (1 + j) from by ring,
                show 1 + 2 * (m + r) + 1 = 2 * (1 + (m + r)) from by ring,
                even_mod_two_mul (1 + j) p, even_mod_two_mul (1 + (m + r)) p]
              have h1j : (1 + j) % p = (1 + (m + r)) % p := by
                rw [hjeq, show 1 + (m + r + p * kk) = 1 + (m + r) + p * kk from by ring]
                exact Nat.add_mul_mod_self_left (1 + (m + r)) p kk
              rw [h1j]
            rw [hqmod, hSdef]
            simp only []
            refine Finset.mem_union_right _ ?_
            refine Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr hrp, hcol, ?_⟩, rfl⟩
            have h0 : RB c' (m + r) = DR n := by
              have h1 := hchain kk
              rw [hcol] at h1
              have h2 : RB c' (m + r + p * kk) = RB c' (m + r) := by
                rw [h1]; funext i; simp
              rw [← hjeq] at h2
              rw [← h2]
              exact hrj
            exact (htransFD (m + r) (by omega)).mp h0
          · exfalso
            set tl : ℕ := (n - m - 1 - (m + r)) / p with htldef
            set jl : ℕ := m + r + p * tl with hjldef
            have hjlw : jl ≤ n - m - 1 ∧ n - m - 1 < jl + p := by
              have h1 := Nat.mod_add_div (n - m - 1 - (m + r)) p
              have h2 := Nat.mod_lt (n - m - 1 - (m + r)) hp
              constructor
              · rw [hjldef, htldef]; omega
              · rw [hjldef, htldef]; omega
            have hkktl : kk < tl := by
              have h1 : j < jl := by omega
              rw [hjeq, hjldef] at h1
              exact Nat.lt_of_mul_lt_mul_left (a := p) (by omega)
            have hmem_selD : ∀ j'', m ≤ j'' → j'' + m < n → j'' % p = j % p →
                P.toPoly.selectedAtom (wrappedFlat n) ⟨c', fun _ => 1 + 2 * j'' + 1⟩ ∧
                P.toPoly.labelOf (wrappedFlat n) ⟨c', fun _ => 1 + 2 * j'' + 1⟩ = D := by
              intro j'' hj''m hj''w hj''mod
              obtain ⟨hf, hb⟩ := iter_eq_of_class (Mc c') hp (hfwd c') (hbwd c')
                hj''m (by omega : m ≤ j) hj''w (by omega : j + m < n) hj''mod
              have hacc_j : (Mc c').accepts (markAt (wrappedFlat n) (1 + 2 * j + 1)) := by
                refine (hMc c' n (1 + 2 * j + 1) (by rw [hlen]; omega)).mp ?_
                rw [← hqD]
                exact ⟨hbsel, hbD⟩
              have hacc : (Mc c').accepts (markAt (wrappedFlat n) (1 + 2 * j'' + 1)) := by
                rw [selBD_eq_of_iter (Mc c') n j'' j (by omega) hjn hf hb]
                exact hacc_j
              exact (hMc c' n (1 + 2 * j'' + 1) (by rw [hlen]; omega)).mpr hacc
            have hrankb' : DR n = fun i => RB c' (m + r) i + (kk : ℤ) * PB c' i := by
              rw [← hrj, hjeq]
              exact hchain kk
            rcases chain_min_endpoint (RB c' (m + r)) (PB c') kk tl hkk1 hkktl hcol
              with hfirst | hlast
            · have hsel0 := hmem_selD (m + r) (by omega) (by omega)
                (by rw [hjeq]; exact (Nat.add_mul_mod_self_left (m + r) p kk).symm)
              refine dstarRank_lex_min P hV harity n hD _ hsel0.1 hsel0.2 ?_
              have hr0 : P.rankOf (wrappedFlat n)
                  (⟨c', fun _ => 1 + 2 * (m + r) + 1⟩ : P.toPoly.Atom) = RB c' (m + r) :=
                hrankmD (m + r) (by omega)
              rw [hr0]
              show WRP.lexLt (RB c' (m + r)) (DR n)
              rw [hrankb']
              exact hfirst
            · have hseltl := hmem_selD jl (by omega) (by omega)
                (by rw [hjldef, hjeq]
                    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left])
              refine dstarRank_lex_min P hV harity n hD _ hseltl.1 hseltl.2 ?_
              have hrl : P.rankOf (wrappedFlat n)
                  (⟨c', fun _ => 1 + 2 * jl + 1⟩ : P.toPoly.Atom) = RB c' jl :=
                hrankmD jl (by omega)
              rw [hrl]
              have hjl_chain : RB c' jl = fun i => RB c' (m + r) i + (tl : ℤ) * PB c' i := by
                rw [hjldef]
                exact hchain tl
              rw [hjl_chain]
              show WRP.lexLt (fun i => RB c' (m + r) i + (tl : ℤ) * PB c' i) (DR n)
              rw [hrankb']
              exact hlast
    · -- suf: `q = 1+2n`, the rank is `RS c' n`; the Back if-piece fires at offset 0
      have hr : RS c' n = DR n := by
        have h1 := hrank'
        rw [hqsuf] at h1
        exact h1
      refine Or.inr (Or.inr ⟨0, ?_, by rw [hlen]; omega⟩)
      rw [hBackdef]
      simp only []
      refine Finset.mem_union_right _ ?_
      rw [if_pos (htransSuf.mp hr)]
      exact Finset.mem_singleton_self 0
  · -- (←) each firing cell certifies the rank equality
    intro hcfg
    rcases hcfg with ⟨hge, hltw, hres⟩ | hfront | ⟨k, hkmem, hkeq⟩
    · -- bulk residue: decode the active class and ride its zero slope
      rw [hSdef] at hres
      simp only [] at hres
      rw [hlen] at hltw
      have hq2p2 : q % (2 * p) % 2 = q % 2 := Nat.mod_mod_of_dvd q ⟨p, rfl⟩
      rcases Finset.mem_union.mp hres with hU | hDD
      · -- a collinear blockU class (odd residue)
        obtain ⟨r, hrmem, hrimg⟩ := Finset.mem_image.mp hU
        obtain ⟨hrrange, hcol, hval⟩ := Finset.mem_filter.mp hrmem
        have hrlt : r < p := Finset.mem_range.mp hrrange
        have hrr : q % (2 * p) = 1 + 2 * ((m + r) % p) := by
          have h1 : (1 + 2 * (m + r)) % (2 * p) = q % (2 * p) := hrimg
          rw [← h1, odd_mod_two_mul (m + r) p hp]
        have hmrp : (m + r) % p < p := Nat.mod_lt _ hp
        have hqodd : q % 2 = 1 := by omega
        obtain ⟨j, hjn', hqU⟩ : ∃ j, j < n ∧ q = 1 + 2 * j := by
          rcases position_cases n q hq2 with hq0 | hU' | ⟨j, _, hqD'⟩ | hqsuf
          · omega
          · exact hU'
          · omega
          · omega
        have hjmod : j % p = (m + r) % p := by
          have h1 : q % (2 * p) = 1 + 2 * (j % p) := by
            rw [hqU, odd_mod_two_mul j p hp]
          omega
        have hjm : m ≤ j := by omega
        have hreq : (j - m) % p = r := by
          rcases Nat.le_total (m + r) j with hle | hle
          · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp hjmod.symm
            have hjeq2 : j - m = r + p * t := by omega
            rw [hjeq2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
          · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp hjmod
            have ht0 : t = 0 := by
              rcases Nat.eq_zero_or_pos t with h | h
              · exact h
              · exfalso
                have := Nat.le_mul_of_pos_right p h
                omega
            rw [ht0, Nat.mul_zero] at ht
            have hjeq2 : j = m + r := by omega
            rw [hjeq2, Nat.add_sub_cancel_left, Nat.mod_eq_of_lt hrlt]
        have hjeq : j = m + r + p * ((j - m) / p) := by
          have := Nat.mod_add_div (j - m) p
          omega
        have hchain0 : RU c' j = RU c' (m + r) := by
          have hit := RankAffine.iterate (fun x hx => hRUrec' c' x hx) (m + r)
            ((j - m) / p) (by omega)
          rw [← hjeq] at hit
          rw [hit, hcol]
          funext i
          rw [Pi.add_apply, Pi.smul_apply]
          simp
        have hfinal : P.rank c' (wrappedFlat n) (fun _ => q) = DR n := by
          rw [hqU, hrankmU j hjn', hchain0]
          exact (htransFU (m + r) (by omega)).mpr hval
        exact hfinal
      · -- a collinear blockD class (even residue)
        obtain ⟨r, hrmem, hrimg⟩ := Finset.mem_image.mp hDD
        obtain ⟨hrrange, hcol, hval⟩ := Finset.mem_filter.mp hrmem
        have hrlt : r < p := Finset.mem_range.mp hrrange
        have hrr : q % (2 * p) = 2 * ((1 + (m + r)) % p) := by
          have h1 : (1 + 2 * (m + r) + 1) % (2 * p) = q % (2 * p) := hrimg
          rw [← h1, show 1 + 2 * (m + r) + 1 = 2 * (1 + (m + r)) from by ring,
            even_mod_two_mul (1 + (m + r)) p]
        have hmrp : (1 + (m + r)) % p < p := Nat.mod_lt _ hp
        have hqeven : q % 2 = 0 := by omega
        obtain ⟨j, hjn', hqD⟩ : ∃ j, j < n ∧ q = 1 + 2 * j + 1 := by
          rcases position_cases n q hq2 with hq0 | ⟨j, _, hqU'⟩ | hD' | hqsuf
          · omega
          · omega
          · exact hD'
          · omega
        have hjmod : (1 + j) % p = (1 + (m + r)) % p := by
          have h1 : q % (2 * p) = 2 * ((1 + j) % p) := by
            rw [hqD, show 1 + 2 * j + 1 = 2 * (1 + j) from by ring,
              even_mod_two_mul (1 + j) p]
          omega
        have hjm : m ≤ j := by omega
        have hreq : (j - m) % p = r := by
          rcases Nat.le_total (m + r) j with hle | hle
          · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' (by omega : 1 + (m + r) ≤ 1 + j)).mp
              hjmod.symm
            have hjeq2 : j - m = r + p * t := by omega
            rw [hjeq2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
          · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' (by omega : 1 + j ≤ 1 + (m + r))).mp
              hjmod
            have ht0 : t = 0 := by
              rcases Nat.eq_zero_or_pos t with h | h
              · exact h
              · exfalso
                have := Nat.le_mul_of_pos_right p h
                omega
            rw [ht0, Nat.mul_zero] at ht
            have hjeq2 : j = m + r := by omega
            rw [hjeq2, Nat.add_sub_cancel_left, Nat.mod_eq_of_lt hrlt]
        have hjeq : j = m + r + p * ((j - m) / p) := by
          have := Nat.mod_add_div (j - m) p
          omega
        have hchain0 : RB c' j = RB c' (m + r) := by
          have hit := RankAffine.iterate (fun x hx => hRBrec' c' x hx) (m + r)
            ((j - m) / p) (by omega)
          rw [← hjeq] at hit
          rw [hit, hcol]
          funext i
          rw [Pi.add_apply, Pi.smul_apply]
          simp
        have hfinal : P.rank c' (wrappedFlat n) (fun _ => q) = DR n := by
          rw [hqD, hrankmD j hjn', hchain0]
          exact (htransFD (m + r) (by omega)).mpr hval
        exact hfinal
    · -- exact front position: decode the piece by the position's value
      rw [hFrontdef] at hfront
      simp only [] at hfront
      rcases Finset.mem_union.mp hfront with hUD | hpre
      · rcases Finset.mem_union.mp hUD with hU | hDD
        · obtain ⟨j', hj'mem, hj'img⟩ := Finset.mem_image.mp hU
          obtain ⟨hj'range, hj'val⟩ := Finset.mem_filter.mp hj'mem
          have hj'lt : j' < m + p := Finset.mem_range.mp hj'range
          have hj'eq : 1 + 2 * j' = q := hj'img
          have hj'n : j' < n := by omega
          have hfinal : P.rank c' (wrappedFlat n) (fun _ => q) = DR n := by
            rw [← hj'eq, hrankmU j' hj'n]
            exact (htransFU j' hj'lt).mpr hj'val
          exact hfinal
        · obtain ⟨j', hj'mem, hj'img⟩ := Finset.mem_image.mp hDD
          obtain ⟨hj'range, hj'val⟩ := Finset.mem_filter.mp hj'mem
          have hj'lt : j' < m + p := Finset.mem_range.mp hj'range
          have hj'eq : 1 + 2 * j' + 1 = q := hj'img
          have hj'n : j' < n := by omega
          have hfinal : P.rank c' (wrappedFlat n) (fun _ => q) = DR n := by
            rw [← hj'eq, hrankmD j' hj'n]
            exact (htransFD j' hj'lt).mpr hj'val
          exact hfinal
      · by_cases hcond : RP c' (rep κ) = DR (rep κ)
        · rw [if_pos hcond] at hpre
          have hq0 : q = 0 := Finset.mem_singleton.mp hpre
          have hfinal : P.rank c' (wrappedFlat n) (fun _ => q) = DR n := by
            rw [hq0]
            exact htransPre.mpr hcond
          exact hfinal
        · rw [if_neg hcond] at hpre
          exact absurd hpre (Finset.notMem_empty q)
    · -- exact end-offset: decode the piece by the offset's value
      rw [hBackdef] at hkmem
      simp only [] at hkmem
      have hkeq' : q + 1 + k = 2 * (n + 1) := by rw [← hlen]; exact hkeq
      rcases Finset.mem_union.mp hkmem with hUD | hsuf
      · rcases Finset.mem_union.mp hUD with hU | hDD
        · obtain ⟨l, hlmem, hlimg⟩ := Finset.mem_image.mp hU
          obtain ⟨hlrange, hlval⟩ := Finset.mem_filter.mp hlmem
          have hllt : l < m + p := Finset.mem_range.mp hlrange
          have hlimg' : 2 * l + 2 = k := hlimg
          have hqval : q = 1 + 2 * (n - 1 - l) := by omega
          have hjn' : n - 1 - l < n := by omega
          have hfinal : P.rank c' (wrappedFlat n) (fun _ => q) = DR n := by
            rw [hqval, hrankmU (n - 1 - l) hjn']
            exact (htransBU l hllt).mpr hlval
          exact hfinal
        · obtain ⟨l, hlmem, hlimg⟩ := Finset.mem_image.mp hDD
          obtain ⟨hlrange, hlval⟩ := Finset.mem_filter.mp hlmem
          have hllt : l < m + p := Finset.mem_range.mp hlrange
          have hlimg' : 2 * l + 1 = k := hlimg
          have hqval : q = 1 + 2 * (n - 1 - l) + 1 := by omega
          have hjn' : n - 1 - l < n := by omega
          have hfinal : P.rank c' (wrappedFlat n) (fun _ => q) = DR n := by
            rw [hqval, hrankmD (n - 1 - l) hjn']
            exact (htransBD l hllt).mpr hlval
          exact hfinal
      · by_cases hcond : RS c' (rep κ) = DR (rep κ)
        · rw [if_pos hcond] at hsuf
          have hk0 : k = 0 := Finset.mem_singleton.mp hsuf
          have hqval : q = 1 + 2 * n := by omega
          have hfinal : P.rank c' (wrappedFlat n) (fun _ => q) = DR n := by
            rw [hqval]
            exact htransSuf.mpr hcond
          exact hfinal
        · rw [if_neg hcond] at hsuf
          exact absurd hsuf (Finset.notMem_empty k)
