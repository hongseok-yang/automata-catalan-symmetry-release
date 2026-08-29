/-
# The §7 `fas` TIE-count assembly (arity-1): eventually-periodic comparison machinery

The generic eventually-periodic machinery the equal-rank selectors of the arity-1 and general-arity
towers rest on:

* `iff_on_class` — a `P`-periodic-beyond-`m₀` predicate is constant along each residue class (the
  transport that lets the per-class data sets be *defined* at a class representative);
* `slope_periodic` — the per-residue slope of an `AffineOnResiduesZ` witness is automatically
  periodic;
* `affineOnResiduesZ_eq_EP` — equality of two `AffineOnResiduesZ` functions is an eventually
  periodic predicate (per class of the common period, the difference is an arithmetic progression:
  zero increment ⇒ constant truth, nonzero increment ⇒ at most one sporadic zero, absorbed by the
  threshold); `affineOnResiduesZ_vec_eq_EP` is the vector (`Fin d`) version, for rank vectors, and
  `affineOnResiduesZ_lt_EP` / `affineOnResiduesZ_lexLt_EP` the strict and lexicographic versions;
* `chain_min_endpoint` and the `lexLt_add_pos_smul_*` steps — the chain comparisons the Case-A
  forcing argument runs on.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`): pure arithmetic.
-/import RequestProject.SliceDstarBridge

namespace SliceFasSelector

open WRP SliceOrder SliceThreshold SliceDstar SliceLexOrder
open scoped Classical

/-! ## Residue-class transport for eventually periodic data -/

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
`SliceOrder.lexLt_eventuallyPeriodic`, which needs a single global slope and so does
not apply to `d*`-shaped thresholds. -/
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
