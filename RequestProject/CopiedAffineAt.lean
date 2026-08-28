/-
# Pinned-period affine algebra (§9 tower, Stage F3.0)

The fibred chain's period discipline: every sequence on the period path is
affine-on-residues AT a pinned period that was fixed before the boundary
width `mS`; thresholds, intercepts and slopes may be per-`mS`.  This file is
the combinator algebra for that discipline (FIBRED_PORTMAP F3.0):

* `AffineOnResiduesAtZ` — the `ℤ`-valued twin of
  `SlicePeriodStar.AffineOnResiduesAt`, with `of_dvd`, rebase, closures, and
  `of_recurrence` (the bridge from `dstar_setup_fibred`'s slope clauses);
* ℕ-side combinators in the `SlicePeriodStar.AffineOnResiduesAt` namespace —
  `add`, `finsetSum`, `select`, `rebase`, `toAffine` … — all INDEX-SIZE-BLIND:
  a shared period in, the SAME period out, thresholds by `Finset.sup`
  (per-`mS` index sets never touch the period);
* classwise tools: `EP_of_classwise_eventually_const`, `EP_class_const`,
  `affineOnResiduesAt_indicator_of_EP`, `affineOnResiduesAt_natSubDiv`.

The comparison/lexMin layer (`lt_EP_at` … `gated_lexMin_affine_at`) follows
in the second half of the file.
-/
import RequestProject.SliceFasSelector
import RequestProject.SlicePeriodStar

namespace CopiedAffineAt

open WRP SliceOrder SliceThreshold SliceAffine SliceDstar SliceDstarCore
  SlicePeriodStar

/-! ## The ℤ-valued pinned shape -/

/-- `ℤ`-valued affineness at the PINNED period `p` (a parameter, never an
existential): beyond a threshold, each residue class is exactly affine. -/
def AffineOnResiduesAtZ (p : ℕ) (F : ℕ → ℤ) : Prop :=
  ∃ m : ℕ, ∀ j, j < p → ∃ b s : ℤ, ∀ k : ℕ, F (m + j + p * k) = b + (k : ℤ) * s

namespace AffineOnResiduesAtZ

/-- Rebase: the class data is available from EVERY base past the threshold. -/
theorem exists_rebase {p : ℕ} (hp : 1 ≤ p) {F : ℕ → ℤ}
    (h : AffineOnResiduesAtZ p F) :
    ∃ m : ℕ, ∀ m', m ≤ m' → ∀ j, j < p →
      ∃ b s : ℤ, ∀ k : ℕ, F (m' + j + p * k) = b + (k : ℤ) * s := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun m' hm' j hj => ?_⟩
  set j' : ℕ := (m' + j - m) % p with hj'
  set k' : ℕ := (m' + j - m) / p with hk'
  have hj'lt : j' < p := Nat.mod_lt _ (by omega)
  obtain ⟨b, s, hbs⟩ := hm j' hj'lt
  refine ⟨b + (k' : ℤ) * s, s, fun k => ?_⟩
  have hdm : p * k' + j' = m' + j - m := Nat.div_add_mod (m' + j - m) p
  have hsplit : p * (k' + k) = p * k' + p * k := Nat.mul_add p k' k
  have harg : m' + j + p * k = m + j' + p * (k' + k) := by
    generalize hA1 : p * k' = A1 at hdm hsplit
    generalize hA2 : p * k = A2 at hsplit ⊢
    generalize hA3 : p * (k' + k) = A3 at hsplit ⊢
    omega
  rw [harg, hbs (k' + k)]
  push_cast
  ring

theorem of_dvd {p p' : ℕ} {F : ℕ → ℤ} (hp : 1 ≤ p) (hdvd : p ∣ p')
    (hp' : 1 ≤ p') (h : AffineOnResiduesAtZ p F) : AffineOnResiduesAtZ p' F := by
  obtain ⟨t, rfl⟩ := hdvd
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun j' hj' => ?_⟩
  obtain ⟨b, s, hbs⟩ := hm (j' % p) (Nat.mod_lt _ (by omega))
  refine ⟨b + ((j' / p : ℕ) : ℤ) * s, (t : ℤ) * s, fun k => ?_⟩
  have hdm : p * (j' / p) + j' % p = j' := Nat.div_add_mod j' p
  have hexp : p * (j' / p + t * k) = p * (j' / p) + p * (t * k) :=
    Nat.mul_add p _ _
  have hexp2 : p * t * k = p * (t * k) := Nat.mul_assoc p t k
  have harg : m + j' + p * t * k = m + j' % p + p * (j' / p + t * k) := by
    generalize hA1 : p * (j' / p) = A1 at hdm hexp
    generalize hA2 : p * (t * k) = A2 at hexp hexp2
    generalize hA3 : p * (j' / p + t * k) = A3 at hexp ⊢
    generalize hA0 : p * t * k = A0 at hexp2 ⊢
    omega
  rw [harg, hbs (j' / p + t * k)]
  push_cast
  ring

theorem const (p : ℕ) (c : ℤ) : AffineOnResiduesAtZ p (fun _ => c) :=
  ⟨0, fun _ _ => ⟨c, 0, fun _ => by ring⟩⟩

theorem add {p : ℕ} (hp : 1 ≤ p) {F G : ℕ → ℤ}
    (hF : AffineOnResiduesAtZ p F) (hG : AffineOnResiduesAtZ p G) :
    AffineOnResiduesAtZ p (fun n => F n + G n) := by
  obtain ⟨mF, hmF⟩ := hF.exists_rebase hp
  obtain ⟨mG, hmG⟩ := hG.exists_rebase hp
  refine ⟨max mF mG, fun j hj => ?_⟩
  obtain ⟨bF, sF, hbsF⟩ := hmF (max mF mG) (le_max_left _ _) j hj
  obtain ⟨bG, sG, hbsG⟩ := hmG (max mF mG) (le_max_right _ _) j hj
  refine ⟨bF + bG, sF + sG, fun k => ?_⟩
  show F (max mF mG + j + p * k) + G (max mF mG + j + p * k) = _
  rw [hbsF k, hbsG k]
  ring

theorem sub {p : ℕ} (hp : 1 ≤ p) {F G : ℕ → ℤ}
    (hF : AffineOnResiduesAtZ p F) (hG : AffineOnResiduesAtZ p G) :
    AffineOnResiduesAtZ p (fun n => F n - G n) := by
  obtain ⟨mF, hmF⟩ := hF.exists_rebase hp
  obtain ⟨mG, hmG⟩ := hG.exists_rebase hp
  refine ⟨max mF mG, fun j hj => ?_⟩
  obtain ⟨bF, sF, hbsF⟩ := hmF (max mF mG) (le_max_left _ _) j hj
  obtain ⟨bG, sG, hbsG⟩ := hmG (max mF mG) (le_max_right _ _) j hj
  refine ⟨bF - bG, sF - sG, fun k => ?_⟩
  show F (max mF mG + j + p * k) - G (max mF mG + j + p * k) = _
  rw [hbsF k, hbsG k]
  ring

theorem smul {p : ℕ} (c : ℤ) {F : ℕ → ℤ} (hF : AffineOnResiduesAtZ p F) :
    AffineOnResiduesAtZ p (fun n => c * F n) := by
  obtain ⟨m, hm⟩ := hF
  refine ⟨m, fun j hj => ?_⟩
  obtain ⟨b, s, hbs⟩ := hm j hj
  refine ⟨c * b, c * s, fun k => ?_⟩
  show c * F (m + j + p * k) = _
  rw [hbs k]
  ring

theorem natCast {p : ℕ} {f : ℕ → ℕ}
    (h : SlicePeriodStar.AffineOnResiduesAt p f) :
    AffineOnResiduesAtZ p (fun n => (f n : ℤ)) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun j hj => ?_⟩
  obtain ⟨b, s, hbs⟩ := hm j hj
  refine ⟨(b : ℤ), (s : ℤ), fun k => ?_⟩
  show ((f (m + j + p * k) : ℤ)) = _
  rw [hbs k]
  push_cast
  ring

/-- **The recurrence bridge**: a global-slope recurrence beyond a threshold is
pinned-affine at the SAME period — how `dstar_setup_fibred`'s `Rcell`/`Bcell`
slope clauses enter the pinned algebra. -/
theorem of_recurrence {p : ℕ} (_hp : 1 ≤ p) {F : ℕ → ℤ} {m : ℕ} {S : ℤ}
    (h : ∀ n, m ≤ n → F (n + p) = F n + S) : AffineOnResiduesAtZ p F := by
  refine ⟨m, fun j hj => ⟨F (m + j), S, fun k => ?_⟩⟩
  induction k with
  | zero => simp
  | succ k ih =>
      have harg : m + j + p * (k + 1) = (m + j + p * k) + p := by ring
      have hk : m ≤ m + j + p * k := by
        generalize p * k = A
        omega
      rw [harg, h _ hk, ih]
      push_cast
      ring

end AffineOnResiduesAtZ

/-! ## Classwise tools -/

/-- An eventually-periodic predicate is CONSTANT along every class tail. -/
theorem EP_class_const {Pr : ℕ → Prop} {p : ℕ}
    (hEP : SliceOrder.EventuallyPeriodic Pr p) :
    ∃ M, ∀ n, M ≤ n → ∀ k, (Pr (n + p * k) ↔ Pr n) := by
  obtain ⟨M, hM⟩ := hEP
  refine ⟨M, fun n hn k => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc]
      exact (hM (n + p * k) (le_trans hn (Nat.le_add_right n (p * k)))).trans ih

/-- Classwise eventual constancy at period `p` IS eventual periodicity at `p`. -/
theorem EP_of_classwise_eventually_const {Pr : ℕ → Prop} (m p : ℕ) (hp : 1 ≤ p)
    (h : ∀ j : Fin p, ∃ (K : ℕ) (Q : Prop), ∀ k, K ≤ k →
      (Pr (m + j.val + p * k) ↔ Q)) :
    SliceOrder.EventuallyPeriodic Pr p := by
  classical
  choose K Q hK using h
  set KS : ℕ := Finset.univ.sup K with hKS
  set PK : ℕ := p * KS with hPK
  refine ⟨m + PK + p, fun n hn => ?_⟩
  set j0 : ℕ := (n - m) % p with hj0def
  set k0 : ℕ := (n - m) / p with hk0def
  have hj0 : j0 < p := Nat.mod_lt _ (by omega)
  have hdm : p * k0 + j0 = n - m := Nat.div_add_mod (n - m) p
  have hk0 : KS ≤ k0 := by
    rw [hk0def, Nat.le_div_iff_mul_le (by omega : 0 < p), Nat.mul_comm]
    show PK ≤ n - m
    omega
  have hKj : K ⟨j0, hj0⟩ ≤ k0 :=
    le_trans (Finset.le_sup (Finset.mem_univ _)) hk0
  set Pk : ℕ := p * k0 with hPkdef
  have hn0 : n = m + j0 + Pk := by omega
  have hsucc : p * (k0 + 1) = Pk + p := by
    rw [Nat.mul_succ, ← hPkdef]
  have hQn : Pr n ↔ Q ⟨j0, hj0⟩ := by
    have hk := hK ⟨j0, hj0⟩ k0 hKj
    have harg : m + (⟨j0, hj0⟩ : Fin p).val + p * k0 = n := by
      show m + j0 + Pk = n
      omega
    rwa [harg] at hk
  have hQnp : Pr (n + p) ↔ Q ⟨j0, hj0⟩ := by
    have hk := hK ⟨j0, hj0⟩ (k0 + 1) (by omega)
    have harg : m + (⟨j0, hj0⟩ : Fin p).val + p * (k0 + 1) = n + p := by
      show m + j0 + p * (k0 + 1) = n + p
      rw [hsucc]
      omega
    rwa [harg] at hk
  exact hQnp.trans hQn.symm

end CopiedAffineAt

/-! ## ℕ-side pinned combinators (dot-notation extensions) -/

namespace SlicePeriodStar.AffineOnResiduesAt

open SlicePeriodStar

/-- Rebase: class data from every base past the threshold (ℕ side). -/
theorem exists_rebase {p : ℕ} (hp : 1 ≤ p) {f : ℕ → ℕ}
    (h : AffineOnResiduesAt p f) :
    ∃ m : ℕ, ∀ m', m ≤ m' → ∀ j, j < p →
      ∃ b s : ℕ, ∀ k : ℕ, f (m' + j + p * k) = b + k * s := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun m' hm' j hj => ?_⟩
  set j' : ℕ := (m' + j - m) % p with hj'
  set k' : ℕ := (m' + j - m) / p with hk'
  have hj'lt : j' < p := Nat.mod_lt _ (by omega)
  obtain ⟨b, s, hbs⟩ := hm j' hj'lt
  refine ⟨b + k' * s, s, fun k => ?_⟩
  have hdm : p * k' + j' = m' + j - m := Nat.div_add_mod (m' + j - m) p
  have hsplit : p * (k' + k) = p * k' + p * k := Nat.mul_add p k' k
  have harg : m' + j + p * k = m + j' + p * (k' + k) := by
    generalize hA1 : p * k' = A1 at hdm hsplit
    generalize hA2 : p * k = A2 at hsplit ⊢
    generalize hA3 : p * (k' + k) = A3 at hsplit ⊢
    omega
  rw [harg, hbs (k' + k)]
  ring

theorem const (p c : ℕ) : AffineOnResiduesAt p (fun _ => c) :=
  ⟨0, fun _ _ => ⟨c, 0, fun _ => by ring⟩⟩

theorem congr' {p : ℕ} {f g : ℕ → ℕ} (hfg : ∀ n, f n = g n)
    (h : AffineOnResiduesAt p f) : AffineOnResiduesAt p g := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun j hj => ?_⟩
  obtain ⟨b, s, hbs⟩ := hm j hj
  exact ⟨b, s, fun k => by rw [← hfg]; exact hbs k⟩

theorem add {p : ℕ} (hp : 1 ≤ p) {f g : ℕ → ℕ}
    (hf : AffineOnResiduesAt p f) (hg : AffineOnResiduesAt p g) :
    AffineOnResiduesAt p (fun n => f n + g n) := by
  obtain ⟨mf, hmf⟩ := hf.exists_rebase hp
  obtain ⟨mg, hmg⟩ := hg.exists_rebase hp
  refine ⟨max mf mg, fun j hj => ?_⟩
  obtain ⟨bf, sf, hbsf⟩ := hmf (max mf mg) (le_max_left _ _) j hj
  obtain ⟨bg, sg, hbsg⟩ := hmg (max mf mg) (le_max_right _ _) j hj
  refine ⟨bf + bg, sf + sg, fun k => ?_⟩
  show f (max mf mg + j + p * k) + g (max mf mg + j + p * k) = _
  rw [hbsf k, hbsg k]
  ring

/-- **Index-size-blind finite sums**: a SHARED pinned period in, the SAME
period out (per-`mS` index sets are harmless — they touch thresholds and
slopes only). -/
theorem finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℕ) {p : ℕ}
    (hp : 1 ≤ p) (h : ∀ i ∈ s, AffineOnResiduesAt p (f i)) :
    AffineOnResiduesAt p (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun j _ => ⟨0, 0, fun k => by simp⟩⟩
  | @insert a s ha ih =>
      exact congr' (fun n => (Finset.sum_insert ha).symm)
        (add hp (h a (Finset.mem_insert_self a s))
          (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))))

/-- **Eventually-periodic selection**: composing a shared-period family with
an eventually-periodic selector keeps the pinned period (the selector is
constant along every class tail). -/
theorem select {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℕ) (sel : ℕ → ι)
    (p : ℕ) (hp : 1 ≤ p) (hf : ∀ i ∈ s, AffineOnResiduesAt p (f i))
    (hmem : ∀ n, sel n ∈ s)
    (hEP : ∀ i ∈ s, SliceOrder.EventuallyPeriodic (fun n => sel n = i) p) :
    AffineOnResiduesAt p (fun n => f (sel n) n) := by
  classical
  choose Mi hMi using fun (i : ι) (hi : i ∈ s) =>
    CopiedAffineAt.EP_class_const (hEP i hi)
  choose mi hmi using fun (i : ι) (hi : i ∈ s) =>
    (hf i hi).exists_rebase hp
  set M : ℕ := (s.attach.sup (fun i => Mi i.1 i.2))
    ⊔ (s.attach.sup (fun i => mi i.1 i.2)) with hM
  refine ⟨M, fun j hj => ?_⟩
  set i0 : ι := sel (M + j) with hi0
  have hi0s : i0 ∈ s := hmem (M + j)
  have hMi0 : Mi i0 hi0s ≤ M + j := by
    have h1 : Mi i0 hi0s ≤ s.attach.sup (fun i => Mi i.1 i.2) :=
      Finset.le_sup (f := fun i => Mi i.1 i.2) (Finset.mem_attach s ⟨i0, hi0s⟩)
    omega
  have hmi0 : mi i0 hi0s ≤ M + j := by
    have h1 : mi i0 hi0s ≤ s.attach.sup (fun i => mi i.1 i.2) :=
      Finset.le_sup (f := fun i => mi i.1 i.2) (Finset.mem_attach s ⟨i0, hi0s⟩)
    omega
  have hsel_const : ∀ k, sel (M + j + p * k) = i0 := by
    intro k
    have hbit := hMi i0 hi0s (M + j) hMi0 k
    exact hbit.mpr rfl
  obtain ⟨b, sl, hbs⟩ := hmi i0 hi0s (M + j) hmi0 0 (by omega)
  refine ⟨b, sl, fun k => ?_⟩
  show f (sel (M + j + p * k)) (M + j + p * k) = b + k * sl
  rw [hsel_const k]
  have harg : M + j + p * k = M + j + 0 + p * k := by
    generalize p * k = A
    omega
  rw [harg]
  exact hbs k

/-- **Rebase above a floor**: pinned class data re-anchored at a base `≥ N0`
(slopes preserved, intercepts absorbed) — the Stage G bridge to `RowAffine`. -/
theorem rebase {p : ℕ} (hp : 1 ≤ p) {f : ℕ → ℕ}
    (h : AffineOnResiduesAt p f) (N0 : ℕ) :
    ∃ N, N0 ≤ N ∧ ∀ j, j < p → ∃ b s : ℕ, ∀ k, f (N + j + p * k) = b + k * s := by
  obtain ⟨m, hm⟩ := h.exists_rebase hp
  exact ⟨max m N0, le_max_right _ _, hm (max m N0) (le_max_left _ _)⟩

/-- The pinned shape implies the unpinned `AffineOnResidues` (period
forgotten — consumers off the period path only). -/
theorem toAffine {p : ℕ} (hp : 1 ≤ p) {f : ℕ → ℕ}
    (h : AffineOnResiduesAt p f) : SliceAffine.AffineOnResidues f := by
  classical
  have hp0 : 0 < p := hp
  obtain ⟨m, hm⟩ := h
  choose b s hbs using hm
  refine ⟨m, p, fun r => s (r % p) (Nat.mod_lt _ hp0), hp, fun r k => ?_⟩
  simp only []
  have hdm : p * (r / p) + r % p = r := Nat.div_add_mod r p
  have hsplit : p * (r / p + k) = p * (r / p) + p * k := Nat.mul_add p (r / p) k
  have harg1 : m + r + p * k = m + r % p + p * (r / p + k) := by
    generalize hA1 : p * (r / p) = A1 at hdm hsplit
    generalize hA2 : p * k = A2 at hsplit ⊢
    generalize hA3 : p * (r / p + k) = A3 at hsplit ⊢
    omega
  have harg0 : m + r = m + r % p + p * (r / p) := by
    generalize hA1 : p * (r / p) = A1 at hdm ⊢
    omega
  have hb1 := hbs (r % p) (Nat.mod_lt _ hp0) (r / p + k)
  have hb0 := hbs (r % p) (Nat.mod_lt _ hp0) (r / p)
  rw [harg1, harg0, hb1, hb0]
  ring

end SlicePeriodStar.AffineOnResiduesAt

namespace CopiedAffineAt

open SlicePeriodStar

/-- The indicator of an eventually-periodic predicate is pinned-affine at the
same period (slopes `0`). -/
theorem affineOnResiduesAt_indicator_of_EP {Pr : ℕ → Prop} [DecidablePred Pr]
    {p : ℕ} (_hp : 1 ≤ p) (hEP : SliceOrder.EventuallyPeriodic Pr p) :
    AffineOnResiduesAt p (fun n => if Pr n then 1 else 0) := by
  obtain ⟨M, hM⟩ := EP_class_const hEP
  refine ⟨M, fun j hj => ?_⟩
  refine ⟨if Pr (M + j) then 1 else 0, 0, fun k => ?_⟩
  show (if Pr (M + j + p * k) then 1 else 0) = (if Pr (M + j) then 1 else 0) + k * 0
  have hbit := hM (M + j) (by omega) k
  by_cases h : Pr (M + j)
  · rw [if_pos (hbit.mpr h), if_pos h]
    omega
  · rw [if_neg (fun hc => h (hbit.mp hc)), if_neg h]
    omega

/-- `n ↦ (n − c) / p` is pinned-affine at `p` (slope `1` per class beyond `c`). -/
theorem affineOnResiduesAt_natSubDiv (c p : ℕ) (hp : 1 ≤ p) :
    AffineOnResiduesAt p (fun n => (n - c) / p) := by
  have hp0 : 0 < p := hp
  refine ⟨c, fun j hj => ⟨j / p, 1, fun k => ?_⟩⟩
  show (c + j + p * k - c) / p = j / p + k * 1
  have harg : c + j + p * k - c = j + p * k := by
    generalize p * k = A
    omega
  rw [harg, Nat.add_mul_div_left j k hp0]
  ring

/-! ## Pinned comparison eventual periodicities -/

open AffineOnResiduesAtZ in
/-- Scalar `<` between two pinned-affine families is eventually periodic AT
the shared period (per class both sides are exactly affine, so the verdict is
eventually constant). -/
theorem lt_EP_at {p : ℕ} (hp : 1 ≤ p) {F G : ℕ → ℤ}
    (hF : AffineOnResiduesAtZ p F) (hG : AffineOnResiduesAtZ p G) :
    SliceOrder.EventuallyPeriodic (fun n => F n < G n) p := by
  obtain ⟨mF, hmF⟩ := hF.exists_rebase hp
  obtain ⟨mG, hmG⟩ := hG.exists_rebase hp
  refine EP_of_classwise_eventually_const (max mF mG) p hp (fun j => ?_)
  obtain ⟨bF, sF, hbsF⟩ := hmF (max mF mG) (le_max_left _ _) j.val j.isLt
  obtain ⟨bG, sG, hbsG⟩ := hmG (max mF mG) (le_max_right _ _) j.val j.isLt
  by_cases hs : sF = sG
  · refine ⟨0, bF < bG, fun k _ => ?_⟩
    rw [hbsF k, hbsG k, hs]
    constructor
    · intro h; omega
    · intro h; omega
  · refine ⟨((bF - bG).natAbs + 1), sF < sG, fun k hk => ?_⟩
    rw [hbsF k, hbsG k]
    have habs : (bF - bG) ≤ ((bF - bG).natAbs : ℤ)
        ∧ (bG - bF) ≤ ((bF - bG).natAbs : ℤ) := by
      constructor <;> [exact Int.le_natAbs; ·
        rw [← Int.natAbs_neg, neg_sub]; exact Int.le_natAbs]
    have hkZ : ((bF - bG).natAbs : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast hk
    constructor
    · intro h
      by_contra hge
      push Not at hge
      have hsg : sG + 1 ≤ sF := by omega
      nlinarith [hkZ, habs.1, habs.2]
    · intro h
      have hsg : sF + 1 ≤ sG := by omega
      nlinarith [hkZ, habs.1, habs.2]

/-- Scalar `=` between two pinned-affine families is eventually periodic AT
the shared period. -/
theorem eq_EP_at {p : ℕ} (hp : 1 ≤ p) {F G : ℕ → ℤ}
    (hF : AffineOnResiduesAtZ p F) (hG : AffineOnResiduesAtZ p G) :
    SliceOrder.EventuallyPeriodic (fun n => F n = G n) p := by
  obtain ⟨mF, hmF⟩ := hF.exists_rebase hp
  obtain ⟨mG, hmG⟩ := hG.exists_rebase hp
  refine EP_of_classwise_eventually_const (max mF mG) p hp (fun j => ?_)
  obtain ⟨bF, sF, hbsF⟩ := hmF (max mF mG) (le_max_left _ _) j.val j.isLt
  obtain ⟨bG, sG, hbsG⟩ := hmG (max mF mG) (le_max_right _ _) j.val j.isLt
  by_cases hs : sF = sG
  · refine ⟨0, bF = bG, fun k _ => ?_⟩
    rw [hbsF k, hbsG k, hs]
    constructor
    · intro h; omega
    · intro h; omega
  · refine ⟨((bF - bG).natAbs + 1), False, fun k hk => ?_⟩
    rw [hbsF k, hbsG k]
    have habs : (bF - bG) ≤ ((bF - bG).natAbs : ℤ)
        ∧ (bG - bF) ≤ ((bF - bG).natAbs : ℤ) := by
      constructor <;> [exact Int.le_natAbs; ·
        rw [← Int.natAbs_neg, neg_sub]; exact Int.le_natAbs]
    have hkZ : ((bF - bG).natAbs : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast hk
    constructor
    · intro h
      rcases lt_or_gt_of_ne (fun hc : sF = sG => hs hc) with hlt | hgt
      · have : sF + 1 ≤ sG := by omega
        nlinarith [hkZ, habs.1, habs.2]
      · have : sG + 1 ≤ sF := by omega
        nlinarith [hkZ, habs.1, habs.2]
    · intro h
      exact absurd h (fun hc => hc.elim)

/-- Vector equality of pinned-affine families is eventually periodic AT the
shared period. -/
theorem vec_eq_EP_at {d : ℕ} {p : ℕ} (hp : 1 ≤ p) {F G : ℕ → Fin d → ℤ}
    (hF : ∀ i, AffineOnResiduesAtZ p (fun n => F n i))
    (hG : ∀ i, AffineOnResiduesAtZ p (fun n => G n i)) :
    SliceOrder.EventuallyPeriodic (fun n => F n = G n) p := by
  have hcoord : ∀ i : Fin d,
      SliceOrder.EventuallyPeriodic (fun n => F n i = G n i) p :=
    fun i => eq_EP_at hp (hF i) (hG i)
  have hall := SliceOrder.EventuallyPeriodic.finset_and
    (Finset.univ : Finset (Fin d)) (fun i n => F n i = G n i) p
    (fun i _ => hcoord i)
  refine hall.congr (fun n => ?_)
  constructor
  · intro h
    funext i
    exact h i (Finset.mem_univ i)
  · intro h i _
    rw [h]

/-- Lexicographic comparison of pinned-affine vector families is eventually
periodic AT the shared period (classes pre-aligned — no period products). -/
theorem lexLt_EP_at {d : ℕ} {p : ℕ} (hp : 1 ≤ p) {F G : ℕ → Fin d → ℤ}
    (hF : ∀ i, AffineOnResiduesAtZ p (fun n => F n i))
    (hG : ∀ i, AffineOnResiduesAtZ p (fun n => G n i)) :
    SliceOrder.EventuallyPeriodic (fun n => WRP.lexLt (F n) (G n)) p := by
  have hreify : ∀ n, WRP.lexLt (F n) (G n) ↔
      ∃ i ∈ (Finset.univ : Finset (Fin d)),
        (∀ j ∈ Finset.univ.filter (fun j => j < i), F n j = G n j)
          ∧ F n i < G n i := by
    intro n
    unfold WRP.lexLt
    constructor
    · rintro ⟨i, hlt, hlti⟩
      exact ⟨i, Finset.mem_univ i, fun j hj => hlt j (Finset.mem_filter.mp hj).2,
        hlti⟩
    · rintro ⟨i, _, hlt, hlti⟩
      exact ⟨i, fun j hj => hlt j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩),
        hlti⟩
  refine (SliceOrder.EventuallyPeriodic.finset_or
    (Finset.univ : Finset (Fin d))
    (fun i n => (∀ j ∈ Finset.univ.filter (fun j => j < i), F n j = G n j)
      ∧ F n i < G n i) p (fun i _ => ?_)).congr (fun n => (hreify n).symm)
  refine SliceOrder.EventuallyPeriodic.and ?_ (lt_EP_at hp (hF i) (hG i))
  exact SliceOrder.EventuallyPeriodic.finset_and _
    (fun j n => F n j = G n j) p (fun j _ => eq_EP_at hp (hF j) (hG j))

/-! ## Gated combinators at the pinned period -/

namespace AffineOnResiduesAtZ

theorem congr' {p : ℕ} {F G : ℕ → ℤ} (hFG : ∀ n, F n = G n)
    (h : AffineOnResiduesAtZ p F) : AffineOnResiduesAtZ p G := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun j hj => ?_⟩
  obtain ⟨b, s, hbs⟩ := hm j hj
  exact ⟨b, s, fun k => by rw [← hFG]; exact hbs k⟩

end AffineOnResiduesAtZ

/-- A gate-selected branch of two pinned-affine families is pinned-affine at
the shared period (the gate bit is constant along every class tail). -/
theorem affineOnResiduesAtZ_ite_of_EP {p : ℕ} (hp : 1 ≤ p) {Pr : ℕ → Prop}
    [DecidablePred Pr] (hEP : SliceOrder.EventuallyPeriodic Pr p)
    {A B : ℕ → ℤ} (hA : AffineOnResiduesAtZ p A) (hB : AffineOnResiduesAtZ p B) :
    AffineOnResiduesAtZ p (fun n => if Pr n then A n else B n) := by
  obtain ⟨M, hM⟩ := EP_class_const hEP
  obtain ⟨mA, hmA⟩ := hA.exists_rebase hp
  obtain ⟨mB, hmB⟩ := hB.exists_rebase hp
  refine ⟨max M (max mA mB), fun j hj => ?_⟩
  obtain ⟨bA, sA, hbsA⟩ := hmA _
    (le_trans (le_max_left mA mB) (le_max_right M _)) j hj
  obtain ⟨bB, sB, hbsB⟩ := hmB _
    (le_trans (le_max_right mA mB) (le_max_right M _)) j hj
  have hMle : M ≤ max M (max mA mB) + j :=
    le_trans (le_max_left _ _) (Nat.le_add_right _ j)
  by_cases h : Pr (max M (max mA mB) + j)
  · refine ⟨bA, sA, fun k => ?_⟩
    show (if Pr (max M (max mA mB) + j + p * k)
        then A (max M (max mA mB) + j + p * k)
        else B (max M (max mA mB) + j + p * k)) = _
    rw [if_pos ((hM _ hMle k).mpr h)]
    exact hbsA k
  · refine ⟨bB, sB, fun k => ?_⟩
    show (if Pr (max M (max mA mB) + j + p * k)
        then A (max M (max mA mB) + j + p * k)
        else B (max M (max mA mB) + j + p * k)) = _
    rw [if_neg (fun hc => h ((hM _ hMle k).mp hc))]
    exact hbsB k

/-- The running maximum of a list of pinned-affine families is pinned-affine
at the shared period. -/
theorem affineOnResiduesAtZ_listMax {p : ℕ} (hp : 1 ≤ p)
    (l : List (ℕ → ℤ)) (h : ∀ f ∈ l, AffineOnResiduesAtZ p f) :
    AffineOnResiduesAtZ p (fun n => (l.map (fun f => f n)).foldr max 0) := by
  classical
  induction l with
  | nil =>
      exact AffineOnResiduesAtZ.const p 0
  | cons f l ih =>
      have hf := h f List.mem_cons_self
      have hR := ih (fun g hg => h g (List.mem_cons_of_mem f hg))
      have hEP : SliceOrder.EventuallyPeriodic
          (fun n => f n ≤ (l.map (fun g => g n)).foldr max 0) p := by
        have hlt := lt_EP_at hp hR hf
        obtain ⟨M, hM⟩ := SliceDstarCore.EP_not hlt
        exact ⟨M, fun n hn => by
          have h2 := hM n hn
          simp only [] at h2
          rw [not_lt, not_lt] at h2
          exact h2⟩
      refine AffineOnResiduesAtZ.congr' (fun n => ?_)
        (affineOnResiduesAtZ_ite_of_EP hp hEP hR hf)
      show (if f n ≤ (l.map (fun g => g n)).foldr max 0
          then (l.map (fun g => g n)).foldr max 0 else f n)
        = ((f :: l).map (fun g => g n)).foldr max 0
      rw [List.map_cons, List.foldr_cons]
      by_cases hc : f n ≤ (l.map (fun g => g n)).foldr max 0
      · rw [if_pos hc, max_eq_right hc]
      · rw [if_neg hc, max_eq_left (le_of_lt (not_le.mp hc))]

/-! ## The pinned lexMin layer -/

open SliceDstarCore

/-- Each coordinate of `lexMin2` of pinned-affine families is pinned-affine
at the shared period (the comparison gate is `lexLt_EP_at`). -/
theorem lexMin2_coord_affine {d : ℕ} {p : ℕ} (hp : 1 ≤ p)
    {F G : ℕ → Fin d → ℤ}
    (hF : ∀ i, AffineOnResiduesAtZ p (fun n => F n i))
    (hG : ∀ i, AffineOnResiduesAtZ p (fun n => G n i)) (i : Fin d) :
    AffineOnResiduesAtZ p (fun n => lexMin2 F G n i) := by
  classical
  have hEP := lexLt_EP_at hp hF hG
  refine AffineOnResiduesAtZ.congr' (fun n => ?_)
    (affineOnResiduesAtZ_ite_of_EP hp hEP (hF i) (hG i))
  show (if WRP.lexLt (F n) (G n) then F n i else G n i) = lexMin2 F G n i
  unfold lexMin2
  by_cases hc : WRP.lexLt (F n) (G n)
  · rw [if_pos hc]
  · rw [if_neg hc]

/-- **Each coordinate of the running lexMin of pinned-affine families is
pinned-affine at the shared period** — the pairwise comparison gates are
derived, not hypothesised. -/
theorem lexMinList_coord_affineOnResiduesAtZ {d : ℕ}
    (Fs : List (ℕ → Fin d → ℤ)) {p : ℕ} (hp : 1 ≤ p)
    (haff : ∀ F ∈ Fs, ∀ i, AffineOnResiduesAtZ p (fun n => F n i)) :
    ∀ i : Fin d, AffineOnResiduesAtZ p (fun n => lexMinList Fs n i) := by
  induction Fs with
  | nil =>
      intro i
      exact AffineOnResiduesAtZ.const p 0
  | cons F rest ih =>
      cases rest with
      | nil =>
          intro i
          exact haff F List.mem_cons_self i
      | cons G rest' =>
          intro i
          have hF := haff F List.mem_cons_self
          have hR := ih (fun F' hF' i' =>
            haff F' (List.mem_cons_of_mem F hF') i')
          show AffineOnResiduesAtZ p
            (fun n => lexMin2 F (lexMinList (G :: rest')) n i)
          exact lexMin2_coord_affine hp hF hR i

open scoped Classical in
/-- **The gated lexMin at the pinned period**: candidates masked to a
dominating `BIG` family by eventually-periodic gates — the pinned replacement
for the wrapped `gated_lexMin_affine` (whose output period was an opaque
existential). -/
theorem gated_lexMin_affine_at {d : ℕ} {p : ℕ} (hp : 1 ≤ p)
    (cands : List ((ℕ → Prop) × (ℕ → Fin d → ℤ)))
    (hgate : ∀ gf ∈ cands, SliceOrder.EventuallyPeriodic gf.1 p)
    (haff : ∀ gf ∈ cands, ∀ i, AffineOnResiduesAtZ p (fun n => gf.2 n i))
    (BIG : ℕ → Fin d → ℤ)
    (hBIGaff : ∀ i, AffineOnResiduesAtZ p (fun n => BIG n i)) (i : Fin d) :
    AffineOnResiduesAtZ p (fun n => lexMinList
      (BIG :: cands.map (fun gf => fun n =>
        if gf.1 n then gf.2 n else BIG n)) n i) := by
  classical
  refine lexMinList_coord_affineOnResiduesAtZ _ hp (fun F hF i' => ?_) i
  rcases List.mem_cons.mp hF with rfl | hF
  · exact hBIGaff i'
  · rw [List.mem_map] at hF
    obtain ⟨gf, hgf, rfl⟩ := hF
    refine AffineOnResiduesAtZ.congr' (fun n => ?_)
      (affineOnResiduesAtZ_ite_of_EP hp (hgate gf hgf)
        (haff gf hgf i') (hBIGaff i'))
    show (if gf.1 n then gf.2 n i' else BIG n i')
      = (fun n => if gf.1 n then gf.2 n else BIG n) n i'
    by_cases hc : gf.1 n
    · rw [if_pos hc]
      show gf.2 n i' = (if gf.1 n then gf.2 n else BIG n) i'
      rw [if_pos hc]
    · rw [if_neg hc]
      show BIG n i' = (if gf.1 n then gf.2 n else BIG n) i'
      rw [if_neg hc]

end CopiedAffineAt
