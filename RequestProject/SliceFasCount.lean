/-
# The `fas` count assembly: joining the MSO selection gate with the rank lex-below count

The rank-comparison count (`SliceLexCount.countLexL` / `countLexL_residue`) counts loop
indices whose rank is `≺`-below a moving threshold.  `fas` counts only the **selected**
`U`-atoms below the threshold, so the rank count must be intersected with the MSO
selection gate — which, on the slice, has the forward/backward convolution shape of
`SliceCountSlice` (`selected(j,n)` is a function of the forward iterate `bF^[j] qpre` and
the backward iterate `bF^[n-1-j]`, both eventually periodic).

This file builds that join.  It starts with the reusable boundary-term tool
`affineOnResidues_indicator_of_EP` (an eventually-periodic predicate has an
`AffineOnResidues` indicator), which the convolution's two boundary regions need.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`): this assembly is purely
arithmetic; the MSO selection (which needs `SliceMSO.buchi`) enters elsewhere.
-/
import RequestProject.SliceLexCount
import RequestProject.SliceOrder
import RequestProject.SliceGatedConv
import RequestProject.SliceCountSlice
import RequestProject.SliceRankBlock

namespace SliceFasCount

open SliceThreshold SliceAffine SliceOrder
open SliceCount MSOMark SliceMSO Step
open scoped Classical

/-- **Eventually-periodic predicate ⇒ `AffineOnResidues` indicator.**  If `Pr` is
eventually periodic with period `p`, its `{0,1}` indicator is affine on residue classes
(constant per class beyond the threshold).  This is the tool the convolution boundary
terms (and the `d*`-existence / domain gates) reduce to. -/
theorem affineOnResidues_indicator_of_EP {Pr : ℕ → Prop} {p : ℕ} (hp : 1 ≤ p)
    (h : EventuallyPeriodic Pr p) : AffineOnResidues (fun n => if Pr n then 1 else 0) := by
  obtain ⟨m, hm⟩ := h
  refine affineOnResidues_of_period (m := m) (p := p) (fun _ => 0) hp ?_
  intro r _ k
  show (if Pr (m + r + p * k) then 1 else 0) = (if Pr (m + r) then 1 else 0) + k * 0
  rw [Nat.mul_zero, Nat.add_zero]
  have hiff : ∀ k, (Pr (m + r + p * k) ↔ Pr (m + r)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [show m + r + p * (k + 1) = (m + r + p * k) + p from by ring, hm _ (by omega)]
        exact ih
  exact if_congr (hiff k) rfl rfl

/-- Iterating the `AffineOnResidues` recurrence: beyond the threshold, `f(x+p·t) = f x +
t·s((x-m)%p)`. -/
theorem affineOnResidues_iterate {f : ℕ → ℕ} (hf : AffineOnResidues f) :
    ∃ (m p : ℕ) (s : ℕ → ℕ), 1 ≤ p ∧ ∀ x t, m ≤ x → f (x + p * t) = f x + t * s ((x - m) % p) := by
  obtain ⟨m, p, s, hp, hrec⟩ := hf
  refine ⟨m, p, s, hp, fun x t hx => ?_⟩
  set r := (x - m) % p with hr
  set q := (x - m) / p with hq
  have hxform : x = m + r + p * q := by have := Nat.div_add_mod (x - m) p; rw [hr, hq]; omega
  have e1 : f (x + p * t) = f (m + r) + (q + t) * s r := by
    rw [show x + p * t = m + r + p * (q + t) from by rw [hxform]; ring, hrec r (q + t)]
  have e2 : f x = f (m + r) + q * s r := by rw [hxform, hrec r q]
  rw [e1, e2]; ring

/-- **The final discharge glue.**  Two `AffineOnResidues` sequences `fas`, `tailU` give a
common-period period-index-affine pair witness — the exact shape
`SliceSemilinear.isSemilinear2_of_affineInPeriod` (hence the axiom) consumes. -/
theorem pair_affineOnResidues_glue {fas tailU : ℕ → ℕ}
    (hF : AffineOnResidues fas) (hT : AffineOnResidues tailU) :
    ∃ p m : ℕ, 1 ≤ p ∧ 1 ≤ m ∧ ∀ j, j < p → ∃ b₁ s₁ b₂ s₂ : ℕ,
      ∀ k, (fas (m + j + p * k), tailU (m + j + p * k)) = (b₁ + k * s₁, b₂ + k * s₂) := by
  obtain ⟨mF, pF, sF, hpF, hiterF⟩ := affineOnResidues_iterate hF
  obtain ⟨mT, pT, sT, hpT, hiterT⟩ := affineOnResidues_iterate hT
  set m := max 1 (max mF mT) with hmdef
  have hmF : mF ≤ m := le_trans (le_trans (le_max_left mF mT) (le_max_right 1 _)) (le_refl m)
  have hmT : mT ≤ m := le_trans (le_trans (le_max_right mF mT) (le_max_right 1 _)) (le_refl m)
  refine ⟨pF * pT, m, Nat.mul_pos hpF hpT, le_trans (le_max_left 1 _) (le_refl m),
    fun j _ => ⟨fas (m + j), pT * sF ((m + j - mF) % pF), tailU (m + j),
      pF * sT ((m + j - mT) % pT), fun k => ?_⟩⟩
  have hxF : mF ≤ m + j := le_trans hmF (Nat.le_add_right m j)
  have hxT : mT ≤ m + j := le_trans hmT (Nat.le_add_right m j)
  have eF : fas (m + j + pF * pT * k) = fas (m + j) + k * (pT * sF ((m + j - mF) % pF)) := by
    rw [show m + j + pF * pT * k = (m + j) + pF * (pT * k) from by ring, hiterF (m + j) (pT * k) hxF]
    ring
  have eT : tailU (m + j + pF * pT * k) = tailU (m + j) + k * (pF * sT ((m + j - mT) % pT)) := by
    rw [show m + j + pF * pT * k = (m + j) + pT * (pF * k) from by ring, hiterT (m + j) (pF * k) hxT]
    ring
  rw [eF, eT]

/-- **Truncated-subtraction closure (partition form).**  If `f` and `g` are
`AffineOnResidues` and `f = g + h` pointwise (so `h = f - g` is a genuine `ℕ`-count),
then `h` is `AffineOnResidues`.  Used for `tailUCount = totalSelectedU − fasCount` (step
10): the per-residue slope of `h` is `s_f − s_g`, forced `≥ 0` because `h ≥ 0` for all `k`. -/
theorem AffineOnResidues.sub_of_partition {f g h : ℕ → ℕ} (hf : AffineOnResidues f)
    (hg : AffineOnResidues g) (hpart : ∀ n, f n = g n + h n) : AffineOnResidues h := by
  obtain ⟨mf, pf, sf, hpf, hfrec⟩ := hf
  obtain ⟨mg, pg, sg, hpg, hgrec⟩ := hg
  set m := max mf mg with hm
  refine ⟨m, pf * pg, fun r => pg * sf (m + r - mf) - pf * sg (m + r - mg),
    Nat.one_le_iff_ne_zero.mpr (by positivity), fun r k => ?_⟩
  show h (m + r + pf * pg * k) = h (m + r) + k * (pg * sf (m + r - mf) - pf * sg (m + r - mg))
  set Sf := pg * sf (m + r - mf) with hSf
  set Sg := pf * sg (m + r - mg) with hSg
  have ef : ∀ t, f (m + r + pf * pg * t) = f (m + r) + t * Sf := by
    intro t
    have hb : m + r = mf + (m + r - mf) := by omega
    rw [show m + r + pf * pg * t = mf + (m + r - mf) + pf * (pg * t) from by rw [← hb]; ring,
      hfrec (m + r - mf) (pg * t), ← hb, hSf]; ring
  have eg : ∀ t, g (m + r + pf * pg * t) = g (m + r) + t * Sg := by
    intro t
    have hb : m + r = mg + (m + r - mg) := by omega
    rw [show m + r + pf * pg * t = mg + (m + r - mg) + pg * (pf * t) from by rw [← hb]; ring,
      hgrec (m + r - mg) (pf * t), ← hb, hSg]; ring
  have hident : ∀ t, h (m + r + pf * pg * t) + t * Sg = h (m + r) + t * Sf := by
    intro t
    have e1 := hpart (m + r + pf * pg * t)
    have e2 := hpart (m + r)
    rw [ef t, eg t] at e1
    omega
  have hSgSf : Sg ≤ Sf := by
    by_contra hc
    push Not at hc
    have hk := hident (h (m + r) + 1)
    have h1 : (h (m + r) + 1) * (Sf + 1) ≤ (h (m + r) + 1) * Sg := Nat.mul_le_mul (le_refl _) hc
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega
  have hk := hident k
  have hAB : k * Sg ≤ k * Sf := Nat.mul_le_mul (le_refl k) hSgSf
  have hms : k * (Sf - Sg) = k * Sf - k * Sg := by
    rw [Nat.mul_comm k (Sf - Sg), Nat.sub_mul, Nat.mul_comm Sf k, Nat.mul_comm Sg k]
  omega

/-- Any eventually-periodic `ℕ`-sequence is `AffineOnResidues` (slope `0` per class). -/
theorem affineOnResidues_of_ev_periodic_seq {f : ℕ → ℕ} {m p : ℕ} (hp : 1 ≤ p)
    (h : ∀ n, m ≤ n → f (n + p) = f n) : AffineOnResidues f := by
  refine affineOnResidues_of_period (m := m) (p := p) (fun _ => 0) hp ?_
  intro r _ k
  show f (m + r + p * k) = f (m + r) + k * 0
  rw [Nat.mul_zero, Nat.add_zero]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show m + r + p * (k + 1) = (m + r + p * k) + p from by ring, h _ (by omega), ih]

/-- **`countPeriodicInterval`** (the linchpin kernel).  Counts loop-indices `j < n` in an
affine interval `[lo n, hi n)` whose marked-DFA gate `M.accepts (markAt W_n (1+2j))` is on,
and shows the count is `AffineOnResidues` in `n`.  Specialises the abstract gated convolution
(`SliceGatedConv.affineOnResidues_gatedConvolution`) to the slice forward iterate
`u j = bF^[j] q_pre` and backward iterate function `v m = bF^[m]`, with the marked-DFA
acceptance as the convolution bit (via `SliceCount.accepts_markAt`/`fwd_blockStart`/
`tau_blockU`).  This is the meeting point of the rank-interval clock and the MSO gate. -/
theorem countPeriodicInterval (M : DetAuto (Step × Bool)) {lo hi : ℕ → ℤ}
    (hlo : AffineOnResiduesZ lo) (hhi : AffineOnResiduesZ hi) :
    AffineOnResidues (fun n => ((Finset.range n).filter
      (fun j : ℕ => lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n
        ∧ M.accepts (markAt (wrappedFlat n) (1 + 2 * j)))).card) := by
  obtain ⟨mu, pu, hpu, hu⟩ := SliceCount.bF_iterate_eventuallyPeriodic M
  obtain ⟨mv, pv, hpv, hv⟩ := SliceCount.bF_func_iterate_eventuallyPeriodic M
  have hgc := SliceGatedConv.affineOnResidues_gatedConvolution
    (fun j => (bF M)^[j] (qpre M)) (fun m => (bF M)^[m])
    (fun q g => M.accept (fStep M (g (fStep M (M.δ q (U, true)) D)) D))
    hpu hu hpv hv hlo hhi
  refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_) hgc
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j hj
  rw [Finset.mem_range] at hj
  refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
  have hb1 : 1 + 2 * j < (wrappedFlat n).length := by rw [length_wrappedFlat]; omega
  rw [SliceCount.accepts_markAt M (wrappedFlat n) (1 + 2 * j) hb1,
    SliceCount.fwd_blockStart M n j (le_of_lt hj),
    SliceCount.wrappedFlat_getElem_U n j hj hb1, SliceCount.tau_blockU M n j hj]

/-- **`countPeriodicInterval_mod`** (residue-restricted interval kernel).  Like
`countPeriodicInterval`, but the loop-index `j` is additionally restricted to one residue class
`j % m = a` (for `1 ≤ m`).  This is the count primitive of the CORRECTED step-9 TIE route: the
residue restriction lets the tie count slice the loop index by its mod-period class — so per
class the block-`U` rank has a single per-residue slope (collinear with the affine `dstarRank`
threshold).  Specialises the abstract gated convolution to the *paired* forward iterate
`u j = (bF^[j] q_pre, j % m)` with period `pu·m`; the residue bit `(u j).2 = a` rides inside the
convolution alongside the marked-DFA acceptance, both constant per residue class. -/
theorem countPeriodicInterval_mod (M : DetAuto (Step × Bool)) (m a : ℕ) (hm : 1 ≤ m)
    {lo hi : ℕ → ℤ} (hlo : AffineOnResiduesZ lo) (hhi : AffineOnResiduesZ hi) :
    AffineOnResidues (fun n => ((Finset.range n).filter
      (fun j : ℕ => lo n ≤ (j : ℤ) ∧ (j : ℤ) < hi n ∧ j % m = a
        ∧ M.accepts (markAt (wrappedFlat n) (1 + 2 * j)))).card) := by
  obtain ⟨mu, pu, hpu, hu⟩ := SliceCount.bF_iterate_eventuallyPeriodic M
  obtain ⟨mv, pv, hpv, hv⟩ := SliceCount.bF_func_iterate_eventuallyPeriodic M
  have hu_iter : ∀ s t, mu ≤ s → (bF M)^[s + pu * t] (qpre M) = (bF M)^[s] (qpre M) := by
    intro s t hs
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, hu _ (by omega), ih]
  have hu' : ∀ i, mu ≤ i →
      ((bF M)^[i + pu * m] (qpre M), (i + pu * m) % m) = ((bF M)^[i] (qpre M), i % m) := by
    intro i hi
    refine Prod.ext (hu_iter i m hi) ?_
    show (i + pu * m) % m = i % m
    rw [Nat.mul_comm pu m, Nat.add_mul_mod_self_left]
  have hgc := SliceGatedConv.affineOnResidues_gatedConvolution
    (fun j => ((bF M)^[j] (qpre M), j % m)) (fun mm => (bF M)^[mm])
    (fun qr g => qr.2 = a ∧ M.accept (fStep M (g (fStep M (M.δ qr.1 (U, true)) D)) D))
    (Nat.mul_pos hpu hm) hu' hpv hv hlo hhi
  refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_) hgc
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  refine and_congr_right
    (fun hj => and_congr_right (fun _ => and_congr_right (fun _ => and_congr Iff.rfl ?_)))
  have hb1 : 1 + 2 * j < (wrappedFlat n).length := by rw [length_wrappedFlat]; omega
  rw [SliceCount.accepts_markAt M (wrappedFlat n) (1 + 2 * j) hb1,
    SliceCount.fwd_blockStart M n j (le_of_lt hj),
    SliceCount.wrappedFlat_getElem_U n j hj hb1, SliceCount.tau_blockU M n j hj]

/-! ## The rank-EQUALITY count (corrected TIE route, build-order steps L1–L2)

The vector rank-equality count, built by dimension augmentation onto the existing lex kernel
(`affineOnResidues_gatedEqConvolution`) plus its slice specialisation `lexEq_count_per_region`.
No reversed-lex kernel is needed.  Axiom-clean. -/

/-- `List.ofFn` of a `Fin.snoc` appends the new element to `List.ofFn` of the base. -/
theorem ofFn_snoc {α : Type*} {d : ℕ} (f : Fin d → α) (a : α) :
    List.ofFn (Fin.snoc f a) = List.ofFn f ++ [a] := by
  rw [List.ofFn_succ']
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- List-lex `lexLtL` on two equal-length lists each extended by one element:
the head comparison reduces to the original lex, with a final tie broken by `a < b`. -/
theorem lexLtL_append_singleton : ∀ (L1 L2 : List ℤ) (a b : ℤ), L1.length = L2.length →
    (SliceLexCount.lexLtL (L1 ++ [a]) (L2 ++ [b]) ↔ SliceLexCount.lexLtL L1 L2 ∨ (L1 = L2 ∧ a < b)) := by
  intro L1
  induction L1 with
  | nil =>
      intro L2 a b hlen
      cases L2 with
      | nil => simp [SliceLexCount.lexLtL]
      | cons y ys => simp at hlen
  | cons x xs ih =>
      intro L2 a b hlen
      cases L2 with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.cons_append, SliceLexCount.lexLtL, List.length_cons, Nat.add_right_cancel_iff] at hlen ⊢
          rw [ih ys a b hlen]
          constructor
          · rintro (h | ⟨he, (h | ⟨he2, hab⟩)⟩)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr ⟨he, h⟩)
            · exact Or.inr ⟨by rw [he, he2], hab⟩
          · rintro ((h | ⟨he, h⟩) | ⟨heq, hab⟩)
            · exact Or.inl h
            · exact Or.inr ⟨he, Or.inl h⟩
            · obtain ⟨rfl, rfl⟩ := List.cons.inj heq
              exact Or.inr ⟨rfl, Or.inr ⟨rfl, hab⟩⟩

/-- **`≤ₗₑₓ` via dimension augmentation.**  `snoc x 0 <ₗₑₓ snoc y 1` iff `x <ₗₑₓ y ∨ x = y`
(the `0 < 1` tie contributes the equality case). -/
theorem lexLt_snoc_le {d : ℕ} (x y : Fin d → ℤ) :
    WRP.lexLt (Fin.snoc x (0:ℤ)) (Fin.snoc y (1:ℤ)) ↔ (WRP.lexLt x y ∨ x = y) := by
  rw [SliceLexCount.lexLt_iff_lexLtL, ofFn_snoc, ofFn_snoc,
    SliceFasCount.lexLtL_append_singleton _ _ _ _ (by rw [List.length_ofFn, List.length_ofFn]),
    ← SliceLexCount.lexLt_iff_lexLtL]
  apply or_congr_right
  rw [List.ofFn_inj]
  simp

/-- **`<ₗₑₓ` via dimension augmentation.**  `snoc x 1 <ₗₑₓ snoc y 0` iff `x <ₗₑₓ y`
(the `1 < 0` tie is impossible, so no equality case). -/
theorem lexLt_snoc_lt {d : ℕ} (x y : Fin d → ℤ) :
    WRP.lexLt (Fin.snoc x (1:ℤ)) (Fin.snoc y (0:ℤ)) ↔ WRP.lexLt x y := by
  rw [SliceLexCount.lexLt_iff_lexLtL, ofFn_snoc, ofFn_snoc,
    SliceFasCount.lexLtL_append_singleton _ _ _ _ (by rw [List.length_ofFn, List.length_ofFn]),
    ← SliceLexCount.lexLt_iff_lexLtL]
  have : ¬ ((1:ℤ) < 0) := by norm_num
  simp [this]

/-- `WRP.lexLt` is irreflexive: a `lexLt`-related pair is unequal. -/
theorem lexLt_ne {d : ℕ} {x y : Fin d → ℤ} (h : WRP.lexLt x y) : x ≠ y := by
  rintro rfl
  obtain ⟨i, _, hlt⟩ := h
  exact lt_irrefl _ hlt

/-- **Equality gated convolution** (route step L1 cont.).  Counts `j < n` with the vector
rank-equality `R j = T n` AND the marked gate `b (u j) (v (n-1-j))` on; `AffineOnResidues` in `n`.
Built WITHOUT a bespoke equality kernel: by dimension augmentation, `#{R = T ∧ bit}` is
`#{R ≤ₗₑₓ T ∧ bit} − #{R <ₗₑₓ T ∧ bit}`, each a `SliceGatedConv.affineOnResidues_gatedLexConvolution`
on the `snoc`-augmented `(d+1)`-vectors, and the subtraction is the lex-trichotomy partition
discharged by `AffineOnResidues.sub_of_partition`. -/
theorem affineOnResidues_gatedEqConvolution {α β : Type*} {d : ℕ}
    (u : ℕ → α) (v : ℕ → β) (b : α → β → Prop)
    {mu pu : ℕ} (hpu : 1 ≤ pu) (hu : ∀ i, mu ≤ i → u (i + pu) = u i)
    {mv pv : ℕ} (hpv : 1 ≤ pv) (hv : ∀ j, mv ≤ j → v (j + pv) = v j)
    (R : ℕ → Fin d → ℤ) {mR pR : ℕ} (PR : Fin d → ℤ) (hpR : 1 ≤ pR)
    (hR : ∀ j, mR ≤ j → R (j + pR) = R j + PR)
    (T : ℕ → Fin d → ℤ) (hT : ∀ i, AffineOnResiduesZ (fun n => T n i)) :
    AffineOnResidues (fun n => ((Finset.range n).filter
      (fun j : ℕ => R j = T n ∧ b (u j) (v (n - 1 - j)))).card) := by
  classical
  set Rle : ℕ → Fin (d+1) → ℤ := fun j => Fin.snoc (R j) (0:ℤ) with hRledef
  set Rlt : ℕ → Fin (d+1) → ℤ := fun j => Fin.snoc (R j) (1:ℤ) with hRltdef
  set Tle : ℕ → Fin (d+1) → ℤ := fun n => Fin.snoc (T n) (1:ℤ) with hTledef
  set Tlt : ℕ → Fin (d+1) → ℤ := fun n => Fin.snoc (T n) (0:ℤ) with hTltdef
  have hRle : ∀ j, mR ≤ j → Rle (j + pR) = Rle j + Fin.snoc PR (0:ℤ) := by
    intro j hj
    funext c
    refine Fin.lastCases ?_ ?_ c
    · simp only [hRledef, Pi.add_apply, Fin.snoc_last, add_zero]
    · intro i
      simp only [hRledef, Pi.add_apply, Fin.snoc_castSucc]
      rw [hR j hj]; simp only [Pi.add_apply]
  have hRlt : ∀ j, mR ≤ j → Rlt (j + pR) = Rlt j + Fin.snoc PR (0:ℤ) := by
    intro j hj
    funext c
    refine Fin.lastCases ?_ ?_ c
    · simp only [hRltdef, Pi.add_apply, Fin.snoc_last, add_zero]
    · intro i
      simp only [hRltdef, Pi.add_apply, Fin.snoc_castSucc]
      rw [hR j hj]; simp only [Pi.add_apply]
  have hTle : ∀ i, AffineOnResiduesZ (fun n => Tle n i) := by
    intro c
    refine Fin.lastCases ?_ ?_ c
    · simpa only [hTledef, Fin.snoc_last] using SliceThreshold.AffineOnResiduesZ.const (1:ℤ)
    · intro i
      simpa only [hTledef, Fin.snoc_castSucc] using hT i
  have hTlt : ∀ i, AffineOnResiduesZ (fun n => Tlt n i) := by
    intro c
    refine Fin.lastCases ?_ ?_ c
    · simpa only [hTltdef, Fin.snoc_last] using SliceThreshold.AffineOnResiduesZ.const (0:ℤ)
    · intro i
      simpa only [hTltdef, Fin.snoc_castSucc] using hT i
  have Ale := SliceGatedConv.affineOnResidues_gatedLexConvolution u v b hpu hu hpv hv
    Rle (Fin.snoc PR (0:ℤ)) hpR hRle Tle hTle
  have Alt := SliceGatedConv.affineOnResidues_gatedLexConvolution u v b hpu hu hpv hv
    Rlt (Fin.snoc PR (0:ℤ)) hpR hRlt Tlt hTlt
  refine AffineOnResidues.sub_of_partition Ale Alt (fun n => ?_)
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hle : WRP.lexLt (Rle j) (Tle n) ↔ (WRP.lexLt (R j) (T n) ∨ R j = T n) := by
    rw [hRledef, hTledef]; exact lexLt_snoc_le (R j) (T n)
  have hlt : WRP.lexLt (Rlt j) (Tlt n) ↔ WRP.lexLt (R j) (T n) := by
    rw [hRltdef, hTltdef]; exact lexLt_snoc_lt (R j) (T n)
  by_cases hb : b (u j) (v (n - 1 - j))
  · by_cases heq : R j = T n
    · have hlexF : ¬ WRP.lexLt (R j) (T n) := fun hh => lexLt_ne hh heq
      rw [if_pos ⟨hle.mpr (Or.inr heq), hb⟩, if_neg (fun hh => hlexF (hlt.mp hh.1)),
        if_pos ⟨heq, hb⟩]
    · by_cases hlex : WRP.lexLt (R j) (T n)
      · rw [if_pos ⟨hle.mpr (Or.inl hlex), hb⟩, if_pos ⟨hlt.mpr hlex, hb⟩, if_neg (fun hh => heq hh.1)]
      · rw [if_neg (fun hh => (hle.mp hh.1).elim hlex heq), if_neg (fun hh => hlex (hlt.mp hh.1)),
          if_neg (fun hh => heq hh.1)]
  · rw [if_neg (fun hh => hb hh.2), if_neg (fun hh => hb hh.2), if_neg (fun hh => hb hh.2)]

/-- **`lexEq_count_per_region`** (build-order step L2 of the corrected mod-counting route).
Counts loop-indices `j < n` with `j % m = a`, block-`U` rank `P.rank c W_{j+1} (·↦1+2j)` EQUAL to a
moving `AffineOnResiduesZ` threshold `T n`, AND the marked-DFA gate on — `AffineOnResidues` in `n`.
The rank-equality analogue of `lexLt_below_count_per_region`: specialises
`affineOnResidues_gatedEqConvolution` to the slice rank with the `j % m`-paired forward iterate
(mirroring `countPeriodicInterval_mod`). -/
theorem lexEq_count_per_region {Gamma : Type*} (P : WRP.Presentation Step Gamma)
    (c : Fin P.toPoly.K) {T : ℕ → Fin P.d → ℤ} (hT : ∀ i, AffineOnResiduesZ (fun n => T n i))
    (m a : ℕ) (hm : 1 ≤ m) (M : DetAuto (Step × Bool)) :
    AffineOnResidues (fun n => ((Finset.range n).filter
      (fun j : ℕ => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j) = T n
        ∧ j % m = a ∧ M.accepts (markAt (wrappedFlat n) (1 + 2 * j)))).card) := by
  obtain ⟨mR, pR, PR, hpR, hR⟩ := SliceRankAtom.rank_block_rankAffine P c
  obtain ⟨mu, pu, hpu, hu⟩ := SliceCount.bF_iterate_eventuallyPeriodic M
  obtain ⟨mv, pv, hpv, hv⟩ := SliceCount.bF_func_iterate_eventuallyPeriodic M
  have hu_iter : ∀ s t, mu ≤ s → (bF M)^[s + pu * t] (qpre M) = (bF M)^[s] (qpre M) := by
    intro s t hs
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, hu _ (by omega), ih]
  have hu' : ∀ i, mu ≤ i →
      ((bF M)^[i + pu * m] (qpre M), (i + pu * m) % m) = ((bF M)^[i] (qpre M), i % m) := by
    intro i hi
    refine Prod.ext (hu_iter i m hi) ?_
    show (i + pu * m) % m = i % m
    rw [Nat.mul_comm pu m, Nat.add_mul_mod_self_left]
  have hker := affineOnResidues_gatedEqConvolution
    (fun j => ((bF M)^[j] (qpre M), j % m)) (fun mm => (bF M)^[mm])
    (fun qr g => qr.2 = a ∧ M.accept (fStep M (g (fStep M (M.δ qr.1 (U, true)) D)) D))
    (Nat.mul_pos hpu hm) hu' hpv hv
    (fun j => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j)) PR hpR hR T hT
  refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_) hker
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  refine and_congr_right
    (fun hj => and_congr_right (fun _ => and_congr Iff.rfl ?_))
  have hb1 : 1 + 2 * j < (wrappedFlat n).length := by rw [length_wrappedFlat]; omega
  rw [SliceCount.accepts_markAt M (wrappedFlat n) (1 + 2 * j) hb1,
    SliceCount.fwd_blockStart M n j (le_of_lt hj),
    SliceCount.wrappedFlat_getElem_U n j hj hb1, SliceCount.tau_blockU M n j hj]

/-- **`lexLt_below_count_per_region`** (build-order step 6).  Counts loop-indices `j < n`
whose block-`U` rank `P.rank c W_{j+1} (·↦1+2j)` is `lexLt` below a moving `AffineOnResiduesZ`
threshold `T n` AND whose marked-DFA gate is on — `AffineOnResidues` in `n`.  The slice
specialisation of the gated **lex**-convolution kernel `affineOnResidues_gatedLexConvolution`
(rank `RankAffine` via `rank_block_rankAffine`; gate via the same `accepts_markAt`/
`fwd_blockStart`/`tau_blockU` decomposition as `countPeriodicInterval`). -/
theorem lexLt_below_count_per_region {Gamma : Type*} (P : WRP.Presentation Step Gamma)
    (c : Fin P.toPoly.K) {T : ℕ → Fin P.d → ℤ} (hT : ∀ i, AffineOnResiduesZ (fun n => T n i))
    (M : DetAuto (Step × Bool)) :
    AffineOnResidues (fun n => ((Finset.range n).filter
      (fun j : ℕ => WRP.lexLt (P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j)) (T n)
        ∧ M.accepts (markAt (wrappedFlat n) (1 + 2 * j)))).card) := by
  obtain ⟨mR, pR, PR, hpR, hR⟩ := SliceRankAtom.rank_block_rankAffine P c
  obtain ⟨mu, pu, hpu, hu⟩ := SliceCount.bF_iterate_eventuallyPeriodic M
  obtain ⟨mv, pv, hpv, hv⟩ := SliceCount.bF_func_iterate_eventuallyPeriodic M
  have hgc := SliceGatedConv.affineOnResidues_gatedLexConvolution
    (fun j => (bF M)^[j] (qpre M)) (fun m => (bF M)^[m])
    (fun q g => M.accept (fStep M (g (fStep M (M.δ q (U, true)) D)) D))
    hpu hu hpv hv
    (fun j => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j)) PR hpR hR T hT
  refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_) hgc
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j hj
  rw [Finset.mem_range] at hj
  refine and_congr_right (fun _ => ?_)
  have hb1 : 1 + 2 * j < (wrappedFlat n).length := by rw [length_wrappedFlat]; omega
  rw [SliceCount.accepts_markAt M (wrappedFlat n) (1 + 2 * j) hb1,
    SliceCount.fwd_blockStart M n j (le_of_lt hj),
    SliceCount.wrappedFlat_getElem_U n j hj hb1, SliceCount.tau_blockU M n j hj]

end SliceFasCount
