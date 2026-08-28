/-
# `WRP.lexLt` is a strict total order on rank vectors

The `d*` position coupling needs the lexicographic rank order `WRP.lexLt` to be a strict
total order (irreflexive, transitive, trichotomous) so that the generic argmin fold
`SliceArgMin.amFold_min` attains the `≺`-minimum.  These are the standard lexicographic
facts for the concrete definition
`lexLt x y := ∃ i, (∀ j < i, x j = y j) ∧ x i < y i`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
import RequestProject.WRP

namespace SliceLexOrder

open scoped Classical

variable {d : ℕ}

/-- `lexLt` is irreflexive. -/
theorem lexLt_irrefl (x : Fin d → ℤ) : ¬ WRP.lexLt x x := by
  rintro ⟨i, _, hi⟩; exact lt_irrefl _ hi

/-- `lexLt` is transitive. -/
theorem lexLt_trans (x y z : Fin d → ℤ) (hxy : WRP.lexLt x y) (hyz : WRP.lexLt y z) :
    WRP.lexLt x z := by
  obtain ⟨i, hieq, hilt⟩ := hxy
  obtain ⟨k, hkeq, hklt⟩ := hyz
  rcases lt_trichotomy i k with hik | hik | hik
  · refine ⟨i, fun j hj => ?_, ?_⟩
    · rw [hieq j hj, hkeq j (hj.trans hik)]
    · rw [← hkeq i hik]; exact hilt
  · subst hik
    exact ⟨i, fun j hj => (hieq j hj).trans (hkeq j hj), hilt.trans hklt⟩
  · refine ⟨k, fun j hj => ?_, ?_⟩
    · rw [hieq j (hj.trans hik), hkeq j hj]
    · rw [hieq k hik]; exact hklt

/-- `lexLt` is trichotomous (hence total). -/
theorem lexLt_trichot (x y : Fin d → ℤ) :
    WRP.lexLt x y ∨ x = y ∨ WRP.lexLt y x := by
  by_cases hxy : x = y
  · exact Or.inr (Or.inl hxy)
  · have hne : (Finset.univ.filter (fun i : Fin d => x i ≠ y i)).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
      exact hxy (funext fun i => not_not.mp (h (Finset.mem_univ i)))
    set i₀ := (Finset.univ.filter (fun i : Fin d => x i ≠ y i)).min' hne with hi₀
    have hi₀mem := (Finset.univ.filter (fun i : Fin d => x i ≠ y i)).min'_mem hne
    rw [Finset.mem_filter] at hi₀mem
    have hlt : ∀ j, j < i₀ → x j = y j := by
      intro j hj
      by_contra hjne
      have hle : i₀ ≤ j := Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjne⟩)
      exact absurd hj (not_lt.mpr hle)
    rcases lt_trichotomy (x i₀) (y i₀) with h | h | h
    · exact Or.inl ⟨i₀, hlt, h⟩
    · exact absurd h hi₀mem.2
    · exact Or.inr (Or.inr ⟨i₀, fun j hj => (hlt j hj).symm, h⟩)

/-- not-below implies above-or-equal. -/
theorem lexLt_not_lt (x y : Fin d → ℤ) (h : ¬ WRP.lexLt x y) : y = x ∨ WRP.lexLt y x := by
  rcases lexLt_trichot x y with hxy | hxy | hxy
  · exact absurd hxy h
  · exact Or.inl hxy.symm
  · exact Or.inr hxy

/-- **Negative transitivity** (`lexLt` is a strict weak order): this is the hypothesis
`SliceArgMin.amFold_min` needs at `lexLt`, valid even when distinct indices tie. -/
theorem lexLt_negtrans (x y z : Fin d → ℤ)
    (h1 : ¬ WRP.lexLt x y) (h2 : ¬ WRP.lexLt y z) : ¬ WRP.lexLt x z := by
  intro hxz
  rcases lexLt_not_lt x y h1 with hyx | hyx
  · rcases lexLt_not_lt y z h2 with hzy | hzy
    · rw [hzy, hyx] at hxz; exact lexLt_irrefl x hxz
    · rw [hyx] at hzy; exact lexLt_irrefl x (lexLt_trans x z x hxz hzy)
  · rcases lexLt_not_lt y z h2 with hzy | hzy
    · rw [hzy] at hxz; exact lexLt_irrefl x (lexLt_trans x y x hxz hyx)
    · exact lexLt_irrefl x (lexLt_trans x z x hxz (lexLt_trans z y x hzy hyx))

/-! ## Lex algebra: translation and scaling

These reduce a comparison of two boundary vectors `F(m+r) + k·P` and `F(m+r) + k₀·P`
to a comparison of `(k-k₀)·P` against the zero vector — the vector analog of the
`omega`/`nlinarith` slope-sign arithmetic in `SliceBoundaryMinCore.bvalue_is_min`. -/

/-- **Translation invariance.** `lexLt x y ↔ lexLt (x - y) 0`. -/
theorem lexLt_sub_zero (x y : Fin d → ℤ) :
    WRP.lexLt x y ↔ WRP.lexLt (fun i => x i - y i) (fun _ => 0) := by
  constructor
  · rintro ⟨i, hpre, hlt⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · show x j - y j = 0; rw [hpre j hj]; ring
    · show x i - y i < 0; have h := hlt; omega
  · rintro ⟨i, hpre, hlt⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · have h0 : x j - y j = 0 := hpre j hj; show x j = y j; omega
    · have h0 : x i - y i < 0 := hlt; show x i < y i; omega

/-- **Scaling sign.** For an integer scalar `c`, `c • P` lex-precedes the zero vector iff
`c > 0` and `P ≺ 0`, or `c < 0` and `0 ≺ P`. -/
theorem lexLt_smul_iff (c : ℤ) (P : Fin d → ℤ) :
    WRP.lexLt (fun i => c * P i) (fun _ => 0) ↔
      (0 < c ∧ WRP.lexLt P (fun _ => 0)) ∨ (c < 0 ∧ WRP.lexLt (fun _ => 0) P) := by
  constructor
  · rintro ⟨i, hpre, hlt⟩
    have hlt' : c * P i < 0 := hlt
    have hpre' : ∀ j, j < i → c * P j = 0 := fun j hj => hpre j hj
    rcases lt_trichotomy c 0 with hc | hc | hc
    · right
      refine ⟨hc, i, fun j hj => ?_, ?_⟩
      · have hz := hpre' j hj
        have hPj : P j = 0 := by
          rcases mul_eq_zero.mp hz with h | h
          exacts [absurd h (ne_of_lt hc), h]
        show (0 : ℤ) = P j; omega
      · show (0 : ℤ) < P i; nlinarith [hlt', hc]
    · subst hc; simp at hlt'
    · left
      refine ⟨hc, i, fun j hj => ?_, ?_⟩
      · have hz := hpre' j hj
        show P j = 0
        rcases mul_eq_zero.mp hz with h | h
        exacts [absurd h (ne_of_gt hc), h]
      · show P i < 0; nlinarith [hlt', hc]
  · rintro (⟨hc, i, hpre, hlt⟩ | ⟨hc, i, hpre, hlt⟩)
    · refine ⟨i, fun j hj => ?_, ?_⟩
      · have hPj : P j = 0 := hpre j hj
        show c * P j = 0; rw [hPj, mul_zero]
      · have hPi : P i < 0 := hlt
        show c * P i < 0; exact mul_neg_of_pos_of_neg hc hPi
    · refine ⟨i, fun j hj => ?_, ?_⟩
      · have hPj : (0 : ℤ) = P j := hpre j hj
        show c * P j = 0; rw [← hPj, mul_zero]
      · have hPi : (0 : ℤ) < P i := hlt
        show c * P i < 0; exact mul_neg_of_neg_of_pos hc hPi

end SliceLexOrder
