/-
# `d*` and the cell transport on the copied slice (§9 tower, Stage F.1)

Two pieces, per the CS-5 freeze:

* the `d*` semantic layer generalised to an ARBITRARY word (`selDListGA'`,
  `exists_min_selDAtomGA'`, `dstarRankGA'`) with `dstarRankGA_m` its
  copied-slice reading and the m = 1 regression
  `dstarRankGA_m_one : dstarRankGA_m P hV 1 n = dstarRankGA P hV n`;
* the fibred cell tuple `cellTupleF` over `RegionSpecF` and its base
  transports: boundary-stretch coordinates are FIXED positions, so the
  boundary reduction (`accepts_copied_arity_reduced`) lands on ONE re-rooted
  pulled-back machine for every base `t` (`markSeg_congr_outside`), whose
  block map is literally `bFN M` — the existing wrapped-flat transports
  (`cell_base_transport_right/left`) are then consumed VERBATIM.
-/
import RequestProject.SliceDstarGA
import RequestProject.CopiedRank

namespace CopiedDstar

open WRP Step SliceFamilyCell MSOMarkN SliceMarkN SliceDstarGA CopiedCells CopiedMark SliceReRoot
open scoped Classical

/-! ## The word-generic `d*` semantic layer (CS-5.1) -/

/-- The selected `D`-atoms of an arbitrary word, over all copies and tuples. -/
noncomputable def selDListGA' (P : WRP.Presentation Step Step) (w : List Step) :
    List P.toPoly.Atom :=
  ((List.finRange P.toPoly.K).flatMap (fun c =>
    (Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
      Finset.range w.length)).toList.map
      (fun ī => (⟨c, ī⟩ : P.toPoly.Atom)))).filter
    (fun a => decide (P.toPoly.selectedAtom w a ∧ P.toPoly.labelOf w a = D))

theorem mem_selDListGA' (P : WRP.Presentation Step Step) (w : List Step)
    (a : P.toPoly.Atom) :
    a ∈ selDListGA' P w ↔
      (P.toPoly.selectedAtom w a ∧ P.toPoly.labelOf w a = D) := by
  rw [selDListGA', List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hsel, hlab⟩
    exact ⟨hsel, hlab⟩
  · rintro ⟨hsel, hlab⟩
    refine ⟨?_, hsel, hlab⟩
    rw [List.mem_flatMap]
    refine ⟨a.1, List.mem_finRange _, ?_⟩
    rw [List.mem_map]
    refine ⟨a.2, ?_, rfl⟩
    rw [Finset.mem_toList, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    exact hsel.1 i

/-- Existence of the `≺`-minimal selected `D`-atom, on an arbitrary word. -/
theorem exists_min_selDAtomGA' (P : WRP.Presentation Step Step) (hV : P.Valid)
    (w : List Step)
    (h : ∃ a, P.toPoly.selectedAtom w a ∧ P.toPoly.labelOf w a = D) :
    ∃ dstar, P.toPoly.selectedAtom w dstar ∧
      P.toPoly.labelOf w dstar = D ∧
      ∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = D →
        dstar = b ∨ P.wrpOrd w dstar b := by
  obtain ⟨a0, ha0⟩ := h
  have hmemiff := mem_selDListGA' P w
  have hlne : selDListGA' P w ≠ [] := fun hcon => by
    have := (hmemiff a0).mpr ha0
    rw [hcon] at this
    exact absurd this (by simp)
  obtain ⟨dstar, hdmem, hdmin⟩ := SliceDstar.exists_min_of_list
    (P.wrpOrd w) (selDListGA' P w) hlne
    (fun a ha b hb => hV.trichot w a b ((hmemiff a).mp ha).1
      ((hmemiff b).mp hb).1)
    (fun a ha b hb c hc => hV.trans w a b c
      ((hmemiff a).mp ha).1 ((hmemiff b).mp hb).1 ((hmemiff c).mp hc).1)
  obtain ⟨hdsel, hdD⟩ := (hmemiff dstar).mp hdmem
  exact ⟨dstar, hdsel, hdD,
    fun b hbsel hbD => hdmin b ((hmemiff b).mpr ⟨hbsel, hbD⟩)⟩

/-- **`d*`-rank of an arbitrary word**: the rank vector of its `≺`-minimal
selected `D`-atom (`0` when `D`-absent).  SEMANTIC and `C`-free. -/
noncomputable def dstarRankGA' (P : WRP.Presentation Step Step) (hV : P.Valid)
    (w : List Step) : Fin P.d → ℤ :=
  if h : ∃ a, P.toPoly.selectedAtom w a ∧ P.toPoly.labelOf w a = D
  then P.rankOf w (Classical.choose (exists_min_selDAtomGA' P hV w h))
  else fun _ => 0

/-- The consumer interface for `dstarRankGA'`. -/
theorem dstarRankGA'_spec (P : WRP.Presentation Step Step) (hV : P.Valid)
    (w : List Step)
    (h : ∃ a, P.toPoly.selectedAtom w a ∧ P.toPoly.labelOf w a = D) :
    ∃ dstar, P.toPoly.selectedAtom w dstar ∧
      P.toPoly.labelOf w dstar = D ∧
      (∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = D →
        dstar = b ∨ P.wrpOrd w dstar b) ∧
      dstarRankGA' P hV w = P.rankOf w dstar := by
  refine ⟨Classical.choose (exists_min_selDAtomGA' P hV w h), ?_⟩
  obtain ⟨hsel, hD, hmin⟩ := Classical.choose_spec (exists_min_selDAtomGA' P hV w h)
  refine ⟨hsel, hD, hmin, ?_⟩
  unfold dstarRankGA'
  rw [dif_pos h]

/-- The fibred `d*`-rank: `dstarRankGA'` read on the copied slice. -/
noncomputable def dstarRankGA_m (P : WRP.Presentation Step Step) (hV : P.Valid)
    (mS n : ℕ) : Fin P.d → ℤ :=
  dstarRankGA' P hV (copiedSlice mS n)

/-! ## The fibred cell tuple (CS-5, transport layer) -/

/-- The position tuple a fibred cell descriptor describes at boundary width
`mS` and base `t`. -/
def cellTupleF {B k : ℕ} (rs : Fin k → RegionSpecF B) (mS t n : ℕ) :
    Fin k → ℕ :=
  fun i => (rs i).posAt mS t n

/-- Core test for a fibred descriptor. -/
def RegionSpecF.isCore {B : ℕ} : RegionSpecF B → Bool
  | .core _ => true
  | _ => false

/-- The underlying wrapped-flat descriptor of a core fibred descriptor (junk
on stretch descriptors). -/
def RegionSpecF.coreOf {B : ℕ} : RegionSpecF B → RegionSpec B
  | .core r => r
  | _ => .pre

/-! ## The fibred base transports -/

section Transport

variable {B k : ℕ}

/-- The coordinates carrying core (middle-window) descriptors. -/
def coreSet (rs : Fin k → RegionSpecF B) : Finset (Fin k) :=
  Finset.univ.filter (fun i => RegionSpecF.isCore (rs i) = true)

/-- The order embedding of the core coordinates. -/
noncomputable def coreEmb (rs : Fin k → RegionSpecF B)
    (i' : Fin (coreSet rs).card) : Fin k :=
  ((coreSet rs).orderIsoOfFin rfl i').val

/-- The underlying wrapped-flat descriptors of the core coordinates. -/
noncomputable def coreSpec (rs : Fin k → RegionSpecF B)
    (i' : Fin (coreSet rs).card) : RegionSpec B :=
  RegionSpecF.coreOf (rs (coreEmb rs i'))

theorem rs_coreEmb (rs : Fin k → RegionSpecF B) (i' : Fin (coreSet rs).card) :
    rs (coreEmb rs i') = RegionSpecF.core (coreSpec rs i') := by
  have hmem : coreEmb rs i' ∈ coreSet rs :=
    ((coreSet rs).orderIsoOfFin rfl i').property
  have h2 : RegionSpecF.isCore (rs (coreEmb rs i')) = true := by
    unfold coreSet at hmem
    rw [Finset.mem_filter] at hmem
    exact hmem.2
  unfold coreSpec
  rcases hr : rs (coreEmb rs i') with r | q | l
  · rfl
  · rw [hr] at h2
    simp [RegionSpecF.isCore] at h2
  · rw [hr] at h2
    simp [RegionSpecF.isCore] at h2

theorem noncore_of_out (rs : Fin k → RegionSpecF B) (i : Fin k)
    (hi : ∀ i', coreEmb rs i' ≠ i) :
    (∃ q, rs i = RegionSpecF.prefIdx q) ∨ ∃ l, rs i = RegionSpecF.sufIdx l := by
  have hnot : i ∉ coreSet rs := by
    intro hcon
    exact hi (((coreSet rs).orderIsoOfFin rfl).symm ⟨i, hcon⟩)
      (congrArg Subtype.val
        (((coreSet rs).orderIsoOfFin rfl).apply_symm_apply ⟨i, hcon⟩))
  unfold coreSet at hnot
  rw [Finset.mem_filter] at hnot
  push Not at hnot
  have hncore := hnot (Finset.mem_univ i)
  rcases hr : rs i with r | q | l
  · rw [hr] at hncore
    simp [RegionSpecF.isCore] at hncore
  · exact Or.inl ⟨q, rfl⟩
  · exact Or.inr ⟨l, rfl⟩

/-- Core cell positions lie in the middle window. -/
theorem cellTupleF_mid (rs : Fin k → RegionSpecF B) (mS t n : ℕ)
    (hm : 1 ≤ mS) (htn : t + B ≤ n) :
    ∀ i', mS - 1 ≤ cellTupleF rs mS t n (coreEmb rs i')
      ∧ cellTupleF rs mS t n (coreEmb rs i') < mS + 2 * n + 1 := by
  intro i'
  unfold cellTupleF
  rw [rs_coreEmb rs i']
  rcases coreSpec rs i' with _ | _ | ⟨f, e⟩ | ⟨l', e⟩ | ⟨δ, e⟩ <;>
    simp only [RegionSpecF.posAt, RegionSpec.posAt]
  · omega
  · omega
  · have := f.isLt
    rcases e with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · have := l'.isLt
    rcases e with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · have := δ.isLt
    rcases e with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Stretch cell positions lie outside the middle window. -/
theorem cellTupleF_out (rs : Fin k → RegionSpecF B) (mS t n : ℕ)
    (hv : ∀ i, (rs i).valid mS) :
    ∀ i, (∀ i', coreEmb rs i' ≠ i) →
      cellTupleF rs mS t n i < mS - 1
        ∨ mS + 2 * n + 1 ≤ cellTupleF rs mS t n i := by
  intro i hi
  unfold cellTupleF
  rcases noncore_of_out rs i hi with ⟨q, hq⟩ | ⟨l, hl⟩
  · left
    have hval := hv i
    rw [hq] at hval ⊢
    exact hval
  · right
    rw [hl]
    simp only [RegionSpecF.posAt]
    omega

/-- The reduced cell tuple is the underlying wrapped-flat cell tuple. -/
theorem cellTupleF_reduced (rs : Fin k → RegionSpecF B) (mS t n : ℕ)
    (_hm : 1 ≤ mS) :
    (fun i' => cellTupleF rs mS t n (coreEmb rs i') - (mS - 1))
      = cellTuple (coreSpec rs) t n := by
  funext i'
  unfold cellTupleF cellTuple
  rw [rs_coreEmb rs i']
  show mS - 1 + (coreSpec rs i').posAt t n - (mS - 1) = _
  omega

/-- The marked boundary stretches of a fibred cell tuple do not depend on the
base `t` (stretch coordinates are fixed; core coordinates are outside both
stretch windows). -/
theorem cellTupleF_seg_congr (rs : Fin k → RegionSpecF B) (mS t₁ t₂ n : ℕ)
    (hm : 1 ≤ mS) (ht₁ : t₁ + B ≤ n) (ht₂ : t₂ + B ≤ n) :
    markSeg k (List.replicate (mS - 1) U) (cellTupleF rs mS t₁ n) 0
        = markSeg k (List.replicate (mS - 1) U) (cellTupleF rs mS t₂ n) 0
      ∧ markSeg k (List.replicate (mS - 1) D) (cellTupleF rs mS t₁ n)
          (mS + 2 * n + 1)
        = markSeg k (List.replicate (mS - 1) D) (cellTupleF rs mS t₂ n)
          (mS + 2 * n + 1) := by
  have hcase : ∀ i, cellTupleF rs mS t₁ n i = cellTupleF rs mS t₂ n i
      ∨ ((mS - 1 ≤ cellTupleF rs mS t₁ n i
            ∧ cellTupleF rs mS t₁ n i < mS + 2 * n + 1)
          ∧ (mS - 1 ≤ cellTupleF rs mS t₂ n i
            ∧ cellTupleF rs mS t₂ n i < mS + 2 * n + 1)) := by
    intro i
    by_cases h : ∃ i', coreEmb rs i' = i
    · obtain ⟨i', rfl⟩ := h
      exact Or.inr ⟨cellTupleF_mid rs mS t₁ n hm ht₁ i',
        cellTupleF_mid rs mS t₂ n hm ht₂ i'⟩
    · push Not at h
      left
      unfold cellTupleF
      rcases noncore_of_out rs i h with ⟨q, hq⟩ | ⟨l, hl⟩
      · rw [hq]
        rfl
      · rw [hl]
        rfl
  constructor
  · apply markSeg_congr_outside
    intro i
    rw [List.length_replicate]
    rcases hcase i with h | ⟨⟨h1, _⟩, ⟨h2, _⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨Or.inr (by omega), Or.inr (by omega)⟩
  · apply markSeg_congr_outside
    intro i
    rcases hcase i with h | ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl (by omega), Or.inl (by omega)⟩

/-- **Rightward fibred base transport**: acceptance of the fibred cell tuple
is invariant under moving the base right by period multiples inside the
window — the boundary reduction lands on one fixed re-rooted pulled-back
machine (same `bFN`, same periods), where the wrapped-flat transport applies
verbatim. -/
theorem cell_base_transport_right_fibred (M : SliceMSO.DetAuto (MarkedN k))
    (mv pv : ℕ) (hEP : ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g])
    (mS : ℕ) (hm : 1 ≤ mS) (rs : Fin k → RegionSpecF B)
    (hv : ∀ i, (rs i).valid mS) (t n j : ℕ)
    (htB : B + mv ≤ t) (htn : t + j * pv + 2 * B + mv ≤ n - B) (hBn : B ≤ n) :
    M.accepts (markAtN k (copiedSlice mS n)
        (cellTupleF rs mS (t + j * pv) n))
      ↔ M.accepts (markAtN k (copiedSlice mS n) (cellTupleF rs mS t n)) := by
  have hw1 : t + j * pv + B ≤ n := by omega
  have hw0 : t + B ≤ n := by omega
  obtain ⟨hsegU, hsegD⟩ := cellTupleF_seg_congr rs mS (t + j * pv) t n hm hw1 hw0
  rw [accepts_copied_arity_reduced M (coreEmb rs) mS n hm
      (cellTupleF rs mS (t + j * pv) n)
      (cellTupleF_mid rs mS (t + j * pv) n hm hw1)
      (cellTupleF_out rs mS (t + j * pv) n hv),
    accepts_copied_arity_reduced M (coreEmb rs) mS n hm
      (cellTupleF rs mS t n)
      (cellTupleF_mid rs mS t n hm hw0)
      (cellTupleF_out rs mS t n hv),
    hsegU, hsegD, cellTupleF_reduced rs mS (t + j * pv) n hm,
    cellTupleF_reduced rs mS t n hm]
  have hEP'' : ∀ g, mv ≤ g →
      (bFN (pullback (reRoot M
        (markSeg k (List.replicate (mS - 1) U) (cellTupleF rs mS t n) 0)
        (markSeg k (List.replicate (mS - 1) D) (cellTupleF rs mS t n)
          (mS + 2 * n + 1))) (mapBits (coreEmb rs))))^[g + pv]
      = (bFN (pullback (reRoot M
        (markSeg k (List.replicate (mS - 1) U) (cellTupleF rs mS t n) 0)
        (markSeg k (List.replicate (mS - 1) D) (cellTupleF rs mS t n)
          (mS + 2 * n + 1))) (mapBits (coreEmb rs))))^[g] := by
    intro g hg
    rw [bFN_pullback, bFN_reRoot]
    exact hEP g hg
  exact cell_base_transport_right _ mv pv hEP'' (coreSpec rs) t n j htB htn hBn

/-- **Leftward fibred base transport**: the `cell_base_transport_left` twin. -/
theorem cell_base_transport_left_fibred (M : SliceMSO.DetAuto (MarkedN k))
    (mv pv : ℕ) (hEP : ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g])
    (mS : ℕ) (hm : 1 ≤ mS) (rs : Fin k → RegionSpecF B)
    (hv : ∀ i, (rs i).valid mS) (t n j : ℕ)
    (htB : B + mv + j * pv ≤ t) (htn : t + 2 * B + mv ≤ n - B) (hBn : B ≤ n) :
    M.accepts (markAtN k (copiedSlice mS n)
        (cellTupleF rs mS (t - j * pv) n))
      ↔ M.accepts (markAtN k (copiedSlice mS n) (cellTupleF rs mS t n)) := by
  have hw1 : t - j * pv + B ≤ n := by omega
  have hw0 : t + B ≤ n := by omega
  obtain ⟨hsegU, hsegD⟩ := cellTupleF_seg_congr rs mS (t - j * pv) t n hm hw1 hw0
  rw [accepts_copied_arity_reduced M (coreEmb rs) mS n hm
      (cellTupleF rs mS (t - j * pv) n)
      (cellTupleF_mid rs mS (t - j * pv) n hm hw1)
      (cellTupleF_out rs mS (t - j * pv) n hv),
    accepts_copied_arity_reduced M (coreEmb rs) mS n hm
      (cellTupleF rs mS t n)
      (cellTupleF_mid rs mS t n hm hw0)
      (cellTupleF_out rs mS t n hv),
    hsegU, hsegD, cellTupleF_reduced rs mS (t - j * pv) n hm,
    cellTupleF_reduced rs mS t n hm]
  have hEP'' : ∀ g, mv ≤ g →
      (bFN (pullback (reRoot M
        (markSeg k (List.replicate (mS - 1) U) (cellTupleF rs mS t n) 0)
        (markSeg k (List.replicate (mS - 1) D) (cellTupleF rs mS t n)
          (mS + 2 * n + 1))) (mapBits (coreEmb rs))))^[g + pv]
      = (bFN (pullback (reRoot M
        (markSeg k (List.replicate (mS - 1) U) (cellTupleF rs mS t n) 0)
        (markSeg k (List.replicate (mS - 1) D) (cellTupleF rs mS t n)
          (mS + 2 * n + 1))) (mapBits (coreEmb rs))))^[g] := by
    intro g hg
    rw [bFN_pullback, bFN_reRoot]
    exact hEP g hg
  exact cell_base_transport_left _ mv pv hEP'' (coreSpec rs) t n j htB htn hBn

end Transport

end CopiedDstar
