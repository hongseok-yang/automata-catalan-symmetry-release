/-
# The marked copied slice (§9 tower, Stage C)

The marked-word decomposition of the copied slice and the boundary reduction
(`CS_DESIGN.json`, CS-2).  `copiedSlice mS n = U^{mS-1} ++ wrappedFlat n ++
D^{mS-1}`, so its `k`-marked form factors into three `markSeg` segments; when
every mark coordinate lies in the MIDDLE window, the boundary segments are
unmarked and acceptance reduces — via `SliceReRoot.reRoot` through the
unmarked stretches — to acceptance of the marked WRAPPED-FLAT word, with
coordinates shifted by `mS - 1`.  Since re-rooting preserves `δ`, every
machine period of the reduced analysis is the wrapped-flat period: `m`-free.

Naming discipline: `k` = mark arity, `mS` = slice copies (CS-2).
-/
import RequestProject.SliceReRoot
import RequestProject.InverseZeta
import RequestProject.WrappedFlat

open Step SliceMSO MSOMarkN SliceMarkN SliceReRoot

namespace CopiedMark

/-- The copied slice as a wrapped-flat word with boundary stretches. -/
theorem copiedSlice_eq_wrap (mS n : ℕ) (hm : 1 ≤ mS) :
    copiedSlice mS n
      = List.replicate (mS - 1) U ++ wrappedFlat n ++ List.replicate (mS - 1) D := by
  rw [copiedSlice, wrappedFlat,
    show mS = (mS - 1) + 1 from by omega,
    List.replicate_succ' (n := mS - 1) (a := U),
    List.replicate_succ (n := mS - 1) (a := D)]
  simp [List.append_assoc]

/-- A word marked with no in-window coordinates. -/
def unmark (k : ℕ) (w : List Step) : List (MarkedN k) :=
  w.map (fun a => mkLetter k a (fun _ => false))

/-- A segment whose window contains no mark coordinate is unmarked. -/
theorem markSeg_unmarked (k : ℕ) (w : List Step) (ī : Fin k → ℕ) :
    ∀ off, (∀ i, ī i < off ∨ off + w.length ≤ ī i) →
      markSeg k w ī off = unmark k w := by
  induction w with
  | nil => intro off _; rfl
  | cons a w ih =>
    intro off hoff
    rw [markSeg, unmark, List.map_cons]
    have hbits : bitsAt k ī off = fun _ => false := by
      apply bitsAt_eq_false
      intro i
      rcases hoff i with h | h
      · omega
      · simp only [List.length_cons] at h
        omega
    rw [hbits, ← unmark]
    congr 1
    apply ih
    intro i
    rcases hoff i with h | h
    · left; omega
    · right
      simp only [List.length_cons] at h
      omega

/-- Mark windows translate. -/
theorem markSeg_shift (k : ℕ) (w : List Step) (ī : Fin k → ℕ) (d : ℕ) :
    ∀ off, markSeg k w (fun i => ī i + d) (off + d) = markSeg k w ī off := by
  induction w with
  | nil => intro off; rfl
  | cons a w ih =>
    intro off
    rw [markSeg, markSeg]
    have hbits : bitsAt k (fun i => ī i + d) (off + d) = bitsAt k ī off := by
      funext i
      simp only [bitsAt]
      by_cases h : off = ī i
      · rw [decide_eq_true (by omega : off + d = ī i + d), decide_eq_true h]
      · rw [decide_eq_false (by omega : ¬ (off + d = ī i + d)),
          decide_eq_false h]
    rw [hbits, show off + d + 1 = (off + 1) + d from by omega, ih (off + 1)]

/-- **The three-segment marked decomposition of the copied slice.** -/
theorem markAtN_copiedSlice (k mS n : ℕ) (hm : 1 ≤ mS) (ī : Fin k → ℕ) :
    markAtN k (copiedSlice mS n) ī
      = markSeg k (List.replicate (mS - 1) U) ī 0
        ++ markSeg k (wrappedFlat n) ī (mS - 1)
        ++ markSeg k (List.replicate (mS - 1) D) ī (mS + 2 * n + 1) := by
  rw [markAtN_eq_markSeg, copiedSlice_eq_wrap mS n hm, markSeg_append,
    markSeg_append]
  have h1 : (0 : ℕ) + (List.replicate (mS - 1) U).length = mS - 1 := by
    simp
  have h2 : (0 : ℕ) + (List.replicate (mS - 1) U ++ wrappedFlat n).length
      = mS + 2 * n + 1 := by
    rw [List.length_append, List.length_replicate, length_wrappedFlat]
    omega
  rw [h1, h2, List.append_assoc]

/-- **Boundary-tagged reduction** (definitional form): acceptance of the marked
copied slice is acceptance of the marked middle by the machine re-rooted
through the MARKED boundary segments. -/
theorem accepts_copied_reRoot {k : ℕ} (M : DetAuto (MarkedN k))
    (mS n : ℕ) (hm : 1 ≤ mS) (ī : Fin k → ℕ) :
    M.accepts (markAtN k (copiedSlice mS n) ī)
      ↔ (reRoot M (markSeg k (List.replicate (mS - 1) U) ī 0)
            (markSeg k (List.replicate (mS - 1) D) ī (mS + 2 * n + 1))).accepts
          (markSeg k (wrappedFlat n) ī (mS - 1)) := by
  rw [markAtN_copiedSlice k mS n hm, accepts_reRoot, List.append_assoc]

/-! ## The mark-arity pullback (boundary-coordinate reduction) -/

/-- The base step of a marked letter. -/
def baseN : (k : ℕ) → MarkedN k → Step
  | 0, a => a
  | (k + 1), ℓ => baseN k ℓ.1

theorem baseN_mkLetter : ∀ (k : ℕ) (s : Step) (f : Fin k → Bool),
    baseN k (mkLetter k s f) = s
  | 0, _, _ => rfl
  | (k + 1), s, f => baseN_mkLetter k s (f ∘ Fin.castSucc)

/-- Re-letter along an arity injection: bits placed via `ι`, false off-range. -/
noncomputable def mapBits {k' k : ℕ} (ι : Fin k' → Fin k) : MarkedN k' → MarkedN k :=
  fun ℓ => mkLetter k (baseN k' ℓ)
    (fun i => if h : ∃ i', ι i' = i then trackBit k' h.choose ℓ else false)

theorem mapBits_mkLetter {k' k : ℕ} (ι : Fin k' → Fin k) (s : Step)
    (f : Fin k' → Bool) :
    mapBits ι (mkLetter k' s f)
      = mkLetter k s (fun i => if h : ∃ i', ι i' = i then f h.choose else false) := by
  rw [mapBits, baseN_mkLetter]
  congr 1
  funext i
  by_cases h : ∃ i', ι i' = i
  · rw [dif_pos h, dif_pos h, trackBit_mkLetter]
  · rw [dif_neg h, dif_neg h]

/-- The all-false letter pulls back to the all-false letter. -/
theorem mapBits_allFalse {k' k : ℕ} (ι : Fin k' → Fin k) (s : Step) :
    mapBits ι (mkLetter k' s (fun _ => false)) = mkLetter k s (fun _ => false) := by
  rw [mapBits_mkLetter]
  congr 1
  funext i
  by_cases h : ∃ i', ι i' = i
  · rw [dif_pos h]
  · rw [dif_neg h]

/-- The pullback acceptor: read `k'`-marked letters through `g`. -/
def pullback {k' k : ℕ} (M : DetAuto (MarkedN k)) (g : MarkedN k' → MarkedN k) :
    DetAuto (MarkedN k') where
  Q := M.Q
  fintypeQ := M.fintypeQ
  q0 := M.q0
  δ := fun q a => M.δ q (g a)
  accept := M.accept

theorem accepts_pullback {k' k : ℕ} (M : DetAuto (MarkedN k))
    (g : MarkedN k' → MarkedN k) (w : List (MarkedN k')) :
    (pullback M g).accepts w ↔ M.accepts (w.map g) := by
  unfold DetAuto.accepts pullback
  rw [List.foldl_map]

/-- **Period preservation through the pullback**: the unmarked step (hence the
block map, hence every iterate period) is unchanged. -/
theorem fStepN_pullback {k' k : ℕ} (M : DetAuto (MarkedN k))
    (ι : Fin k' → Fin k) :
    SliceMarkN.fStepN (pullback M (mapBits ι)) = SliceMarkN.fStepN M := by
  funext q a
  show M.δ q (mapBits ι (mkLetter k' a (fun _ => false)))
    = M.δ q (mkLetter k a (fun _ => false))
  rw [mapBits_allFalse]

theorem bFN_pullback {k' k : ℕ} (M : DetAuto (MarkedN k)) (ι : Fin k' → Fin k) :
    SliceMarkN.bFN (pullback M (mapBits ι)) = SliceMarkN.bFN M := by
  funext q
  show SliceMarkN.fStepN (pullback M (mapBits ι))
      (SliceMarkN.fStepN (pullback M (mapBits ι)) q U) D = _
  rw [fStepN_pullback]
  rfl

/-- Mark vectors agreeing on the window produce the same segment. -/
theorem markSeg_congr_outside {k : ℕ} (w : List Step) (ī₁ ī₂ : Fin k → ℕ) :
    ∀ off, (∀ i, ī₁ i = ī₂ i ∨ ((ī₁ i < off ∨ off + w.length ≤ ī₁ i)
        ∧ (ī₂ i < off ∨ off + w.length ≤ ī₂ i))) →
      markSeg k w ī₁ off = markSeg k w ī₂ off := by
  induction w with
  | nil => intro off _; rfl
  | cons a w ih =>
    intro off hoff
    rw [markSeg, markSeg]
    have hbits : bitsAt k ī₁ off = bitsAt k ī₂ off := by
      funext i
      simp only [bitsAt]
      rcases hoff i with h | ⟨h1, h2⟩
      · rw [h]
      · rw [decide_eq_false (by simp only [List.length_cons] at h1; omega),
          decide_eq_false (by simp only [List.length_cons] at h2; omega)]
    rw [hbits]
    congr 1
    apply ih
    intro i
    rcases hoff i with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨?_, ?_⟩ <;> simp only [List.length_cons] at h1 h2 <;> omega

/-- **The mapped-segment bridge**: a `k'`-marked segment pushed through
`mapBits ι` is the `k`-marked segment of any vector matching on the range of
`ι` and missing the window off it. -/
theorem map_mapBits_markSeg {k' k : ℕ} (ι : Fin k' → Fin k)
    (w : List Step) (ī' : Fin k' → ℕ)
    (ī : Fin k → ℕ) (hr : ∀ i', ī (ι i') = ī' i') :
    ∀ off, (∀ i, (∀ i', ι i' ≠ i) → (ī i < off ∨ off + w.length ≤ ī i)) →
      (markSeg k' w ī' off).map (mapBits ι) = markSeg k w ī off := by
  induction w with
  | nil => intro off _; rfl
  | cons a w ih =>
    intro off houtside
    rw [markSeg, markSeg, List.map_cons, mapBits_mkLetter]
    have hbits : (fun i => if h : ∃ i', ι i' = i
          then bitsAt k' ī' off h.choose else false)
        = bitsAt k ī off := by
      funext i
      by_cases h : ∃ i', ι i' = i
      · rw [dif_pos h]
        simp only [bitsAt]
        have hch : ī (ι h.choose) = ī' h.choose := hr h.choose
        rw [h.choose_spec] at hch
        rw [← hch]
      · rw [dif_neg h]
        simp only [bitsAt]
        push Not at h
        rcases houtside i h with h1 | h1
        · rw [decide_eq_false (by omega)]
        · rw [decide_eq_false (by
            simp only [List.length_cons] at h1
            omega)]
    rw [hbits]
    congr 1
    apply ih
    intro i hi
    rcases houtside i hi with h1 | h1
    · exact Or.inl (by omega)
    · right
      simp only [List.length_cons] at h1
      omega

/-- **The arity-reduced acceptance capstone**: for an atom whose `ι`-range
coordinates lie in the middle window and whose other coordinates lie in the
boundary stretches, acceptance on the marked copied slice is acceptance of the
REDUCED-arity marked wrapped-flat word, by the machine pulled back along `ι`
and re-rooted through the (marked) boundary segments.  The reduced machine's
block map is literally `bFN M` (`bFN_pullback` ∘ `bFN_reRoot`): all periods
are `m`-free and assignment-free. -/
theorem accepts_copied_arity_reduced {k k' : ℕ} (M : DetAuto (MarkedN k))
    (ι : Fin k' → Fin k) (mS n : ℕ) (hm : 1 ≤ mS) (ī : Fin k → ℕ)
    (hmid : ∀ i', mS - 1 ≤ ī (ι i') ∧ ī (ι i') < mS + 2 * n + 1)
    (hbound : ∀ i, (∀ i', ι i' ≠ i) → ī i < mS - 1 ∨ mS + 2 * n + 1 ≤ ī i) :
    M.accepts (markAtN k (copiedSlice mS n) ī)
      ↔ (pullback (reRoot M (markSeg k (List.replicate (mS - 1) U) ī 0)
            (markSeg k (List.replicate (mS - 1) D) ī (mS + 2 * n + 1)))
          (mapBits ι)).accepts
          (markAtN k' (wrappedFlat n) (fun i' => ī (ι i') - (mS - 1))) := by
  classical
  rw [accepts_copied_reRoot M mS n hm, accepts_pullback,
    markAtN_eq_markSeg]
  -- push the reduced segment through the re-lettering
  have hmap : (markSeg k' (wrappedFlat n) (fun i' => ī (ι i') - (mS - 1)) 0).map
        (mapBits ι)
      = markSeg k (wrappedFlat n)
          (fun i => if ∃ i', ι i' = i then ī i - (mS - 1) else 2 * n + 2) 0 := by
    apply map_mapBits_markSeg ι (wrappedFlat n) _ _ ?_ 0 ?_
    · intro i'
      rw [if_pos ⟨i', rfl⟩]
    · intro i hi
      rw [if_neg (by push Not; exact fun i' => hi i')]
      right
      rw [length_wrappedFlat]
      omega
  rw [hmap]
  -- shift the window up by mS - 1
  rw [← markSeg_shift k (wrappedFlat n)
    (fun i => if ∃ i', ι i' = i then ī i - (mS - 1) else 2 * n + 2) (mS - 1) 0]
  simp only [Nat.zero_add]
  -- identify with the original vector: equal on the range, both outside off it
  have hcongr : markSeg k (wrappedFlat n)
        (fun i => (if ∃ i', ι i' = i then ī i - (mS - 1) else 2 * n + 2)
          + (mS - 1)) (mS - 1)
      = markSeg k (wrappedFlat n) ī (mS - 1) := by
    apply markSeg_congr_outside
    intro i
    by_cases h : ∃ i', ι i' = i
    · left
      rw [if_pos h]
      obtain ⟨i', rfl⟩ := h
      have := (hmid i').1
      omega
    · right
      rw [if_neg h, length_wrappedFlat]
      push Not at h
      rcases hbound i h with h1 | h1 <;> constructor <;> omega
  rw [hcongr]

end CopiedMark
