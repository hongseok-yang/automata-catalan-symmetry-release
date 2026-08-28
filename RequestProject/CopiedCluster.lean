/-
# The fibred one-cluster property (§9 tower, Stage D assembly)

`one_cluster_fibred`: on the copied slice, beyond a machine-determined depth `B`
(quantified BEFORE the budget and the slice parameter `mS`) and a threshold `N`
(after them), no budget-respecting selected atom has two middle-block
coordinates `B`-deep and `B`-separated.  The assembly: enumerate the atom's
middle-window coordinates (`Finset.orderIsoOfFin`), reduce acceptance to the
wrapped-flat word at the pulled-back re-rooted machine
(`accepts_copied_arity_reduced` — positions `mS + 2j` land exactly on
`1 + 2j`), transport the budget through the reconstruction injection, and
apply `bad_pair_collapse_pinned` at period data independent of the machine's
boundary re-rooting (`bFN_pullback`, `bFN_reRoot`).
-/
import RequestProject.CopiedMark
import RequestProject.SliceGrowthCollapse

open Step MSOMarkN SliceMarkN SliceMSO SliceReRoot CopiedMark

namespace CopiedCluster

theorem one_cluster_fibred (P : WRP.Presentation Step Step) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ C mS : ℕ, 1 ≤ mS → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ c : Fin P.toPoly.K, ∀ ī : Fin (P.toPoly.arity c) → ℕ,
      P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, ī⟩ →
      (∀ l : List (Fin (P.toPoly.arity c) → ℕ), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
        l.length ≤ C * (mS + n + 1)) →
      ∀ (i₁ i₂ : Fin (P.toPoly.arity c)) (j j' : ℕ),
        (ī i₁ = mS + 2 * j ∨ ī i₁ = mS + 2 * j + 1) →
        (ī i₂ = mS + 2 * j' ∨ ī i₂ = mS + 2 * j' + 1) →
        B ≤ j → j + B ≤ j' → j' + B ≤ n → False := by
  classical
  -- per-copy selection machines and their (machine-level, mS-free) period data
  choose M hM using fun c => SliceGrowthCollapse.exists_selDFA P c
  choose mvc pvc hpvc hEPc using
    fun c => bFN_func_iterate_eventuallyPeriodic (M c)
  refine ⟨max 1 (Finset.univ.sup
    (fun c => (P.toPoly.arity c + 2) * (mvc c + pvc c) + 2)), le_max_left _ _,
    fun C mS hm => ?_⟩
  -- pinned thresholds: one per copy and reduced arity, uniform in the machine
  have hpin := fun (c : Fin P.toPoly.K) (k' : Fin (P.toPoly.arity c + 1)) =>
    SliceGrowthCollapse.bad_pair_collapse_pinned (m := k'.val)
      (mvc c) (pvc c) (hpvc c) (C * (mS + 1))
  choose Nck hNck using hpin
  refine ⟨Finset.univ.sup (fun c => Finset.univ.sup (fun k'' => Nck c k'')),
    fun n hn c ī hsel hcard i₁ i₂ j j' hb1 hb2 hBj hjj' hj'n => ?_⟩
  have hB1 : 1 ≤ max 1 (Finset.univ.sup
      (fun c => (P.toPoly.arity c + 2) * (mvc c + pvc c) + 2)) :=
    le_max_left _ _
  have hBc : (P.toPoly.arity c + 2) * (mvc c + pvc c) + 2
      ≤ max 1 (Finset.univ.sup
        (fun c => (P.toPoly.arity c + 2) * (mvc c + pvc c) + 2)) := by
    have h1 : (P.toPoly.arity c + 2) * (mvc c + pvc c) + 2
        ≤ Finset.univ.sup
          (fun c => (P.toPoly.arity c + 2) * (mvc c + pvc c) + 2) :=
      Finset.le_sup
        (f := fun c => (P.toPoly.arity c + 2) * (mvc c + pvc c) + 2)
        (Finset.mem_univ c)
    exact le_trans h1 (le_max_right _ _)
  -- validity bookkeeping
  have hlen : (copiedSlice mS n).length = 2 * (mS + n) := length_copiedSlice mS n
  have hvalid : ∀ i, ī i < (copiedSlice mS n).length := fun i => hsel.1 i
  have hval : ∀ i, ī i < 2 * (mS + n) := by
    intro i
    have h := hvalid i
    rw [hlen] at h
    exact h
  -- the middle-coordinate set and its order enumeration
  set S : Finset (Fin (P.toPoly.arity c)) :=
    Finset.univ.filter (fun i => mS - 1 ≤ ī i ∧ ī i < mS + 2 * n + 1) with hS
  have hSmem : ∀ i, i ∈ S ↔ (mS - 1 ≤ ī i ∧ ī i < mS + 2 * n + 1) := by
    intro i
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
  have hk'le : S.card ≤ P.toPoly.arity c := by
    calc S.card ≤ (Finset.univ : Finset (Fin (P.toPoly.arity c))).card :=
          Finset.card_le_univ S
      _ = P.toPoly.arity c := by rw [Finset.card_univ, Fintype.card_fin]
  set ι : Fin S.card → Fin (P.toPoly.arity c) :=
    fun i' => ((S.orderIsoOfFin rfl) i').val with hι
  have hιinj : Function.Injective ι := by
    intro a b h
    exact (S.orderIsoOfFin rfl).injective (Subtype.ext h)
  have hιmem : ∀ i', ι i' ∈ S := fun i' => ((S.orderIsoOfFin rfl) i').property
  have hιsurj : ∀ i ∈ S, ∃ i', ι i' = i := by
    intro i hi
    refine ⟨(S.orderIsoOfFin rfl).symm ⟨i, hi⟩, ?_⟩
    show ((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩)).val = i
    rw [OrderIso.apply_symm_apply]
  -- the middle/boundary dichotomy
  have hmid : ∀ i', mS - 1 ≤ ī (ι i') ∧ ī (ι i') < mS + 2 * n + 1 :=
    fun i' => (hSmem (ι i')).mp (hιmem i')
  have hbound : ∀ i, (∀ i', ι i' ≠ i) →
      ī i < mS - 1 ∨ mS + 2 * n + 1 ≤ ī i := by
    intro i hi
    by_contra hcon
    push Not at hcon
    obtain ⟨i', hi'⟩ := hιsurj i ((hSmem i).mpr hcon)
    exact hi i' hi'
  -- the boundary stretches, the reduced machine, and its period data
  set u : List (MarkedN (P.toPoly.arity c)) :=
    markSeg (P.toPoly.arity c) (List.replicate (mS - 1) U) ī 0 with hu
  set v : List (MarkedN (P.toPoly.arity c)) :=
    markSeg (P.toPoly.arity c) (List.replicate (mS - 1) D) ī
      (mS + 2 * n + 1) with hv
  set M'' : DetAuto (MarkedN S.card) :=
    pullback (reRoot (M c) u v) (mapBits ι) with hM''
  have hbfn : SliceMarkN.bFN M'' = SliceMarkN.bFN (M c) :=
    (bFN_pullback (reRoot (M c) u v) ι).trans (bFN_reRoot (M c) u v)
  have hEP'' : ∀ g, mvc c ≤ g →
      (SliceMarkN.bFN M'')^[g + pvc c] = (SliceMarkN.bFN M'')^[g] := by
    intro g hg
    rw [hbfn]
    exact hEPc c g hg
  -- the reduced vector, its validity, and acceptance
  set ī' : Fin S.card → ℕ := fun i' => ī (ι i') - (mS - 1) with hī'
  have hval' : ∀ i', ī' i' < (wrappedFlat n).length := by
    intro i'
    show ī (ι i') - (mS - 1) < (wrappedFlat n).length
    rw [length_wrappedFlat]
    have h1 := (hmid i').2
    omega
  have hacc : (M c).accepts (markAtN (P.toPoly.arity c) (copiedSlice mS n) ī) :=
    (hM c (copiedSlice mS n) ī hvalid).mpr hsel.2
  have hacc'' : M''.accepts (markAtN S.card (wrappedFlat n) ī') :=
    (accepts_copied_arity_reduced (M c) ι mS n hm ī hmid hbound).mp hacc
  -- the budget transport through the reconstruction injection
  have hcard'' : ∀ l : List (Fin S.card → ℕ), l.Nodup →
      (∀ y ∈ l, (∀ i, y i < (wrappedFlat n).length) ∧
        M''.accepts (markAtN S.card (wrappedFlat n) y)) →
      l.length ≤ C * (mS + 1) * (n + 1) := by
    intro l hnd hmem
    set recon : (Fin S.card → ℕ) → (Fin (P.toPoly.arity c) → ℕ) :=
      fun y i => if h : ∃ i', ι i' = i then y h.choose + (mS - 1) else ī i
      with hrecon
    have hreconι : ∀ y i', recon y (ι i') = y i' + (mS - 1) := by
      intro y i'
      show (if h : ∃ i'', ι i'' = ι i' then y h.choose + (mS - 1)
          else ī (ι i')) = y i' + (mS - 1)
      rw [dif_pos (⟨i', rfl⟩ : ∃ i'', ι i'' = ι i')]
      show y (⟨i', rfl⟩ : ∃ i'', ι i'' = ι i').choose + (mS - 1)
          = y i' + (mS - 1)
      have hch : (⟨i', rfl⟩ : ∃ i'', ι i'' = ι i').choose = i' :=
        hιinj (⟨i', rfl⟩ : ∃ i'', ι i'' = ι i').choose_spec
      rw [hch]
    have hreconout : ∀ y i, (∀ i', ι i' ≠ i) → recon y i = ī i := by
      intro y i hi
      show (if h : ∃ i', ι i' = i then y h.choose + (mS - 1) else ī i) = ī i
      have hni : ¬ ∃ i', ι i' = i := by
        rintro ⟨i', hi'⟩
        exact hi i' hi'
      rw [dif_neg hni]
    have hreconinj : Function.Injective recon := by
      intro x y h
      funext i'
      have h1 := congrFun h (ι i')
      rw [hreconι x i', hreconι y i'] at h1
      omega
    -- each reconstructed tuple is a selected atom of the copied slice
    have hreconsel : ∀ y ∈ l, P.toPoly.selectedAtom (copiedSlice mS n)
        ⟨c, recon y⟩ := by
      intro y hy
      obtain ⟨hyval, hyacc⟩ := hmem y hy
      have hreconmid : ∀ i', mS - 1 ≤ recon y (ι i')
          ∧ recon y (ι i') < mS + 2 * n + 1 := by
        intro i'
        rw [hreconι y i']
        have h1 := hyval i'
        rw [length_wrappedFlat] at h1
        omega
      have hreconbound : ∀ i, (∀ i', ι i' ≠ i) →
          recon y i < mS - 1 ∨ mS + 2 * n + 1 ≤ recon y i := by
        intro i hi
        rw [hreconout y i hi]
        exact hbound i hi
      -- the boundary segments of the reconstruction agree with the original's
      have hsegU : markSeg (P.toPoly.arity c) (List.replicate (mS - 1) U)
          (recon y) 0 = u := by
        rw [hu]
        apply markSeg_congr_outside
        intro i
        rw [List.length_replicate]
        by_cases h : ∃ i', ι i' = i
        · obtain ⟨i', rfl⟩ := h
          have hr := hreconι y i'
          have hmidl := (hmid i').1
          right
          exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
        · exact Or.inl (hreconout y i (fun i' hi' => h ⟨i', hi'⟩))
      have hsegD : markSeg (P.toPoly.arity c) (List.replicate (mS - 1) D)
          (recon y) (mS + 2 * n + 1) = v := by
        rw [hv]
        apply markSeg_congr_outside
        intro i
        by_cases h : ∃ i', ι i' = i
        · obtain ⟨i', rfl⟩ := h
          have hr := hreconι y i'
          have h1 := hyval i'
          rw [length_wrappedFlat] at h1
          have hmidr := (hmid i').2
          right
          exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
        · exact Or.inl (hreconout y i (fun i' hi' => h ⟨i', hi'⟩))
      -- the reduced vector of the reconstruction is the original tuple
      have hredvec : (fun i' => recon y (ι i') - (mS - 1)) = y := by
        funext i'
        rw [hreconι y i']
        omega
      have hacc_recon : (M c).accepts (markAtN (P.toPoly.arity c)
          (copiedSlice mS n) (recon y)) := by
        rw [accepts_copied_arity_reduced (M c) ι mS n hm (recon y)
          hreconmid hreconbound]
        rw [hredvec]
        rw [hsegU]
        rw [hsegD]
        exact hyacc
      have hreconval : ∀ t, recon y t < (copiedSlice mS n).length := by
        intro t
        rw [hlen]
        by_cases h : ∃ i', ι i' = t
        · obtain ⟨i', rfl⟩ := h
          have hr := hreconι y i'
          have h1 := hyval i'
          rw [length_wrappedFlat] at h1
          omega
        · rw [hreconout y t (fun i' hi' => h ⟨i', hi'⟩)]
          exact hval t
      exact ⟨hreconval,
        (hM c (copiedSlice mS n) (recon y) hreconval).mp hacc_recon⟩
    have hmapped := hcard (l.map recon) (hnd.map hreconinj)
      (fun x hx => by
        rw [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact hreconsel y hy)
    rw [List.length_map] at hmapped
    have hfac : mS + n + 1 ≤ (mS + 1) * (n + 1) := by
      have h1 : mS + n + 1 ≤ mS * n + (mS + n + 1) :=
        Nat.le_add_left (mS + n + 1) (mS * n)
      have h2 : mS * n + (mS + n + 1) = (mS + 1) * (n + 1) := by ring
      rw [← h2]
      exact h1
    calc l.length ≤ C * (mS + n + 1) := hmapped
      _ ≤ C * ((mS + 1) * (n + 1)) := Nat.mul_le_mul (le_refl C) hfac
      _ = C * (mS + 1) * (n + 1) := by ring
  -- the bad pair sits in the middle window, hence on the range of ι
  have hi₁S : i₁ ∈ S := by
    refine (hSmem i₁).mpr ⟨?_, ?_⟩ <;> rcases hb1 with h | h <;> omega
  have hi₂S : i₂ ∈ S := by
    refine (hSmem i₂).mpr ⟨?_, ?_⟩ <;> rcases hb2 with h | h <;> omega
  obtain ⟨ĩ₁, hĩ₁⟩ := hιsurj i₁ hi₁S
  obtain ⟨ĩ₂, hĩ₂⟩ := hιsurj i₂ hi₂S
  -- positions shift exactly: mS + 2j ↦ 1 + 2j
  have hpos₁ : ī' ĩ₁ = 1 + 2 * j ∨ ī' ĩ₁ = 1 + 2 * j + 1 := by
    have h1 : ī' ĩ₁ = ī (ι ĩ₁) - (mS - 1) := rfl
    rw [h1, hĩ₁]
    rcases hb1 with h | h
    · left; omega
    · right; omega
  have hpos₂ : ī' ĩ₂ = 1 + 2 * j' ∨ ī' ĩ₂ = 1 + 2 * j' + 1 := by
    have h1 : ī' ĩ₂ = ī (ι ĩ₂) - (mS - 1) := rfl
    rw [h1, hĩ₂]
    rcases hb2 with h | h
    · left; omega
    · right; omega
  -- depth bounds at the reduced arity, via monotonicity in the arity
  have hk'lt : S.card < P.toPoly.arity c + 1 := by omega
  have hmono : (S.card + 2) * (mvc c + pvc c)
      ≤ (P.toPoly.arity c + 2) * (mvc c + pvc c) :=
    Nat.mul_le_mul (by omega) (le_refl (mvc c + pvc c))
  have hP1B : (S.card + 2) * (mvc c + pvc c) + 2
      ≤ max 1 (Finset.univ.sup
        (fun c => (P.toPoly.arity c + 2) * (mvc c + pvc c) + 2)) :=
    le_trans (Nat.add_le_add_right hmono 2) hBc
  have hbj1 : (S.card + 2) * (mvc c + pvc c) + 2 ≤ j := le_trans hP1B hBj
  have hbj2 : j + (S.card + 2) * (mvc c + pvc c) + 2 ≤ j' := by
    rw [Nat.add_assoc]
    exact le_trans (Nat.add_le_add_left hP1B j) hjj'
  have hbj3 : j' + (S.card + 2) * (mvc c + pvc c) + 2 ≤ n := by
    rw [Nat.add_assoc]
    exact le_trans (Nat.add_le_add_left hP1B j') hj'n
  -- the threshold bound at this copy and reduced arity
  have hNle : Nck c ⟨S.card, hk'lt⟩ ≤ n := by
    have h1 : Nck c ⟨S.card, hk'lt⟩
        ≤ Finset.univ.sup (fun k'' => Nck c k'') :=
      Finset.le_sup (f := fun k'' => Nck c k'') (Finset.mem_univ _)
    have h2 : Finset.univ.sup (fun k'' => Nck c k'')
        ≤ Finset.univ.sup (fun c => Finset.univ.sup (fun k'' => Nck c k'')) :=
      Finset.le_sup (f := fun c => Finset.univ.sup (fun k'' => Nck c k''))
        (Finset.mem_univ c)
    omega
  exact hNck c ⟨S.card, hk'lt⟩ M'' hEP'' n hNle ī' hval' hacc'' hcard''
    ĩ₁ ĩ₂ j j' hpos₁ hpos₂ hbj1 hbj2 hbj3

end CopiedCluster
