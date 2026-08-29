import RequestProject.CopiedSelector
import RequestProject.InverseZetaNotWRP

/-!
# §9 d4 / 2b — arity-1 helpers for the TIE point bridge

This file collects arity-1 ingredients used by the TIE point bridge.  The
capstone uses the budgeted row-indexed bridge in `CopiedTieSlice` rather than
a single `(mS % qM, n % pG)`-indexed gate.

An `hbud`-free target cannot be a direct port of the n-direction template
`SliceFasSelectorGA.tie_point_bridge_GA`, which threads `hbud` through its selector.  The
budgeted bridge keeps `hbud` explicit at the consumer boundary, while these helpers
still provide the arity-1 periodicity and selection infrastructure used by the
surrounding bridge work.

* `arity_one_hbud` — the automatic `C = 2` budget for arity-1 presentations, which
  discharges the `hbud` hypothesis of the equal-rank cell selector so that the cell
  config `cfgCellGAFL` is available for every `mS` with no external linear-growth
  assumption.
* `achievesDstar_iff_on_n_class_of_budget` — the n-residue-class transport of
  "achieves the `d*`-rank" that the activation-set folds consume.

The budgeted bridge avoids forcing this config into one uniform finite family before
the row is known; the finite row index records the bounded activation data selected
for the concrete row and budget proof.
-/

namespace CopiedTie2b

open WRP Step
open scoped Classical

/-- For an ARITY-1 presentation, the per-`mS` selected-atom budget `hbud` holds
automatically with `C = 2`: a selected atom `⟨c, x⟩` is a single coordinate with
`x 0 < |copiedSlice mS n| = 2(mS+n)`, so any `Nodup` list of them injects (via
evaluation at the unique coordinate) into `range (2(mS+n))`, bounding its length. -/
theorem arity_one_hbud (P : WRP.Presentation Step Step)
    (harity1 : ∀ c, P.toPoly.arity c = 1) :
    ∃ C : ℕ, ∀ (mS : ℕ), 1 ≤ mS →
      ∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ C * (mS + n + 1) := by
  refine ⟨2, fun mS hmS n hdom c l hnodup hsel => ?_⟩
  have hsub : Subsingleton (Fin (P.toPoly.arity c)) := by rw [harity1 c]; infer_instance
  have j0 : Fin (P.toPoly.arity c) := ⟨0, by rw [harity1 c]; omega⟩
  have hinj : Function.Injective (fun x : Fin (P.toPoly.arity c) → ℕ => x j0) := by
    intro x y h
    funext i
    have hxy : x j0 = y j0 := h
    rw [Subsingleton.elim i j0]; exact hxy
  have hmapnodup : (l.map (fun x => x j0)).Nodup := hnodup.map hinj
  have hbound : ∀ y ∈ l.map (fun x => x j0), y < 2 * (mS + n) := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨x, hxl, rfl⟩ := hy
    have hv : x j0 < (copiedSlice mS n).length := (hsel x hxl).1 j0
    rwa [length_copiedSlice] at hv
  have key : (l.map (fun x => x j0)).length ≤ 2 * (mS + n) := by
    rw [← List.toFinset_card_of_nodup hmapnodup]
    calc (l.map (fun x => x j0)).toFinset.card
        ≤ (Finset.range (2 * (mS + n))).card :=
          Finset.card_le_card (by
            intro y hy
            rw [List.mem_toFinset] at hy
            rw [Finset.mem_range]
            exact hbound y hy)
      _ = 2 * (mS + n) := Finset.card_range _
  rw [List.length_map] at key
  omega

section ConfigEP

open CopiedCells CopiedDstar SliceOrder CopiedAffineAt

/-- **"Achieves the d*-rank" agrees across an n residue class** (the n-leg of the selector-mS
config d*-membership transport).  At a FIXED mS,
`rank(cellTupleF rs mS t n) = dstarRankGA_m P hV mS n` agrees at any two n in the same class past a
threshold, given domain ∧ D-present at both.  Proof: the n-direction setup gives the rank window
decomposition `Rcell t + Bcell n` (`dstar_setup_fibred`, with `Bcell` affine-in-n via the
recurrence) and the n-affine d* `dstarC` (`dstarC_exists_fibred`, budget auto via
`arity_one_hbud`); their equality is EP-in-n (`vec_eq_EP_at`), and the agreement
`dstarRankGA_m = dstarC n` glues both ends through `iff_on_class`.  Used at a FIXED representative
row `mS` (so the per-rep n-threshold is a fixed nat). -/
theorem achievesDstar_iff_on_n_class_of_budget
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (Cbud : ℕ)
    (hbudC : ∀ (mS : ℕ), 1 ≤ mS →
      ∀ n, P.toPoly.domain (copiedSlice mS n) →
        ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
          (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
          l.length ≤ Cbud * (mS + n + 1))
    {B : ℕ} (_hB1 : 1 ≤ B) :
    ∃ (p0 : ℕ), 1 ≤ p0 ∧ ∀ (c : Fin P.toPoly.K)
      (rs : Fin (P.toPoly.arity c) → CopiedCells.RegionSpecF B) (mS : ℕ), 1 ≤ mS →
      (∀ i, (rs i).valid mS) → ∀ (t : ℕ), B + 1 ≤ t →
      ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → t + B + 1 ≤ n → t + B + 1 ≤ n' → n % p0 = n' % p0 →
        P.toPoly.domain (copiedSlice mS n) →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D) →
        P.toPoly.domain (copiedSlice mS n') →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS n') a
          ∧ P.toPoly.labelOf (copiedSlice mS n') a = D) →
        ((P.rank c (copiedSlice mS n) (cellTupleF rs mS t n)
            = CopiedDstar.dstarRankGA_m P hV mS n) ↔
         (P.rank c (copiedSlice mS n') (cellTupleF rs mS t n')
            = CopiedDstar.dstarRankGA_m P hV mS n')) := by
  classical
  obtain ⟨pstar, hpstar, hdstarC⟩ := CopiedDstarC.dstarC_exists_fibred P hV
  obtain ⟨m, p, Mc, hp, hmB, hMc, hbwd, hsetupB⟩ := CopiedSetup.dstar_setup_fibred P B
  set p0 : ℕ := p * pstar with hp0def
  have hp0 : 1 ≤ p0 := Nat.mul_pos hp hpstar
  have hp_dvd : p ∣ p0 := ⟨pstar, rfl⟩
  have hpstar_dvd : pstar ∣ p0 := ⟨p, by rw [hp0def]; ring⟩
  refine ⟨p0, hp0, fun c rs mS hm hvalid t ht => ?_⟩
  obtain ⟨Rcell, Bcell, PR, PBn, hwineq, hRrec, hBrec⟩ := hsetupB mS hm
  obtain ⟨dstarC, N0, hCaff, hCagree⟩ := hdstarC Cbud mS hm (hbudC mS hm)
  have hEP : EventuallyPeriodic
      (fun n => (fun i => Rcell c rs t i + Bcell c rs n i) = dstarC n) p0 := by
    refine CopiedAffineAt.vec_eq_EP_at hp0 (fun i => ?_) (fun i => ?_)
    · refine AffineOnResiduesAtZ.of_dvd hp hp_dvd hp0
        (AffineOnResiduesAtZ.of_recurrence (m := m) (S := PBn c rs i) hp (fun n hn => ?_))
      have hb := congrFun (hBrec c rs n hn) i
      rw [Pi.add_apply] at hb
      show Rcell c rs t i + Bcell c rs (n + p) i
        = Rcell c rs t i + Bcell c rs n i + PBn c rs i
      rw [hb]; ring
    · exact AffineOnResiduesAtZ.of_dvd hpstar hpstar_dvd hp0 (hCaff i)
  obtain ⟨Nep, hstep⟩ := hEP
  refine ⟨max Nep N0, fun n n' hn hn' hrn hrn' hmod hdom hDp hdom' hDp' => ?_⟩
  have hwn : P.rank c (copiedSlice mS n) (cellTupleF rs mS t n)
      = fun i => Rcell c rs t i + Bcell c rs n i := hwineq c rs hvalid t n ht hrn
  have hwn' : P.rank c (copiedSlice mS n') (cellTupleF rs mS t n')
      = fun i => Rcell c rs t i + Bcell c rs n' i := hwineq c rs hvalid t n' ht hrn'
  have hagn : CopiedDstar.dstarRankGA_m P hV mS n = dstarC n :=
    hCagree n (le_trans (le_max_right _ _) hn) hdom hDp
  have hagn' : CopiedDstar.dstarRankGA_m P hV mS n' = dstarC n' :=
    hCagree n' (le_trans (le_max_right _ _) hn') hdom' hDp'
  rw [hwn, hwn', hagn, hagn']
  exact SliceFasSelector.iff_on_class
    (Pr := fun x => (fun i => Rcell c rs t i + Bcell c rs x i) = dstarC x)
    hp0 hstep (le_trans (le_max_left _ _) hn) (le_trans (le_max_left _ _) hn') hmod

end ConfigEP

end CopiedTie2b
