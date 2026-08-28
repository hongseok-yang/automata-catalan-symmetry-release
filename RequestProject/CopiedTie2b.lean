import RequestProject.CopiedSelector
import RequestProject.CopiedTieGateF
import RequestProject.InverseZetaNotWRP
import RequestProject.CopiedDstarCMS
import RequestProject.CopiedGates

/-!
# §9 d4 / 2b — arity-1 helpers for the TIE point bridge

This file collects arity-1 ingredients used by the TIE point bridge.  The
capstone uses the budgeted row-indexed bridge in `CopiedTieSlice` rather than
a single `(mS % qM, n % pG)`-indexed gate.

An hbud-free target cannot be a direct port of the n-direction template
`tie_point_bridge_GA` (`SliceFasSelectorGA`), which threads `hbud` through
`eqRankD_cell_selector'`.  The budgeted bridge keeps `hbud` explicit at the consumer
boundary, while these helpers still provide the arity-1 periodicity and selection
infrastructure used by the surrounding bridge work.

* `arity_one_hbud` — the automatic `C = 2` budget for arity-1 presentations.
* `eqRankD_cell_selector_fibred_one` — `CopiedSelector.eqRankD_cell_selector_fibred`
  with `hbud` discharged, so the equal-rank cell config `cfgCellGAFL` is available
  for every `mS` with no external linear-growth assumption.

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

/-- **The `hbud`-free arity-1 equal-rank cell selector.**  Identical to
`CopiedSelector.eqRankD_cell_selector_fibred` but with the `hbud` hypothesis
discharged internally via `arity_one_hbud` (so the budget constant `C` is no
longer threaded).  The cell config `cfgCellGAFL` characterising `rank b = d*` is
thus available for every `mS` with no external linear-growth assumption. -/
theorem eqRankD_cell_selector_fibred_one (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity1 : ∀ c, P.toPoly.arity c = 1) :
    ∃ (B Bh M mthrL pstar p0 : ℕ),
      1 ≤ pstar ∧ pstar ∣ p0 ∧ 1 ≤ p0 ∧ B ≤ Bh ∧ M % 2 = 0 ∧ 1 ≤ Bh ∧
      ∀ (mS : ℕ), 1 ≤ mS →
      ∃ (N1 : ℕ)
        (S1L : ℕ → (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF B) → Finset ℕ)
        (F2L : ℕ → (c' : Fin P.toPoly.K) →
          (Fin (P.toPoly.arity c') → CopiedCells.RegionSpecF Bh) → Finset ℕ),
        2 * Bh + 2 ≤ N1 ∧
        (∀ κ c' rs, ∀ r ∈ S1L κ c' rs, r < M ∧ r % 2 = 1) ∧
        (∀ κ c' rs', ∀ f ∈ F2L κ c' rs', f < 2 * Bh + 2 ∧ f % 2 = 1) ∧
        ∀ n, N1 ≤ n → P.toPoly.domain (copiedSlice mS n) →
          (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a ∧
            P.toPoly.labelOf (copiedSlice mS n) a = D) →
          ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) b →
            P.toPoly.labelOf (copiedSlice mS n) b = D →
            (P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n ↔
              CopiedTieGate.cfgCellGAFL B Bh M mthrL (S1L (n % p0))
                (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (F2L (n % p0))
                (fun _ _ => ∅) mS n b) := by
  obtain ⟨B, Bh, M, mthrL, pstar, p0, hps, hpsd, hp0, hBB, hM2, hBh1, _hB1, hbody⟩ :=
    CopiedSelector.eqRankD_cell_selector_fibred P hV
  obtain ⟨C, hC⟩ := arity_one_hbud P harity1
  exact ⟨B, Bh, M, mthrL, pstar, p0, hps, hpsd, hp0, hBB, hM2, hBh1,
    fun mS hmS => hbody C mS hmS (hC mS hmS)⟩

section GateEP

open CopiedCells SliceMSO MSOMarkN CopiedGateEP CopiedSetupMS CopiedDstar
  SliceOrder CopiedDstarCMS CopiedRegionF

/-- **Gate-acceptance EP-in-mS, in candidate form.**  For a FIXED marked DFA `M` and an
mS-invariant deep shape `ds`, acceptance of `M` on the marked copied slice at the moving
cell tuple `mixedTupleF ds mS t0 n` is eventually periodic in `mS` at a machine-only
period `qC`.  Repackages `CopiedDstarCMS.gateF_deepShape_EP_mS_uniform` via the `gateF`
definition and `cellTupleF_deepShapeF`.  This is the gate half of the `mS % qM`-fold for
`gate_fold_2a`: a representative gate `M`, run on the actual (mS-varying) slice at a
cell-shaped candidate, has acceptance constant within each `mS`-residue class past
threshold.  (Use `ds := Sum.inl ∘ rs` for the `rs` from `cells_cover_one_mS`, making the
deep-shape hypothesis vacuous.) -/
theorem gate_accepts_EP_mS {B k : ℕ} (M : DetAuto (MarkedN k))
    (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ))
    (hdeep : ∀ i e, ds i = .inr e → 1 ≤ e.elim id id) (t0 n : ℕ) (hwin : t0 + B ≤ n) :
    ∃ qC, 1 ≤ qC ∧ EventuallyPeriodic
      (fun mS => M.accepts (markAtN k (copiedSlice mS n) (mixedTupleF ds mS t0 n))) qC := by
  obtain ⟨qC, hqC, hep⟩ := gateF_deepShape_EP_mS_uniform (B := B) M
  refine ⟨qC, hqC, ?_⟩
  have hfun : (fun mS => M.accepts (markAtN k (copiedSlice mS n) (mixedTupleF ds mS t0 n)))
            = (fun mS => gateF M (deepShapeF ds mS) mS t0 n) := by
    funext mS
    unfold gateF
    rw [cellTupleF_deepShapeF]
  rw [hfun]
  exact hep ds t0 n hwin hdeep

end GateEP

section DomainEP

open SliceMSO SliceOrder CopiedSetupMS CopiedGates SliceSelect

/-- **An MSO sentence's truth on the copied slice is EP-in-mS.**  Two-sided pumping:
`copiedSlice mS n = U^mS ++ (UD)^n ++ D^mS` (`copiedSlice_eq_blocks`), so as `mS` grows
both outer blocks grow uniformly; the Büchi DFA's acceptance is then EP-in-mS by
`accepts_two_sided_EP`. -/
theorem sentence_EP_mS (φ : MSO.Sentence Step) (n : ℕ) :
    ∃ q, 1 ≤ q ∧ EventuallyPeriodic
      (fun mS => φ.Sat (copiedSlice mS n) Fin.elim0 Fin.elim0) q := by
  obtain ⟨M, hM⟩ := SliceMSO.buchi φ
  obtain ⟨q, hq, hep⟩ := accepts_two_sided_EP M
    (fun mS => List.replicate mS U) (fun mS => List.replicate mS D)
    ((List.replicate n [U, D]).flatten) [] [] U D 0 0
    (fun mS _ => by simp) (fun mS _ => by simp)
  refine ⟨q, hq, ?_⟩
  refine eventuallyPeriodic_congr_eventually 1 (fun mS hmS => ?_) hep
  rw [copiedSlice_eq_blocks mS n hmS]
  exact (hM _).symm

/-- **`domain` is EP-in-mS on the copied slice** (the domain half of the fork-A regime
gap: needed so `domain` holds at the mS-residue representative). -/
theorem domain_EP_mS (P : WRP.Presentation Step Step) (n : ℕ) :
    ∃ q, 1 ≤ q ∧ EventuallyPeriodic (fun mS => P.toPoly.domain (copiedSlice mS n)) q := by
  obtain ⟨φ, hφ⟩ := P.toPoly.domainDef
  obtain ⟨q, hq, hep⟩ := sentence_EP_mS φ n
  exact ⟨q, hq, eventuallyPeriodic_congr_eventually 0
    (fun mS _ => hφ (copiedSlice mS n)) hep⟩

/-- **`D`-present (a selected `D`-atom exists) is EP-in-mS on the copied slice** (the
`D`-present half of the fork-A regime gap).  Together with `domain_EP_mS` this lets the
`d* = dstarRankGA_m` equality (`dstarC_exists_fibred_mS`, valid only under domain∧D-present)
be transported to the mS-residue representative for `rankEqDstar_atom_EP_mS`. -/
theorem Dpresent_EP_mS (P : WRP.Presentation Step Step) (n : ℕ) :
    ∃ q, 1 ≤ q ∧ EventuallyPeriodic (fun mS =>
      ∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
        ∧ P.toPoly.labelOf (copiedSlice mS n) a = D) q := by
  obtain ⟨q, hq, hep⟩ := sentence_EP_mS (SliceSelect.existsSentence P.toPoly D) n
  exact ⟨q, hq, eventuallyPeriodic_congr_eventually 0
    (fun mS _ => (SliceSelect.sat_existsSentence P.toPoly D (copiedSlice mS n)).symm) hep⟩

/-- **An MSO sentence's truth on the copied slice is EP-in-n** (the n-twin of `sentence_EP_mS`).
Single-block pumping: `copiedSlice mS n = U^mS ++ (UD)^n ++ D^mS` (`copiedSlice_eq_blocks`), so as
`n` grows the MIDDLE `(UD)^n` block grows with FIXED outer blocks; the Büchi DFA's acceptance is then
EP-in-n by `SliceMSO.detAuto_slice_eventuallyPeriodic` (the one-loop-slice EP).  Needed (with
`domain_EP_n`/`Dpresent_EP_n`) so the selector-mS bridge can transport domain∧D-present from the actual
`n` to the n-residue representative `rep κ` — the connection point between the n-direction d* `dstarC`
and the mS-direction d* `dstarC_mS`, which agree only via `dstarRankGA_m` under domain∧D-present. -/
theorem sentence_EP_n (φ : MSO.Sentence Step) (mS : ℕ) (hmS : 1 ≤ mS) :
    ∃ q, 1 ≤ q ∧ EventuallyPeriodic
      (fun n => φ.Sat (copiedSlice mS n) Fin.elim0 Fin.elim0) q := by
  obtain ⟨M, hM⟩ := SliceMSO.buchi φ
  obtain ⟨m, p, hp, hper⟩ := SliceMSO.detAuto_slice_eventuallyPeriodic M
    (List.replicate mS U) [U, D] (List.replicate mS D)
  have hep : EventuallyPeriodic
      (fun n => M.accepts (List.replicate mS U
        ++ (List.replicate n [U, D]).flatten ++ List.replicate mS D)) p := ⟨m, hper⟩
  refine ⟨p, hp, eventuallyPeriodic_congr_eventually 0 (fun n _ => ?_) hep⟩
  rw [copiedSlice_eq_blocks mS n hmS]
  exact (hM _).symm

/-- **`domain` is EP-in-n on the copied slice** (the n-twin of `domain_EP_mS`). -/
theorem domain_EP_n (P : WRP.Presentation Step Step) (mS : ℕ) (hmS : 1 ≤ mS) :
    ∃ q, 1 ≤ q ∧ EventuallyPeriodic (fun n => P.toPoly.domain (copiedSlice mS n)) q := by
  obtain ⟨φ, hφ⟩ := P.toPoly.domainDef
  obtain ⟨q, hq, hep⟩ := sentence_EP_n φ mS hmS
  exact ⟨q, hq, eventuallyPeriodic_congr_eventually 0
    (fun n _ => hφ (copiedSlice mS n)) hep⟩

/-- **`D`-present (a selected `D`-atom exists) is EP-in-n on the copied slice** (the n-twin of
`Dpresent_EP_mS`). -/
theorem Dpresent_EP_n (P : WRP.Presentation Step Step) (mS : ℕ) (hmS : 1 ≤ mS) :
    ∃ q, 1 ≤ q ∧ EventuallyPeriodic (fun n =>
      ∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
        ∧ P.toPoly.labelOf (copiedSlice mS n) a = D) q := by
  obtain ⟨q, hq, hep⟩ := sentence_EP_n (SliceSelect.existsSentence P.toPoly D) mS hmS
  exact ⟨q, hq, eventuallyPeriodic_congr_eventually 0
    (fun n _ => (SliceSelect.sat_existsSentence P.toPoly D (copiedSlice mS n)).symm) hep⟩

/-- **One-loop-slice acceptance is EP-in-n with period UNIFORM in the prefix/suffix.**  Unlike
`SliceMSO.detAuto_slice_eventuallyPeriodic` (per-start period via `iterate_eventuallyPeriodic`),
this uses `endofunction_EP_mul` on the loop-step function — whose period works for ALL start
states — so the SAME period `p` and threshold `m` serve every `pre`/`suf`.  This is what lets the
selector-mS bridge FOLD the domain n-period into the config period `p0` (the period must be fixed
before the `∀ mS` binder). -/
theorem detAuto_slice_EP_uniform {Alpha : Type*} (M : SliceMSO.DetAuto Alpha) (loop : List Alpha) :
    ∃ m p : ℕ, 1 ≤ p ∧ ∀ (pre suf : List Alpha) (n : ℕ), m ≤ n →
      (M.accepts (pre ++ (List.replicate (n + p) loop).flatten ++ suf) ↔
       M.accepts (pre ++ (List.replicate n loop).flatten ++ suf)) := by
  have := M.fintypeQ
  obtain ⟨m, p, hp, hper⟩ := endofunction_EP_mul (fun s => List.foldl M.δ s loop)
  refine ⟨m, p, hp, fun pre suf n hn => ?_⟩
  simp only [SliceMSO.DetAuto.accepts, List.foldl_append, SliceMSO.foldl_replicate_flatten]
  have hfun : (fun s => List.foldl M.δ s loop)^[n + p]
      = (fun s => List.foldl M.δ s loop)^[n] := by
    have h := hper 1 n hn; rwa [Nat.mul_one] at h
  rw [hfun]

/-- **MSO sentence truth on the copied slice is EP-in-n with both threshold and period
uniform in `mS`.**  This is the threshold-exposing form needed when the n-class representative
must be chosen before the actual `mS` is known. -/
theorem sentence_EP_n_uniform_floor (φ : MSO.Sentence Step) :
    ∃ N p, 1 ≤ p ∧ ∀ mS, 1 ≤ mS → ∀ n, N ≤ n →
      (φ.Sat (copiedSlice mS (n + p)) Fin.elim0 Fin.elim0 ↔
       φ.Sat (copiedSlice mS n) Fin.elim0 Fin.elim0) := by
  obtain ⟨N, p, hp, hper⟩ := SlicePeriodStar.mso_slice_EP_uniform φ [U, D]
  refine ⟨N, p, hp, fun mS hmS n hn => ?_⟩
  rw [copiedSlice_eq_blocks mS (n + p) hmS, copiedSlice_eq_blocks mS n hmS]
  exact hper (List.replicate mS U) (List.replicate mS D) n hn

/-- **`domain` is EP-in-n with threshold and period uniform in `mS`.** -/
theorem domain_EP_n_uniform_floor (P : WRP.Presentation Step Step) :
    ∃ N p, 1 ≤ p ∧ ∀ mS, 1 ≤ mS → ∀ n, N ≤ n →
      (P.toPoly.domain (copiedSlice mS (n + p)) ↔
       P.toPoly.domain (copiedSlice mS n)) := by
  obtain ⟨φ, hφ⟩ := P.toPoly.domainDef
  obtain ⟨N, p, hp, hper⟩ := sentence_EP_n_uniform_floor φ
  refine ⟨N, p, hp, fun mS hmS n hn => ?_⟩
  exact (hφ (copiedSlice mS (n + p))).trans
    ((hper mS hmS n hn).trans (hφ (copiedSlice mS n)).symm)

/-- **`D`-present is EP-in-n with threshold and period uniform in `mS`.** -/
theorem Dpresent_EP_n_uniform_floor (P : WRP.Presentation Step Step) :
    ∃ N p, 1 ≤ p ∧ ∀ mS, 1 ≤ mS → ∀ n, N ≤ n →
      ((∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS (n + p)) a
          ∧ P.toPoly.labelOf (copiedSlice mS (n + p)) a = D) ↔
       (∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D)) := by
  obtain ⟨N, p, hp, hper⟩ :=
    sentence_EP_n_uniform_floor (SliceSelect.existsSentence P.toPoly D)
  refine ⟨N, p, hp, fun mS hmS n hn => ?_⟩
  exact (SliceSelect.sat_existsSentence P.toPoly D (copiedSlice mS (n + p))).symm.trans
    ((hper mS hmS n hn).trans
      (SliceSelect.sat_existsSentence P.toPoly D (copiedSlice mS n)))

end DomainEP

section RankEP

open SliceOrder CopiedAffineAt CopiedDstarCMS CopiedSetupMS

/-- **`rank = dstarC` is EP-in-mS at a cell-shaped atom** (the equal-rank conjunct, in its
regime-free form against the AFFINE vector `dstarC`).  `vec_eq_EP_at` of the cell-rank
affineness (`rank_cell_mixedDeep_vec_uniform`) against the supplied affine `dstarC`, both
lifted to the merged period `p1 * pstar`.  The `dstarRankGA_m = dstarC` swap (valid only
under domain∧D-present, via `dstarC_exists_fibred_mS`) is applied later at assembly — where
`domain_EP_mS`/`Dpresent_EP_mS` carry the regime to the mS-residue representative. -/
theorem rankEqDstarC_atom_EP_mS (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    {B : ℕ} (hB : 1 ≤ B)
    (ds : Fin (P.toPoly.arity c) → CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ))
    (hdeep : ∀ j e, ds j = .inr e → 1 ≤ e.elim id id) (t n : ℕ) (hwin : t + B ≤ n)
    (pstar : ℕ) (hpstar : 1 ≤ pstar) (dstarC : ℕ → Fin P.d → ℤ)
    (hdstarCaff : ∀ i, AffineOnResiduesAtZ pstar (fun mS => dstarC mS i)) :
    ∃ q, 1 ≤ q ∧ EventuallyPeriodic
      (fun mS => P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n) = dstarC mS) q := by
  obtain ⟨p1, hp1, haff1⟩ := rank_cell_mixedDeep_vec_uniform P c ds hB hdeep
  refine ⟨p1 * pstar, Nat.mul_pos hp1 hpstar,
    vec_eq_EP_at (Nat.mul_pos hp1 hpstar) (fun i => ?_) (fun i => ?_)⟩
  · exact AffineOnResiduesAtZ.of_dvd hp1 (dvd_mul_right p1 pstar)
      (Nat.mul_pos hp1 hpstar) (haff1 t n hwin i)
  · exact AffineOnResiduesAtZ.of_dvd hpstar (dvd_mul_left pstar p1)
      (Nat.mul_pos hp1 hpstar) (hdstarCaff i)

end RankEP

section EPHelpers

open SliceOrder

/-- `EventuallyPeriodic` is closed under negation (used to turn the equal-rank conjunct
into the `∀b` implication `(selD ∧ rankEq) → ord = A.accepts ∨ ¬rankEq`). -/
theorem EP_not {Pr : ℕ → Prop} {p : ℕ} (hP : EventuallyPeriodic Pr p) :
    EventuallyPeriodic (fun n => ¬ Pr n) p := by
  obtain ⟨m, hm⟩ := hP
  exact ⟨m, fun n hn => not_congr (hm n hn)⟩

end EPHelpers

section MultibaseGateEP

open CopiedCells CopiedDstar CopiedSetupMS CopiedMark SliceReRoot CopiedDstarCMS
  MSOMarkN SliceMarkN SliceMSO SliceOrder CopiedRegionF SliceFamilyCell CopiedAffineAt

/-- mS-free upper bound forcing a single fibred descriptor's stretch validity. -/
def vbound {B : ℕ} : RegionSpecF B → ℕ
  | .core _ => 0
  | .prefIdx q => q + 2
  | .sufIdx l => l + 2

/-- A fixed fibred-descriptor tuple is valid at all large `mS`. -/
theorem regionSpecF_eventually_valid {B k : ℕ} (rs : Fin k → RegionSpecF B) :
    ∃ vth, ∀ mS, vth ≤ mS → ∀ j, (rs j).valid mS := by
  classical
  refine ⟨Finset.univ.sup (fun j => vbound (rs j)) + 1, fun mS hmS j => ?_⟩
  have hb : vbound (rs j) ≤ Finset.univ.sup (fun j => vbound (rs j)) :=
    Finset.le_sup (f := fun j => vbound (rs j)) (Finset.mem_univ j)
  cases h : rs j with
  | core r => simp [RegionSpecF.valid]
  | prefIdx q =>
      simp only [RegionSpecF.valid]
      have hvb : vbound (rs j) = q + 2 := by simp only [h, vbound]
      omega
  | sufIdx l =>
      simp only [RegionSpecF.valid]
      have hvb : vbound (rs j) = l + 2 := by simp only [h, vbound]
      omega

/-- **Per-coordinate-base gate-acceptance EP-in-mS.**  For a FIXED marked DFA `A` and a
fibred-descriptor tuple `rs` with PER-COORDINATE bases `t`, acceptance of `A` on the marked
copied slice at the per-coordinate-base tuple `fun j => (rs j).posAt mS (t j) n` is
eventually periodic in `mS`.

This is the ingredient the single-base `gate_accepts_EP_mS` cannot supply: two arity-1
cover cells can ride bulk clusters `Θ(n)` apart (`one_cluster` only bounds the spread
WITHIN one atom, vacuous across two distinct arity-1 atoms), so they cannot be expressed
at a common cluster base `δ < B`.  The fix gives each coordinate its OWN base.  Proof: the
generic, base-free `accepts_copied_arity_reduced` reduces copied-slice acceptance to a
boundary-stretch frame plus an mS-FREE wrapped-flat middle word (the per-coordinate-base
core marks); the base-free `cellSegU_deepForm`/`cellSegD_deepForm` put the marked U/D
stretches into two-sided growth form (core coords always land in `[mS-1, mS+2n]`, outside
both stretch windows, so the base is irrelevant there); `accepts_two_sided_EP_deepSuf_mp`
then pumps. -/
theorem gate_accepts_EP_mS_multibase {B k : ℕ} (A : DetAuto (MarkedN k))
    (rs : Fin k → RegionSpecF B) (t : Fin k → ℕ) (n : ℕ)
    (hBn : B ≤ n) (hwin : ∀ j, t j + B ≤ n) :
    ∃ q, 1 ≤ q ∧ EventuallyPeriodic
      (fun mS => A.accepts (markAtN k (copiedSlice mS n)
        (fun j => (rs j).posAt mS (t j) n))) q := by
  classical
  obtain ⟨qC, hqC, hMP⟩ := accepts_two_sided_EP_deepSuf_mp A
    (mkLetter k U (fun _ => false)) (mkLetter k D (fun _ => false))
  set ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ) := fun j => Sum.inl (rs j) with hds
  have hdeep : ∀ i e, ds i = .inr e → 1 ≤ e.elim id id := by
    intro i e h; rw [hds] at h; exact absurd h (by simp)
  obtain ⟨cP, preBaseFront, preBaseEnd, _hcP, hpreU⟩ := cellSegU_deepForm ds (n - B) n hdeep
  obtain ⟨cS, sufBaseFront, sufBaseEnd, _hcS, hsufD⟩ := cellSegD_deepForm ds (n - B) hdeep
  obtain ⟨vth, hvalid⟩ := regionSpecF_eventually_valid rs
  set midFixed : Fin (coreSet rs).card → ℕ :=
    fun i' => (coreSpec rs i').posAt (t (coreEmb rs i')) n with hmidF
  set MIDfixed : List (MarkedN k) :=
    (markAtN (coreSet rs).card (wrappedFlat n) midFixed).map (mapBits (coreEmb rs)) with hMIDF
  refine ⟨qC, hqC, ?_⟩
  have hQEP := hMP
    (fun mS => preBaseFront ++ List.replicate (mS - cP) (mkLetter k U (fun _ => false)))
    (fun mS => List.replicate (mS - cS) (mkLetter k D (fun _ => false)) ++ sufBaseEnd)
    (preBaseEnd ++ MIDfixed ++ sufBaseFront)
    preBaseFront sufBaseEnd cP cS
    (fun _ _ => rfl) (fun _ _ => rfl)
  refine eventuallyPeriodic_congr_eventually
    (max (max 1 vth) (max cP cS)) (fun mS hmS => ?_) hQEP
  have hm1 : 1 ≤ mS := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hmS)
  have hvmS : vth ≤ mS := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hmS)
  have hcPmS : cP ≤ mS := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hmS)
  have hcSmS : cS ≤ mS := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hmS)
  have hv : ∀ j, (rs j).valid mS := hvalid mS hvmS
  set ī : Fin k → ℕ := fun j => (rs j).posAt mS (t j) n with hīdef
  have hīi : ∀ i, ī i = (rs i).posAt mS (t i) n := fun i => rfl
  have hmixi : ∀ i, mixedTupleF ds mS (n - B) n i = (rs i).posAt mS (n - B) n := fun i => rfl
  have hcoreU : ∀ (r : RegionSpec B) (T : ℕ),
      0 + (mS - 1) ≤ (RegionSpecF.core r).posAt mS T n := by
    intro r T; rw [Nat.zero_add]; simp only [RegionSpecF.posAt]; omega
  have hcoreD : ∀ (r : RegionSpec B) (T : ℕ), T + B ≤ n →
      (RegionSpecF.core r).posAt mS T n < mS + 2 * n + 1 := by
    intro r T hT
    rcases r with _ | _ | ⟨f, e⟩ | ⟨l', e⟩ | ⟨δ, e⟩ <;>
      simp only [RegionSpecF.posAt, RegionSpec.posAt]
    · omega
    · omega
    · have := f.isLt; rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    · have := l'.isLt; rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    · have := δ.isLt; rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have hmid : ∀ i', mS - 1 ≤ ī (coreEmb rs i') ∧ ī (coreEmb rs i') < mS + 2 * n + 1 :=
    fun i' => cellTupleF_mid rs mS (t (coreEmb rs i')) n hm1 (hwin (coreEmb rs i')) i'
  have hbound : ∀ i, (∀ i', coreEmb rs i' ≠ i) →
      ī i < mS - 1 ∨ mS + 2 * n + 1 ≤ ī i :=
    fun i hi => cellTupleF_out rs mS (t i) n hv i hi
  rw [accepts_copied_arity_reduced A (coreEmb rs) mS n hm1 ī hmid hbound,
    accepts_pullback, accepts_reRoot]
  have hmidEq : (fun i' => ī (coreEmb rs i') - (mS - 1)) = midFixed := by
    funext i'
    show ī (coreEmb rs i') - (mS - 1) = (coreSpec rs i').posAt (t (coreEmb rs i')) n
    rw [hīi (coreEmb rs i'), rs_coreEmb rs i']
    show mS - 1 + (coreSpec rs i').posAt (t (coreEmb rs i')) n - (mS - 1)
      = (coreSpec rs i').posAt (t (coreEmb rs i')) n
    omega
  rw [hmidEq]
  have hUseg : markSeg k (List.replicate (mS - 1) U) ī 0
      = preBaseFront ++ List.replicate (mS - cP) (mkLetter k U (fun _ => false)) ++ preBaseEnd := by
    have e1 : markSeg k (List.replicate (mS - 1) U) ī 0
        = markSeg k (List.replicate (mS - 1) U) (mixedTupleF ds mS (n - B) n) 0 := by
      apply markSeg_congr_outside
      intro i
      rw [List.length_replicate, hīi i, hmixi i]
      cases hri : rs i with
      | core r => exact Or.inr ⟨Or.inr (hcoreU r (t i)), Or.inr (hcoreU r (n - B))⟩
      | prefIdx q => exact Or.inl rfl
      | sufIdx l => exact Or.inl rfl
    rw [e1, hpreU mS hcPmS]
  have hDseg : markSeg k (List.replicate (mS - 1) D) ī (mS + 2 * n + 1)
      = sufBaseFront ++ List.replicate (mS - cS) (mkLetter k D (fun _ => false)) ++ sufBaseEnd := by
    have e1 : markSeg k (List.replicate (mS - 1) D) ī (mS + 2 * n + 1)
        = markSeg k (List.replicate (mS - 1) D) (mixedTupleF ds mS (n - B) n) (mS + 2 * n + 1) := by
      apply markSeg_congr_outside
      intro i
      rw [List.length_replicate, hīi i, hmixi i]
      cases hri : rs i with
      | core r =>
          exact Or.inr ⟨Or.inl (hcoreD r (t i) (hwin i)), Or.inl (hcoreD r (n - B) (by omega))⟩
      | prefIdx q => exact Or.inl rfl
      | sufIdx l => exact Or.inl rfl
    rw [e1]
    have hsd := hsufD mS hcSmS
    have hslice : (n - B) + B = n := by omega
    rw [hslice] at hsd
    rw [hsd]
  rw [hUseg, hDseg]
  simp only [hMIDF, List.append_assoc]

/-- **MIXED (deep-capable) per-coordinate-base gate-acceptance EP-in-mS.**  Generalises
`gate_accepts_EP_mS_multibase` to a deep-capable shape `ds`: each coordinate is a fibred
descriptor or a DEEP offset (`inr`), and the `inl`-core coordinates carry INDEPENDENT bases.
Needed when a deep competitor atom (the d*-route's minimal equal-rank `D`-atom can ride the
growing suffix) is paired with a far-apart bulk candidate.  The deep coordinates are handled
by the deep `cellSegU_deepForm`/`cellSegD_deepForm` (their fixed blocks are base-free); the
`inl`-core middle marks reduce via `coreOnly ds` exactly as in the non-deep case. -/
theorem gate_accepts_EP_mS_mixed {B k : ℕ} (A : DetAuto (MarkedN k))
    (ds : Fin k → RegionSpecF B ⊕ (ℕ ⊕ ℕ))
    (hdeep : ∀ i e, ds i = .inr e → 1 ≤ e.elim id id)
    (t : Fin k → ℕ) (n : ℕ) (hBn : B ≤ n) (hwin : ∀ j, t j + B ≤ n) :
    ∃ q, 1 ≤ q ∧ EventuallyPeriodic
      (fun mS => A.accepts (markAtN k (copiedSlice mS n)
        (fun j => mixedPosAt (ds j) mS (t j) n))) q := by
  classical
  obtain ⟨qC, hqC, hMP⟩ := accepts_two_sided_EP_deepSuf_mp A
    (mkLetter k U (fun _ => false)) (mkLetter k D (fun _ => false))
  obtain ⟨cP, preBaseFront, preBaseEnd, _hcP, hpreU⟩ := cellSegU_deepForm ds (n - B) n hdeep
  obtain ⟨cS, sufBaseFront, sufBaseEnd, _hcS, hsufD⟩ := cellSegD_deepForm ds (n - B) hdeep
  obtain ⟨vth, hvth⟩ := deepShape_valid_ge ds hdeep
  set co : Fin k → RegionSpecF B := coreOnly ds with hco
  set midFixed : Fin (coreSet co).card → ℕ :=
    fun i' => (coreSpec co i').posAt (t (coreEmb co i')) n with hmidF
  set MIDfixed : List (MarkedN k) :=
    (markAtN (coreSet co).card (wrappedFlat n) midFixed).map (mapBits (coreEmb co)) with hMIDF
  refine ⟨qC, hqC, ?_⟩
  have hQEP := hMP
    (fun mS => preBaseFront ++ List.replicate (mS - cP) (mkLetter k U (fun _ => false)))
    (fun mS => List.replicate (mS - cS) (mkLetter k D (fun _ => false)) ++ sufBaseEnd)
    (preBaseEnd ++ MIDfixed ++ sufBaseFront)
    preBaseFront sufBaseEnd cP cS
    (fun _ _ => rfl) (fun _ _ => rfl)
  refine eventuallyPeriodic_congr_eventually
    (max (max 1 vth) (max cP cS)) (fun mS hmS => ?_) hQEP
  have hm1 : 1 ≤ mS := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hmS)
  have hvmS : vth ≤ mS := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hmS)
  have hcPmS : cP ≤ mS := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hmS)
  have hcSmS : cS ≤ mS := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hmS)
  have hvalid : ∀ i, (deepShapeF ds mS i).valid mS := hvth mS hvmS
  set ī : Fin k → ℕ := fun j => mixedPosAt (ds j) mS (t j) n with hīdef
  have hdsi : ∀ i, ī i = mixedPosAt (ds i) mS (t i) n := fun i => rfl
  have hmix2 : ∀ i, mixedTupleF ds mS (n - B) n i = mixedPosAt (ds i) mS (n - B) n := fun i => rfl
  have hmixco : ∀ j, RegionSpecF.isCore (co j) = true → ī j = (co j).posAt mS (t j) n := by
    intro j hj
    rw [hdsi j, hco]
    cases hdj : ds j with
    | inl r => simp only [coreOnly, mixedPosAt, hdj]
    | inr e =>
        have hfalse : RegionSpecF.isCore (co j) = false := by
          rw [hco]; simp only [coreOnly, hdj, RegionSpecF.isCore]
        rw [hfalse] at hj; exact absurd hj (by simp)
  have hcoreU : ∀ (r : RegionSpec B) (T : ℕ),
      0 + (mS - 1) ≤ (RegionSpecF.core r).posAt mS T n := by
    intro r T; rw [Nat.zero_add]; simp only [RegionSpecF.posAt]; omega
  have hcoreD : ∀ (r : RegionSpec B) (T : ℕ), T + B ≤ n →
      (RegionSpecF.core r).posAt mS T n < mS + 2 * n + 1 := by
    intro r T hT
    rcases r with _ | _ | ⟨f, e⟩ | ⟨l', e⟩ | ⟨δ, e⟩ <;>
      simp only [RegionSpecF.posAt, RegionSpec.posAt]
    · omega
    · omega
    · have := f.isLt; rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    · have := l'.isLt; rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    · have := δ.isLt; rcases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have hmid : ∀ i', mS - 1 ≤ ī (coreEmb co i') ∧ ī (coreEmb co i') < mS + 2 * n + 1 := by
    intro i'
    have hic : RegionSpecF.isCore (co (coreEmb co i')) = true :=
      (Finset.mem_filter.mp (coreEmb_mem co i')).2
    rw [hmixco (coreEmb co i') hic]
    exact cellTupleF_mid co mS (t (coreEmb co i')) n hm1 (hwin (coreEmb co i')) i'
  have hbound : ∀ i, (∀ i', coreEmb co i' ≠ i) →
      ī i < mS - 1 ∨ mS + 2 * n + 1 ≤ ī i := by
    intro i hi
    have hvi := hvalid i
    rw [hdsi i]
    cases hdi : ds i with
    | inl r =>
        cases r with
        | core rr =>
            exfalso
            refine not_mem_coreSet_of_not_range co i hi ?_
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
            rw [hco]; simp only [coreOnly, hdi, RegionSpecF.isCore]
        | prefIdx q =>
            left
            simp only [deepShapeF, hdi, RegionSpecF.valid] at hvi
            simp only [mixedPosAt, RegionSpecF.posAt]; omega
        | sufIdx l => right; simp only [mixedPosAt, RegionSpecF.posAt]; omega
    | inr e =>
        cases e with
        | inl i_off => right; simp only [mixedPosAt]; omega
        | inr i_off =>
            left
            simp only [deepShapeF, hdi, RegionSpecF.valid] at hvi
            simp only [mixedPosAt]; omega
  rw [accepts_copied_arity_reduced A (coreEmb co) mS n hm1 ī hmid hbound,
    accepts_pullback, accepts_reRoot]
  have hmidEq : (fun i' => ī (coreEmb co i') - (mS - 1)) = midFixed := by
    funext i'
    have hic : RegionSpecF.isCore (co (coreEmb co i')) = true :=
      (Finset.mem_filter.mp (coreEmb_mem co i')).2
    rw [hmixco (coreEmb co i') hic, rs_coreEmb co i']
    show mS - 1 + (coreSpec co i').posAt (t (coreEmb co i')) n - (mS - 1)
      = (coreSpec co i').posAt (t (coreEmb co i')) n
    omega
  rw [hmidEq]
  have hUseg : markSeg k (List.replicate (mS - 1) U) ī 0
      = preBaseFront ++ List.replicate (mS - cP) (mkLetter k U (fun _ => false)) ++ preBaseEnd := by
    have e1 : markSeg k (List.replicate (mS - 1) U) ī 0
        = markSeg k (List.replicate (mS - 1) U) (mixedTupleF ds mS (n - B) n) 0 := by
      apply markSeg_congr_outside
      intro i
      rw [List.length_replicate, hdsi i, hmix2 i]
      cases hdi : ds i with
      | inl r =>
          cases r with
          | core rr =>
              exact Or.inr ⟨Or.inr (by simp only [mixedPosAt]; exact hcoreU rr (t i)),
                Or.inr (by simp only [mixedPosAt]; exact hcoreU rr (n - B))⟩
          | prefIdx q => exact Or.inl (by simp only [mixedPosAt, RegionSpecF.posAt])
          | sufIdx l => exact Or.inl (by simp only [mixedPosAt, RegionSpecF.posAt])
      | inr e => cases e with
          | inl i_off => exact Or.inl (by simp only [mixedPosAt])
          | inr i_off => exact Or.inl (by simp only [mixedPosAt])
    rw [e1, hpreU mS hcPmS]
  have hDseg : markSeg k (List.replicate (mS - 1) D) ī (mS + 2 * n + 1)
      = sufBaseFront ++ List.replicate (mS - cS) (mkLetter k D (fun _ => false)) ++ sufBaseEnd := by
    have e1 : markSeg k (List.replicate (mS - 1) D) ī (mS + 2 * n + 1)
        = markSeg k (List.replicate (mS - 1) D) (mixedTupleF ds mS (n - B) n) (mS + 2 * n + 1) := by
      apply markSeg_congr_outside
      intro i
      rw [List.length_replicate, hdsi i, hmix2 i]
      cases hdi : ds i with
      | inl r =>
          cases r with
          | core rr =>
              exact Or.inr ⟨Or.inl (by simp only [mixedPosAt]; exact hcoreD rr (t i) (hwin i)),
                Or.inl (by simp only [mixedPosAt]; exact hcoreD rr (n - B) (by omega))⟩
          | prefIdx q => exact Or.inl (by simp only [mixedPosAt, RegionSpecF.posAt])
          | sufIdx l => exact Or.inl (by simp only [mixedPosAt, RegionSpecF.posAt])
      | inr e => cases e with
          | inl i_off => exact Or.inl (by simp only [mixedPosAt])
          | inr i_off => exact Or.inl (by simp only [mixedPosAt])
    rw [e1]
    have hsd := hsufD mS hcSmS
    have hslice : (n - B) + B = n := by omega
    rw [hslice] at hsd
    rw [hsd]
  rw [hUseg, hDseg]
  simp only [hMIDF, List.append_assoc]

end MultibaseGateEP

section ConfigEP

open CopiedCells CopiedDstar CopiedSetupMS SliceOrder CopiedAffineAt

/-- **The equal-rank class transport in mS** (the mS-twin of the selector's `htransBk`,
which transports across n-classes via `SliceFasSelector.iff_on_class` against the n-direction
EP).  For a fixed cell shape `rs`, base `t`, slice length `n`, and an affine `dstarC`, the
equal-rank predicate `rank(cellTupleF rs mS t n) = dstarC mS` agrees at any two `mS, mS'` in
the same residue class past a threshold — because it is EP-in-mS (`rankEqDstarC_atom_EP_mS`).
This is the per-residue ingredient for the selector config `S1L(mS)` being EP-in-mS, the sole
new ingredient of the fork-3b gate-machine route to the TIE point bridge. -/
theorem rankEq_iff_on_mS_class (P : WRP.Presentation Step Step) (c' : Fin P.toPoly.K)
    {B : ℕ} (hB : 1 ≤ B)
    (rs : Fin (P.toPoly.arity c') → RegionSpecF B) (t n : ℕ) (hwin : t + B ≤ n)
    (pstar : ℕ) (hpstar : 1 ≤ pstar) (dstarC : ℕ → Fin P.d → ℤ)
    (hdstarCaff : ∀ i, AffineOnResiduesAtZ pstar (fun mS => dstarC mS i)) :
    ∃ (q m₀ : ℕ), 1 ≤ q ∧ ∀ mS mS', m₀ ≤ mS → m₀ ≤ mS' → mS % q = mS' % q →
      ((P.rank c' (copiedSlice mS n) (cellTupleF rs mS t n) = dstarC mS) ↔
       (P.rank c' (copiedSlice mS' n) (cellTupleF rs mS' t n) = dstarC mS')) := by
  have hdeep : ∀ i (e : ℕ ⊕ ℕ), (Sum.inl (rs i)) = .inr e → 1 ≤ e.elim id id := by
    intro i e h; exact absurd h (by simp)
  obtain ⟨q, hq, m₀, hm0⟩ :=
    rankEqDstarC_atom_EP_mS P c' hB (fun j => Sum.inl (rs j)) hdeep t n hwin
      pstar hpstar dstarC hdstarCaff
  refine ⟨q, m₀, hq, fun mS mS' hm hm' hmod => ?_⟩
  exact SliceFasSelector.iff_on_class
    (Pr := fun x => P.rank c' (copiedSlice x n) (cellTupleF rs x t n) = dstarC x)
    hq hm0 hm hm' hmod

/-- **A range-filtered Finset is EP-in-mS when each membership predicate is.**  If each `Q r`
agrees across its own residue class past its own threshold, the Finset
`(range N).filter (Q · mS)` is constant on the merged residue class (period = product of the
per-element periods) past the merged threshold.  This turns the per-residue
`rankEq_iff_on_mS_class` into the selector config `S1L(mS)` (a `range`-filter image) being
EP-in-mS. -/
theorem range_filter_EP_mS (N : ℕ) (Q : ℕ → ℕ → Prop)
    (qs : ℕ → ℕ) (m0s : ℕ → ℕ) (hq : ∀ r, 1 ≤ qs r)
    (htrans : ∀ r, ∀ mS mS', m0s r ≤ mS → m0s r ≤ mS' → mS % qs r = mS' % qs r →
      (Q r mS ↔ Q r mS')) :
    ∃ q m0, 1 ≤ q ∧ ∀ mS mS', m0 ≤ mS → m0 ≤ mS' → mS % q = mS' % q →
      (Finset.range N).filter (fun r => Q r mS) = (Finset.range N).filter (fun r => Q r mS') := by
  classical
  refine ⟨∏ r ∈ Finset.range N, qs r, (Finset.range N).sup m0s, ?_,
    fun mS mS' hm hm' hmod => ?_⟩
  · exact Finset.prod_pos (f := qs) (fun r _ => hq r)
  apply Finset.filter_congr
  intro r hr
  have hdvd : qs r ∣ ∏ r' ∈ Finset.range N, qs r' := Finset.dvd_prod_of_mem qs hr
  have hmodr : mS % qs r = mS' % qs r := Nat.ModEq.of_dvd hdvd hmod
  have hm0r : m0s r ≤ (Finset.range N).sup m0s := Finset.le_sup hr
  exact htrans r mS mS' (le_trans hm0r hm) (le_trans hm0r hm') hmodr

/-
**"Achieves the d*-rank" agrees across an mS residue class** (the mS-leg of the selector-mS
config d*-membership transport).  For a (deep-capable) cell shape `ds`, base `t`, slice `n`,
`rank(mixedTupleF ds mS t n) = dstarRankGA_m P hV mS n` agrees at any two mS in the same residue
class past a threshold, GIVEN domain∧D-present at both endpoints.  Proof: the agreement
`dstarRankGA_m = dstarC_mS` (`dstarC_exists_fibred_mS`, UNIFORM threshold N0_mS) rewrites both sides
to the affine `dstarC_mS`, then `rankEqDstarC_atom_EP_mS` + `iff_on_class` transports the
pure-affine equality.  The threshold `Nn` (on n) is the d*-existence threshold; the per-call period
`q` and threshold `m₀` are uniform over the residue class. -/
/-- Abstract mS-row affine `dstarC` package used by the mS-class transport.
The arity-1 theorem and the emerging budgeted arbitrary-arity theorem both
produce this shape, with different routes to the agreement clause. -/
def DstarCAffineMS (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
  ∃ (pstar_mS : ℕ), 1 ≤ pstar_mS ∧ ∃ (Nn : ℕ), ∀ n, Nn ≤ n →
    ∃ (dstarC_mS : ℕ → Fin P.d → ℤ) (N0_mS : ℕ),
      (∀ i, AffineOnResiduesAtZ pstar_mS (fun mS => dstarC_mS mS i)) ∧
      ∀ mS, N0_mS ≤ mS →
        P.toPoly.domain (copiedSlice mS n) →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D) →
        CopiedDstar.dstarRankGA_m P hV mS n = dstarC_mS mS

theorem achievesDstar_iff_on_mS_class_of_dstarC_mS
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hdstar : DstarCAffineMS P hV) {B : ℕ} (hB1 : 1 ≤ B) :
    ∃ Nn : ℕ, ∀ (c : Fin P.toPoly.K)
      (ds : Fin (P.toPoly.arity c) → CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      (∀ j e, ds j = .inr e → 1 ≤ e.elim id id) → ∀ (t n : ℕ),
      t + B ≤ n → Nn ≤ n →
      ∃ (q m₀ : ℕ), 1 ≤ q ∧ ∀ mS mS', m₀ ≤ mS → m₀ ≤ mS' → mS % q = mS' % q →
        P.toPoly.domain (copiedSlice mS n) →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D) →
        P.toPoly.domain (copiedSlice mS' n) →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS' n) a
          ∧ P.toPoly.labelOf (copiedSlice mS' n) a = D) →
        ((P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)
            = CopiedDstar.dstarRankGA_m P hV mS n) ↔
         (P.rank c (copiedSlice mS' n) (mixedTupleF ds mS' t n)
            = CopiedDstar.dstarRankGA_m P hV mS' n)) := by
  obtain ⟨pstar_mS, hpstar_mS, Nn, hms⟩ := hdstar
  refine ⟨Nn, fun c ds hdeep t n hwin hn => ?_⟩
  obtain ⟨dstarC_mS, N0_mS, haff, hagree⟩ := hms n hn
  obtain ⟨q, hq, hep⟩ :=
    rankEqDstarC_atom_EP_mS P c hB1 ds hdeep t n hwin pstar_mS hpstar_mS dstarC_mS haff
  obtain ⟨m₀, hstep⟩ := hep
  refine ⟨q, max m₀ N0_mS, hq, fun mS mS' hm hm' hmod hdom hDp hdom' hDp' => ?_⟩
  have hagmS : CopiedDstar.dstarRankGA_m P hV mS n = dstarC_mS mS :=
    hagree mS (le_trans (le_max_right _ _) hm) hdom hDp
  have hagmS' : CopiedDstar.dstarRankGA_m P hV mS' n = dstarC_mS mS' :=
    hagree mS' (le_trans (le_max_right _ _) hm') hdom' hDp'
  rw [hagmS, hagmS']
  exact SliceFasSelector.iff_on_class
    (Pr := fun x => P.rank c (copiedSlice x n) (mixedTupleF ds x t n) = dstarC_mS x)
    hq hstep (le_trans (le_max_left _ _) hm) (le_trans (le_max_left _ _) hm') hmod

theorem achievesDstar_iff_on_mS_class (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity1 : ∀ c, P.toPoly.arity c = 1) {B : ℕ} (hB1 : 1 ≤ B) :
    ∃ Nn : ℕ, ∀ (c : Fin P.toPoly.K)
      (ds : Fin (P.toPoly.arity c) → CopiedCells.RegionSpecF B ⊕ (ℕ ⊕ ℕ)),
      (∀ j e, ds j = .inr e → 1 ≤ e.elim id id) → ∀ (t n : ℕ),
      t + B ≤ n → Nn ≤ n →
      ∃ (q m₀ : ℕ), 1 ≤ q ∧ ∀ mS mS', m₀ ≤ mS → m₀ ≤ mS' → mS % q = mS' % q →
        P.toPoly.domain (copiedSlice mS n) →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D) →
        P.toPoly.domain (copiedSlice mS' n) →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS' n) a
          ∧ P.toPoly.labelOf (copiedSlice mS' n) a = D) →
        ((P.rank c (copiedSlice mS n) (mixedTupleF ds mS t n)
            = CopiedDstar.dstarRankGA_m P hV mS n) ↔
         (P.rank c (copiedSlice mS' n) (mixedTupleF ds mS' t n)
            = CopiedDstar.dstarRankGA_m P hV mS' n)) :=
  achievesDstar_iff_on_mS_class_of_dstarC_mS P hV
    (CopiedDstarCMS.dstarC_exists_fibred_mS P hV harity1) hB1

/-- **"Achieves the d*-rank" agrees across an n residue class** (the n-leg of the selector-mS
config d*-membership transport; the n-direction twin of `achievesDstar_iff_on_mS_class`).  At a
FIXED mS, `rank(cellTupleF rs mS t n) = dstarRankGA_m P hV mS n` agrees at any two n in the same
class past a threshold, given domain∧D-present at both.  Proof: the n-direction setup gives the
rank window decomposition `Rcell t + Bcell n` (`dstar_setup_fibred`, with `Bcell` affine-in-n via
the recurrence) and the n-affine d* `dstarC` (`dstarC_exists_fibred`, budget auto via
`arity_one_hbud`); their equality is EP-in-n (`vec_eq_EP_at`), and the agreement
`dstarRankGA_m = dstarC n` glues both ends through `iff_on_class`.  Used at the FIXED rep mS = repM
(so the per-rep n-threshold is a fixed nat) as the second leg after `achievesDstar_iff_on_mS_class`. -/
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

theorem achievesDstar_iff_on_n_class (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity1 : ∀ c, P.toPoly.arity c = 1) {B : ℕ} (hB1 : 1 ≤ B) :
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
  obtain ⟨Cbud, hbudC⟩ := arity_one_hbud P harity1
  exact achievesDstar_iff_on_n_class_of_budget P hV Cbud hbudC hB1

/-- **Cell-representation identity** (definitional): a `RegionSpecF` cell tuple is the all-`inl`
mixed tuple.  Bridges the n-leg `achievesDstar_iff_on_n_class` (`cellTupleF` form) and the mS-leg
`achievesDstar_iff_on_mS_class` (`mixedTupleF` form). -/
theorem cellTupleF_eq_mixedTupleF_inl {B k : ℕ} (rs : Fin k → RegionSpecF B) (mS t n : ℕ) :
    cellTupleF rs mS t n = mixedTupleF (fun i => Sum.inl (rs i)) mS t n := by
  funext i; rfl

/-- **The mS-leg of the bulk d*-achievement transport, in `cellTupleF` form.**
At a FIXED slice-length `n`, "the cell `cellTupleF rs · t n` achieves the d*-rank" agrees across an
mS residue class (given domain ∧ D-present at both endpoints).  This is the mixed-tuple mS-leg
`achievesDstar_iff_on_mS_class` transported to the `cellTupleF` representation via
`cellTupleF_eq_mixedTupleF_inl`; composing it (at fixed `n`, transport `mS → repM`) with the n-leg
`achievesDstar_iff_on_n_class` (at fixed `mS = repM`, transport `n → rep κ`) gives the full BULK
rank-eq transport `Ach(mS,n) ↔ Ach(repM, rep κ)`.  Needs NO validity hypothesis on `rs` — sound for
any descriptor, including the `.core`-cluster descriptors that the bulk config arm `S1` sees. -/
theorem achievesDstar_mS_transport_of_dstarC_mS
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hdstar : DstarCAffineMS P hV) {B : ℕ} (hB1 : 1 ≤ B) :
    ∃ Nn : ℕ, ∀ (c : Fin P.toPoly.K)
      (rs : Fin (P.toPoly.arity c) → RegionSpecF B) (t n : ℕ),
      t + B ≤ n → Nn ≤ n →
      ∃ (q m₀ : ℕ), 1 ≤ q ∧ ∀ mS mS', m₀ ≤ mS → m₀ ≤ mS' → mS % q = mS' % q →
        P.toPoly.domain (copiedSlice mS n) →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D) →
        P.toPoly.domain (copiedSlice mS' n) →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS' n) a
          ∧ P.toPoly.labelOf (copiedSlice mS' n) a = D) →
        ((P.rank c (copiedSlice mS n) (cellTupleF rs mS t n)
            = CopiedDstar.dstarRankGA_m P hV mS n) ↔
         (P.rank c (copiedSlice mS' n) (cellTupleF rs mS' t n)
            = CopiedDstar.dstarRankGA_m P hV mS' n)) := by
  obtain ⟨Nn, hms⟩ := achievesDstar_iff_on_mS_class_of_dstarC_mS P hV hdstar hB1
  refine ⟨Nn, fun c rs t n htn hNn => ?_⟩
  have hdeep : ∀ j (e : ℕ ⊕ ℕ), (fun i => Sum.inl (rs i)) j = .inr e → 1 ≤ e.elim id id := by
    intro j e h; exact absurd h (by simp)
  obtain ⟨q, m₀, hq, hstep⟩ := hms c (fun i => Sum.inl (rs i)) hdeep t n htn hNn
  refine ⟨q, m₀, hq, fun mS mS' h1 h2 h3 hd1 hD1 hd2 hD2 => ?_⟩
  have h := hstep mS mS' h1 h2 h3 hd1 hD1 hd2 hD2
  rwa [← cellTupleF_eq_mixedTupleF_inl rs mS t n,
    ← cellTupleF_eq_mixedTupleF_inl rs mS' t n] at h

theorem achievesDstar_mS_transport (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity1 : ∀ c, P.toPoly.arity c = 1) {B : ℕ} (hB1 : 1 ≤ B) :
    ∃ Nn : ℕ, ∀ (c : Fin P.toPoly.K)
      (rs : Fin (P.toPoly.arity c) → RegionSpecF B) (t n : ℕ),
      t + B ≤ n → Nn ≤ n →
      ∃ (q m₀ : ℕ), 1 ≤ q ∧ ∀ mS mS', m₀ ≤ mS → m₀ ≤ mS' → mS % q = mS' % q →
        P.toPoly.domain (copiedSlice mS n) →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a
          ∧ P.toPoly.labelOf (copiedSlice mS n) a = D) →
        P.toPoly.domain (copiedSlice mS' n) →
        (∃ a, P.toPoly.selectedAtom (copiedSlice mS' n) a
          ∧ P.toPoly.labelOf (copiedSlice mS' n) a = D) →
        ((P.rank c (copiedSlice mS n) (cellTupleF rs mS t n)
            = CopiedDstar.dstarRankGA_m P hV mS n) ↔
         (P.rank c (copiedSlice mS' n) (cellTupleF rs mS' t n)
            = CopiedDstar.dstarRankGA_m P hV mS' n)) :=
  achievesDstar_mS_transport_of_dstarC_mS P hV
    (CopiedDstarCMS.dstarC_exists_fibred_mS P hV harity1) hB1

end ConfigEP

end CopiedTie2b
