/-
# `thm:wrp-not-closed` with paper-exact witnesses

`thm:wrp-not-closed` (paper.tex) is existential — its
witnesses `D` and `S` must themselves lie in the paper's `def:wrp` class.  The
Lean witnesses of `WRPCompWitness.lean` / `WRPNotClosedComp.lean` /
`SMapWRP.lean` live in the deliberately larger `WRP.IsWRP` (the
concat tie-order is `False` across blocks, so `χ` is not total; and the
sentinel/separator copies have arity `0`, violating the paper's `k_c ≥ 1`).
This file upgrades the witnesses into `WRP.IsWRPPaper` and restates the
theorem's three clauses with them:

* **`χ`-total concatenation** (`ccOrdT`/`ccPolyT`/`ccPresT`): the concat
  tie-order refined by "earlier block first" — exactly the paper's (R2)
  robustness construction (paper.tex).  The block-tag rank
  coordinate separates blocks, so the combined order `≺` is unchanged
  (`ccPresT_wrpOrd_iff`) and the outputs are identical
  (`ccPresT_isOutput_iff`); the refined `χ` is a strict total order when the
  component tie-orders are (`ccPolyT_valid`).  Packaged as
  `isWRPTieTotal_concat`, with `isWRPTieTotal_relabel` (relabelling keeps `χ`)
  and `wncPoly_valid` / `idPoly_valid` (the two block witnesses have genuine
  copy-then-position scan tie-orders).
* **arity positivity** via the `ArityLift` anchor: `liftPoly_valid` (the lift
  preserves `χ`-totality) and `isWRPPaper_restrict_nonempty` (a `χ`-total WRP
  map restricted to nonempty inputs lies in the paper's class).  The
  restriction is exactly the paper's own convention: with `k_c ≥ 1` no atom
  exists on `ε`, so the paper's `D` outputs `ε` there while the Lean `compD`
  outputs `G#` via its arity-`0` sentinel — the two agree on every nonempty
  input, and `ε ∈ L_{≥0}` makes the empty input irrelevant to all three
  clauses (see `WRPCompWitness.lean`'s header note).
* **the paper-exact witness** `compDPos` (= `D` on nonempty inputs, undefined
  at `ε`) with `compDPos_isWRPPaper`, and the three clauses:
  `wrp_not_closed_preimage_comp_paper` (claim 1: `D⁻¹(K) = L_{≥0} \ {ε}` not
  regular), `wrp_not_closed_composition_paper` (the Moreover clause with the
  left-to-right 2DFT `S`), and `wrp_not_closed_under_composition_paper` (two
  paper-exact WRP maps whose composite is not WRP — a fortiori not
  paper-exact WRP).

Trust: the concat/lift/relabel upgrades and claim 1 are axiom-clean; the
composition clauses admit `SliceMSO.buchi` (through
`lem:wrp-nonempty-regular`), exactly as the `IsWRP`-level originals.
-/
import RequestProject.WRPTieTotal
import RequestProject.WRPNotClosedComp
import RequestProject.SMapWRP
import RequestProject.ArityLift

open MSO

/-! ## Relabelling preserves `χ`-totality -/

namespace WRPClosures

section Relabel

variable {Alpha : Type*}

/-- The relabelled polyregular presentation keeps its selection and tie-order,
so paper-validity (`χ` a strict total order) transfers. -/
theorem relabelPoly_valid {Γ Γ' : Type*} [Fintype Γ] [DecidableEq Γ']
    (P : Polyreg.Presentation Alpha Γ) (hV : P.Valid) (ℓ : Γ → Γ') :
    (relabelPoly P ℓ).Valid where
  irrefl := fun w a ha => hV.irrefl w a ha
  trans := fun w a b c ha hb hc => hV.trans w a b c ha hb hc
  trichot := fun w a b ha hb => hV.trichot w a b ha hb

/-- **Output relabelling in the `χ`-total class** (`thm:wrp-closures` (iv)):
the relabelling construction of `isWRP_relabel` does not touch selection or
tie-order, so it preserves membership in the paper's `χ`-total class. -/
theorem isWRPTieTotal_relabel {Γ Γ' : Type*} [Fintype Γ] [DecidableEq Γ'] (ℓ : Γ → Γ')
    {T : List Alpha → Option (List Γ)} (h : WRP.IsWRPTieTotal T) :
    WRP.IsWRPTieTotal (fun w => (T w).map (List.map ℓ)) := by
  obtain ⟨P, hPV, hT⟩ := h
  have hV : P.Valid := P.valid_of_polyValid hPV
  refine ⟨relabelPres P ℓ, relabelPoly_valid P.toPoly hPV ℓ, fun w out' => ?_⟩
  show (T w).map (List.map ℓ) = some out' ↔ _
  constructor
  · intro hout'
    rcases hTw : T w with _ | out
    · rw [hTw] at hout'; exact absurd hout' (by simp)
    · refine ⟨((hT w out).mp hTw).1, ?_⟩
      have hval : out' = out.map ℓ := by
        rw [hTw] at hout'
        exact (Option.some.inj hout').symm
      rw [hval]
      exact relabelPres_isOutput_map P ℓ w out ((hT w out).mp hTw).2
  · rintro ⟨hdom, hOut'⟩
    obtain ⟨out, hPout, rfl⟩ := relabelPres_isOutput_of P ℓ w out' hOut'
    rw [(hT w out).mpr ⟨hdom, hPout⟩]
    rfl

end Relabel

/-! ## The `χ`-total concatenation (the paper's (R2) refinement)

`ccOrd` is `False` across blocks; the block-tag rank coordinate makes the
cross-block value of `χ` immaterial for the output order, but leaves `χ`
non-total.  `ccOrdT` refines it by "earlier block first" — the (R2)
construction — leaving the combined order `≺`, hence the outputs, unchanged. -/

section ConcatT

variable {Alpha Γ : Type} (sep : Γ) (Wf Wg : WRP.Presentation Alpha Γ)

/-- The block-refined concat tie-order: earlier block first; within a block,
the original `ccOrd`. -/
@[reducible] def ccOrdT (c c' : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg c) → ℕ) (ī' : Fin (ccArity Wf Wg c') → ℕ) : Prop :=
  ccBlock Wf Wg c < ccBlock Wf Wg c' ∨
    (ccBlock Wf Wg c = ccBlock Wf Wg c' ∧ ccOrd Wf Wg c c' w ī ī')

theorem ccOrdT_def (c c' : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg c) → ℕ) (ī' : Fin (ccArity Wf Wg c') → ℕ) :
    ccOrdT Wf Wg c c' w ī ī' ↔
      (ccBlock Wf Wg c < ccBlock Wf Wg c' ∨
        (ccBlock Wf Wg c = ccBlock Wf Wg c' ∧ ccOrd Wf Wg c c' w ī ī')) :=
  Iff.rfl

theorem ccOrdT_iff_of_block_eq {c c' : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)}
    (hbe : ccBlock Wf Wg c = ccBlock Wf Wg c') (w : List Alpha)
    (ī : Fin (ccArity Wf Wg c) → ℕ) (ī' : Fin (ccArity Wf Wg c') → ℕ) :
    ccOrdT Wf Wg c c' w ī ī' ↔ ccOrd Wf Wg c c' w ī ī' := by
  rw [ccOrdT_def]
  constructor
  · rintro (hlt | ⟨-, h⟩)
    · rw [hbe] at hlt; exact absurd hlt (lt_irrefl _)
    · exact h
  · intro h
    exact Or.inr ⟨hbe, h⟩

theorem ccOrdT_of_block_lt {c c' : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)}
    (hlt : ccBlock Wf Wg c < ccBlock Wf Wg c') (w : List Alpha)
    (ī : Fin (ccArity Wf Wg c) → ℕ) (ī' : Fin (ccArity Wf Wg c') → ℕ) :
    ccOrdT Wf Wg c c' w ī ī' :=
  (ccOrdT_def Wf Wg c c' w ī ī').mpr (Or.inl hlt)

theorem not_ccOrdT_of_block_gt {c c' : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)}
    (hgt : ccBlock Wf Wg c' < ccBlock Wf Wg c) (w : List Alpha)
    (ī : Fin (ccArity Wf Wg c) → ℕ) (ī' : Fin (ccArity Wf Wg c') → ℕ) :
    ¬ ccOrdT Wf Wg c c' w ī ī' := by
  rw [ccOrdT_def]
  rintro (h | ⟨h, -⟩) <;> omega

/-- The refined order is MSO-definable per copy pair: the block comparison is
a constant, so each of the nine copy-pair cases is `True`, `False`, or the
original `ccOrd` formula. -/
theorem ccOrdTDef (c c' : Fin (Wf.toPoly.K + 1 + Wg.toPoly.K)) :
    MSODefinableRel (ccArity Wf Wg c + ccArity Wf Wg c')
      (fun w ij => ccOrdT Wf Wg c c' w (fun t => ij (Fin.castAdd _ t))
        (fun t => ij (Fin.natAdd _ t))) := by
  rcases ccCopy_cases Wf Wg c with ⟨cf, rfl⟩ | rfl | ⟨cg, rfl⟩ <;>
    rcases ccCopy_cases Wf Wg c' with ⟨cf', rfl⟩ | rfl | ⟨cg', rfl⟩
  -- FF: same block, defer to `ccOrd`
  · exact mso_congr (fun w ij => (ccOrdT_iff_of_block_eq Wf Wg
        (by rw [ccBlock_F, ccBlock_F]) w _ _).symm) (ccOrdDef Wf Wg _ _)
  -- FS: block 0 < 1, `True`
  · exact mso_congr (R := fun _ _ => True) (fun w ij => iff_of_true trivial
      (ccOrdT_of_block_lt Wf Wg (by rw [ccBlock_F, ccBlock_S]; norm_num) w _ _))
      ⟨.tru, fun w ρ => by simp⟩
  -- FG: block 0 < 2, `True`
  · exact mso_congr (R := fun _ _ => True) (fun w ij => iff_of_true trivial
      (ccOrdT_of_block_lt Wf Wg (by rw [ccBlock_F, ccBlock_G]; norm_num) w _ _))
      ⟨.tru, fun w ρ => by simp⟩
  -- SF: block 1 > 0, `False`
  · exact mso_congr (fun w ij => iff_of_false not_false
      (not_ccOrdT_of_block_gt Wf Wg (by rw [ccBlock_F, ccBlock_S]; norm_num) w _ _))
      (mso_false _)
  -- SS: same block, defer to `ccOrd` (which is `False` there anyway)
  · exact mso_congr (fun w ij => (ccOrdT_iff_of_block_eq Wf Wg rfl w _ _).symm)
      (ccOrdDef Wf Wg _ _)
  -- SG: block 1 < 2, `True`
  · exact mso_congr (R := fun _ _ => True) (fun w ij => iff_of_true trivial
      (ccOrdT_of_block_lt Wf Wg (by rw [ccBlock_S, ccBlock_G]; norm_num) w _ _))
      ⟨.tru, fun w ρ => by simp⟩
  -- GF: block 2 > 0, `False`
  · exact mso_congr (fun w ij => iff_of_false not_false
      (not_ccOrdT_of_block_gt Wf Wg (by rw [ccBlock_F, ccBlock_G]; norm_num) w _ _))
      (mso_false _)
  -- GS: block 2 > 1, `False`
  · exact mso_congr (fun w ij => iff_of_false not_false
      (not_ccOrdT_of_block_gt Wf Wg (by rw [ccBlock_S, ccBlock_G]; norm_num) w _ _))
      (mso_false _)
  -- GG: same block, defer to `ccOrd`
  · exact mso_congr (fun w ij => (ccOrdT_iff_of_block_eq Wf Wg
        (by rw [ccBlock_G, ccBlock_G]) w _ _).symm) (ccOrdDef Wf Wg _ _)

variable [DecidableEq Γ]

/-- The concat polyregular presentation with the block-refined tie-order. -/
@[reducible] def ccPolyT : Polyreg.Presentation Alpha Γ :=
  { ccPoly sep Wf Wg with
    ord := ccOrdT Wf Wg
    ordDef := ccOrdTDef Wf Wg }

/-- The concat WRP presentation with the block-refined tie-order: same rank
data as `ccPres`. -/
@[reducible] def ccPresT : WRP.Presentation Alpha Γ :=
  { ccPres sep Wf Wg with toPoly := ccPolyT sep Wf Wg }

theorem ccPolyT_atomOrd_iff (w : List Alpha) (x y : (ccPres sep Wf Wg).toPoly.Atom) :
    (ccPolyT sep Wf Wg).atomOrd w x y ↔
      (ccBlock Wf Wg x.1 < ccBlock Wf Wg y.1 ∨
        (ccBlock Wf Wg x.1 = ccBlock Wf Wg y.1 ∧
          (ccPres sep Wf Wg).toPoly.atomOrd w x y)) :=
  Iff.rfl

/-- Rank coordinate `0` of a concat atom is its block index. -/
theorem rankOf_zero_eq_ccBlock (w : List Alpha) (x : (ccPres sep Wf Wg).toPoly.Atom) :
    (ccPres sep Wf Wg).rankOf w x (ccZero Wf Wg) = ccBlock Wf Wg x.1 := by
  rcases ccAtom_cases sep Wf Wg x with ⟨a, rfl⟩ | rfl | ⟨b, rfl⟩
  · rw [ccBlockVal_F]
    exact (ccBlock_F Wf Wg a.1).symm
  · rw [ccBlockVal_S]
    exact (ccBlock_S Wf Wg).symm
  · rw [ccBlockVal_G]
    exact (ccBlock_G Wf Wg b.1).symm

/-- **The refinement changes nothing about the output order**: on rank-equal
atoms the blocks agree (the block index is rank coordinate `0`), where the
refined `χ` coincides with the original; on rank-distinct atoms neither order
consults `χ`. -/
theorem ccPresT_wrpOrd_iff (w : List Alpha) (x y : (ccPres sep Wf Wg).toPoly.Atom) :
    (ccPresT sep Wf Wg).wrpOrd w x y ↔ (ccPres sep Wf Wg).wrpOrd w x y := by
  constructor
  · rintro (hlex | ⟨heq, hordT⟩)
    · exact Or.inl hlex
    · refine Or.inr ⟨heq, ?_⟩
      rcases (ccPolyT_atomOrd_iff sep Wf Wg w x y).mp hordT with hblk | ⟨-, hord⟩
      · exfalso
        rw [← rankOf_zero_eq_ccBlock sep Wf Wg w x,
          ← rankOf_zero_eq_ccBlock sep Wf Wg w y] at hblk
        have heq' : (ccPres sep Wf Wg).rankOf w x = (ccPres sep Wf Wg).rankOf w y := heq
        rw [congrFun heq' (ccZero Wf Wg)] at hblk
        exact lt_irrefl _ hblk
      · exact hord
  · rintro (hlex | ⟨heq, hord⟩)
    · exact Or.inl hlex
    · refine Or.inr ⟨heq, (ccPolyT_atomOrd_iff sep Wf Wg w x y).mpr (Or.inr ⟨?_, hord⟩)⟩
      rw [← rankOf_zero_eq_ccBlock sep Wf Wg w x,
        ← rankOf_zero_eq_ccBlock sep Wf Wg w y]
      exact congrFun heq (ccZero Wf Wg)

/-- The refined presentation has the same declarative outputs. -/
theorem ccPresT_isOutput_iff (w : List Alpha) (out : List Γ) :
    (ccPresT sep Wf Wg).IsOutput w out ↔ (ccPres sep Wf Wg).IsOutput w out := by
  constructor
  · rintro ⟨atoms, hnd, hmem, hpw, hout⟩
    exact ⟨atoms, hnd, hmem,
      hpw.imp (fun {a b} h => (ccPresT_wrpOrd_iff sep Wf Wg w a b).mp h), hout⟩
  · rintro ⟨atoms, hnd, hmem, hpw, hout⟩
    exact ⟨atoms, hnd, hmem,
      hpw.imp (fun {a b} h => (ccPresT_wrpOrd_iff sep Wf Wg w a b).mpr h), hout⟩

/-! Cross-block `ccOrd` is `False`, at the atom level. -/

theorem ccAtomOrd_fs_false (w : List Alpha) (a : Wf.toPoly.Atom) :
    ¬ (ccPres sep Wf Wg).toPoly.atomOrd w (ccfAtom sep Wf Wg a) (ccsAtom sep Wf Wg) := by
  show ¬ ccOrd Wf Wg (ccF Wf Wg a.1) (ccS Wf Wg) w
    (ccfAtom sep Wf Wg a).2 (ccsAtom sep Wf Wg).2
  rw [ccOrd_FS]
  exact not_false

theorem ccAtomOrd_fg_false (w : List Alpha) (a : Wf.toPoly.Atom) (b : Wg.toPoly.Atom) :
    ¬ (ccPres sep Wf Wg).toPoly.atomOrd w (ccfAtom sep Wf Wg a) (ccgAtom sep Wf Wg b) := by
  show ¬ ccOrd Wf Wg (ccF Wf Wg a.1) (ccG Wf Wg b.1) w
    (ccfAtom sep Wf Wg a).2 (ccgAtom sep Wf Wg b).2
  rw [ccOrd_FG]
  exact not_false

theorem ccAtomOrd_sf_false (w : List Alpha) (a : Wf.toPoly.Atom) :
    ¬ (ccPres sep Wf Wg).toPoly.atomOrd w (ccsAtom sep Wf Wg) (ccfAtom sep Wf Wg a) := by
  show ¬ ccOrd Wf Wg (ccS Wf Wg) (ccF Wf Wg a.1) w
    (ccsAtom sep Wf Wg).2 (ccfAtom sep Wf Wg a).2
  rw [ccOrd_SF]
  exact not_false

theorem ccAtomOrd_ss_false (w : List Alpha) :
    ¬ (ccPres sep Wf Wg).toPoly.atomOrd w (ccsAtom sep Wf Wg) (ccsAtom sep Wf Wg) := by
  show ¬ ccOrd Wf Wg (ccS Wf Wg) (ccS Wf Wg) w
    (ccsAtom sep Wf Wg).2 (ccsAtom sep Wf Wg).2
  rw [ccOrd_SS]
  exact not_false

theorem ccAtomOrd_sg_false (w : List Alpha) (b : Wg.toPoly.Atom) :
    ¬ (ccPres sep Wf Wg).toPoly.atomOrd w (ccsAtom sep Wf Wg) (ccgAtom sep Wf Wg b) := by
  show ¬ ccOrd Wf Wg (ccS Wf Wg) (ccG Wf Wg b.1) w
    (ccsAtom sep Wf Wg).2 (ccgAtom sep Wf Wg b).2
  rw [ccOrd_SG]
  exact not_false

theorem ccAtomOrd_gf_false (w : List Alpha) (b : Wg.toPoly.Atom) (a : Wf.toPoly.Atom) :
    ¬ (ccPres sep Wf Wg).toPoly.atomOrd w (ccgAtom sep Wf Wg b) (ccfAtom sep Wf Wg a) := by
  show ¬ ccOrd Wf Wg (ccG Wf Wg b.1) (ccF Wf Wg a.1) w
    (ccgAtom sep Wf Wg b).2 (ccfAtom sep Wf Wg a).2
  rw [ccOrd_GF]
  exact not_false

theorem ccAtomOrd_gs_false (w : List Alpha) (b : Wg.toPoly.Atom) :
    ¬ (ccPres sep Wf Wg).toPoly.atomOrd w (ccgAtom sep Wf Wg b) (ccsAtom sep Wf Wg) := by
  show ¬ ccOrd Wf Wg (ccG Wf Wg b.1) (ccS Wf Wg) w
    (ccgAtom sep Wf Wg b).2 (ccsAtom sep Wf Wg).2
  rw [ccOrd_GS]
  exact not_false

/-- **The refined tie-order is a strict total order on selected atoms** when
the component tie-orders are — the (R2) construction: block order first,
within a block the component's own strict total order. -/
theorem ccPolyT_valid (hPf : Wf.toPoly.Valid) (hPg : Wg.toPoly.Valid) :
    (ccPolyT sep Wf Wg).Valid := by
  refine ⟨?_, ?_, ?_⟩
  · -- irreflexivity
    intro w x hx hbad
    rcases (ccPolyT_atomOrd_iff sep Wf Wg w x x).mp hbad with hlt | ⟨-, hord⟩
    · exact lt_irrefl _ hlt
    · rcases ccAtom_cases sep Wf Wg x with ⟨a, rfl⟩ | rfl | ⟨b, rfl⟩
      · exact hPf.irrefl w a ((ccSelectedAtom_fAtom sep Wf Wg w a).mp hx)
          ((ccAtomOrd_ff sep Wf Wg w a a).mp hord)
      · exact ccAtomOrd_ss_false sep Wf Wg w hord
      · exact hPg.irrefl w b ((ccSelectedAtom_gAtom sep Wf Wg w b).mp hx)
          ((ccAtomOrd_gg sep Wf Wg w b b).mp hord)
  · -- transitivity
    intro w x y z hx hy hz hxy hyz
    rw [ccPolyT_atomOrd_iff] at hxy hyz
    rw [ccPolyT_atomOrd_iff]
    rcases hxy with hlt | ⟨heq, hord⟩ <;> rcases hyz with hlt' | ⟨heq', hord'⟩
    · exact Or.inl (hlt.trans hlt')
    · exact Or.inl (heq' ▸ hlt)
    · exact Or.inl (heq ▸ hlt')
    · refine Or.inr ⟨heq.trans heq', ?_⟩
      rcases ccAtom_cases sep Wf Wg x with ⟨a, rfl⟩ | rfl | ⟨b, rfl⟩
      · rcases ccAtom_cases sep Wf Wg y with ⟨a', rfl⟩ | rfl | ⟨b', rfl⟩
        · rcases ccAtom_cases sep Wf Wg z with ⟨a'', rfl⟩ | rfl | ⟨b'', rfl⟩
          · exact (ccAtomOrd_ff sep Wf Wg w a a'').mpr
              (hPf.trans w a a' a''
                ((ccSelectedAtom_fAtom sep Wf Wg w a).mp hx)
                ((ccSelectedAtom_fAtom sep Wf Wg w a').mp hy)
                ((ccSelectedAtom_fAtom sep Wf Wg w a'').mp hz)
                ((ccAtomOrd_ff sep Wf Wg w a a').mp hord)
                ((ccAtomOrd_ff sep Wf Wg w a' a'').mp hord'))
          · exact absurd hord' (ccAtomOrd_fs_false sep Wf Wg w a')
          · exact absurd hord' (ccAtomOrd_fg_false sep Wf Wg w a' b'')
        · exact absurd hord (ccAtomOrd_fs_false sep Wf Wg w a)
        · exact absurd hord (ccAtomOrd_fg_false sep Wf Wg w a b')
      · rcases ccAtom_cases sep Wf Wg y with ⟨a', rfl⟩ | rfl | ⟨b', rfl⟩
        · exact absurd hord (ccAtomOrd_sf_false sep Wf Wg w a')
        · exact absurd hord (ccAtomOrd_ss_false sep Wf Wg w)
        · exact absurd hord (ccAtomOrd_sg_false sep Wf Wg w b')
      · rcases ccAtom_cases sep Wf Wg y with ⟨a', rfl⟩ | rfl | ⟨b', rfl⟩
        · exact absurd hord (ccAtomOrd_gf_false sep Wf Wg w b a')
        · exact absurd hord (ccAtomOrd_gs_false sep Wf Wg w b)
        · rcases ccAtom_cases sep Wf Wg z with ⟨a'', rfl⟩ | rfl | ⟨b'', rfl⟩
          · exact absurd hord' (ccAtomOrd_gf_false sep Wf Wg w b' a'')
          · exact absurd hord' (ccAtomOrd_gs_false sep Wf Wg w b')
          · exact (ccAtomOrd_gg sep Wf Wg w b b'').mpr
              (hPg.trans w b b' b''
                ((ccSelectedAtom_gAtom sep Wf Wg w b).mp hx)
                ((ccSelectedAtom_gAtom sep Wf Wg w b').mp hy)
                ((ccSelectedAtom_gAtom sep Wf Wg w b'').mp hz)
                ((ccAtomOrd_gg sep Wf Wg w b b').mp hord)
                ((ccAtomOrd_gg sep Wf Wg w b' b'').mp hord'))
  · -- trichotomy
    intro w x y hx hy
    rw [ccPolyT_atomOrd_iff sep Wf Wg w x y, ccPolyT_atomOrd_iff sep Wf Wg w y x]
    rcases lt_trichotomy (ccBlock Wf Wg x.1) (ccBlock Wf Wg y.1) with hb | hb | hb
    · exact Or.inl (Or.inl hb)
    · rcases ccAtom_cases sep Wf Wg x with ⟨a, rfl⟩ | rfl | ⟨b, rfl⟩ <;>
        rcases ccAtom_cases sep Wf Wg y with ⟨a', rfl⟩ | rfl | ⟨b', rfl⟩
      -- FF
      · rcases hPf.trichot w a a'
            ((ccSelectedAtom_fAtom sep Wf Wg w a).mp hx)
            ((ccSelectedAtom_fAtom sep Wf Wg w a').mp hy) with h | h | h
        · exact Or.inl (Or.inr ⟨hb, (ccAtomOrd_ff sep Wf Wg w a a').mpr h⟩)
        · exact Or.inr (Or.inl (by rw [h]))
        · exact Or.inr (Or.inr (Or.inr ⟨hb.symm, (ccAtomOrd_ff sep Wf Wg w a' a).mpr h⟩))
      -- FS, FG, SF: blocks differ, contradicting `hb`
      · exfalso
        exact absurd hb (by rw [show (ccfAtom sep Wf Wg a).1 = ccF Wf Wg a.1 from rfl,
          show (ccsAtom sep Wf Wg).1 = ccS Wf Wg from rfl,
          ccBlock_F, ccBlock_S]; norm_num)
      · exfalso
        exact absurd hb (by rw [show (ccfAtom sep Wf Wg a).1 = ccF Wf Wg a.1 from rfl,
          show (ccgAtom sep Wf Wg b').1 = ccG Wf Wg b'.1 from rfl,
          ccBlock_F, ccBlock_G]; norm_num)
      · exfalso
        exact absurd hb (by rw [show (ccsAtom sep Wf Wg).1 = ccS Wf Wg from rfl,
          show (ccfAtom sep Wf Wg a').1 = ccF Wf Wg a'.1 from rfl,
          ccBlock_S, ccBlock_F]; norm_num)
      -- SS
      · exact Or.inr (Or.inl rfl)
      -- SG, GF, GS: blocks differ
      · exfalso
        exact absurd hb (by rw [show (ccsAtom sep Wf Wg).1 = ccS Wf Wg from rfl,
          show (ccgAtom sep Wf Wg b').1 = ccG Wf Wg b'.1 from rfl,
          ccBlock_S, ccBlock_G]; norm_num)
      · exfalso
        exact absurd hb (by rw [show (ccgAtom sep Wf Wg b).1 = ccG Wf Wg b.1 from rfl,
          show (ccfAtom sep Wf Wg a').1 = ccF Wf Wg a'.1 from rfl,
          ccBlock_G, ccBlock_F]; norm_num)
      · exfalso
        exact absurd hb (by rw [show (ccgAtom sep Wf Wg b).1 = ccG Wf Wg b.1 from rfl,
          show (ccsAtom sep Wf Wg).1 = ccS Wf Wg from rfl,
          ccBlock_G, ccBlock_S]; norm_num)
      -- GG
      · rcases hPg.trichot w b b'
            ((ccSelectedAtom_gAtom sep Wf Wg w b).mp hx)
            ((ccSelectedAtom_gAtom sep Wf Wg w b').mp hy) with h | h | h
        · exact Or.inl (Or.inr ⟨hb, (ccAtomOrd_gg sep Wf Wg w b b').mpr h⟩)
        · exact Or.inr (Or.inl (by rw [h]))
        · exact Or.inr (Or.inr (Or.inr ⟨hb.symm, (ccAtomOrd_gg sep Wf Wg w b' b).mpr h⟩))
    · exact Or.inr (Or.inr (Or.inl hb))

/-- **Concatenation with a separator in the `χ`-total class**
(`thm:wrp-closures` (iii) with the (R2)-refined tie-order): the concatenation
of two `χ`-total WRP maps is `χ`-total WRP. -/
theorem isWRPTieTotal_concat {f g : List Alpha → Option (List Γ)}
    (hf : WRP.IsWRPTieTotal f) (hg : WRP.IsWRPTieTotal g) :
    WRP.IsWRPTieTotal (fun w => match f w, g w with
      | some a, some b => some (a ++ [sep] ++ b)
      | _, _ => none) := by
  obtain ⟨Pf, hPVf, hPf⟩ := hf
  obtain ⟨Pg, hPVg, hPg⟩ := hg
  have hVf : Pf.Valid := Pf.valid_of_polyValid hPVf
  have hVg : Pg.Valid := Pg.valid_of_polyValid hPVg
  have hVT : (ccPresT sep Pf Pg).Valid :=
    (ccPresT sep Pf Pg).valid_of_polyValid (ccPolyT_valid sep Pf Pg hPVf hPVg)
  refine ⟨ccPresT sep Pf Pg, ccPolyT_valid sep Pf Pg hPVf hPVg, fun w out => ?_⟩
  show (match f w, g w with
      | some a, some b => some (a ++ [sep] ++ b)
      | _, _ => none) = some out ↔ _
  constructor
  · intro hout
    rcases hfw : f w with _ | outf
    · rw [hfw] at hout; exact absurd hout (by simp)
    · rcases hgw : g w with _ | outg
      · rw [hfw, hgw] at hout; exact absurd hout (by simp)
      · rw [hfw, hgw] at hout
        obtain ⟨hdomf, hOf⟩ := (hPf w outf).mp hfw
        obtain ⟨hdomg, hOg⟩ := (hPg w outg).mp hgw
        refine ⟨⟨hdomf, hdomg⟩, ?_⟩
        rw [← Option.some.inj hout]
        exact (ccPresT_isOutput_iff sep Pf Pg w _).mpr
          (ccPres_isOutput_append sep Pf Pg w outf outg hOf hOg)
  · rintro ⟨⟨hdomf, hdomg⟩, hOut⟩
    obtain ⟨outf, hOf⟩ := isWRP_some_of_domain hVf hPf hdomf
    obtain ⟨outg, hOg⟩ := isWRP_some_of_domain hVg hPg hdomg
    rw [hOf, hOg]
    have hAppend : (ccPresT sep Pf Pg).IsOutput w (outf ++ [sep] ++ outg) :=
      (ccPresT_isOutput_iff sep Pf Pg w _).mpr
        (ccPres_isOutput_append sep Pf Pg w outf outg
          ((hPf w outf).mp hOf).2 ((hPg w outg).mp hOg).2)
    have hu : out = outf ++ [sep] ++ outg :=
      isOutput_unique (ccPresT sep Pf Pg) hVT hOut hAppend
    rw [hu]

end ConcatT

end WRPClosures

/-! ## The arity lift preserves `χ`-totality -/

namespace ArityLift

variable {Alpha Gamma : Type*}

/-- The lifted polyregular presentation compares atoms through their original
coordinates and pins the anchor at `0`, so paper-validity transfers. -/
theorem liftPoly_valid {P : Polyreg.Presentation Alpha Gamma} (hV : P.Valid) :
    (liftPoly P).Valid where
  irrefl := fun w a ha hbad => by
    obtain ⟨c, v⟩ := a
    have haT := ((liftPoly_selectedAtom_iff P w c v).mp ha).2.2
    exact hV.irrefl w _ haT hbad
  trans := fun w a b cc ha hb hc hab hbc => by
    obtain ⟨ca, va⟩ := a
    obtain ⟨cb, vb⟩ := b
    obtain ⟨cx, vx⟩ := cc
    have haT := ((liftPoly_selectedAtom_iff P w ca va).mp ha).2.2
    have hbT := ((liftPoly_selectedAtom_iff P w cb vb).mp hb).2.2
    have hcT := ((liftPoly_selectedAtom_iff P w cx vx).mp hc).2.2
    exact hV.trans w _ _ _ haT hbT hcT hab hbc
  trichot := fun w a b ha hb => by
    obtain ⟨ca, va⟩ := a
    obtain ⟨cb, vb⟩ := b
    obtain ⟨h0a, -, haT⟩ := (liftPoly_selectedAtom_iff P w ca va).mp ha
    obtain ⟨h0b, -, hbT⟩ := (liftPoly_selectedAtom_iff P w cb vb).mp hb
    rcases hV.trichot w _ _ haT hbT with h | h | h
    · exact Or.inl h
    · refine Or.inr (Or.inl ?_)
      have hc : ca = cb := congrArg Sigma.fst h
      subst hc
      have hts : Fin.tail va = Fin.tail vb := by
        injection h with h1 h2
      have hv : va = vb := by
        rw [← cons0_tail_eq va h0a, ← cons0_tail_eq vb h0b, hts]
      rw [hv]
    · exact Or.inr (Or.inr h)

/-- **Arity-0 elimination in the paper's class**: a `χ`-total WRP map
restricted to nonempty inputs lies in the paper's `def:wrp` class
(`χ`-total and arity-positive). -/
theorem isWRPPaper_restrict_nonempty {T : List Alpha → Option (List Gamma)}
    (h : WRP.IsWRPTieTotal T) :
    WRP.IsWRPPaper (fun w => match w with | [] => none | _ => T w) := by
  obtain ⟨P, hPV, hT⟩ := h
  refine ⟨liftPres P, liftPoly_valid hPV, fun c => Nat.succ_pos _, fun w out => ?_⟩
  cases w with
  | nil =>
      constructor
      · intro h
        exact absurd h (by simp)
      · rintro ⟨⟨-, hlen⟩, -⟩
        simp at hlen
  | cons x rest =>
      show T (x :: rest) = some out ↔ _
      rw [hT (x :: rest) out]
      have hw : 0 < (x :: rest).length := by simp
      constructor
      · rintro ⟨hdom, hout⟩
        exact ⟨⟨hdom, hw⟩, (liftPres_isOutput_iff P hw out).mpr hout⟩
      · rintro ⟨⟨hdom, -⟩, hout⟩
        exact ⟨hdom, (liftPres_isOutput_iff P hw out).mp hout⟩

end ArityLift

/-! ## The witness blocks are `χ`-total -/

namespace WRPNotClosed

/-- **The two-copy witness presentation has a strict-total tie-order**: copy
first (sentinel before `B`), position second — a genuine scan-type order. -/
theorem wncPoly_valid : wncPoly.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · -- irreflexivity
    rintro w a - hbad
    rcases hbad with h | ⟨-, h⟩
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h
  · -- transitivity
    rintro w a b c - - - hab hbc
    rcases hab with h | ⟨he, hp⟩ <;> rcases hbc with h' | ⟨he', hp'⟩
    · exact Or.inl (h.trans h')
    · exact Or.inl (he' ▸ h)
    · exact Or.inl (he ▸ h')
    · exact Or.inr ⟨he.trans he', hp.trans hp'⟩
  · -- trichotomy
    rintro w a b - -
    rcases atom_cases a with rfl | ⟨p, rfl⟩ <;> rcases atom_cases b with rfl | ⟨q, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (Or.inl Nat.zero_lt_one)
    · exact Or.inr (Or.inr (Or.inl Nat.zero_lt_one))
    · have hidx : ∀ r : ℕ, idxPos c1 (fun _ => r) = r := fun r => by
        simp only [idxPos]
        split
        · next hc => exact absurd hc (by decide)
        · rfl
      rcases lt_trichotomy p q with h | rfl | h
      · refine Or.inl (Or.inr ⟨rfl, ?_⟩)
        show idxPos c1 (fun _ => p) < idxPos c1 (fun _ => q)
        rw [hidx, hidx]
        exact h
      · exact Or.inr (Or.inl rfl)
      · refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
        show idxPos c1 (fun _ => q) < idxPos c1 (fun _ => p)
        rw [hidx, hidx]
        exact h

/-- **The witness transduction is `χ`-total WRP** — same presentation as
`wncD_isWRP`, with the tie-order's strict totality made explicit. -/
theorem wncD_isWRPTieTotal : WRP.IsWRPTieTotal (fun w : List Step => some (wncD w)) :=
  ⟨wncPres, wncPoly_valid, fun w _out =>
    ⟨fun h => ⟨trivial, (Option.some.inj h) ▸ wncD_isOutput w⟩,
     fun ⟨_, hout⟩ => congrArg some
       (isOutput_unique wncPres wncPres_valid (wncD_isOutput w) hout)⟩⟩

end WRPNotClosed

/-! ## The paper-exact witness `D` and the three clauses -/

namespace WRPComp

open WRPNotClosed WRPClosures

/-- The identity transduction is `χ`-total WRP (its tie-order is the position
order, a strict total order — `idPoly_valid`). -/
theorem idStep_isWRPTieTotal : WRP.IsWRPTieTotal (fun w : List Step => some w) := by
  refine WRP.isWRPTieTotal_of_isPolyregular ⟨idPoly, idPoly_valid, fun w out => ?_⟩
  constructor
  · intro h
    obtain rfl : w = out := Option.some.inj h
    exact ⟨trivial, idPoly_isOutput w⟩
  · rintro ⟨-, hout⟩
    exact congrArg some (idPoly.isOutput_unique idPoly_valid (idPoly_isOutput w) hout)

/-- **`D` is `χ`-total WRP**: the relabelled blocks keep their strict-total
tie-orders, and the (R2)-refined concatenation `ccPresT` totalises `χ` across
the three blocks. -/
theorem compD_isWRPTieTotal : WRP.IsWRPTieTotal (fun w => some (compD w)) := by
  have h1 : WRP.IsWRPTieTotal (fun w : List Step => some ((wncD w).map relGB)) := by
    simpa using isWRPTieTotal_relabel relGB wncD_isWRPTieTotal
  have h2 : WRP.IsWRPTieTotal (fun w : List Step => some (w.map relStep)) := by
    simpa using isWRPTieTotal_relabel relStep idStep_isWRPTieTotal
  have h3 := isWRPTieTotal_concat (sep := GBD.sep) h1 h2
  convert h3 using 1
  funext w
  rfl

/-- **The paper-exact witness**: `D` restricted to nonempty inputs.  On the
paper's arity-positive convention no atom exists on `ε`, so this is exactly
the paper's `D` (which outputs `ε`'s worth of atoms there — none — while the
Lean `compD` emits `G#` via its arity-0 sentinel; the two agree on every
nonempty input). -/
def compDPos : List Step → Option (List GBD) := fun w =>
  match w with
  | [] => none
  | _ => some (compD w)

/-- **`D ∈ WRP` in the paper's `def:wrp` class**: `χ`-total by the (R2)
refinement, arity-positive by the anchor lift. -/
theorem compDPos_isWRPPaper : WRP.IsWRPPaper compDPos := by
  have h := ArityLift.isWRPPaper_restrict_nonempty compD_isWRPTieTotal
  convert h using 1
  funext w
  cases w <;> rfl

/-- The preimage of `K = G·Γ_D^*` under the paper-exact `D` is
`L_{≥0} \ {ε}`. -/
theorem preimage_compDPos_eq_LnnPos :
    {w : List Step | ∃ out, compDPos w = some out ∧ out ∈ compK} = LnnPos := by
  ext w
  cases w with
  | nil =>
      simp only [compDPos, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨out, hout, -⟩
        exact absurd hout (by simp)
      · rintro ⟨-, hne⟩
        exact absurd rfl hne
  | cons x rest =>
      simp only [compDPos, Set.mem_ofPred_eq, Option.some.injEq]
      constructor
      · rintro ⟨out, rfl, hmem⟩
        exact ⟨(head_compD_eq_g_iff (x :: rest)).mp hmem, by simp⟩
      · rintro ⟨hmem, -⟩
        exact ⟨compD (x :: rest), rfl, (head_compD_eq_g_iff (x :: rest)).mpr hmem⟩

/-- **`thm:wrp-not-closed`, claim 1, with the witness in the paper's
`def:wrp` class** (paper.tex): a paper-exact WRP map `D`
and a regular `K` with `D⁻¹(K)` not regular.  Axiom-clean. -/
theorem wrp_not_closed_preimage_comp_paper :
    ∃ (D : List Step → Option (List GBD)) (K : Set (List GBD)),
      WRP.IsWRPPaper D ∧ IsRegularLang K ∧
      ¬ IsRegularLang {w | ∃ out, D w = some out ∧ out ∈ K} := by
  refine ⟨compDPos, compK, compDPos_isWRPPaper, compK_isRegular, ?_⟩
  rw [preimage_compDPos_eq_LnnPos]
  exact not_regular_LnnPos

/-- `F_{≥0}` restricted to nonempty inputs — the composite of the paper-exact
`D` with `S`. -/
def Fge0Pos : List Step → Option (List GBD) := fun w =>
  match w with
  | [] => none
  | _ => Fge0 w

/-- `F_{≥0}` on nonempty inputs is not WRP: its nonempty-output preimage is
still `L_{≥0} \ {ε}`. -/
theorem Fge0Pos_not_isWRP : ¬ WRP.IsWRP Fge0Pos := by
  intro h
  have hreg := WRPNonemptyRegular.wrp_nonempty_preimage_regular Fge0Pos h
  have hset : {w : List Step | ∃ out, Fge0Pos w = some out ∧ out ≠ []} = LnnPos := by
    ext w
    cases w with
    | nil =>
        simp only [Fge0Pos, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨out, hout, -⟩
          exact absurd hout (by simp)
        · rintro ⟨-, hne⟩
          exact absurd rfl hne
    | cons x rest =>
        simp only [Fge0Pos, Fge0, Option.some.injEq, Set.mem_ofPred_eq, LnnPos]
        constructor
        · rintro ⟨out, rfl, hne⟩
          by_cases hw : ∀ i, i < (x :: rest).length → 0 ≤ height (x :: rest) i
          · exact ⟨hw, by simp⟩
          · rw [if_neg hw] at hne
            exact absurd rfl hne
        · rintro ⟨hmem, -⟩
          refine ⟨(x :: rest).map relStep, ?_, by simp⟩
          rw [if_pos (show ∀ i, i < (x :: rest).length → 0 ≤ height (x :: rest) i
            from hmem)]
  rw [hset] at hreg
  exact not_regular_LnnPos hreg

/-- **`thm:wrp-not-closed`, Moreover clause, with the witness in the
paper's `def:wrp` class**: the paper-exact `D` and regular `K` of claim 1,
and the left-to-right 2DFT `S`, such that any composite `S ∘ D` is not WRP —
a fortiori not paper-exact WRP. -/
theorem wrp_not_closed_composition_paper :
    ∃ (Dm : List Step → Option (List GBD)) (K : Set (List GBD)) (S : TwoDFT GBD GBD),
      WRP.IsWRPPaper Dm ∧ IsRegularLang K ∧
      ¬ IsRegularLang {w | ∃ out, Dm w = some out ∧ out ∈ K} ∧
      S.LeftToRight ∧
      ∀ SD : List Step → Option (List GBD),
        (∀ w out, SD w = some out ↔ ∃ y, Dm w = some y ∧ S.Computes y out) →
        ¬ WRP.IsWRP SD := by
  refine ⟨compDPos, compK, compS, compDPos_isWRPPaper, compK_isRegular, ?_,
    compS_leftToRight, ?_⟩
  · rw [preimage_compDPos_eq_LnnPos]
    exact not_regular_LnnPos
  · intro SD hSD hWRP
    have hEq : SD = Fge0Pos := by
      funext w
      cases w with
      | nil =>
          rcases hval : SD [] with _ | out
          · rfl
          · obtain ⟨y, hy, -⟩ := (hSD [] out).mp hval
            exact absurd hy (by simp [compDPos])
      | cons x rest =>
          have hval := compS_computes_compD (x :: rest)
          have hiff := hSD (x :: rest)
            (if ∀ i, i < (x :: rest).length → 0 ≤ height (x :: rest) i
              then (x :: rest).map relStep else [])
          show SD (x :: rest) = Fge0 (x :: rest)
          rw [show Fge0 (x :: rest) = some (if ∀ i, i < (x :: rest).length →
              0 ≤ height (x :: rest) i then (x :: rest).map relStep else []) from rfl]
          exact hiff.mpr ⟨compD (x :: rest), rfl, hval⟩
    exact Fge0Pos_not_isWRP (hEq ▸ hWRP)

/-- `S ∈ WRP` in the paper's `def:wrp` class: `sMap` has a direct arity-1
presentation whose validity is `χ`-totality. -/
theorem sMap_isWRPPaper : WRP.IsWRPPaper sMap :=
  WRP.isWRPPaper_of_isRegular sMap_isRegular

/-- **`thm:wrp-not-closed`, the "consequently", inside the paper's
`def:wrp` class**: two paper-exact WRP maps — `D` and the map `sMap` computed
by the left-to-right 2DFT `S` — whose composite is not WRP, a fortiori not
paper-exact WRP.  Hence the paper's `def:wrp` class is not closed under
composition. -/
theorem wrp_not_closed_under_composition_paper :
    ∃ (Dm : List Step → Option (List GBD)) (Sm : List GBD → Option (List GBD)),
      WRP.IsWRPPaper Dm ∧ WRP.IsWRPPaper Sm ∧
      (∀ y out, Sm y = some out ↔ compS.Computes y out) ∧
      ¬ WRP.IsWRP (fun w => (Dm w).bind Sm) := by
  refine ⟨compDPos, sMap, compDPos_isWRPPaper, sMap_isWRPPaper, ?_, ?_⟩
  · intro y out
    exact (compS_computes_iff_sMap y out).symm
  · have hEq : (fun w : List Step => (compDPos w).bind sMap) = Fge0Pos := by
      funext w
      cases w with
      | nil => rfl
      | cons x rest =>
          show (some (compD (x :: rest))).bind sMap = Fge0 (x :: rest)
          exact sMap_compD (x :: rest)
    rw [hEq]
    exact Fge0Pos_not_isWRP

end WRPComp
