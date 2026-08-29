/-
# The suffix-run atomOrd gate (§9 single-gate selector-mS, slope-0 boundary)

When the boundary `D^mS` suffix run ties the minimal rank `d*` (the slope-0 all-tie case), it
contributes `~mS` equal-rank selected `D`-atoms.  The tie gate's competitor quantifier
`∀b sel-D (rank b = d* → atomOrd(a,b))` over them collapses to ONE MSO clause
"∀ p in the final maximal D-run, sel-D(p) → ordDef(a, p)" — `atomOrd = ordDef` is MSO, so a single
universal-over-positions clause realises it (no per-shape config; the mS-growing boundary shapes are
folded into one DFA whose acceptance is EP-in-mS by run periodicity).

* `inFinalDRun` — the MSO "position in the final maximal D-run" guard + its sat lemma.
* `gordNB` — the `ordDef` address map with NO base slot (the no-`z` twin of `SliceFasGatesGA.gord`).
* `sufOrdClause` — the universal-over-the-competitor-coord atomOrd clause (the `cellClause` shape with
  `inFinalDRun` in place of the cell-config decode).
* `gate_semantic_split` — the logical core of the single-gate integration: the tie competitor
  quantifier splits into a CORE part plus per-residue-class suffix-run and prefix-run parts.
* `affine_class_uniform` / `class_uniform_of_dom` — the slope-0 collapse the split's backward
  direction consumes.

The clause shape mirrors `SliceFasGatesGA.cellClause` (the universal-over-config version).
-/
import RequestProject.CopiedTieGate

namespace CopiedSufRunGate

open WRP Step MSO MSOMarkN

/-- **"position `x_0` lies in the final maximal D-run."**  MSO formula with one free FO variable:
the letter at `x_0` is `D`, and every later valid position is also `D`. -/
def inFinalDRun : MSO.Formula Step 1 0 :=
  MSO.Formula.and (MSO.Formula.labelEq 0 D)
    (MSO.Formula.faFO (MSO.Formula.imp (MSO.Formula.lt 1 0) (MSO.Formula.labelEq 0 D)))

theorem sat_inFinalDRun (w : List Step) (ρ : Fin 1 → ℕ) (σ : Fin 0 → Finset ℕ) :
    (inFinalDRun).Sat w ρ σ ↔
      (w[ρ 0]? = some D ∧ ∀ q, q < w.length → ρ 0 < q → w[q]? = some D) := by
  have hc0 : ∀ q : ℕ, (Fin.cons q ρ : Fin 2 → ℕ) 0 = q := fun q => rfl
  have hc1 : ∀ q : ℕ, (Fin.cons q ρ : Fin 2 → ℕ) 1 = ρ 0 := fun q => rfl
  unfold inFinalDRun
  simp only [MSO.Formula.sat_and, SliceFasGates.sat_faFO, SliceFasGates.sat_imp,
    MSO.Formula.sat_lt, MSO.Formula.sat_labelEq, hc0, hc1]

/-- The `ordDef` address map WITHOUT a base slot (the no-`z` twin of `SliceFasGatesGA.gord`):
the `c`-atom (`ordDef`'s first block) maps to the HIGH mark block `arity c' + ·`, the `c'`-atom
(second block) to the LOW bound block `·`. -/
def gordNB (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) :
    Fin (P.toPoly.arity c + P.toPoly.arity c') →
    Fin (P.toPoly.arity c + P.toPoly.arity c') :=
  fun idx => if h : idx.1 < P.toPoly.arity c
    then ⟨P.toPoly.arity c' + idx.1, by omega⟩
    else ⟨idx.1 - P.toPoly.arity c, by have := idx.2; omega⟩

/-- **The suffix-run atomOrd clause.**  For the marked `c`-atom `a`: every `c'`-tuple `xb` all of
whose coordinates lie in the final D-run and which is a selected `D`-atom is `ordDef`-preceded by `a`.
This is the `cellClause` shape with NO base slot and `inFinalDRun` in place of the cell-config decode;
it folds the (slope-0 all-tie) boundary competitors into ONE clause. -/
noncomputable def sufOrdClause (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K) :
    MSO.Formula Step (P.toPoly.arity c) 0 :=
  SliceFasGatesGA.faFOs (P.toPoly.arity c') (MSO.Formula.imp
    (MSO.Formula.and
      (MSOMarkN.andList ((List.finRange (P.toPoly.arity c')).map (fun i =>
        SliceFasGates.relabelFO
          (fun _ : Fin 1 =>
            (⟨i.1, by have := i.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          inFinalDRun)))
      (MSO.Formula.and
        (SliceFasGates.relabelFO
          (fun t : Fin (P.toPoly.arity c') =>
            (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          (P.toPoly.selDef c').choose)
        (SliceFasGates.relabelFO
          (fun t : Fin (P.toPoly.arity c') =>
            (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c')))
          (P.toPoly.labelDef c' D).choose)))
    (SliceFasGates.relabelFO (gordNB P c c') (P.toPoly.ordDef c c').choose))

/-- Composition: the low embedding reads the bound tuple `pb`. -/
theorem comp_embNB (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (pb : Fin (P.toPoly.arity c') → ℕ) (ī : Fin (P.toPoly.arity c) → ℕ) :
    (SliceFasGatesGA.appFO pb ī) ∘ (fun t : Fin (P.toPoly.arity c') =>
        (⟨t.1, by have := t.2; omega⟩ : Fin (P.toPoly.arity c + P.toPoly.arity c'))) = pb := by
  funext t
  exact SliceFasGatesGA.appFO_low pb ī t.1 (by have := t.2; omega) (by have := t.2; omega)

/-- Composition: the `gordNB` relabel reads `(ī, pb)` in `ordDef`'s block convention. -/
theorem comp_gordNB (P : WRP.Presentation Step Step) (c c' : Fin P.toPoly.K)
    (pb : Fin (P.toPoly.arity c') → ℕ) (ī : Fin (P.toPoly.arity c) → ℕ) :
    ((fun t => ((SliceFasGatesGA.appFO pb ī) ∘ gordNB P c c') (Fin.castAdd (P.toPoly.arity c') t))
        = ī)
    ∧ ((fun t => ((SliceFasGatesGA.appFO pb ī) ∘ gordNB P c c') (Fin.natAdd (P.toPoly.arity c) t))
        = pb) := by
  constructor
  · funext t
    show SliceFasGatesGA.appFO pb ī (gordNB P c c' (Fin.castAdd _ t)) = ī t
    have hg : gordNB P c c' (Fin.castAdd (P.toPoly.arity c') t)
        = ⟨P.toPoly.arity c' + t.1, by have := t.2; omega⟩ := by
      unfold gordNB
      rw [dif_pos (show ((Fin.castAdd (P.toPoly.arity c') t) : ℕ) < P.toPoly.arity c from t.2)]
      rfl
    rw [hg, SliceFasGatesGA.appFO_high pb ī t.1 t.2 (by have := t.2; omega)]
  · funext t
    show SliceFasGatesGA.appFO pb ī (gordNB P c c' (Fin.natAdd _ t)) = pb t
    have hg : gordNB P c c' (Fin.natAdd (P.toPoly.arity c) t) = ⟨t.1, by have := t.2; omega⟩ := by
      unfold gordNB
      rw [dif_neg (show ¬(((Fin.natAdd (P.toPoly.arity c) t) : ℕ) < P.toPoly.arity c) from by
        have hv : ((Fin.natAdd (P.toPoly.arity c) t) : ℕ) = P.toPoly.arity c + t.1 := rfl
        omega)]
      congr 1
      show ((Fin.natAdd (P.toPoly.arity c) t) : ℕ) - P.toPoly.arity c = (t : ℕ)
      have hv : ((Fin.natAdd (P.toPoly.arity c) t) : ℕ) = P.toPoly.arity c + t.1 := rfl
      omega
    rw [hg]
    exact SliceFasGatesGA.appFO_low pb ī t.1 (by have := t.2; omega) (by have := t.2; omega)

/-! ## The PREFIX twin (the `U^mS` initial run) -/

/-- **"position `x_0` lies in the initial maximal U-run."**  MSO: the letter at `x_0` is `U`, and
every earlier valid position is also `U`. -/
def inInitialURun : MSO.Formula Step 1 0 :=
  MSO.Formula.and (MSO.Formula.labelEq 0 U)
    (MSO.Formula.faFO (MSO.Formula.imp (MSO.Formula.lt 0 1) (MSO.Formula.labelEq 0 U)))

theorem sat_inInitialURun (w : List Step) (ρ : Fin 1 → ℕ) (σ : Fin 0 → Finset ℕ) :
    (inInitialURun).Sat w ρ σ ↔
      (w[ρ 0]? = some U ∧ ∀ q, q < w.length → q < ρ 0 → w[q]? = some U) := by
  have hc0 : ∀ q : ℕ, (Fin.cons q ρ : Fin 2 → ℕ) 0 = q := fun q => rfl
  have hc1 : ∀ q : ℕ, (Fin.cons q ρ : Fin 2 → ℕ) 1 = ρ 0 := fun q => rfl
  unfold inInitialURun
  simp only [MSO.Formula.sat_and, SliceFasGates.sat_faFO, SliceFasGates.sat_imp,
    MSO.Formula.sat_lt, MSO.Formula.sat_labelEq, hc0, hc1]

/-! ## The integration semantic core: the gate-semantic `∀b` split -/

/-- **The gate-semantic `∀b` SPLIT** (the logical core of the single-gate integration, step 4).
The tie competitor quantifier `∀b sel-D, achieves-d* → atomOrd` over ALL atoms is equivalent to: the
CORE part (competitors in neither boundary run), plus, PER RESIDUE CLASS `r`, the suffix-run and
prefix-run parts — each gated by "class `r` ties d*".  The forward direction is pure logic; the backward
direction uses the per-class UNIFORMITY facts `hsufUniform`/`hpreUniform` (a run atom achieving d* forces
its whole residue class to achieve d* — the slope-0 structure; these are the next sub-lemmas, from the
committed lex-extreme infra).  Generic in the atom type; instantiated at the copied slice with
`inSuf` = in the final D-run, `inPre` = in the initial U-run, `cls b` = b's position mod the rank period.
The suffix/prefix per-class parts are realised by the banded run clauses of `CopiedBandRunGate`; the
core part by the bounded-shape `cfgCellGAFL` selector. -/
theorem gate_semantic_split {Atom : Type*}
    (selD ach atOrd inSuf inPre : Atom → Prop) (cls : Atom → ℕ)
    (hsufUniform : ∀ b, inSuf b → selD b → ach b →
      ∀ b', inSuf b' → cls b' = cls b → selD b' → ach b')
    (hpreUniform : ∀ b, inPre b → selD b → ach b →
      ∀ b', inPre b' → cls b' = cls b → selD b' → ach b') :
    (∀ b, selD b → ach b → atOrd b) ↔
      ((∀ b, ¬ inSuf b → ¬ inPre b → selD b → ach b → atOrd b)
        ∧ (∀ r, (∀ b, inSuf b → cls b = r → selD b → ach b) →
            (∀ b, inSuf b → cls b = r → selD b → atOrd b))
        ∧ (∀ r, (∀ b, inPre b → cls b = r → selD b → ach b) →
            (∀ b, inPre b → cls b = r → selD b → atOrd b))) := by
  classical
  constructor
  · intro hL
    refine ⟨?_, ?_, ?_⟩
    · intro b _ _ hsel hach; exact hL b hsel hach
    · intro r hclass b hsuf hcls hsel
      exact hL b hsel (hclass b hsuf hcls hsel)
    · intro r hclass b hpre hcls hsel
      exact hL b hsel (hclass b hpre hcls hsel)
  · rintro ⟨hcore, hsuf, hpre⟩ b hsel hach
    by_cases hb : inSuf b
    · exact hsuf (cls b)
        (fun b' hsuf' hcls' hsel' => hsufUniform b hb hsel hach b' hsuf' hcls' hsel')
        b hb rfl hsel
    · by_cases hb' : inPre b
      · exact hpre (cls b)
          (fun b'' hpre'' hcls'' hsel'' => hpreUniform b hb' hsel hach b'' hpre'' hcls'' hsel'')
          b hb' rfl hsel
      · exact hcore b hb hb' hsel hach

/-- **Affine-on-a-class uniformity (arithmetic core of step 4a).**  A boundary-run rank restricted to
one residue class is affine in the class-index: `G k i = G 0 i + k * P i`.  If two DISTINCT class
indices have equal value, the slope `P` vanishes and `G` is constant on the class.  This converts "a
strictly-deep run atom achieving the class-min, with the class-endpoint also achieving it" into "the
WHOLE class achieves d*" — the `hsufUniform`/`hpreUniform` hypotheses of `gate_semantic_split`.

⚠ The full per-class uniformity ALSO needs (the next sub-lemmas): selection is CONSTANT on each class
(take the class period `Q = lcm(rank period, selection period)`, both periodic on the homogeneous run),
so the sel-D class members are the whole class; and the endpoint (class-min) value = d* via
`SliceDstarBridge.selBvec_le_member` (domination) + the global-min sandwich. -/
theorem affine_class_uniform {d : ℕ} (G : ℕ → Fin d → ℤ) (P : Fin d → ℤ)
    (hrec : ∀ k i, G k i = G 0 i + (k : ℤ) * P i)
    {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) (heq : G k₁ = G k₂) :
    ∀ k, G k = G 0 := by
  have hP : P = 0 := by
    funext i
    have h1 := hrec k₁ i
    have h2 := hrec k₂ i
    have hgi : G k₁ i = G k₂ i := congrFun heq i
    rw [h1, h2] at hgi
    have hmul : ((k₁ : ℤ) - (k₂ : ℤ)) * P i = 0 := by ring_nf; linarith
    have hk : ((k₁ : ℤ) - (k₂ : ℤ)) ≠ 0 := by
      have : (k₁ : ℤ) ≠ (k₂ : ℤ) := by exact_mod_cast hne
      omega
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hk
    · simpa using h
  intro k
  funext i
  rw [hrec k i, hP]
  simp

/-- **(4a) domination-sandwich uniformity.**  An affine class (`F k = F 0 + k•P`) whose ENDPOINT
`k_e` lex-dominates the class (`hdom : ¬ lexLt (F k_b) (F k_e)`, i.e. `F k_e ≤ F k_b`; from
`SliceDstarBridge.selBvec_le_member`), with `dstar` the GLOBAL min over selected atoms so
`dstar ≤ F k_e` (`hglob`, the endpoint being selected — automatic since the class period absorbs the
gate cycle), and a strictly-interior achiever `k_b` (`F k_b = dstar`, `k_b ≠ k_e`): the whole class
equals `dstar`.  This is `hsufUniform`/`hpreUniform` of `gate_semantic_split` once instantiated at the
boundary run via `coordCands_cycle_lengths` (gives `hrec` AND selection-uniformity). -/
theorem class_uniform_of_dom {d : ℕ} (F : ℕ → Fin d → ℤ) (P dstar : Fin d → ℤ)
    (hrec : ∀ k i, F k i = F 0 i + (k : ℤ) * P i)
    {k_e k_b : ℕ} (hne : k_e ≠ k_b)
    (hdom : ¬ WRP.lexLt (F k_b) (F k_e))
    (hglob : ¬ WRP.lexLt (F k_e) dstar)
    (hb : F k_b = dstar) :
    ∀ k, F k = dstar := by
  have hae : F k_e = F k_b := by
    rcases SliceLexOrder.lexLt_not_lt (F k_b) (F k_e) hdom with h | h
    · exact h
    · rw [hb] at h; exact absurd h hglob
  have hconst := affine_class_uniform F P hrec hne hae
  have h0 : F 0 = dstar := by rw [← hconst k_b]; exact hb
  intro k; rw [hconst k, h0]

end CopiedSufRunGate
