/-
# MSO gates for the arity-1 `fas` discharge

The rank-interval kernel (`SliceFasCount.countPeriodicInterval`) consumes a marked DFA
`M` whose acceptance, on the slice, encodes the *MSO part* of the per-atom predicate —
the selectedness, the label, and the `χ`-tie ordering — while the rank arithmetic stays
in the interval endpoints.  This file builds those marked DFAs:

* `blockSelectedD_indicator_periodic` — a DFA deciding "the block atom at position
  `1+2j` (resp. `1+2j+1`) is selected and labelled `D`".

Each is an arity-1 unary MSO formula (`SliceSelCount.mso_arity_one` on the presentation's
`selDef`/`labelDef`/`ordDef`) fed to `MSOMark.markedDFA_exists`.  These therefore rest on
the textbook Büchi axiom (`#print axioms` = `[propext, Classical.choice, Quot.sound,
SliceMSO.buchi]`); the rank-interval side (`SliceFasCount`) stays axiom-clean.
-/
import RequestProject.SliceSelCount
import RequestProject.SliceBridge
import RequestProject.WRP

namespace SliceFasGates

open MSO MSOMark SliceCount SliceMSO Step
open scoped Classical

/-- **Block selectedness-and-`D` gate.**  For an arity-1 WRP presentation `P` and a copy
`c`, the predicate "the atom of copy `c` at the block position `1+2j` (`region = true`) or
`1+2j+1` (`region = false`) of `W_n` is selected and labelled `D`" is decided, for `j < n`,
by a single deterministic marked DFA over `Step × Bool`.  The position's validity is
automatic (`1+2j`, `1+2j+1 < |W_n| = 2(n+1)` for `j < n`), so the marked-DFA acceptance is
exactly the selection-∧-label MSO conjunction. -/
theorem blockSelectedD_indicator_periodic (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (harity : ∀ c, P.toPoly.arity c = 1) (region : Bool) :
    ∃ M : DetAuto (Step × Bool), ∀ n j, j < n →
      ((P.toPoly.selectedAtom (wrappedFlat n)
          ⟨c, fun _ => if region then 1 + 2 * j else 1 + 2 * j + 1⟩
        ∧ P.toPoly.labelOf (wrappedFlat n)
          ⟨c, fun _ => if region then 1 + 2 * j else 1 + 2 * j + 1⟩ = D)
       ↔ M.accepts (markAt (wrappedFlat n) (if region then 1 + 2 * j else 1 + 2 * j + 1))) := by
  obtain ⟨φsel, hsel⟩ := mso_arity_one (harity c) (P.toPoly.selDef c)
  obtain ⟨φlab, hlab⟩ := mso_arity_one (harity c) (P.toPoly.labelDef c D)
  obtain ⟨Mc, hMc⟩ := markedDFA_exists (Formula.and φsel φlab)
  refine ⟨Mc, fun n j hj => ?_⟩
  set q := if region then 1 + 2 * j else 1 + 2 * j + 1 with hqdef
  have hqlt : q < (wrappedFlat n).length := by
    rw [length_wrappedFlat, hqdef]; split <;> omega
  rw [hMc (wrappedFlat n) q hqlt, Formula.sat_and,
    ← hsel (wrappedFlat n) q, ← hlab (wrappedFlat n) q]
  constructor
  · rintro ⟨⟨_, hs⟩, hl⟩; exact ⟨hs, hl⟩
  · rintro ⟨hs, hl⟩; exact ⟨⟨fun _ => hqlt, hs⟩, hl⟩

/-- **General-position selectedness-and-`D` gate.**  For an arity-1 WRP presentation `P` and a
copy `c`, a single marked DFA decides, at *every* in-range position `q`, whether the atom of `c`
at `q` is selected and labelled `D`.  (The position-uniform version of
`blockSelectedD_indicator_periodic`, also covering the trailing-`D`/suf position.) -/
theorem selectedD_gate (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (harity : ∀ c, P.toPoly.arity c = 1) :
    ∃ M : DetAuto (Step × Bool), ∀ n q, q < (wrappedFlat n).length →
      ((P.toPoly.selectedAtom (wrappedFlat n) ⟨c, fun _ => q⟩
        ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, fun _ => q⟩ = D)
       ↔ M.accepts (markAt (wrappedFlat n) q)) := by
  obtain ⟨φsel, hsel⟩ := mso_arity_one (harity c) (P.toPoly.selDef c)
  obtain ⟨φlab, hlab⟩ := mso_arity_one (harity c) (P.toPoly.labelDef c D)
  obtain ⟨Mc, hMc⟩ := markedDFA_exists (Formula.and φsel φlab)
  refine ⟨Mc, fun n q hq => ?_⟩
  rw [hMc (wrappedFlat n) q hq, Formula.sat_and,
    ← hsel (wrappedFlat n) q, ← hlab (wrappedFlat n) q]
  constructor
  · rintro ⟨⟨_, hs⟩, hl⟩; exact ⟨hs, hl⟩
  · rintro ⟨hs, hl⟩; exact ⟨⟨fun _ => hq, hs⟩, hl⟩

/-- **General-position selectedness-and-`U` gate** (the `label = U` twin of
`selectedD_gate`, for the STRICT-count kernels of the L6/L7 assembly). -/
theorem selectedU_gate (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (harity : ∀ c, P.toPoly.arity c = 1) :
    ∃ M : DetAuto (Step × Bool), ∀ n q, q < (wrappedFlat n).length →
      ((P.toPoly.selectedAtom (wrappedFlat n) ⟨c, fun _ => q⟩
        ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, fun _ => q⟩ = U)
       ↔ M.accepts (markAt (wrappedFlat n) q)) := by
  obtain ⟨φsel, hsel⟩ := mso_arity_one (harity c) (P.toPoly.selDef c)
  obtain ⟨φlab, hlab⟩ := mso_arity_one (harity c) (P.toPoly.labelDef c U)
  obtain ⟨Mc, hMc⟩ := markedDFA_exists (Formula.and φsel φlab)
  refine ⟨Mc, fun n q hq => ?_⟩
  rw [hMc (wrappedFlat n) q hq, Formula.sat_and,
    ← hsel (wrappedFlat n) q, ← hlab (wrappedFlat n) q]
  constructor
  · rintro ⟨⟨_, hs⟩, hl⟩; exact ⟨hs, hl⟩
  · rintro ⟨hs, hl⟩; exact ⟨⟨fun _ => hq, hs⟩, hl⟩

/-- **First-order variable renaming.**  Renames the free FO variables of a formula along
`f : Fin nf → Fin nf'` (the SO variables are untouched).  Under a binder the map is lifted
so the freshly-bound variable stays at index `0`.  This is the missing MSO primitive needed
to address `ordDef`'s binary formula (copy `c`'s argument at index `0`) inside a `faFO` that
binds the quantified `D`-atom at index `0`. -/
def relabelFO {Alpha : Type*} : ∀ {nf nf' ns : ℕ}, (Fin nf → Fin nf') →
    MSO.Formula Alpha nf ns → MSO.Formula Alpha nf' ns
  | _, _, _, f, .lt i j => .lt (f i) (f j)
  | _, _, _, f, .labelEq i a => .labelEq (f i) a
  | _, _, _, f, .mem i j => .mem (f i) j
  | _, _, _, _, .tru => .tru
  | _, _, _, f, .neg φ => .neg (relabelFO f φ)
  | _, _, _, f, .and φ ψ => .and (relabelFO f φ) (relabelFO f ψ)
  | _, _, _, f, .or φ ψ => .or (relabelFO f φ) (relabelFO f ψ)
  | _, _, _, f, .exFO φ => .exFO (relabelFO (Fin.cases 0 (fun i => (f i).succ)) φ)
  | _, _, _, f, .exSO φ => .exSO (relabelFO f φ)

/-- **`relabelFO` naturality.**  Satisfaction of a renamed formula precomposes the valuation
with the renaming: `Sat w ρ σ (relabelFO f φ) ↔ Sat w (ρ ∘ f) σ φ`. -/
theorem sat_relabelFO {Alpha : Type*} (w : List Alpha) :
    ∀ {nf nf' ns : ℕ} (f : Fin nf → Fin nf') (ρ : Fin nf' → ℕ) (σ : Fin ns → Finset ℕ)
      (φ : MSO.Formula Alpha nf ns),
      Formula.Sat w ρ σ (relabelFO f φ) ↔ Formula.Sat w (ρ ∘ f) σ φ := by
  intro nf nf' ns f ρ σ φ
  induction φ generalizing nf' ρ with
  | lt i j => simp [relabelFO]
  | labelEq i a => simp [relabelFO]
  | mem i j => simp [relabelFO]
  | tru => simp [relabelFO]
  | neg φ ih => simp [relabelFO, ih]
  | and φ ψ ihφ ihψ => simp [relabelFO, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [relabelFO, ihφ, ihψ]
  | exFO φ ih =>
      simp only [relabelFO, Formula.sat_exFO]
      refine exists_congr (fun p => and_congr_right (fun _ => ?_))
      rw [ih]
      have hval : (Fin.cons p ρ : Fin _ → ℕ) ∘ Fin.cases 0 (fun i => (f i).succ)
          = Fin.cons p (ρ ∘ f) := by
        funext x; refine Fin.cases ?_ ?_ x <;> simp
      rw [hval]
  | exSO φ ih =>
      simp only [relabelFO, Formula.sat_exSO]
      exact exists_congr (fun S => and_congr_right (fun _ => ih f ρ _))

/-- **Finite conjunction** of a list of formulas. -/
def bigAnd {Alpha : Type*} {nf ns : ℕ} : List (MSO.Formula Alpha nf ns) → MSO.Formula Alpha nf ns
  | [] => .tru
  | φ :: φs => .and φ (bigAnd φs)

theorem sat_bigAnd {Alpha : Type*} (w : List Alpha) {nf ns : ℕ} (ρ : Fin nf → ℕ)
    (σ : Fin ns → Finset ℕ) (φs : List (MSO.Formula Alpha nf ns)) :
    Formula.Sat w ρ σ (bigAnd φs) ↔ ∀ φ ∈ φs, Formula.Sat w ρ σ φ := by
  induction φs with
  | nil => simp [bigAnd]
  | cons φ φs ih => simp [bigAnd, ih]

/-- **`fasU_atomOrd_gate_DFA`** (build-order step 8).  The unary MSO gate "the block atom at
`1+2j` is selected, labelled `U`, and `atomOrd`-precedes every selected `D`-atom", as a single
marked DFA.  The `∀`-over-`D`-atoms clause is `faFO` over the binary `ordDef`; the `ordDef`
formula (copy `c`'s argument at index `0`) is renamed by `relabelFO` so that, inside the
`faFO` (which binds the quantified atom at index `0`), the marked atom `u` sits at index `1`
and the bound `D`-atom at index `0` — the risk-#3 de-Bruijn handling, done by one
arity-aware `relabelFO`. -/
theorem fasU_atomOrd_gate_DFA (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (harity : ∀ c, P.toPoly.arity c = 1) :
    ∃ M : DetAuto (Step × Bool), ∀ n j, j < n →
      ((P.toPoly.selectedAtom (wrappedFlat n) ⟨c, fun _ => 1 + 2 * j⟩
        ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, fun _ => 1 + 2 * j⟩ = U
        ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
            P.toPoly.labelOf (wrappedFlat n) b = D →
            P.toPoly.atomOrd (wrappedFlat n) ⟨c, fun _ => 1 + 2 * j⟩ b)
       ↔ M.accepts (markAt (wrappedFlat n) (1 + 2 * j))) := by
  obtain ⟨φsel, hsel⟩ := mso_arity_one (harity c) (P.toPoly.selDef c)
  obtain ⟨φlabU, hlabU⟩ := mso_arity_one (harity c) (P.toPoly.labelDef c U)
  choose φselD hselD using fun c' => mso_arity_one (harity c') (P.toPoly.selDef c')
  choose φlabD hlabD using fun c' => mso_arity_one (harity c') (P.toPoly.labelDef c' D)
  choose φord hord using fun c' => P.toPoly.ordDef c c'
  set gord : ∀ c' : Fin P.toPoly.K, Fin (P.toPoly.arity c + P.toPoly.arity c') → Fin 2 :=
    fun _ idx => if idx.1 < P.toPoly.arity c then 1 else 0 with hgord
  set clause : Fin P.toPoly.K → Formula Step 2 0 := fun c' =>
    Formula.imp
      (Formula.and (relabelFO (fun _ => 0) (φselD c')) (relabelFO (fun _ => 0) (φlabD c')))
      (relabelFO (gord c') (φord c')) with hclause
  obtain ⟨M, hM⟩ := markedDFA_exists
    (Formula.and φsel (Formula.and φlabU
      (Formula.faFO (bigAnd ((List.finRange P.toPoly.K).map clause)))))
  refine ⟨M, fun n j hj => ?_⟩
  set W := wrappedFlat n with hW
  set q := 1 + 2 * j with hqdef
  have hq : q < W.length := by rw [hW, length_wrappedFlat, hqdef]; omega
  -- per-clause satisfaction
  have hclauseSat : ∀ (p : ℕ) (c' : Fin P.toPoly.K),
      Formula.Sat W (Fin.cons p (fun _ => q)) Fin.elim0 (clause c')
      ↔ ((P.toPoly.sel c' W (fun _ => p) ∧ P.toPoly.label c' W (fun _ => p) = D) →
          P.toPoly.ord c c' W (fun _ => q) (fun _ => p)) := by
    intro p c'
    simp only [hclause, Formula.imp, Formula.sat_or, Formula.sat_neg, Formula.sat_and,
      sat_relabelFO]
    have hwkv : (Fin.cons p (fun _ => q) : Fin 2 → ℕ) ∘ (fun _ : Fin 1 => (0 : Fin 2))
        = fun _ => p := by funext x; simp
    have hordval : Formula.Sat W ((Fin.cons p (fun _ => q) : Fin 2 → ℕ) ∘ gord c') Fin.elim0
          (φord c')
        ↔ P.toPoly.ord c c' W (fun _ => q) (fun _ => p) := by
      rw [← hord c' W ((Fin.cons p (fun _ => q) : Fin 2 → ℕ) ∘ gord c')]
      refine iff_of_eq (congrArg₂ (P.toPoly.ord c c' W) ?_ ?_)
      · funext t
        show (Fin.cons p (fun _ => q) : Fin 2 → ℕ) (gord c' (Fin.castAdd _ t)) = q
        simp only [hgord, Fin.val_castAdd]; rw [if_pos t.2]; rfl
      · funext t
        show (Fin.cons p (fun _ => q) : Fin 2 → ℕ) (gord c' (Fin.natAdd _ t)) = p
        simp only [hgord, Fin.val_natAdd]; rw [if_neg (by omega)]; rfl
    rw [hwkv, ← hselD c' W p, ← hlabD c' W p, hordval]
    tauto
  rw [hM W q hq, Formula.sat_and, Formula.sat_and]
  rw [show Formula.Sat W (fun _ => q) Fin.elim0
          (Formula.faFO (bigAnd ((List.finRange P.toPoly.K).map clause)))
      ↔ ∀ p, p < W.length → ∀ c' : Fin P.toPoly.K,
          (P.toPoly.sel c' W (fun _ => p) ∧ P.toPoly.label c' W (fun _ => p) = D) →
          P.toPoly.ord c c' W (fun _ => q) (fun _ => p) from ?_]
  · rw [← hsel W q, ← hlabU W q]
    refine and_congr ?_ (and_congr Iff.rfl ?_)
    · exact ⟨fun h => h.2, fun h => ⟨fun _ => hq, h⟩⟩
    · constructor
      · intro hall p hp c' hsel'
        exact hall ⟨c', fun _ => p⟩ ⟨fun _ => hp, hsel'.1⟩ hsel'.2
      · intro hall b hbsel hbD
        set p := b.2 (SliceBridge.z P.toPoly harity b.1) with hp
        have hbeq : b = ⟨b.1, fun _ => p⟩ := SliceBridge.atom_eq P.toPoly harity b
        rw [hbeq] at hbsel hbD ⊢
        exact hall p (hbsel.1 (SliceBridge.z P.toPoly harity b.1)) b.1 ⟨hbsel.2, hbD⟩
  · rw [Formula.faFO, Formula.sat_neg, Formula.sat_exFO]
    push Not
    refine forall_congr' (fun p => imp_congr_right (fun _ => ?_))
    rw [Formula.sat_neg, not_not, sat_bigAnd]
    constructor
    · intro hall c' hc'
      exact (hclauseSat p c').mp (hall (clause c') (List.mem_map_of_mem (List.mem_finRange c'))) hc'
    · intro hall φ' hφ'
      obtain ⟨c', _, rfl⟩ := List.mem_map.mp hφ'
      exact (hclauseSat p c').mpr (fun h => hall c' h)

/-! ## Modular-residue MSO predicate (route step L3a)

`mso_position_mod M c` is an MSO `Formula Alpha 1 0` deciding "position `p` ≡ `c` (mod `M`)"
(for `c < M`), built from `M` second-order residue-class sets (closed by `closeAllSO`) with
partition / first-position / successor axioms.  This is the new primitive that lets the L3
gate restrict the `∀`-over-`D`-atoms to a residue class (so the equal-rank restriction
becomes MSO).  Pure MSO `Sat`, axiom-clean (no `buchi`).  Reusable helpers `closeAllSO`,
`bigOr`, `sat_faFO`, `sat_imp` are defined here too. -/
section ModularResidue

variable {Alpha : Type*}

/-- Close all `k` free second-order variables by existential quantification. -/
def closeAllSO : {k : ℕ} → MSO.Formula Alpha 1 k → MSO.Formula Alpha 1 0
  | 0, φ => φ
  | (_ + 1), φ => closeAllSO (.exSO φ)

theorem sat_closeAllSO : ∀ {k : ℕ} (φ : MSO.Formula Alpha 1 k) (w : List Alpha) (ρ : Fin 1 → ℕ),
    (closeAllSO φ).Sat w ρ Fin.elim0 ↔
      ∃ σ : Fin k → Finset ℕ, (∀ t, ∀ x ∈ σ t, x < w.length) ∧ φ.Sat w ρ σ
  | 0, φ, w, ρ => by
      constructor
      · intro h
        exact ⟨Fin.elim0, fun t => t.elim0, h⟩
      · rintro ⟨σ, _, h⟩
        have : σ = Fin.elim0 := funext (fun t : Fin 0 => t.elim0)
        rwa [this] at h
  | (k + 1), φ, w, ρ => by
      refine (sat_closeAllSO (.exSO φ) w ρ).trans ?_
      simp only [Formula.sat_exSO]
      constructor
      · rintro ⟨σ, hσ, S, hS, hsat⟩
        refine ⟨Fin.cons S σ, fun t => ?_, hsat⟩
        refine Fin.cases ?_ ?_ t
        · simpa using hS
        · intro i; simpa using hσ i
      · rintro ⟨σ', hσ', hsat⟩
        refine ⟨Fin.tail σ', fun t => hσ' t.succ, σ' 0, hσ' 0, ?_⟩
        rwa [Fin.cons_self_tail σ']

/-- Finite disjunction of a list of formulas (at any arity). -/
def bigOr {nf ns : ℕ} : List (MSO.Formula Alpha nf ns) → MSO.Formula Alpha nf ns
  | [] => .neg .tru
  | φ :: φs => .or φ (bigOr φs)

theorem sat_bigOr (w : List Alpha) {nf ns : ℕ} (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ) :
    ∀ (φs : List (MSO.Formula Alpha nf ns)),
      (bigOr φs).Sat w ρ σ ↔ ∃ φ ∈ φs, φ.Sat w ρ σ
  | [] => by simp [bigOr, Formula.Sat]
  | φ :: φs => by
      simp only [bigOr, Formula.sat_or, sat_bigOr w ρ σ φs, List.mem_cons]
      constructor
      · rintro (h | ⟨ψ, hψ, hsat⟩)
        · exact ⟨φ, Or.inl rfl, h⟩
        · exact ⟨ψ, Or.inr hψ, hsat⟩
      · rintro ⟨ψ, (rfl | hψ), hsat⟩
        · exact Or.inl hsat
        · exact Or.inr ⟨ψ, hψ, hsat⟩

theorem sat_faFO {nf ns : ℕ} (w : List Alpha) (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ)
    (φ : MSO.Formula Alpha (nf + 1) ns) :
    (Formula.faFO φ).Sat w ρ σ ↔ ∀ q, q < w.length → φ.Sat w (Fin.cons q ρ) σ := by
  simp only [Formula.faFO, Formula.sat_neg, Formula.sat_exFO]
  push Not
  rfl

theorem sat_imp {nf ns : ℕ} (w : List Alpha) (ρ : Fin nf → ℕ) (σ : Fin ns → Finset ℕ)
    (φ ψ : MSO.Formula Alpha nf ns) :
    (Formula.imp φ ψ).Sat w ρ σ ↔ (φ.Sat w ρ σ → ψ.Sat w ρ σ) := by
  simp only [Formula.imp, Formula.sat_or, Formula.sat_neg]
  tauto

/-- The class index `(i+1) mod M`. -/
def rotIdx {M : ℕ} (hM : 0 < M) (i : Fin M) : Fin M := ⟨(i.1 + 1) % M, Nat.mod_lt _ hM⟩

/-- Class index `0` as a `Fin M`. -/
def zeroIdx {M : ℕ} (hM : 0 < M) : Fin M := ⟨0, hM⟩

/-- A1: every valid position lies in exactly one residue class.  Free: FO 0 = position `p`,
SO `0..M-1` = residue classes.  Under the `faFO` binder, the bound `q` is at FO index 0
(and `p` shifts to index 1, unused here). -/
def axPartition (M : ℕ) : MSO.Formula Alpha 1 M :=
  Formula.faFO
    (Formula.and
      (bigOr ((List.finRange M).map (fun i => Formula.mem (0 : Fin 2) i)))
      (bigAnd ((List.finRange M).flatMap (fun i =>
        (List.finRange M).filterMap (fun i' =>
          if i.1 < i'.1 then
            some (Formula.neg (Formula.and (Formula.mem (0 : Fin 2) i) (Formula.mem (0 : Fin 2) i')))
          else none)))))

/-- A2: the first valid position is in class 0. `isFirst q := ∀ r, ¬ r < q`. Under the outer
`faFO` `q` is at FO 0; under the inner `faFO` (for `r`), `r` is FO 0 and `q` is FO 1. -/
def axFirst {M : ℕ} (hM : 0 < M) : MSO.Formula Alpha 1 M :=
  Formula.faFO
    (Formula.imp
      (Formula.faFO (Formula.neg (Formula.lt (0 : Fin 3) (1 : Fin 3))))
      (Formula.mem (0 : Fin 2) (zeroIdx hM)))

/-- A3: successor positions shift the class by `+1 (mod M)`.  Outer `faFO` binds `q` (then
shifted to FO 1 by the inner binder), inner `faFO` binds `q'` at FO 0.  `succ(q,q') := q < q'
∧ ¬∃ r, q < r < q'`. -/
def axSucc {M : ℕ} (hM : 0 < M) : MSO.Formula Alpha 1 M :=
  Formula.faFO
    (Formula.faFO
      (Formula.imp
        -- succ(q, q') : q at FO 1, q' at FO 0
        (Formula.and (Formula.lt (1 : Fin 3) (0 : Fin 3))
          (Formula.faFO  -- bind r at FO 0; then q' at FO 1, q at FO 2
            (Formula.neg (Formula.and (Formula.lt (2 : Fin 4) (0 : Fin 4))
              (Formula.lt (0 : Fin 4) (1 : Fin 4))))))
        (bigAnd ((List.finRange M).map (fun i =>
          -- (q ∈ X_i) ↔ (q' ∈ X_{(i+1) mod M}) :  q at FO 1, q' at FO 0
          Formula.and
            (Formula.imp (Formula.mem (1 : Fin 3) i) (Formula.mem (0 : Fin 3) (rotIdx hM i)))
            (Formula.imp (Formula.mem (0 : Fin 3) (rotIdx hM i)) (Formula.mem (1 : Fin 3) i)))))))

/-- A4: the free position `p` (FO 0) is in class `c`. -/
def axMem {M : ℕ} (c : Fin M) : MSO.Formula Alpha 1 M :=
  Formula.mem (0 : Fin 1) c

/-- The body of the modular-counting formula: conjunction of A1–A4. -/
def modBody {M : ℕ} (hM : 0 < M) (c : Fin M) : MSO.Formula Alpha 1 M :=
  bigAnd [axPartition M, axFirst hM, axSucc hM, axMem c]

theorem sat_axMem {M : ℕ} (c : Fin M) (w : List Alpha) (p : ℕ) (σ : Fin M → Finset ℕ) :
    (axMem c).Sat w (fun _ => p) σ ↔ p ∈ σ c := by
  simp only [axMem, Formula.sat_mem]

theorem sat_axPartition {M : ℕ} (w : List Alpha) (p : ℕ) (σ : Fin M → Finset ℕ) :
    (axPartition M).Sat w (fun _ => p) σ ↔
      ∀ q, q < w.length →
        ((∃ i : Fin M, q ∈ σ i) ∧
         (∀ i i' : Fin M, i.1 < i'.1 → ¬(q ∈ σ i ∧ q ∈ σ i'))) := by
  rw [axPartition, sat_faFO]
  refine forall_congr' (fun q => imp_congr_right (fun _ => ?_))
  rw [Formula.sat_and, sat_bigOr, sat_bigAnd]
  refine and_congr ?_ ?_
  · simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨ψ, ⟨i, rfl⟩, hsat⟩
      exact ⟨i, by simpa [Formula.sat_mem] using hsat⟩
    · rintro ⟨i, hi⟩
      exact ⟨Formula.mem 0 i, ⟨i, rfl⟩, by simpa [Formula.sat_mem] using hi⟩
  · constructor
    · intro hall i i' hii'
      have hmem := hall (Formula.neg (Formula.and (Formula.mem (0 : Fin 2) i) (Formula.mem (0 : Fin 2) i')))
      rw [List.mem_flatMap] at hmem
      have hsat := hmem ⟨i, List.mem_finRange i, by
        rw [List.mem_filterMap]; exact ⟨i', List.mem_finRange i', by rw [if_pos hii']⟩⟩
      simpa [Formula.sat_neg, Formula.sat_and, Formula.sat_mem] using hsat
    · intro hall ψ hψ
      rw [List.mem_flatMap] at hψ
      obtain ⟨i, _, hψ⟩ := hψ
      rw [List.mem_filterMap] at hψ
      obtain ⟨i', _, hψ⟩ := hψ
      split at hψ
      · rename_i hsplit
        injection hψ with hψ
        subst hψ
        simpa [Formula.sat_neg, Formula.sat_and, Formula.sat_mem] using hall i i' hsplit
      · exact absurd hψ (by simp)

theorem sat_axFirst {M : ℕ} (hM : 0 < M) (w : List Alpha) (p : ℕ) (σ : Fin M → Finset ℕ) :
    (axFirst hM).Sat w (fun _ => p) σ ↔
      ∀ q, q < w.length → (∀ r, r < w.length → ¬ r < q) → q ∈ σ (zeroIdx hM) := by
  rw [axFirst, sat_faFO]
  refine forall_congr' (fun q => imp_congr_right (fun _ => ?_))
  rw [sat_imp, sat_faFO]
  refine imp_congr ?_ ?_
  · refine forall_congr' (fun r => imp_congr_right (fun _ => ?_))
    simp only [Formula.sat_neg, Formula.sat_lt]
    constructor
    · intro h hlt; exact h (by simpa using hlt)
    · intro h hlt; exact h (by simpa using hlt)
  · simp only [Formula.sat_mem]
    constructor
    · intro h; simpa using h
    · intro h; simpa using h

theorem sat_axSucc {M : ℕ} (hM : 0 < M) (w : List Alpha) (p : ℕ) (σ : Fin M → Finset ℕ) :
    (axSucc hM).Sat w (fun _ => p) σ ↔
      ∀ q, q < w.length → ∀ q', q' < w.length →
        (q < q' ∧ ¬ ∃ r, r < w.length ∧ q < r ∧ r < q') →
        ∀ i : Fin M, (q ∈ σ i ↔ q' ∈ σ (rotIdx hM i)) := by
  rw [axSucc, sat_faFO]
  refine forall_congr' (fun q => imp_congr_right (fun _ => ?_))
  rw [sat_faFO]
  refine forall_congr' (fun q' => imp_congr_right (fun _ => ?_))
  rw [sat_imp]
  refine imp_congr ?_ ?_
  · -- succ(q,q') part
    rw [Formula.sat_and, Formula.sat_lt, sat_faFO]
    refine and_congr Iff.rfl ?_
    · -- ¬∃ r, q<r<q'
      constructor
      · intro h
        rintro ⟨r, hr, hqr, hrq'⟩
        have hcon := h r hr
        rw [Formula.sat_neg, Formula.sat_and, Formula.sat_lt, Formula.sat_lt] at hcon
        exact hcon ⟨hqr, hrq'⟩
      · intro h r hr
        rw [Formula.sat_neg, Formula.sat_and, Formula.sat_lt, Formula.sat_lt]
        rintro ⟨h1, h2⟩
        exact h ⟨r, hr, h1, h2⟩
  · -- conclusion bigAnd
    rw [sat_bigAnd]
    constructor
    · intro hall i
      have hψ := hall _ (List.mem_map_of_mem (List.mem_finRange i))
      rw [Formula.sat_and, sat_imp, sat_imp] at hψ
      exact ⟨hψ.1, hψ.2⟩
    · intro hall ψ hψ
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hψ
      rw [Formula.sat_and, sat_imp, sat_imp]
      exact ⟨(hall i).1, (hall i).2⟩

/-- `n ↦ (n+1) % M` is injective on residues. -/
theorem succ_mod_inj {M a b : ℕ} (_hM : 0 < M) (ha : a < M) (hb : b < M)
    (h : (a + 1) % M = (b + 1) % M) : a = b := by
  rcases Nat.lt_or_ge (a + 1) M with hlt | hge
  · rcases Nat.lt_or_ge (b + 1) M with hlt' | hge'
    · rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt'] at h; omega
    · have hb1 : b + 1 = M := by omega
      rw [Nat.mod_eq_of_lt hlt, hb1, Nat.mod_self] at h; omega
  · have ha1 : a + 1 = M := by omega
    rcases Nat.lt_or_ge (b + 1) M with hlt' | hge'
    · rw [ha1, Nat.mod_self, Nat.mod_eq_of_lt hlt'] at h; omega
    · have hb1 : b + 1 = M := by omega
      omega

theorem mso_position_mod {Alpha : Type*} (M c : ℕ) (hc : c < M) :
    ∃ φ : MSO.Formula Alpha 1 0, ∀ (w : List Alpha) (p : ℕ), p < w.length →
      (φ.Sat w (fun _ => p) Fin.elim0 ↔ p % M = c) := by
  have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le _) hc
  refine ⟨closeAllSO (modBody hM ⟨c, hc⟩), fun w p hp => ?_⟩
  rw [modBody, sat_closeAllSO]
  -- abbreviation for the residue-class index of `n`
  have hmkmod : ∀ n : ℕ, (⟨n % M, Nat.mod_lt _ hM⟩ : Fin M).1 = n % M := fun _ => rfl
  constructor
  · -- forward: Sat ⇒ p % M = c
    rintro ⟨σ, hσ, hbody⟩
    rw [sat_bigAnd] at hbody
    have hA1 := (sat_axPartition w p σ).mp (hbody _ (by simp))
    have hA2 := (sat_axFirst hM w p σ).mp (hbody _ (by simp))
    have hA3 := (sat_axSucc hM w p σ).mp (hbody _ (by simp))
    have hA4 := (sat_axMem ⟨c, hc⟩ w p σ).mp (hbody _ (by simp))
    -- crux: every valid q lies in its own residue class
    have key : ∀ q, q < w.length → q ∈ σ ⟨q % M, Nat.mod_lt _ hM⟩ := by
      intro q
      induction q using Nat.strong_induction_on with
      | _ q ih =>
        intro hq
        match q with
        | 0 =>
          have hfirst : (0 : ℕ) ∈ σ (zeroIdx hM) :=
            hA2 0 hq (fun r _ => by omega)
          have : zeroIdx hM = (⟨0 % M, Nat.mod_lt _ hM⟩ : Fin M) := by
            apply Fin.ext; simp [zeroIdx, Nat.zero_mod]
          rwa [this] at hfirst
        | q₀ + 1 =>
          have hq₀lt : q₀ < w.length := by omega
          have hq₀mem : q₀ ∈ σ ⟨q₀ % M, Nat.mod_lt _ hM⟩ := ih q₀ (by omega) hq₀lt
          -- succ(q₀, q₀+1)
          have hsuccrel := hA3 q₀ hq₀lt (q₀ + 1) hq
            ⟨by omega, by rintro ⟨r, _, h1, h2⟩; omega⟩
          have hshift := (hsuccrel ⟨q₀ % M, Nat.mod_lt _ hM⟩).mp hq₀mem
          have hrot : rotIdx hM ⟨q₀ % M, Nat.mod_lt _ hM⟩
              = (⟨(q₀ + 1) % M, Nat.mod_lt _ hM⟩ : Fin M) := by
            apply Fin.ext
            simp only [rotIdx]
            rw [Nat.mod_add_mod]
          rwa [hrot] at hshift
    -- now p ∈ σ ⟨p % M⟩ and p ∈ σ ⟨c⟩; uniqueness forces p % M = c
    have hpmod : p ∈ σ ⟨p % M, Nat.mod_lt _ hM⟩ := key p hp
    have hpc : p ∈ σ ⟨c, hc⟩ := hA4
    by_contra hne
    have huniq := (hA1 p hp).2
    -- compare indices ⟨p%M⟩ and ⟨c⟩
    rcases lt_trichotomy (p % M) c with h | h | h
    · exact huniq ⟨p % M, Nat.mod_lt _ hM⟩ ⟨c, hc⟩ h ⟨hpmod, hpc⟩
    · exact hne h
    · exact huniq ⟨c, hc⟩ ⟨p % M, Nat.mod_lt _ hM⟩ h ⟨hpc, hpmod⟩
  · -- backward: p % M = c ⇒ Sat
    intro hpc
    refine ⟨fun i => (Finset.range w.length).filter (· % M = i.1), ?_, ?_⟩
    · intro i x hx
      rw [Finset.mem_filter, Finset.mem_range] at hx
      exact hx.1
    · rw [sat_bigAnd]
      intro φ hφ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
      rcases hφ with rfl | rfl | rfl | rfl
      · -- A1
        rw [sat_axPartition]
        intro q hq
        refine ⟨⟨⟨q % M, Nat.mod_lt _ hM⟩, ?_⟩, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hq, rfl⟩
        · rintro i i' hii' ⟨hi, hi'⟩
          rw [Finset.mem_filter] at hi hi'
          have : (i.1 : ℕ) = i'.1 := by rw [← hi.2, ← hi'.2]
          omega
      · -- A2
        rw [sat_axFirst]
        intro q hq hfirst
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨hq, ?_⟩
        have hq0 : q = 0 := by
          by_contra hq0
          have : 0 < q := Nat.pos_of_ne_zero hq0
          exact hfirst 0 (by omega) this
        simp [hq0, zeroIdx, Nat.zero_mod]
      · -- A3
        rw [sat_axSucc]
        intro q hq q' hq' ⟨hlt, hbetween⟩ i
        -- succ in [0,len) forces q' = q + 1
        have hq'eq : q' = q + 1 := by
          by_contra hne
          have : q + 1 < q' := by omega
          exact hbetween ⟨q + 1, by omega, by omega, by omega⟩
        subst hq'eq
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨_, hqi⟩
          refine ⟨hq', ?_⟩
          show (q + 1) % M = (rotIdx hM i).1
          simp only [rotIdx]
          rw [← hqi, Nat.mod_add_mod]
        · rintro ⟨_, hq1i⟩
          refine ⟨hq, ?_⟩
          -- hq1i : (q+1)%M = (rotIdx i).1 = (↑i+1)%M
          have heq : (q % M + 1) % M = (i.1 + 1) % M := by
            rw [Nat.mod_add_mod, hq1i]; simp only [rotIdx]
          exact succ_mod_inj hM (Nat.mod_lt _ hM) i.2 heq
      · -- A4
        rw [sat_axMem, Finset.mem_filter, Finset.mem_range]
        exact ⟨hp, by simp [hpc]⟩

/-- **Position-offset MSO predicate** (route GA-6 prerequisite).  For a fixed `k`, a
two-free-variable MSO formula deciding `x₁ = x₀ + k` at valid positions: offset `0` is
position equality, offset `k+1` composes offset `k` with the immediate-successor
relation.  The GA TIE gate uses it to pin a quantified atom's cluster coordinates to
fixed offsets from the base coordinate. -/
theorem mso_offset_eq (k : ℕ) :
    ∃ φ : MSO.Formula Alpha 2 0, ∀ (w : List Alpha) (p q : ℕ), p < w.length →
      q < w.length →
      (φ.Sat w (Fin.cons p (Fin.cons q Fin.elim0)) Fin.elim0 ↔ q = p + k) := by
  induction k with
  | zero =>
      refine ⟨Formula.eqPos 1 0, fun w p q hp hq => ?_⟩
      rw [Formula.sat_eqPos]
      show q = p ↔ q = p + 0
      omega
  | succ k ih =>
      obtain ⟨φk, hφk⟩ := ih
      refine ⟨Formula.exFO (Formula.and
          (relabelFO (Fin.cons 1 (Fin.cons 0 Fin.elim0)) φk)
          (Formula.and (Formula.lt (0 : Fin 3) (2 : Fin 3))
            (Formula.faFO (Formula.neg (Formula.and (Formula.lt (1 : Fin 4) (0 : Fin 4))
              (Formula.lt (0 : Fin 4) (3 : Fin 4))))))),
        fun w p q hp hq => ?_⟩
      rw [Formula.sat_exFO]
      constructor
      · rintro ⟨z, hz, hsat⟩
        rw [Formula.sat_and, Formula.sat_and, sat_relabelFO] at hsat
        obtain ⟨hk, hlt, hbetween⟩ := hsat
        have hcomp : (Fin.cons z (Fin.cons p (Fin.cons q Fin.elim0)) : Fin 3 → ℕ)
            ∘ (Fin.cons 1 (Fin.cons 0 Fin.elim0))
            = Fin.cons p (Fin.cons z Fin.elim0) := by
          funext i
          fin_cases i <;> rfl
        rw [hcomp] at hk
        have hzpk : z = p + k := (hφk w p z hp hz).mp hk
        have hzq : z < q := hlt
        rw [sat_faFO] at hbetween
        have hqz1 : q = z + 1 := by
          by_contra hne
          have hr : z + 1 < w.length := by omega
          have hcon := hbetween (z + 1) hr
          rw [Formula.sat_neg, Formula.sat_and, Formula.sat_lt, Formula.sat_lt] at hcon
          exact hcon ⟨by show z < z + 1; omega, by show z + 1 < q; omega⟩
        omega
      · intro hq1
        refine ⟨p + k, by omega, ?_⟩
        rw [Formula.sat_and, Formula.sat_and, sat_relabelFO]
        have hcomp : (Fin.cons (p + k) (Fin.cons p (Fin.cons q Fin.elim0)) : Fin 3 → ℕ)
            ∘ (Fin.cons 1 (Fin.cons 0 Fin.elim0))
            = Fin.cons p (Fin.cons (p + k) Fin.elim0) := by
          funext i
          fin_cases i <;> rfl
        rw [hcomp]
        refine ⟨(hφk w p (p + k) hp (by omega)).mpr rfl, by show p + k < q; omega, ?_⟩
        rw [sat_faFO]
        intro r hr
        rw [Formula.sat_neg, Formula.sat_and, Formula.sat_lt, Formula.sat_lt]
        rintro ⟨h1, h2⟩
        have hh1 : p + k < r := h1
        have hh2 : r < q := h2
        omega

/-- **Position-equals-a-constant MSO predicate** (route step L4 prerequisite).  For a
fixed `k`, an MSO formula deciding `p = k` at every valid position `p`: by induction on
`k` — `p = 0` says "no position precedes `p`", and `p = k+1` says "the immediate
predecessor of `p` exists and equals `k`". -/
theorem mso_position_eq (k : ℕ) :
    ∃ φ : MSO.Formula Alpha 1 0, ∀ (w : List Alpha) (p : ℕ), p < w.length →
      (φ.Sat w (fun _ => p) Fin.elim0 ↔ p = k) := by
  induction k with
  | zero =>
      refine ⟨Formula.faFO (Formula.neg (Formula.lt (0 : Fin 2) (1 : Fin 2))),
        fun w p hp => ?_⟩
      rw [sat_faFO]
      constructor
      · intro h
        by_contra hne
        have hcon := h 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hp)
        rw [Formula.sat_neg, Formula.sat_lt] at hcon
        exact hcon (by show (0 : ℕ) < p; omega)
      · rintro rfl r _
        rw [Formula.sat_neg, Formula.sat_lt]
        show ¬ r < 0
        omega
  | succ k ih =>
      obtain ⟨φk, hφk⟩ := ih
      refine ⟨Formula.exFO (Formula.and (Formula.lt (0 : Fin 2) (1 : Fin 2))
        (Formula.and (relabelFO (fun _ => (0 : Fin 2)) φk)
          (Formula.faFO (Formula.neg (Formula.and (Formula.lt (1 : Fin 3) (0 : Fin 3))
            (Formula.lt (0 : Fin 3) (2 : Fin 3))))))),
        fun w p hp => ?_⟩
      rw [Formula.sat_exFO]
      constructor
      · rintro ⟨s, hs, hsat⟩
        rw [Formula.sat_and, Formula.sat_and] at hsat
        obtain ⟨hlt, hk, hbet⟩ := hsat
        have hsp : s < p := hlt
        rw [sat_relabelFO] at hk
        have hval : (Fin.cons s (fun _ => p) : Fin 2 → ℕ) ∘ (fun _ : Fin 1 => (0 : Fin 2))
            = fun _ => s := by funext x; simp
        rw [hval] at hk
        have hsk : s = k := (hφk w s hs).mp hk
        rw [sat_faFO] at hbet
        by_contra hne
        have hcon := hbet (s + 1) (by omega)
        rw [Formula.sat_neg, Formula.sat_and, Formula.sat_lt, Formula.sat_lt] at hcon
        exact hcon ⟨by show s < s + 1; omega, by show s + 1 < p; omega⟩
      · rintro rfl
        refine ⟨k, by omega, ?_⟩
        rw [Formula.sat_and, Formula.sat_and]
        refine ⟨?_, ?_, ?_⟩
        · rw [Formula.sat_lt]; show k < k + 1; omega
        · rw [sat_relabelFO]
          have hval : (Fin.cons k (fun _ => k + 1) : Fin 2 → ℕ) ∘ (fun _ : Fin 1 => (0 : Fin 2))
              = fun _ => k := by funext x; simp
          rw [hval]
          exact (hφk w k (by omega)).mpr rfl
        · rw [sat_faFO]
          intro r _
          rw [Formula.sat_neg, Formula.sat_and, Formula.sat_lt, Formula.sat_lt]
          rintro ⟨h1, h2⟩
          have hh1 : k < r := h1
          have hh2 : r < k + 1 := h2
          omega

/-- **Position-from-the-end MSO predicate** (route step L4 prerequisite).  For a fixed
`k`, an MSO formula deciding `p + 1 + k = |w|` ("`p` is the `k`-th position from the
end") at every valid position `p`: by induction on `k` — `k = 0` says "no position
follows `p`", and `k+1` says "the immediate successor of `p` is the `k`-th from the
end". -/
theorem mso_position_fromEnd (k : ℕ) :
    ∃ φ : MSO.Formula Alpha 1 0, ∀ (w : List Alpha) (p : ℕ), p < w.length →
      (φ.Sat w (fun _ => p) Fin.elim0 ↔ p + 1 + k = w.length) := by
  induction k with
  | zero =>
      refine ⟨Formula.faFO (Formula.neg (Formula.lt (1 : Fin 2) (0 : Fin 2))),
        fun w p hp => ?_⟩
      rw [sat_faFO]
      constructor
      · intro h
        by_contra hne
        have hcon := h (p + 1) (by omega)
        rw [Formula.sat_neg, Formula.sat_lt] at hcon
        exact hcon (by show p < p + 1; omega)
      · intro heq r hr
        rw [Formula.sat_neg, Formula.sat_lt]
        show ¬ p < r
        omega
  | succ k ih =>
      obtain ⟨φk, hφk⟩ := ih
      refine ⟨Formula.exFO (Formula.and (Formula.lt (1 : Fin 2) (0 : Fin 2))
        (Formula.and (relabelFO (fun _ => (0 : Fin 2)) φk)
          (Formula.faFO (Formula.neg (Formula.and (Formula.lt (2 : Fin 3) (0 : Fin 3))
            (Formula.lt (0 : Fin 3) (1 : Fin 3))))))),
        fun w p hp => ?_⟩
      rw [Formula.sat_exFO]
      constructor
      · rintro ⟨s, hs, hsat⟩
        rw [Formula.sat_and, Formula.sat_and] at hsat
        obtain ⟨hlt, hk, hbet⟩ := hsat
        have hps : p < s := hlt
        rw [sat_relabelFO] at hk
        have hval : (Fin.cons s (fun _ => p) : Fin 2 → ℕ) ∘ (fun _ : Fin 1 => (0 : Fin 2))
            = fun _ => s := by funext x; simp
        rw [hval] at hk
        have hsk : s + 1 + k = w.length := (hφk w s hs).mp hk
        rw [sat_faFO] at hbet
        -- no position strictly between `p` and `s` forces `s = p + 1`
        have hsp1 : s = p + 1 := by
          by_contra hne
          have hcon := hbet (p + 1) (by omega)
          rw [Formula.sat_neg, Formula.sat_and, Formula.sat_lt, Formula.sat_lt] at hcon
          exact hcon ⟨by show p < p + 1; omega, by show p + 1 < s; omega⟩
        omega
      · intro heq
        refine ⟨p + 1, by omega, ?_⟩
        rw [Formula.sat_and, Formula.sat_and]
        refine ⟨?_, ?_, ?_⟩
        · rw [Formula.sat_lt]; show p < p + 1; omega
        · rw [sat_relabelFO]
          have hval : (Fin.cons (p + 1) (fun _ => p) : Fin 2 → ℕ)
              ∘ (fun _ : Fin 1 => (0 : Fin 2)) = fun _ => p + 1 := by funext x; simp
          rw [hval]
          exact (hφk w (p + 1) (by omega)).mpr (by omega)
        · rw [sat_faFO]
          intro r _
          rw [Formula.sat_neg, Formula.sat_and, Formula.sat_lt, Formula.sat_lt]
          rintro ⟨h1, h2⟩
          have hh1 : p < r := h1
          have hh2 : r < p + 1 := h2
          omega

end ModularResidue

/-- **`fasU_atomOrd_eqRankD_gate`** (route step L3b).  The equal-rank atomOrd gate as a marked
DFA: the block atom at `1+2j` is selected, labelled `U`, and `atomOrd`-precedes every selected
`D`-atom whose position lies in an active residue class (`pos_b % M ∈ S b.1`).  Extends
`fasU_atomOrd_gate_DFA` by the `mso_position_mod` (L3a) residue conjunct on the bound `D`-atom (a
`bigOr` over `S c'`).  A faithful MSO-gate→DFA; the correctness that taking `S` = the
collinear-with-`d*`-rank classes captures the equal-rank `D`-atoms is the L6 assembly's job, not
asserted here.  Base `+ SliceMSO.buchi`. -/
theorem fasU_atomOrd_eqRankD_gate (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (harity : ∀ c, P.toPoly.arity c = 1) (M : ℕ) (S : Fin P.toPoly.K → Finset ℕ)
    (hS : ∀ c', ∀ r ∈ S c', r < M) :
    ∃ Mdfa : DetAuto (Step × Bool), ∀ n j, j < n →
      ((P.toPoly.selectedAtom (wrappedFlat n) ⟨c, fun _ => 1 + 2 * j⟩
        ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, fun _ => 1 + 2 * j⟩ = U
        ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
            P.toPoly.labelOf (wrappedFlat n) b = D →
            b.2 (SliceBridge.z P.toPoly harity b.1) % M ∈ S b.1 →
            P.toPoly.atomOrd (wrappedFlat n) ⟨c, fun _ => 1 + 2 * j⟩ b)
       ↔ Mdfa.accepts (markAt (wrappedFlat n) (1 + 2 * j))) := by
  obtain ⟨φsel, hsel⟩ := mso_arity_one (harity c) (P.toPoly.selDef c)
  obtain ⟨φlabU, hlabU⟩ := mso_arity_one (harity c) (P.toPoly.labelDef c U)
  choose φselD hselD using fun c' => mso_arity_one (harity c') (P.toPoly.selDef c')
  choose φlabD hlabD using fun c' => mso_arity_one (harity c') (P.toPoly.labelDef c' D)
  choose φord hord using fun c' => P.toPoly.ordDef c c'
  choose φmod hφmod using fun (r : Fin M) => mso_position_mod (Alpha := Step) M r.1 r.2
  set gord : ∀ c' : Fin P.toPoly.K, Fin (P.toPoly.arity c + P.toPoly.arity c') → Fin 2 :=
    fun _ idx => if idx.1 < P.toPoly.arity c then 1 else 0 with hgord
  set resClause : Fin P.toPoly.K → Formula Step 2 0 := fun c' =>
    bigOr ((S c').toList.attach.map (fun rr =>
      relabelFO (fun _ => (0 : Fin 2)) (φmod ⟨rr.1, hS c' rr.1 (Finset.mem_toList.mp rr.2)⟩)))
    with hresClause
  set clause : Fin P.toPoly.K → Formula Step 2 0 := fun c' =>
    Formula.imp
      (Formula.and
        (Formula.and (relabelFO (fun _ => 0) (φselD c')) (relabelFO (fun _ => 0) (φlabD c')))
        (resClause c'))
      (relabelFO (gord c') (φord c')) with hclause
  obtain ⟨Mdfa, hM⟩ := markedDFA_exists
    (Formula.and φsel (Formula.and φlabU
      (Formula.faFO (bigAnd ((List.finRange P.toPoly.K).map clause)))))
  refine ⟨Mdfa, fun n j hj => ?_⟩
  set W := wrappedFlat n with hW
  set q := 1 + 2 * j with hqdef
  have hq : q < W.length := by rw [hW, length_wrappedFlat, hqdef]; omega
  -- residue conjunct unfolding
  have hresSat : ∀ (p : ℕ) (c' : Fin P.toPoly.K), p < W.length →
      (Formula.Sat W (Fin.cons p (fun _ => q)) Fin.elim0 (resClause c') ↔ p % M ∈ S c') := by
    intro p c' hp
    rw [hresClause]
    rw [sat_bigOr]
    constructor
    · rintro ⟨φ', hφ', hsat⟩
      rw [List.mem_map] at hφ'
      obtain ⟨rr, _, rfl⟩ := hφ'
      rw [sat_relabelFO] at hsat
      have hval : (Fin.cons p (fun _ => q) : Fin 2 → ℕ) ∘ (fun _ : Fin 1 => (0 : Fin 2))
          = fun _ => p := by funext x; simp
      rw [hval] at hsat
      have := (hφmod ⟨rr.1, hS c' rr.1 (Finset.mem_toList.mp rr.2)⟩ W p hp).mp hsat
      simp only at this
      rw [this]
      exact Finset.mem_toList.mp rr.2
    · intro hmem
      refine ⟨relabelFO (fun _ => (0 : Fin 2))
        (φmod ⟨p % M, hS c' (p % M) hmem⟩), ?_, ?_⟩
      · rw [List.mem_map]
        refine ⟨⟨p % M, Finset.mem_toList.mpr hmem⟩, List.mem_attach _ _, ?_⟩
        rfl
      · rw [sat_relabelFO]
        have hval : (Fin.cons p (fun _ => q) : Fin 2 → ℕ) ∘ (fun _ : Fin 1 => (0 : Fin 2))
            = fun _ => p := by funext x; simp
        rw [hval]
        exact (hφmod ⟨p % M, hS c' (p % M) hmem⟩ W p hp).mpr rfl
  -- per-clause satisfaction
  have hclauseSat : ∀ (p : ℕ) (c' : Fin P.toPoly.K), p < W.length →
      (Formula.Sat W (Fin.cons p (fun _ => q)) Fin.elim0 (clause c')
      ↔ ((P.toPoly.sel c' W (fun _ => p) ∧ P.toPoly.label c' W (fun _ => p) = D
            ∧ p % M ∈ S c') →
          P.toPoly.ord c c' W (fun _ => q) (fun _ => p))) := by
    intro p c' hp
    simp only [hclause, Formula.imp, Formula.sat_or, Formula.sat_neg, Formula.sat_and,
      sat_relabelFO]
    have hwkv : (Fin.cons p (fun _ => q) : Fin 2 → ℕ) ∘ (fun _ : Fin 1 => (0 : Fin 2))
        = fun _ => p := by funext x; simp
    have hordval : Formula.Sat W ((Fin.cons p (fun _ => q) : Fin 2 → ℕ) ∘ gord c') Fin.elim0
          (φord c')
        ↔ P.toPoly.ord c c' W (fun _ => q) (fun _ => p) := by
      rw [← hord c' W ((Fin.cons p (fun _ => q) : Fin 2 → ℕ) ∘ gord c')]
      refine iff_of_eq (congrArg₂ (P.toPoly.ord c c' W) ?_ ?_)
      · funext t
        show (Fin.cons p (fun _ => q) : Fin 2 → ℕ) (gord c' (Fin.castAdd _ t)) = q
        simp only [hgord, Fin.val_castAdd]; rw [if_pos t.2]; rfl
      · funext t
        show (Fin.cons p (fun _ => q) : Fin 2 → ℕ) (gord c' (Fin.natAdd _ t)) = p
        simp only [hgord, Fin.val_natAdd]; rw [if_neg (by omega)]; rfl
    have hres := hresSat p c' hp
    rw [hresClause] at hres
    rw [hwkv, ← hselD c' W p, ← hlabD c' W p, hordval, hres]
    tauto
  rw [hM W q hq, Formula.sat_and, Formula.sat_and]
  rw [show Formula.Sat W (fun _ => q) Fin.elim0
          (Formula.faFO (bigAnd ((List.finRange P.toPoly.K).map clause)))
      ↔ ∀ p, p < W.length → ∀ c' : Fin P.toPoly.K,
          (P.toPoly.sel c' W (fun _ => p) ∧ P.toPoly.label c' W (fun _ => p) = D
            ∧ p % M ∈ S c') →
          P.toPoly.ord c c' W (fun _ => q) (fun _ => p) from ?_]
  · rw [← hsel W q, ← hlabU W q]
    refine and_congr ?_ (and_congr Iff.rfl ?_)
    · exact ⟨fun h => h.2, fun h => ⟨fun _ => hq, h⟩⟩
    · constructor
      · intro hall p hp c' hsel'
        exact hall ⟨c', fun _ => p⟩ ⟨fun _ => hp, hsel'.1⟩ hsel'.2.1 hsel'.2.2
      · intro hall b hbsel hbD hbres
        set p := b.2 (SliceBridge.z P.toPoly harity b.1) with hp
        have hbeq : b = ⟨b.1, fun _ => p⟩ := SliceBridge.atom_eq P.toPoly harity b
        rw [hbeq] at hbsel hbD ⊢
        exact hall p (hbsel.1 (SliceBridge.z P.toPoly harity b.1)) b.1 ⟨hbsel.2, hbD, hbres⟩
  · rw [Formula.faFO, Formula.sat_neg, Formula.sat_exFO]
    push Not
    refine forall_congr' (fun p => imp_congr_right (fun hp => ?_))
    rw [Formula.sat_neg, not_not, sat_bigAnd]
    constructor
    · intro hall c' hc'
      exact (hclauseSat p c' hp).mp
        (hall (clause c') (List.mem_map_of_mem (List.mem_finRange c'))) hc'
    · intro hall φ' hφ'
      obtain ⟨c', _, rfl⟩ := List.mem_map.mp hφ'
      exact (hclauseSat p c' hp).mpr (fun h => hall c' h)

/-- **The L4 positional cell condition.**  The position-separated description of the
equal-rank selected-`D` set, produced by the L5 selector (`eqRankD_position_selector`)
and consumed by the L4 gate and the L6 assembly: position `p` (in a word of length
`len`) is *bulk* (clear of both boundaries by `mthr` and in an active residue class of
`S`), an *exact front position* (`p ∈ Front`, fixed constants — covering the pre
position `0`, transient block positions of either parity, and Case-A first-members), or
an *exact end-offset* (`p + 1 + k = len` for `k ∈ Back` — covering the suffix `k = 0`,
transient back blocks of either parity, and Case-A last-members).  Unlike the
residue-only filter of `fasU_atomOrd_eqRankD_gate`, the front/back cells are pinned to
EXACT positions, so a transient boundary `D`-atom can never collide with a bulk residue
class (the session-3 L3b undercount finding).  NB the cells deliberately cover ALL
positions, not just the blockD parity: `labelOf` is the presentation's own MSO labelling,
so a selected `D`-atom can sit at the pre position or at an odd block position. -/
def cfgPos (M mthr : ℕ) (S Front Back : Finset ℕ) (len p : ℕ) : Prop :=
  (mthr ≤ p ∧ p + mthr < len ∧ p % M ∈ S)
  ∨ p ∈ Front
  ∨ (∃ k ∈ Back, p + 1 + k = len)

/-- **`fasU_atomOrd_cfg_gate`** (route step L4).  The position-separated unified atomOrd
gate as a marked DFA, POSITION-UNIFORM in the marked atom: the atom of copy `c` at *any*
in-range position `q` is selected, labelled `U`, and `atomOrd`-precedes every selected
`D`-atom whose position satisfies the `cfgPos` cell condition (bulk-region-guarded
residue ∨ exact-front position ∨ exact end-offset).  (The L6 assembly marks TIE-counted
`a`-atoms at all four position regions — pre `0`, blockU `1+2j`, blockD `1+2j+1`, suf
`1+2n` — with the same DFA.)  Replaces the superseded `fasU_atomOrd_eqRankD_gate`: the
threshold conjuncts are `mso_position_eq`/`mso_position_fromEnd` disjunctions, the
residue conjunct is `mso_position_mod`.  A faithful MSO-gate→DFA; the correctness that
the L5-selected `(S, Front, Back)` data captures exactly the equal-rank `D`-atoms is the
L5/L6 assembly's job, not asserted here.  Base `+ SliceMSO.buchi`. -/
theorem fasU_atomOrd_cfg_gate (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (harity : ∀ c, P.toPoly.arity c = 1) (M mthr : ℕ)
    (S Front Back : Fin P.toPoly.K → Finset ℕ)
    (hS : ∀ c', ∀ r ∈ S c', r < M) :
    ∃ Mdfa : DetAuto (Step × Bool), ∀ n q, q < (wrappedFlat n).length →
      ((P.toPoly.selectedAtom (wrappedFlat n) ⟨c, fun _ => q⟩
        ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, fun _ => q⟩ = U
        ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
            P.toPoly.labelOf (wrappedFlat n) b = D →
            cfgPos M mthr (S b.1) (Front b.1) (Back b.1)
              (wrappedFlat n).length (b.2 (SliceBridge.z P.toPoly harity b.1)) →
            P.toPoly.atomOrd (wrappedFlat n) ⟨c, fun _ => q⟩ b)
       ↔ Mdfa.accepts (markAt (wrappedFlat n) q)) := by
  obtain ⟨φsel, hsel⟩ := mso_arity_one (harity c) (P.toPoly.selDef c)
  obtain ⟨φlabU, hlabU⟩ := mso_arity_one (harity c) (P.toPoly.labelDef c U)
  choose φselD hselD using fun c' => mso_arity_one (harity c') (P.toPoly.selDef c')
  choose φlabD hlabD using fun c' => mso_arity_one (harity c') (P.toPoly.labelDef c' D)
  choose φord hord using fun c' => P.toPoly.ordDef c c'
  choose φmod hφmod using fun (r : Fin M) => mso_position_mod (Alpha := Step) M r.1 r.2
  choose φeq hφeq using fun k : ℕ => mso_position_eq (Alpha := Step) k
  choose φfe hφfe using fun k : ℕ => mso_position_fromEnd (Alpha := Step) k
  set gord : ∀ c' : Fin P.toPoly.K, Fin (P.toPoly.arity c + P.toPoly.arity c') → Fin 2 :=
    fun _ idx => if idx.1 < P.toPoly.arity c then 1 else 0 with hgord
  -- the three-way position-cell clause, as a single-FO-variable formula at the D-atom position
  set posClause : Fin P.toPoly.K → Formula Step 1 0 := fun c' =>
    Formula.or
      (Formula.and (Formula.neg (bigOr ((List.range mthr).map φeq)))
        (Formula.and (Formula.neg (bigOr ((List.range mthr).map φfe)))
          (bigOr ((S c').toList.attach.map (fun rr =>
            φmod ⟨rr.1, hS c' rr.1 (Finset.mem_toList.mp rr.2)⟩)))))
      (Formula.or
        (bigOr ((Front c').toList.map φeq))
        (bigOr ((Back c').toList.map φfe))) with hposClause
  set clause : Fin P.toPoly.K → Formula Step 2 0 := fun c' =>
    Formula.imp
      (Formula.and
        (Formula.and (relabelFO (fun _ => 0) (φselD c')) (relabelFO (fun _ => 0) (φlabD c')))
        (relabelFO (fun _ => (0 : Fin 2)) (posClause c')))
      (relabelFO (gord c') (φord c')) with hclause
  obtain ⟨Mdfa, hM⟩ := markedDFA_exists
    (Formula.and φsel (Formula.and φlabU
      (Formula.faFO (bigAnd ((List.finRange P.toPoly.K).map clause)))))
  refine ⟨Mdfa, fun n q hq' => ?_⟩
  set W := wrappedFlat n with hW
  have hq : q < W.length := hq'
  -- the position clause decodes to `cfgPos`
  have hposSat : ∀ (p : ℕ) (c' : Fin P.toPoly.K), p < W.length →
      (Formula.Sat W (fun _ => p) Fin.elim0 (posClause c')
        ↔ cfgPos M mthr (S c') (Front c') (Back c') W.length p) := by
    intro p c' hp
    rw [hposClause]
    have h1 : ((bigOr ((List.range mthr).map φeq)).Sat W (fun _ => p) Fin.elim0)
        ↔ p < mthr := by
      rw [sat_bigOr]
      constructor
      · rintro ⟨φ', hφ', hsat⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hφ'
        rw [List.mem_range] at hi
        rw [hφeq i W p hp] at hsat
        omega
      · intro hlt
        exact ⟨φeq p, List.mem_map_of_mem (List.mem_range.mpr hlt), (hφeq p W p hp).mpr rfl⟩
    have h2 : ((bigOr ((List.range mthr).map φfe)).Sat W (fun _ => p) Fin.elim0)
        ↔ W.length ≤ p + mthr := by
      rw [sat_bigOr]
      constructor
      · rintro ⟨φ', hφ', hsat⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hφ'
        rw [List.mem_range] at hi
        rw [hφfe i W p hp] at hsat
        omega
      · intro hle
        refine ⟨φfe (W.length - p - 1),
          List.mem_map_of_mem (List.mem_range.mpr (by omega)), ?_⟩
        exact (hφfe _ W p hp).mpr (by omega)
    have h3 : ((bigOr ((S c').toList.attach.map (fun rr =>
          φmod ⟨rr.1, hS c' rr.1 (Finset.mem_toList.mp rr.2)⟩))).Sat W (fun _ => p) Fin.elim0)
        ↔ p % M ∈ S c' := by
      rw [sat_bigOr]
      constructor
      · rintro ⟨φ', hφ', hsat⟩
        obtain ⟨rr, _, rfl⟩ := List.mem_map.mp hφ'
        have := (hφmod ⟨rr.1, hS c' rr.1 (Finset.mem_toList.mp rr.2)⟩ W p hp).mp hsat
        simp only at this
        rw [this]
        exact Finset.mem_toList.mp rr.2
      · intro hmem
        refine ⟨φmod ⟨p % M, hS c' (p % M) hmem⟩, ?_, ?_⟩
        · exact List.mem_map.mpr ⟨⟨p % M, Finset.mem_toList.mpr hmem⟩, List.mem_attach _ _, rfl⟩
        · exact (hφmod ⟨p % M, hS c' (p % M) hmem⟩ W p hp).mpr rfl
    have h4 : ((bigOr ((Front c').toList.map φeq)).Sat W (fun _ => p) Fin.elim0)
        ↔ p ∈ Front c' := by
      rw [sat_bigOr]
      constructor
      · rintro ⟨φ', hφ', hsat⟩
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hφ'
        rw [(hφeq f W p hp).mp hsat]
        exact Finset.mem_toList.mp hf
      · intro hmem
        exact ⟨φeq p, List.mem_map_of_mem (Finset.mem_toList.mpr hmem),
          (hφeq p W p hp).mpr rfl⟩
    have h5 : ((bigOr ((Back c').toList.map φfe)).Sat W (fun _ => p) Fin.elim0)
        ↔ ∃ k ∈ Back c', p + 1 + k = W.length := by
      rw [sat_bigOr]
      constructor
      · rintro ⟨φ', hφ', hsat⟩
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ'
        exact ⟨k, Finset.mem_toList.mp hk, (hφfe _ W p hp).mp hsat⟩
      · rintro ⟨k, hk, heq⟩
        exact ⟨φfe k, List.mem_map_of_mem (Finset.mem_toList.mpr hk),
          (hφfe _ W p hp).mpr heq⟩
    simp only [Formula.sat_or, Formula.sat_and, Formula.sat_neg]
    rw [h1, h2, h3, h4, h5, cfgPos]
    constructor
    · rintro (⟨ha, hb, hc⟩ | h)
      · exact Or.inl ⟨by omega, by omega, hc⟩
      · exact Or.inr h
    · rintro (⟨ha, hb, hc⟩ | h)
      · exact Or.inl ⟨by omega, by omega, hc⟩
      · exact Or.inr h
  -- per-clause satisfaction
  have hclauseSat : ∀ (p : ℕ) (c' : Fin P.toPoly.K), p < W.length →
      (Formula.Sat W (Fin.cons p (fun _ => q)) Fin.elim0 (clause c')
      ↔ ((P.toPoly.sel c' W (fun _ => p) ∧ P.toPoly.label c' W (fun _ => p) = D
            ∧ cfgPos M mthr (S c') (Front c') (Back c') W.length p) →
          P.toPoly.ord c c' W (fun _ => q) (fun _ => p))) := by
    intro p c' hp
    simp only [hclause, Formula.imp, Formula.sat_or, Formula.sat_neg, Formula.sat_and,
      sat_relabelFO]
    have hwkv : (Fin.cons p (fun _ => q) : Fin 2 → ℕ) ∘ (fun _ : Fin 1 => (0 : Fin 2))
        = fun _ => p := by funext x; simp
    have hordval : Formula.Sat W ((Fin.cons p (fun _ => q) : Fin 2 → ℕ) ∘ gord c') Fin.elim0
          (φord c')
        ↔ P.toPoly.ord c c' W (fun _ => q) (fun _ => p) := by
      rw [← hord c' W ((Fin.cons p (fun _ => q) : Fin 2 → ℕ) ∘ gord c')]
      refine iff_of_eq (congrArg₂ (P.toPoly.ord c c' W) ?_ ?_)
      · funext t
        show (Fin.cons p (fun _ => q) : Fin 2 → ℕ) (gord c' (Fin.castAdd _ t)) = q
        simp only [hgord, Fin.val_castAdd]; rw [if_pos t.2]; rfl
      · funext t
        show (Fin.cons p (fun _ => q) : Fin 2 → ℕ) (gord c' (Fin.natAdd _ t)) = p
        simp only [hgord, Fin.val_natAdd]; rw [if_neg (by omega)]; rfl
    have hpos := hposSat p c' hp
    rw [hwkv, ← hselD c' W p, ← hlabD c' W p, hordval, hpos]
    tauto
  rw [hM W q hq, Formula.sat_and, Formula.sat_and]
  rw [show Formula.Sat W (fun _ => q) Fin.elim0
          (Formula.faFO (bigAnd ((List.finRange P.toPoly.K).map clause)))
      ↔ ∀ p, p < W.length → ∀ c' : Fin P.toPoly.K,
          (P.toPoly.sel c' W (fun _ => p) ∧ P.toPoly.label c' W (fun _ => p) = D
            ∧ cfgPos M mthr (S c') (Front c') (Back c') W.length p) →
          P.toPoly.ord c c' W (fun _ => q) (fun _ => p) from ?_]
  · rw [← hsel W q, ← hlabU W q]
    refine and_congr ?_ (and_congr Iff.rfl ?_)
    · exact ⟨fun h => h.2, fun h => ⟨fun _ => hq, h⟩⟩
    · constructor
      · intro hall p hp c' hsel'
        exact hall ⟨c', fun _ => p⟩ ⟨fun _ => hp, hsel'.1⟩ hsel'.2.1 hsel'.2.2
      · intro hall b hbsel hbD hbres
        set p := b.2 (SliceBridge.z P.toPoly harity b.1) with hp
        have hbeq : b = ⟨b.1, fun _ => p⟩ := SliceBridge.atom_eq P.toPoly harity b
        rw [hbeq] at hbsel hbD ⊢
        exact hall p (hbsel.1 (SliceBridge.z P.toPoly harity b.1)) b.1 ⟨hbsel.2, hbD, hbres⟩
  · rw [Formula.faFO, Formula.sat_neg, Formula.sat_exFO]
    push Not
    refine forall_congr' (fun p => imp_congr_right (fun hp => ?_))
    rw [Formula.sat_neg, not_not, sat_bigAnd]
    constructor
    · intro hall c' hc'
      exact (hclauseSat p c' hp).mp
        (hall (clause c') (List.mem_map_of_mem (List.mem_finRange c'))) hc'
    · intro hall φ' hφ'
      obtain ⟨c', _, rfl⟩ := List.mem_map.mp hφ'
      exact (hclauseSat p c' hp).mpr (fun h => hall c' h)

end SliceFasGates
