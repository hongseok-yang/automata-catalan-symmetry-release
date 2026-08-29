/-
# `S` is itself a WRP map: composition failure inside WRP

The proof of the paper's `thm:wrp-not-closed` closes with: "By Theorem
`thm:eh` and Proposition `prop:conservative`, `S` itself belongs to `WRP`.
Hence two `WRP` maps, `D` and `S`, have a composite outside `WRP`, proving
that the class is not closed under composition" (paper.tex, Appendix
A.4).

This file discharges that observation **without** formalising `thm:eh`
(Engelfriet–Hoogeboom): we exhibit the word map computed by the machine `S`
directly,

    `sMap y = (the suffix of y after its first #)  if y starts with G, else ε`

prove that it is exactly the map the 2DFT `compS` computes
(`compS_computes_iff_sMap`, via runs of `S` on arbitrary inputs), and give it
a direct arity-1 polyregular presentation `sPoly` (selection: "the first
letter is `G` and some `#` lies strictly before this position"; label: the
letter at the position; order: the position order; no rank).  Hence

* `sMap_isRegular` — `sMap` is a deterministic MSO string transduction
  (`Polyreg.IsRegular`), matching the paper's "every deterministic 2DFT is a
  deterministic MSO string transduction";
* `sMap_isPolyregular`, `sMap_isWRP`, `sMap_isWRPPos` — so `S ∈ WRP`, also in
  the paper's arity-positive class;
* `sMap_compD_eq_Fge0` — the composite with the witness `D` is `F_{≥0}`;
* `wrp_not_closed_under_composition` — the paper's conclusion: two WRP maps
  (`D` and the map computed by `S`) whose composite is not WRP.

Trust: everything here is axiom-clean except the final corollary, which
admits `SliceMSO.buchi` through `Fge0_not_isWRP`.
-/
import RequestProject.WRPNotClosedComp
import RequestProject.WRPArityPos

open MSO WRPNotClosed TwoDFT

namespace WRPComp

open SState

/-! ## The suffix after the first separator -/

/-- The suffix of `y` strictly after its first `#` (empty if there is none). -/
def afterFirstSep : List GBD → List GBD
  | [] => []
  | a :: t => if a = GBD.sep then t else afterFirstSep t

theorem afterFirstSep_cons_sep (t : List GBD) :
    afterFirstSep (GBD.sep :: t) = t := by
  rw [afterFirstSep, if_pos rfl]

theorem afterFirstSep_cons_ne {a : GBD} (h : a ≠ GBD.sep) (t : List GBD) :
    afterFirstSep (a :: t) = afterFirstSep t := by
  rw [afterFirstSep, if_neg h]

theorem afterFirstSep_of_not_mem {y : List GBD} (h : GBD.sep ∉ y) :
    afterFirstSep y = [] := by
  induction y with
  | nil => rfl
  | cons a t ih =>
      rw [afterFirstSep_cons_ne (fun ha => h (ha ▸ List.mem_cons_self)) t]
      exact ih (fun ht => h (List.mem_cons_of_mem _ ht))

theorem afterFirstSep_append {pre : List GBD} (h : GBD.sep ∉ pre) (post : List GBD) :
    afterFirstSep (pre ++ GBD.sep :: post) = post := by
  induction pre with
  | nil => exact afterFirstSep_cons_sep post
  | cons a t ih =>
      rw [List.cons_append,
        afterFirstSep_cons_ne (fun ha => h (ha ▸ List.mem_cons_self)) _]
      exact ih (fun ht => h (List.mem_cons_of_mem _ ht))

/-- First-occurrence decomposition at the separator. -/
theorem first_sep_decomp : ∀ (l : List GBD), GBD.sep ∈ l →
    ∃ pre post, l = pre ++ GBD.sep :: post ∧ GBD.sep ∉ pre
  | [], h => absurd h (by simp)
  | a :: t, h => by
      by_cases ha : a = GBD.sep
      · exact ⟨[], t, by rw [ha, List.nil_append], by simp⟩
      · obtain ⟨pre, post, heq, hpre⟩ := first_sep_decomp t (by
          rcases List.mem_cons.mp h with h' | h'
          · exact absurd h'.symm ha
          · exact h')
        refine ⟨a :: pre, post, by rw [List.cons_append, heq], ?_⟩
        intro hmem
        rcases List.mem_cons.mp hmem with h' | h'
        · exact ha h'.symm
        · exact hpre h'

/-! ## The word map computed by `S` -/

/-- **The word map computed by the machine `S`**: gate on "the first letter is
`G`", then emit the suffix after the first `#`. -/
def sMap (y : List GBD) : Option (List GBD) :=
  some (if y.head? = some GBD.g then afterFirstSep y else [])

/-! ## The runs of `S` on arbitrary inputs -/

/-- The empty input: `S` steps off `⊢`, meets `⊣`, halts accepting with `ε`. -/
theorem compS_run_nil : compS.Computes [] [] := by
  have hη : compS.η init (tapeSym ([] : List GBD) 0) = some (first, true, []) := by
    rw [tapeSym_zero]
    exact compS_η_init_lmark
  have hrefl : compS.Steps ([] : List GBD) (first, 1) [] (first, 1) := Steps.refl _
  refine ⟨(first, 1), ?_, ?_, trivial⟩
  · show compS.Steps ([] : List GBD) (init, 0) [] (first, 1)
    simpa using Steps.head hη hrefl
  show compS.η first (tapeSym ([] : List GBD) 1) = none
  rw [tapeSym_ge ([] : List GBD) 1 (by simp), compS_η_rmark]

/-- A first letter other than `G`: the sink consumes everything, emitting `ε`. -/
theorem compS_run_notg {x : GBD} (hx : x ≠ GBD.g) (rest : List GBD) :
    compS.Computes (x :: rest) [] := by
  have s0 : compS.Steps (x :: rest) (init, 0) [] (first, 1) := by
    have hη : compS.η init (tapeSym (x :: rest) 0) = some (first, true, []) := by
      rw [tapeSym_zero]
      exact compS_η_init_lmark
    have hrefl : compS.Steps (x :: rest) (first, 1) [] (first, 1) := Steps.refl _
    simpa using Steps.head hη hrefl
  have s1 : compS.Steps (x :: rest) (first, 1) [] (sink, 2) := by
    have hη : compS.η first (tapeSym (x :: rest) 1) = some (sink, true, []) := by
      rw [tapeSym_cons_one, compS_η_first_letter, if_neg hx]
    have hrefl : compS.Steps (x :: rest) (sink, 2) [] (sink, 2) := Steps.refl _
    simpa using Steps.head hη hrefl
  have s2 := sink_sweep x rest
  have hsteps : compS.Steps (x :: rest) (init, 0) [] (sink, 2 + rest.length) := by
    simpa using (s0.trans s1).trans s2
  refine ⟨_, hsteps, ?_, trivial⟩
  show compS.η sink (tapeSym (x :: rest) (2 + rest.length)) = none
  rw [tapeSym_ge (x :: rest) _ (by simp only [List.length_cons]; omega), compS_η_rmark]

/-- First letter `G`, no separator: `seekSep` consumes everything, emitting
`ε`, and halts accepting at `⊣`. -/
theorem compS_run_g_nosep (rest : List GBD) (h : ∀ x ∈ rest, x ≠ GBD.sep) :
    compS.Computes (GBD.g :: rest) [] := by
  have s0 : compS.Steps (GBD.g :: rest) (init, 0) [] (first, 1) := by
    have hη : compS.η init (tapeSym (GBD.g :: rest) 0) = some (first, true, []) := by
      rw [tapeSym_zero]
      exact compS_η_init_lmark
    have hrefl : compS.Steps (GBD.g :: rest) (first, 1) [] (first, 1) := Steps.refl _
    simpa using Steps.head hη hrefl
  have s1 : compS.Steps (GBD.g :: rest) (first, 1) [] (seekSep, 2) := by
    have hη : compS.η first (tapeSym (GBD.g :: rest) 1) = some (seekSep, true, []) := by
      rw [tapeSym_cons_one, compS_η_first_letter, if_pos rfl]
    have hrefl : compS.Steps (GBD.g :: rest) (seekSep, 2) [] (seekSep, 2) := Steps.refl _
    simpa using Steps.head hη hrefl
  have s2 : compS.Steps (GBD.g :: rest) (seekSep, 2) [] (seekSep, 2 + rest.length) := by
    have hscan := steps_scan (T := compS) (w := GBD.g :: rest) (q := seekSep)
      (em := fun _ => []) rest 2
      (fun k hk => by
        rw [show 2 + k = k + 2 by omega]
        exact tapeSym_cons_succ GBD.g rest k hk)
      (fun a ha => by
        rw [compS_η_seekSep_letter, if_neg (h a ha)]
        rfl)
    have hnil : (rest.flatMap fun _ => ([] : List GBD)) = [] := by simp
    rw [hnil] at hscan
    exact hscan
  have hsteps : compS.Steps (GBD.g :: rest) (init, 0) [] (seekSep, 2 + rest.length) := by
    simpa using (s0.trans s1).trans s2
  refine ⟨_, hsteps, ?_, trivial⟩
  show compS.η seekSep (tapeSym (GBD.g :: rest) (2 + rest.length)) = none
  rw [tapeSym_ge (GBD.g :: rest) _ (by simp only [List.length_cons]; omega), compS_η_rmark]

/-- First letter `G`, separator present: `S` emits exactly the block after the
first `#`. -/
theorem compS_run_g (pre post : List GBD) (hpre : ∀ x ∈ pre, x ≠ GBD.sep) :
    compS.Computes (GBD.g :: (pre ++ [GBD.sep] ++ post)) post := by
  set y := GBD.g :: (pre ++ [GBD.sep] ++ post) with hy
  have hylen : y.length = pre.length + post.length + 2 := by
    rw [hy]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  have hcell : ∀ j, (hj : j < y.length) →
      tapeSym y (j + 1) = .letter y[j] :=
    fun j hj => tapeSym_succ y j hj
  have s0 : compS.Steps y (init, 0) [] (first, 1) := by
    have hη : compS.η init (tapeSym y 0) = some (first, true, []) := by
      rw [tapeSym_zero]
      exact compS_η_init_lmark
    have hrefl : compS.Steps y (first, 1) [] (first, 1) := Steps.refl _
    simpa using Steps.head hη hrefl
  have s1 : compS.Steps y (first, 1) [] (seekSep, 2) := by
    have hη : compS.η first (tapeSym y 1) = some (seekSep, true, []) := by
      rw [hy, tapeSym_cons_one, compS_η_first_letter, if_pos rfl]
    have hrefl : compS.Steps y (seekSep, 2) [] (seekSep, 2) := Steps.refl _
    simpa using Steps.head hη hrefl
  have s2 : compS.Steps y (seekSep, 2) [] (seekSep, 2 + pre.length) := by
    have hscan := steps_scan (T := compS) (w := y) (q := seekSep)
      (em := fun _ => []) pre 2
      (fun k hk => by
        rw [show 2 + k = k + 2 by omega, hy,
          tapeSym_cons_succ _ _ k (by
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega)]
        congr 1
        rw [List.getElem_append_left (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega)]
        rw [List.getElem_append_left hk])
      (fun a ha => by
        rw [compS_η_seekSep_letter, if_neg (hpre a ha)]
        rfl)
    have hnil : (pre.flatMap fun _ => ([] : List GBD)) = [] := by simp
    rw [hnil] at hscan
    exact hscan
  have s3 : compS.Steps y (seekSep, 2 + pre.length) [] (copier, 3 + pre.length) := by
    have hcellsep : tapeSym y (2 + pre.length) = .letter GBD.sep := by
      rw [show 2 + pre.length = pre.length + 2 by omega, hy,
        tapeSym_cons_succ _ _ pre.length (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega)]
      congr 1
      rw [List.getElem_append_left (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega)]
      rw [List.getElem_append_right (le_refl _)]
      simp
    have hη : compS.η seekSep (tapeSym y (2 + pre.length))
        = some (copier, true, []) := by
      rw [hcellsep, compS_η_seekSep_letter, if_pos rfl]
    have hrefl : compS.Steps y (copier, moveDir (2 + pre.length) true) []
        (copier, moveDir (2 + pre.length) true) := Steps.refl _
    have h := Steps.head hη hrefl
    have hmv : moveDir (2 + pre.length) true = 3 + pre.length := by
      rw [moveDir_true]
      omega
    rw [hmv] at h
    simpa using h
  have s4 : compS.Steps y (copier, 3 + pre.length) post
      (copier, 3 + pre.length + post.length) := by
    have hscan := steps_scan (T := compS) (w := y) (q := copier)
      (em := fun a => [a]) post (3 + pre.length)
      (fun k hk => by
        rw [show 3 + pre.length + k = (pre.length + 1 + k) + 2 by omega, hy,
          tapeSym_cons_succ _ _ (pre.length + 1 + k) (by
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega)]
        congr 1
        rw [List.getElem_append_right (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega)]
        congr 1
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega)
      (fun a _ => compS_η_copier_letter a)
    have hflat : (post.flatMap fun a => ([a] : List GBD)) = post := by simp
    rw [hflat] at hscan
    exact hscan
  have hsteps : compS.Steps y (init, 0) post
      (copier, 3 + pre.length + post.length) := by
    simpa using (((s0.trans s1).trans s2).trans s3).trans s4
  refine ⟨_, hsteps, ?_, trivial⟩
  show compS.η copier (tapeSym y (3 + pre.length + post.length)) = none
  rw [tapeSym_ge y _ (by omega), compS_η_rmark]

/-- The value computed by `S` on an arbitrary input is `sMap`'s payload. -/
theorem compS_computes_val (y : List GBD) :
    compS.Computes y (if y.head? = some GBD.g then afterFirstSep y else []) := by
  cases y with
  | nil =>
      rw [if_neg (by simp)]
      exact compS_run_nil
  | cons a rest =>
      by_cases ha : a = GBD.g
      · subst ha
        rw [List.head?_cons, if_pos rfl,
          afterFirstSep_cons_ne (by decide) rest]
        by_cases hsep : GBD.sep ∈ rest
        · obtain ⟨pre, post, rfl, hpre⟩ := first_sep_decomp rest hsep
          have hpre' : ∀ x ∈ pre, x ≠ GBD.sep := fun x hx h' => hpre (h' ▸ hx)
          rw [afterFirstSep_append hpre post,
            show pre ++ GBD.sep :: post = pre ++ [GBD.sep] ++ post by simp]
          exact compS_run_g pre post hpre'
        · rw [afterFirstSep_of_not_mem hsep]
          exact compS_run_g_nosep rest (fun x hx h' => hsep (h' ▸ hx))
      · rw [List.head?_cons, if_neg (fun h => ha (Option.some.inj h))]
        exact compS_run_notg ha rest

/-- **`sMap` is the map computed by the machine `S`.** -/
theorem compS_computes_iff_sMap (y out : List GBD) :
    compS.Computes y out ↔ sMap y = some out := by
  have hval := compS_computes_val y
  constructor
  · intro h
    have heq := computes_unique h hval
    rw [sMap, heq]
  · intro h
    have heq : (if y.head? = some GBD.g then afterFirstSep y else []) = out :=
      Option.some.inj h
    rw [← heq]
    exact hval

/-! ## The arity-1 presentation of `sMap`

Selection: "some `#` lies strictly before this position, and the first letter
is `G`."  Label: the letter at the position.  Order: the position order. -/

/-- The selection formula: `(∃ p < x, y[p] = #) ∧ (∃ p₀ minimal, y[p₀] = G)`. -/
def sSelFormula : Formula GBD 1 0 :=
  Formula.and
    (Formula.exFO (Formula.and (Formula.lt 0 1) (Formula.labelEq 0 GBD.sep)))
    (Formula.exFO (Formula.and
      (Formula.neg (Formula.exFO (Formula.lt 0 1)))
      (Formula.labelEq 0 GBD.g)))

private theorem sLabelDef (γ : GBD) :
    MSODefinableRel (Alpha := GBD) 1
      (fun w (ī : Fin 1 → ℕ) => (w[ī ⟨0, Nat.one_pos⟩]?).getD GBD.g = γ) := by
  cases γ with
  | g =>
      refine ⟨Formula.neg (Formula.or (Formula.labelEq 0 GBD.b)
        (Formula.or (Formula.labelEq 0 GBD.sep)
          (Formula.or (Formula.labelEq 0 GBD.u) (Formula.labelEq 0 GBD.d)))),
        fun w ρ => ?_⟩
      show ((w[ρ ⟨0, Nat.one_pos⟩]?).getD GBD.g = GBD.g) ↔
        ¬ (w[ρ ⟨0, Nat.one_pos⟩]? = some GBD.b ∨
          (w[ρ ⟨0, Nat.one_pos⟩]? = some GBD.sep ∨
            (w[ρ ⟨0, Nat.one_pos⟩]? = some GBD.u ∨
              w[ρ ⟨0, Nat.one_pos⟩]? = some GBD.d)))
      cases ho : w[ρ ⟨0, Nat.one_pos⟩]? with
      | none => simp
      | some a => cases a <;> simp
  | b =>
      refine ⟨Formula.labelEq 0 GBD.b, fun w ρ => ?_⟩
      show ((w[ρ ⟨0, Nat.one_pos⟩]?).getD GBD.g = GBD.b) ↔
        w[ρ ⟨0, Nat.one_pos⟩]? = some GBD.b
      cases ho : w[ρ ⟨0, Nat.one_pos⟩]? with
      | none => simp
      | some a => cases a <;> simp
  | sep =>
      refine ⟨Formula.labelEq 0 GBD.sep, fun w ρ => ?_⟩
      show ((w[ρ ⟨0, Nat.one_pos⟩]?).getD GBD.g = GBD.sep) ↔
        w[ρ ⟨0, Nat.one_pos⟩]? = some GBD.sep
      cases ho : w[ρ ⟨0, Nat.one_pos⟩]? with
      | none => simp
      | some a => cases a <;> simp
  | u =>
      refine ⟨Formula.labelEq 0 GBD.u, fun w ρ => ?_⟩
      show ((w[ρ ⟨0, Nat.one_pos⟩]?).getD GBD.g = GBD.u) ↔
        w[ρ ⟨0, Nat.one_pos⟩]? = some GBD.u
      cases ho : w[ρ ⟨0, Nat.one_pos⟩]? with
      | none => simp
      | some a => cases a <;> simp
  | d =>
      refine ⟨Formula.labelEq 0 GBD.d, fun w ρ => ?_⟩
      show ((w[ρ ⟨0, Nat.one_pos⟩]?).getD GBD.g = GBD.d) ↔
        w[ρ ⟨0, Nat.one_pos⟩]? = some GBD.d
      cases ho : w[ρ ⟨0, Nat.one_pos⟩]? with
      | none => simp
      | some a => cases a <;> simp

private theorem sOrdDef :
    MSODefinableRel (Alpha := GBD) (1 + 1)
      (fun _ (ij : Fin (1 + 1) → ℕ) =>
        ij (Fin.castAdd 1 ⟨0, Nat.one_pos⟩) < ij (Fin.natAdd 1 ⟨0, Nat.one_pos⟩)) :=
  ⟨Formula.lt (Fin.castAdd 1 ⟨0, Nat.one_pos⟩) (Fin.natAdd 1 ⟨0, Nat.one_pos⟩),
   fun _ _ => Iff.rfl⟩

/-- The presentation of `sMap`: one copy of arity `1`, total domain, the
`sSelFormula` selection (as its own satisfaction predicate, so the
definability certificate is definitional), the letter label, the position
order, no rank. -/
def sPoly : Polyreg.Presentation GBD GBD where
  K := 1
  arity := fun _ => 1
  domain := fun _ => True
  domainDef := ⟨Formula.tru, fun _ => Iff.rfl⟩
  sel := fun _ w ī => sSelFormula.Sat w ī Fin.elim0
  selDef := fun _ => ⟨sSelFormula, fun _ _ => Iff.rfl⟩
  label := fun _ w ī => (w[ī ⟨0, Nat.one_pos⟩]?).getD GBD.g
  labelDef := fun _ γ => sLabelDef γ
  ord := fun _ _ _ ii jj => ii ⟨0, Nat.one_pos⟩ < jj ⟨0, Nat.one_pos⟩
  ordDef := fun _ _ => sOrdDef

/-- The unique copy index of `sPoly`. -/
def sC : Fin sPoly.K := ⟨0, by decide⟩

/-- The arity-1 atom of `sPoly` at position `p`. -/
def sAtom (p : ℕ) : sPoly.Atom := ⟨sC, fun _ => p⟩

/-- The position of an `sPoly` atom. -/
def sPos (a : sPoly.Atom) : ℕ := a.2 ⟨0, Nat.one_pos⟩

@[simp] theorem sPos_sAtom (p : ℕ) : sPos (sAtom p) = p := rfl

theorem sFin_arity_eq {c : Fin sPoly.K} (t : Fin (sPoly.arity c)) :
    t = ⟨0, Nat.one_pos⟩ := by
  apply Fin.ext
  show t.val = 0
  have h : t.val < 1 := t.isLt
  omega

theorem sCopy_eq (c : Fin sPoly.K) : c = sC := by
  apply Fin.ext
  have h : c.val < 1 := c.isLt
  have h0 : sC.val = 0 := rfl
  omega

theorem eq_sAtom (a : sPoly.Atom) : a = sAtom (sPos a) := by
  obtain ⟨c, ī⟩ := a
  obtain rfl : c = sC := sCopy_eq c
  exact congrArg (Sigma.mk sC) (funext fun t => by rw [sFin_arity_eq t]; rfl)

theorem atomOrd_sAtom (w : List GBD) (p q : ℕ) :
    sPoly.atomOrd w (sAtom p) (sAtom q) ↔ p < q := by
  constructor
  · intro h; exact h
  · intro h; exact h

theorem sAtomOrd_iff (w : List GBD) (a b : sPoly.Atom) :
    sPoly.atomOrd w a b ↔ sPos a < sPos b := by
  conv_lhs => rw [eq_sAtom a, eq_sAtom b]
  exact atomOrd_sAtom w _ _

theorem sPoly_valid : sPoly.Valid where
  irrefl := fun w a _ hbad => by
    rw [sAtomOrd_iff] at hbad
    exact lt_irrefl _ hbad
  trans := fun w a b c _ _ _ hab hbc => by
    rw [sAtomOrd_iff] at hab hbc ⊢
    exact lt_trans hab hbc
  trichot := fun w a b _ _ => by
    rcases lt_trichotomy (sPos a) (sPos b) with h | h | h
    · exact Or.inl ((sAtomOrd_iff w a b).mpr h)
    · refine Or.inr (Or.inl ?_)
      rw [eq_sAtom a, eq_sAtom b, h]
    · exact Or.inr (Or.inr ((sAtomOrd_iff w b a).mpr h))

/-! ## Semantics of the selection -/

private theorem sat_head_iff (w : List GBD) :
    (∃ p₀, p₀ < w.length ∧ ((¬ ∃ q, q < w.length ∧ q < p₀) ∧ w[p₀]? = some GBD.g)) ↔
      w.head? = some GBD.g := by
  cases w with
  | nil => simp
  | cons a t =>
      rw [List.head?_cons]
      constructor
      · rintro ⟨p₀, hlen, hmin, hlab⟩
        obtain rfl : p₀ = 0 := by
          by_contra hne
          exact hmin ⟨0, by omega, by omega⟩
        simpa using hlab
      · intro hg
        exact ⟨0, by simp, fun ⟨q, _, hq⟩ => by omega, by
          rw [List.getElem?_cons_zero]
          exact hg⟩

/-- The selection formula's semantics: the first letter is `G` and some `#`
lies strictly before the position. -/
theorem sSel_iff (y : List GBD) (x : ℕ) :
    sSelFormula.Sat y (fun _ => x) Fin.elim0 ↔
      (y.head? = some GBD.g ∧ ∃ p, p < y.length ∧ p < x ∧ y[p]? = some GBD.sep) := by
  show ((∃ p, p < y.length ∧ (p < x ∧ y[p]? = some GBD.sep)) ∧
      (∃ p₀, p₀ < y.length ∧ ((¬ ∃ q, q < y.length ∧ q < p₀) ∧ y[p₀]? = some GBD.g))) ↔ _
  rw [sat_head_iff]
  constructor
  · rintro ⟨⟨p, h1, h2, h3⟩, hh⟩
    exact ⟨hh, p, h1, h2, h3⟩
  · rintro ⟨hh, p, h1, h2, h3⟩
    exact ⟨⟨p, h1, h2, h3⟩, hh⟩

/-- Selectedness of the atom at `x`. -/
theorem selectedAtom_sAtom_iff (y : List GBD) (x : ℕ) :
    sPoly.selectedAtom y (sAtom x) ↔
      (x < y.length ∧ y.head? = some GBD.g ∧
        ∃ p, p < y.length ∧ p < x ∧ y[p]? = some GBD.sep) := by
  constructor
  · rintro ⟨hval, hsel⟩
    obtain ⟨hh, hp⟩ := (sSel_iff y x).mp hsel
    exact ⟨hval ⟨0, Nat.one_pos⟩, hh, hp⟩
  · rintro ⟨hx, hh, hp⟩
    exact ⟨fun _ => hx, (sSel_iff y x).mpr ⟨hh, hp⟩⟩

/-! ## The declarative outputs of `sPoly` -/

/-- No selected atoms when the first letter is not `G`. -/
theorem sPoly_isOutput_nil_of_not_headg {y : List GBD}
    (h : y.head? ≠ some GBD.g) : sPoly.IsOutput y [] := by
  refine ⟨[], List.nodup_nil, ?_, List.Pairwise.nil, rfl⟩
  intro a
  constructor
  · intro h'
    exact absurd h' (by simp)
  · intro hsel
    exfalso
    rw [eq_sAtom a] at hsel
    obtain ⟨-, hh, -⟩ := (selectedAtom_sAtom_iff y (sPos a)).mp hsel
    exact h hh

/-- No selected atoms when there is no separator. -/
theorem sPoly_isOutput_nil_of_no_sep {y : List GBD}
    (h : GBD.sep ∉ y) : sPoly.IsOutput y [] := by
  refine ⟨[], List.nodup_nil, ?_, List.Pairwise.nil, rfl⟩
  intro a
  constructor
  · intro h'
    exact absurd h' (by simp)
  · intro hsel
    exfalso
    rw [eq_sAtom a] at hsel
    obtain ⟨-, -, p, -, -, hplab⟩ := (selectedAtom_sAtom_iff y (sPos a)).mp hsel
    exact h (List.mem_of_getElem? hplab)

/-- On `G ‖ pre ‖ # ‖ post` (no `#` in `pre`), the selected atoms are exactly
the positions of `post`, in order, labelled by `post` — the output is `post`. -/
theorem sPoly_isOutput_g (pre post : List GBD) (hpre : GBD.sep ∉ pre) :
    sPoly.IsOutput (GBD.g :: (pre ++ GBD.sep :: post)) post := by
  have hlen : (GBD.g :: (pre ++ GBD.sep :: post)).length
      = pre.length + post.length + 2 := by
    simp only [List.length_cons, List.length_append]
    omega
  -- the cell before the window is the separator …
  have hsepcell : (GBD.g :: (pre ++ GBD.sep :: post))[pre.length + 1]?
      = some GBD.sep := by
    rw [show pre.length + 1 = pre.length + 1 from rfl, List.getElem?_cons_succ,
      List.getElem?_append_right (le_refl _), Nat.sub_self,
      List.getElem?_cons_zero]
  -- … and every earlier cell is not
  have hnosep : ∀ p, p < pre.length + 1 →
      (GBD.g :: (pre ++ GBD.sep :: post))[p]? ≠ some GBD.sep := by
    intro p hp hlab
    rcases Nat.eq_zero_or_pos p with rfl | hpos
    · rw [List.getElem?_cons_zero] at hlab
      exact absurd (Option.some.inj hlab) (by decide)
    · obtain ⟨j, rfl⟩ : ∃ j, p = j + 1 := ⟨p - 1, by omega⟩
      have hj : j < pre.length := by omega
      rw [List.getElem?_cons_succ, List.getElem?_append_left hj,
        List.getElem?_eq_getElem hj] at hlab
      exact hpre ((Option.some.inj hlab) ▸ List.getElem_mem hj)
  -- selected positions = the window [pre.length + 2, length)
  have hself : ∀ x, sPoly.selectedAtom (GBD.g :: (pre ++ GBD.sep :: post)) (sAtom x) ↔
      (pre.length + 2 ≤ x ∧ x < pre.length + post.length + 2) := by
    intro x
    rw [selectedAtom_sAtom_iff, hlen]
    constructor
    · rintro ⟨hx, -, p, hplen, hpx, hplab⟩
      refine ⟨?_, hx⟩
      by_contra hlt
      push Not at hlt
      exact hnosep p (by omega) hplab
    · rintro ⟨hge, hx⟩
      exact ⟨hx, rfl, pre.length + 1, by omega, by omega, hsepcell⟩
  refine ⟨(List.range post.length).map (fun j => sAtom (pre.length + 2 + j)),
    ?_, ?_, ?_, ?_⟩
  · refine List.nodup_range.map (fun j k h => ?_)
    have h' := congrArg sPos h
    simp only [sPos_sAtom] at h'
    omega
  · intro a
    rw [List.mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [List.mem_range] at hj
      exact (hself _).mpr ⟨by omega, by omega⟩
    · intro hselA
      rw [eq_sAtom a] at hselA
      obtain ⟨hge, hlt⟩ := (hself (sPos a)).mp hselA
      refine ⟨sPos a - (pre.length + 2), List.mem_range.mpr (by omega), ?_⟩
      rw [show pre.length + 2 + (sPos a - (pre.length + 2)) = sPos a by omega]
      exact (eq_sAtom a).symm
  · refine List.Pairwise.map _ (fun j k hjk => ?_) List.pairwise_lt_range
    exact (atomOrd_sAtom _ _ _).mpr (by omega)
  · rw [List.map_map]
    refine List.ext_getElem (by simp) fun i hi hi' => ?_
    have hipost : i < post.length := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
    show post[i] = ((GBD.g :: (pre ++ GBD.sep :: post))[pre.length + 2 + i]?).getD GBD.g
    rw [show pre.length + 2 + i = (pre.length + (1 + i)) + 1 by omega,
      List.getElem?_cons_succ,
      List.getElem?_append_right (by omega),
      Nat.add_sub_cancel_left,
      show 1 + i = i + 1 by omega,
      List.getElem?_cons_succ,
      List.getElem?_eq_getElem hipost,
      Option.getD_some]

/-- The declarative output of `sPoly` is `sMap`'s payload. -/
theorem sPoly_isOutput_val (y : List GBD) :
    sPoly.IsOutput y (if y.head? = some GBD.g then afterFirstSep y else []) := by
  by_cases hg : y.head? = some GBD.g
  · rw [if_pos hg]
    obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp hg
    rw [afterFirstSep_cons_ne (by decide) rest]
    by_cases hsep : GBD.sep ∈ rest
    · obtain ⟨pre, post, rfl, hpre⟩ := first_sep_decomp rest hsep
      rw [afterFirstSep_append hpre post]
      exact sPoly_isOutput_g pre post hpre
    · rw [afterFirstSep_of_not_mem hsep]
      refine sPoly_isOutput_nil_of_no_sep ?_
      intro hmem
      rcases List.mem_cons.mp hmem with h' | h'
      · exact absurd h'.symm (by decide)
      · exact hsep h'
  · rw [if_neg hg]
    exact sPoly_isOutput_nil_of_not_headg hg

/-! ## `sMap` is a regular string transduction, hence WRP -/

/-- **`sMap` is a deterministic MSO string transduction** (arity-1 valid
polyregular presentation) — the model the paper's `thm:eh` identifies with
deterministic 2DFTs. -/
theorem sMap_isRegular : Polyreg.IsRegular sMap := by
  refine ⟨sPoly, sPoly_valid, fun _ => rfl, fun y out => ?_⟩
  constructor
  · intro h
    refine ⟨trivial, ?_⟩
    have heq : (if y.head? = some GBD.g then afterFirstSep y else []) = out :=
      Option.some.inj h
    rw [← heq]
    exact sPoly_isOutput_val y
  · rintro ⟨-, hout⟩
    exact congrArg some
      (sPoly.isOutput_unique sPoly_valid (sPoly_isOutput_val y) hout)

theorem sMap_isPolyregular : Polyreg.IsPolyregular sMap :=
  sMap_isRegular.isPolyregular

/-- **`S ∈ WRP`** — with a direct presentation, not through `thm:eh`. -/
theorem sMap_isWRP : WRP.IsWRP sMap :=
  WRP.isWRP_of_isPolyregular sMap_isPolyregular

/-- `S` also lies in the paper's arity-positive class. -/
theorem sMap_isWRPPos : WRP.IsWRPPos sMap :=
  WRP.isWRPPos_of_isPolyregularPos sMap_isRegular.isPolyregularPos

/-! ## The composite with `D` -/

/-- On the witness `D`'s outputs, `sMap` computes exactly `F_{≥0}`. -/
theorem sMap_compD (w : List Step) : sMap (compD w) = Fge0 w := by
  by_cases hw : ∀ i, i < w.length → 0 ≤ height w i
  · have hg : (compD w).head? = some GBD.g := (head_compD_eq_g_iff w).mpr hw
    have hnosep : GBD.sep ∉ (wncD w).map relGB := by
      intro hmem
      obtain ⟨xb, -, hb⟩ := List.mem_map.mp hmem
      exact relGB_ne_sep xb hb
    rw [sMap, if_pos hg, Fge0, if_pos hw]
    congr 1
    rw [show compD w = (wncD w).map relGB ++ GBD.sep :: w.map relStep by
      rw [compD]; simp]
    exact afterFirstSep_append hnosep _
  · have hg : (compD w).head? ≠ some GBD.g :=
      fun h => hw ((head_compD_eq_g_iff w).mp h)
    rw [sMap, if_neg hg, Fge0, if_neg hw]

/-- **`thm:wrp-not-closed`, the "consequently" (paper.tex, Appendix
A.4), inside WRP**: two WRP maps — the witness `D` and the map computed
by the left-to-right 2DFT `S` — whose composite (= `F_{≥0}`) is not a WRP
map.  Hence `WRP` is not closed under composition. -/
theorem wrp_not_closed_under_composition :
    ∃ (Dm : List Step → Option (List GBD)) (Sm : List GBD → Option (List GBD)),
      WRP.IsWRP Dm ∧ WRP.IsWRP Sm ∧
      (∀ y out, Sm y = some out ↔ compS.Computes y out) ∧
      ¬ WRP.IsWRP (fun w => (Dm w).bind Sm) := by
  refine ⟨fun w => some (compD w), sMap, compD_isWRP, sMap_isWRP, ?_, ?_⟩
  · intro y out
    exact (compS_computes_iff_sMap y out).symm
  · have hEq : (fun w : List Step => ((some (compD w)).bind sMap)) = Fge0 :=
      funext fun w => sMap_compD w
    rw [hEq]
    exact Fge0_not_isWRP

end WRPComp
