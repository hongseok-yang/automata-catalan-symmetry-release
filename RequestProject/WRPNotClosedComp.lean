/-
# Composition failure: `S ∘ D = F_{≥0} ∉ WRP` (`thm:wrp-not-closed`, Moreover)

`thm:wrp-not-closed` (paper.tex) adds:
"Moreover, there exists a deterministic 2DFT `S` whose input head moves only
from left to right such that `S ∘ D ∉ WRP`."  The proof (Appendix
A.4) takes the three-block witness `D` of `WRPCompWitness.lean`, and the
one-way machine `S` that

* records in its finite control whether the first letter is `G`,
* skips the rest of block 0 and the separator (advancing past the first `#`),
* copies the remaining block-2 letters to its output iff that bit is set,
* halts (acceptingly) at the right end marker.

On `D(w)` the composite outputs the verbatim input copy when `w ∈ L_{≥0}`
(first letter `G`) and `ε` otherwise; that is, `S ∘ D = F_{≥0}`, the map
`w ↦ (w if every prefix height is ≥ 0 else ε)` from the proof of
`thm:wrp-strict-below-logspace` (which the paper cites at this point), and
`F_{≥0} ∉ WRP` because its nonempty-output preimage `Lnn \ {ε}` would have to
be regular (`lem:wrp-nonempty-regular` = `wrp_nonempty_preimage_regular`) but
is not (the same `U^p D^q U` pigeonhole as `not_regular_Lnn`).

Contents:

* `compS` — the machine `S`, with `compS_leftToRight`;
* `compS_computes_of_mem` / `compS_computes_of_not_mem` — the run of `S` on
  `D(w)`, assembled with `TwoDFT.steps_scan`;
* `Fge0` / `Fge0_not_isWRP` — the map `F_{≥0}` (into the block-2 alphabet)
  and its non-membership, via `wrp_nonempty_preimage_regular` and the
  pigeonhole `not_regular_LnnPos`;
* `wrp_not_closed_composition` — the packaged paper statement: the SAME
  `D` and `K` as claim 1, the left-to-right `S`, and: any function realising
  the relational composite `S ∘ D` is not WRP.

Trust: `Fge0_not_isWRP` and the final theorem admit `SliceMSO.buchi` (through
`wrp_nonempty_preimage_regular`); everything else is axiom-clean.

(The paper's closing observation that `S` itself lies in `WRP` — via
Theorem `thm:eh` (Engelfriet–Hoogeboom) and `prop:conservative` — is cited
background: `thm:eh` is not formalised in this repository, and the observation
is not needed for the theorem statement above.)
-/
import RequestProject.TwoDFT
import RequestProject.WRPCompWitness
import RequestProject.WRPNonemptyRegular

open Step WRPNotClosed TwoDFT

namespace WRPComp

/-! ## The machine `S` (paper.tex) -/

/-- States of `S`: initial (at `⊢`), reading the first letter, seeking the
separator with the `G`-bit set, copying block 2, and the emitless sink (the
`G`-bit unset). -/
inductive SState | init | first | seekSep | copier | sink
  deriving DecidableEq

instance : Fintype SState :=
  ⟨⟨{.init, .first, .seekSep, .copier, .sink}, by decide⟩,
    fun x => by cases x <;> decide⟩

open SState

/-- **The left-to-right 2DFT `S`.**  From `⊢` it enters the word; on the first
letter it branches on "is it `G`?"; with the bit set it advances to the first
`#` and then copies every later letter; with the bit unset it consumes the
input emitting nothing.  It halts at `⊣` in every state, always accepting. -/
def compS : TwoDFT GBD GBD where
  Q := SState
  fintypeQ := inferInstance
  q0 := init
  F := fun _ => True
  η := fun q s => match q, s with
    | init, .lmark => some (first, true, [])
    | first, .letter x => if x = GBD.g then some (seekSep, true, []) else some (sink, true, [])
    | seekSep, .letter x => if x = GBD.sep then some (copier, true, []) else some (seekSep, true, [])
    | copier, .letter x => some (copier, true, [x])
    | sink, .letter _ => some (sink, true, [])
    | _, _ => none
  lmark_right := by
    intro q q' d u h
    cases q <;> simp_all
  rmark_left := by
    intro q q' d u h
    cases q <;> simp_all

@[simp] theorem compS_η_init_lmark :
    compS.η init .lmark = some (first, true, []) := rfl

@[simp] theorem compS_η_first_letter (x : GBD) :
    compS.η first (.letter x)
      = (if x = GBD.g then some (seekSep, true, []) else some (sink, true, [])) := rfl

@[simp] theorem compS_η_seekSep_letter (x : GBD) :
    compS.η seekSep (.letter x)
      = (if x = GBD.sep then some (copier, true, []) else some (seekSep, true, [])) := rfl

@[simp] theorem compS_η_copier_letter (x : GBD) :
    compS.η copier (.letter x) = some (copier, true, [x]) := rfl

@[simp] theorem compS_η_rmark (q : SState) : compS.η q .rmark = none := by
  cases q <;> rfl

/-- `S`'s head moves only from left to right (the condition in the paper's
`thm:wrp-not-closed`). -/
theorem compS_leftToRight : compS.LeftToRight := by
  rintro q s ⟨q', d, u⟩ h
  cases q <;> cases s <;>
    (try simp only [compS_η_first_letter, compS_η_seekSep_letter] at h) <;>
    (try split at h) <;> (try cases h) <;> rfl

/-! ## The letters of the diagnostic block are never the separator -/

theorem relGB_ne_sep (x : GB) : relGB x ≠ GBD.sep := by
  cases x <;> simp [relGB]

theorem relGB_eq_g_iff (x : GB) : relGB x = GBD.g ↔ x = GB.g := by
  cases x <;> simp [relGB]

/-! ## Tape-cell helpers on cons-form words -/

theorem tapeSym_cons_one (x : GBD) (R : List GBD) :
    tapeSym (x :: R) 1 = .letter x := by
  have h := tapeSym_succ (x :: R) 0 (by simp)
  simpa using h

theorem tapeSym_cons_succ (x : GBD) (R : List GBD) (k : ℕ)
    (hk : k < R.length) :
    tapeSym (x :: R) (k + 2) = .letter R[k] := by
  have h := tapeSym_succ (x :: R) (k + 1) (by simpa using Nat.succ_lt_succ hk)
  rw [List.getElem_cons_succ] at h
  rw [show k + 2 = k + 1 + 1 by omega]
  exact h

/-! ## The run of `S` on `D(w)` -/

/-- The generic sink sweep: from `(sink, 2)` on `x :: R`, the machine consumes
the rest of the tape emitting nothing. -/
theorem sink_sweep (x : GBD) (R : List GBD) :
    compS.Steps (x :: R) (sink, 2) [] (sink, 2 + R.length) := by
  have h := steps_scan (T := compS) (w := x :: R) (q := sink) (em := fun _ => []) R 2
    (fun k hk => by
      rw [show 2 + k = k + 2 by omega]
      exact tapeSym_cons_succ x R k hk)
    (fun a _ => rfl)
  have hnil : (R.flatMap fun _ => ([] : List GBD)) = [] := by simp
  rw [hnil] at h
  exact h

/-- **The rejecting run** (first letter not `G`): `S` maps `D(w)` to `ε`. -/
theorem compS_computes_of_not_mem (w : List Step) (hw : w ∉ Lnn) :
    compS.Computes (compD w) [] := by
  obtain ⟨b0, t0, hd⟩ : ∃ b0 t0, wncD w = b0 :: t0 := by
    cases hwd : wncD w with
    | nil => exact absurd hwd (wncD_ne_nil w)
    | cons b0 t0 => exact ⟨b0, t0, rfl⟩
  have hb0 : b0 ≠ GB.g := by
    intro h
    apply hw
    rw [← head_wncD_eq_g_iff w, hd, h]
    rfl
  have hy : compD w = relGB b0 :: (t0.map relGB ++ [GBD.sep] ++ w.map relStep) := by
    rw [compD, hd]
    rfl
  have hylen : (compD w).length
      = 1 + (t0.map relGB ++ [GBD.sep] ++ w.map relStep).length := by
    rw [hy]
    simp only [List.length_cons]
    omega
  have s0 : compS.Steps (compD w) (init, 0) [] (first, 1) := by
    have hη : compS.η init (tapeSym (compD w) 0) = some (first, true, []) := by
      rw [tapeSym_zero]
      exact compS_η_init_lmark
    have hrefl : compS.Steps (compD w) (first, 1) [] (first, 1) := Steps.refl _
    simpa using Steps.head hη hrefl
  have s1 : compS.Steps (compD w) (first, 1) [] (sink, 2) := by
    have hcell1 : tapeSym (compD w) 1 = .letter (relGB b0) := by
      rw [hy]
      exact tapeSym_cons_one _ _
    have hη : compS.η first (tapeSym (compD w) 1) = some (sink, true, []) := by
      rw [hcell1, compS_η_first_letter,
        if_neg (fun hgg => hb0 ((relGB_eq_g_iff b0).mp hgg))]
    have hrefl : compS.Steps (compD w) (sink, 2) [] (sink, 2) := Steps.refl _
    simpa using Steps.head hη hrefl
  have s2 : compS.Steps (compD w) (sink, 2) []
      (sink, 2 + (t0.map relGB ++ [GBD.sep] ++ w.map relStep).length) := by
    have h := sink_sweep (relGB b0) (t0.map relGB ++ [GBD.sep] ++ w.map relStep)
    rwa [← hy] at h
  have hsteps : compS.Steps (compD w) (init, 0) []
      (sink, 2 + (t0.map relGB ++ [GBD.sep] ++ w.map relStep).length) := by
    have h := (s0.trans s1).trans s2
    simpa using h
  refine ⟨_, hsteps, ?_, trivial⟩
  show compS.η sink
      (tapeSym (compD w) (2 + (t0.map relGB ++ [GBD.sep] ++ w.map relStep).length))
    = none
  rw [tapeSym_ge (compD w) _ (by omega), compS_η_rmark]

/-- **The accepting-copy run** (first letter `G`): `S` maps `D(w)` to the
verbatim block-2 copy of `w`. -/
theorem compS_computes_of_mem (w : List Step) (hw : w ∈ Lnn) :
    compS.Computes (compD w) (w.map relStep) := by
  obtain ⟨dT, hd⟩ : ∃ dT, (wncD w).map relGB = GBD.g :: dT := by
    rw [← List.head?_eq_some_iff, List.head?_map,
      (head_wncD_eq_g_iff w).mpr hw]
    rfl
  have hy : compD w = GBD.g :: (dT ++ [GBD.sep] ++ w.map relStep) := by
    rw [compD, hd]
    rfl
  have hylen : (compD w).length = dT.length + w.length + 2 := by
    rw [hy]
    simp only [List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega
  have hdT_ne_sep : ∀ x ∈ dT, x ≠ GBD.sep := by
    intro x hx
    have hx' : x ∈ (wncD w).map relGB := by
      rw [hd]
      exact List.mem_cons_of_mem _ hx
    obtain ⟨bb, -, rfl⟩ := List.mem_map.mp hx'
    exact relGB_ne_sep bb
  -- run pieces
  have s0 : compS.Steps (compD w) (init, 0) [] (first, 1) := by
    have hη : compS.η init (tapeSym (compD w) 0) = some (first, true, []) := by
      rw [tapeSym_zero]
      exact compS_η_init_lmark
    have hrefl : compS.Steps (compD w) (first, 1) [] (first, 1) := Steps.refl _
    simpa using Steps.head hη hrefl
  have s1 : compS.Steps (compD w) (first, 1) [] (seekSep, 2) := by
    have hcell1 : tapeSym (compD w) 1 = .letter GBD.g := by
      rw [hy]
      exact tapeSym_cons_one _ _
    have hη : compS.η first (tapeSym (compD w) 1) = some (seekSep, true, []) := by
      rw [hcell1, compS_η_first_letter, if_pos rfl]
    have hrefl : compS.Steps (compD w) (seekSep, 2) [] (seekSep, 2) := Steps.refl _
    simpa using Steps.head hη hrefl
  have s2 : compS.Steps (compD w) (seekSep, 2) [] (seekSep, 2 + dT.length) := by
    have h := steps_scan (T := compS) (w := compD w) (q := seekSep) (em := fun _ => []) dT 2
      (fun k hk => by
        rw [show 2 + k = k + 2 by omega, hy,
          tapeSym_cons_succ _ _ k (by
            simp only [List.length_append, List.length_cons, List.length_nil,
              List.length_map]
            omega)]
        congr 1
        rw [List.getElem_append_left (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega)]
        rw [List.getElem_append_left hk])
      (fun a ha => by
        rw [compS_η_seekSep_letter, if_neg (hdT_ne_sep a ha)]
        rfl)
    have hnil : (dT.flatMap fun _ => ([] : List GBD)) = [] := by simp
    rw [hnil] at h
    exact h
  have s3 : compS.Steps (compD w) (seekSep, 2 + dT.length) []
      (copier, 3 + dT.length) := by
    have hcellsep : tapeSym (compD w) (2 + dT.length) = .letter GBD.sep := by
      rw [show 2 + dT.length = dT.length + 2 by omega, hy,
        tapeSym_cons_succ _ _ dT.length (by
          simp only [List.length_append, List.length_cons, List.length_nil,
            List.length_map]
          omega)]
      congr 1
      rw [List.getElem_append_left (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega)]
      rw [List.getElem_append_right (le_refl _)]
      simp
    have hη : compS.η seekSep (tapeSym (compD w) (2 + dT.length))
        = some (copier, true, []) := by
      rw [hcellsep, compS_η_seekSep_letter, if_pos rfl]
    have hrefl : compS.Steps (compD w) (copier, moveDir (2 + dT.length) true) []
        (copier, moveDir (2 + dT.length) true) := Steps.refl _
    have h := Steps.head hη hrefl
    have hmv : moveDir (2 + dT.length) true = 3 + dT.length := by
      rw [moveDir_true]
      omega
    rw [hmv] at h
    simpa using h
  have s4 : compS.Steps (compD w) (copier, 3 + dT.length) (w.map relStep)
      (copier, 3 + dT.length + (w.map relStep).length) := by
    have h := steps_scan (T := compS) (w := compD w) (q := copier) (em := fun a => [a])
      (w.map relStep) (3 + dT.length)
      (fun k hk => by
        rw [show 3 + dT.length + k = (dT.length + 1 + k) + 2 by omega, hy,
          tapeSym_cons_succ _ _ (dT.length + 1 + k) (by
            simp only [List.length_append, List.length_cons, List.length_nil,
              List.length_map] at hk ⊢
            omega)]
        congr 1
        rw [List.getElem_append_right (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega)]
        congr 1
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega)
      (fun a _ => compS_η_copier_letter a)
    have hflat : ((w.map relStep).flatMap fun a => ([a] : List GBD)) = w.map relStep := by
      simp
    rw [hflat] at h
    exact h
  have hsteps : compS.Steps (compD w) (init, 0) (w.map relStep)
      (copier, 3 + dT.length + (w.map relStep).length) := by
    have h := (((s0.trans s1).trans s2).trans s3).trans s4
    simpa using h
  refine ⟨_, hsteps, ?_, trivial⟩
  show compS.η copier
      (tapeSym (compD w) (3 + dT.length + (w.map relStep).length)) = none
  rw [tapeSym_ge (compD w) _ (by
    simp only [List.length_map]
    omega), compS_η_rmark]

/-! ## `F_{≥0}` and its non-membership in WRP -/

/-- **The map `F_{≥0}`** (from the proof of `thm:wrp-strict-below-logspace`,
paper.tex Appendix A.3), landing in the block-2 alphabet: the
verbatim copy of `w` when every prefix height is `≥ 0`, and `ε` otherwise. -/
def Fge0 : List Step → Option (List GBD) := fun w =>
  some (if ∀ i, i < w.length → 0 ≤ height w i then w.map relStep else [])

/-- `S ∘ D = F_{≥0}`: on `D(w)`, the machine `S` computes exactly the value of
`F_{≥0}` at `w`. -/
theorem compS_computes_compD (w : List Step) :
    compS.Computes (compD w)
      (if ∀ i, i < w.length → 0 ≤ height w i then w.map relStep else []) := by
  by_cases hw : ∀ i, i < w.length → 0 ≤ height w i
  · rw [if_pos hw]
    exact compS_computes_of_mem w hw
  · rw [if_neg hw]
    exact compS_computes_of_not_mem w hw

/-- The nonempty-`Lnn` words: the nonempty-output preimage of `F_{≥0}`. -/
def LnnPos : Set (List Step) := {w | w ∈ Lnn ∧ w ≠ []}

/-- **`Lnn \ {ε}` is not regular** — the same `U^p D^q U` pigeonhole as
`not_regular_Lnn` (all witnesses are nonempty). -/
theorem not_regular_LnnPos : ¬ IsRegularLang LnnPos := by
  rintro ⟨A, hA⟩
  have := A.finQ
  have := A.decEqQ
  let runU : ℕ → A.Q := fun k => (List.replicate k U).foldl A.delta A.q0
  obtain ⟨p, q, hpq, hcol⟩ : ∃ p q, p < q ∧ runU p = runU q := by
    have hcard : (Finset.univ : Finset A.Q).card
        < (Finset.range (Fintype.card A.Q + 1)).card := by simp
    obtain ⟨i, _, j, _, hij, he⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
        (fun a _ => Finset.mem_univ (runU a))
    rcases Nat.lt_or_ge i j with h | h
    · exact ⟨i, j, h, he⟩
    · exact ⟨j, i, lt_of_le_of_ne h hij.symm, he.symm⟩
  have hfold : ∀ k, (wit k q).foldl A.delta A.q0
      = (List.replicate q D ++ [U]).foldl A.delta (runU k) := by
    intro k; rw [wit, List.foldl_append]
  have hrun_eq : (wit p q).foldl A.delta A.q0 = (wit q q).foldl A.delta A.q0 := by
    rw [hfold, hfold, hcol]
  have hacc_iff : wit p q ∈ LnnPos ↔ wit q q ∈ LnnPos := by
    rw [← hA]
    show A.accepts _ ↔ A.accepts _
    unfold DFA'.accepts
    rw [hrun_eq]
  have h1 : wit q q ∈ LnnPos := by
    refine ⟨wit_qq_mem_Lnn q, ?_⟩
    apply List.ne_nil_of_length_pos
    rw [wit_length]
    omega
  have h2 : wit p q ∉ LnnPos := fun h => wit_pq_not_mem_Lnn p q hpq h.1
  exact h2 (hacc_iff.mpr h1)

/-- **`F_{≥0}` is not a WRP map**: its nonempty-output preimage is
`Lnn \ {ε}`, which is not regular, contradicting
`lem:wrp-nonempty-regular` (`wrp_nonempty_preimage_regular`). -/
theorem Fge0_not_isWRP : ¬ WRP.IsWRP Fge0 := by
  intro h
  have hreg := WRPNonemptyRegular.wrp_nonempty_preimage_regular Fge0 h
  have hset : {w : List Step | ∃ out, Fge0 w = some out ∧ out ≠ []} = LnnPos := by
    ext w
    simp only [Fge0, Option.some.injEq, Set.mem_ofPred_eq, LnnPos]
    constructor
    · rintro ⟨out, rfl, hne⟩
      by_cases hw : ∀ i, i < w.length → 0 ≤ height w i
      · refine ⟨hw, ?_⟩
        rw [if_pos hw] at hne
        intro hnil
        exact hne (by rw [hnil]; rfl)
      · rw [if_neg hw] at hne
        exact absurd rfl hne
    · rintro ⟨hmem, hne⟩
      refine ⟨w.map relStep, ?_, by simpa using hne⟩
      rw [if_pos (show ∀ i, i < w.length → 0 ≤ height w i from hmem)]
  rw [hset] at hreg
  exact not_regular_LnnPos hreg

/-! ## The packaged paper theorem -/

/-- **`thm:wrp-not-closed`, Moreover clause (paper.tex,
proof in Appendix A.4).**  The same witness `D` and regular `K` as claim 1
(`wrp_not_closed_preimage_comp`), together with a deterministic 2DFT `S`
whose input head moves only from left to right, such that the composite
`S ∘ D` — any partial function `SD` with `SD w = out` iff `S` accepts `D(w)`
with output `out` — is not a WRP map.  Consequently `WRP` is not closed under
composition (the paper observes `S ∈ WRP` via Theorem `thm:eh` and
`prop:conservative`; `thm:eh` is cited background). -/
theorem wrp_not_closed_composition :
    ∃ (Dm : List Step → Option (List GBD)) (K : Set (List GBD)) (S : TwoDFT GBD GBD),
      WRP.IsWRP Dm ∧ IsRegularLang K ∧
      ¬ IsRegularLang {w | ∃ out, Dm w = some out ∧ out ∈ K} ∧
      S.LeftToRight ∧
      ∀ SD : List Step → Option (List GBD),
        (∀ w out, SD w = some out ↔ ∃ y, Dm w = some y ∧ S.Computes y out) →
        ¬ WRP.IsWRP SD := by
  refine ⟨fun w => some (compD w), compK, compS, compD_isWRP, compK_isRegular, ?_,
    compS_leftToRight, ?_⟩
  · rw [preimage_compK_eq_Lnn]
    exact not_regular_Lnn
  · intro SD hSD hWRP
    have hEq : SD = Fge0 := by
      funext w
      have hval := compS_computes_compD w
      have hiff := hSD w
        (if ∀ i, i < w.length → 0 ≤ height w i then w.map relStep else [])
      rw [show Fge0 w = some (if ∀ i, i < w.length → 0 ≤ height w i
          then w.map relStep else []) from rfl]
      rw [(hiff.mpr ⟨compD w, rfl, hval⟩ : SD w = _)]
    exact Fge0_not_isWRP (hEq ▸ hWRP)

end WRPComp
