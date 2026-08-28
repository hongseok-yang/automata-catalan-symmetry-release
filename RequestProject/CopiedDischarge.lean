/-
# The fibred discharge interfaces (§9 tower, Stage F.0 — pinned shapes)

The wrapped stage-0 layer (`SliceProfileDischargeGA`) is word-generic in all but
spelling: output existence sorts the selected atoms of ANY word, the counting
bridge only reads `w.length`, and the semantic bridge runs through the already
word-generic `SliceOutput.firstAscent_eq_countP`.  This file provides the
primed (arbitrary-word) layer and its copied-slice readings — fas-only, per
the frozen design (NO tailU twin):

* `selAtoms'` / `exists_isOutput'` / `atom_countP_eq_sigmaSum'`;
* `fasCount'` — THE pinned first-ascent count of an arbitrary word;
* `fas_eq_firstAscent_out'` — any output's `firstAscent` equals the count;
* `fasCountGA_m` / `gatedFasCountGA_m` — the copied-slice readings, with the
  m = 1 regression to the wrapped `fasCountGA`;
* `hbud_of_hgrow_m` — the copied budget supplier, in EXACTLY the shape
  `one_cluster_fibred`/`cells_cover_fibred` consume (`≤ C * (mS + n + 1)`).
-/
import RequestProject.SliceProfileDischargeGA
import RequestProject.InverseZeta

namespace CopiedDischarge

open WRP Step
open scoped Classical

/-! ## The selected-atom Finset of an arbitrary word -/

/-- The selected atoms of `w`, over all copies and all valid tuples. -/
noncomputable def selAtoms' (P : WRP.Presentation Step Step) (w : List Step) :
    Finset P.toPoly.Atom :=
  ((Finset.univ : Finset (Fin P.toPoly.K)).sigma (fun c =>
    Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
      Finset.range w.length))).filter
    (fun a => P.toPoly.selectedAtom w a)

theorem mem_selAtoms' (P : WRP.Presentation Step Step) (w : List Step)
    (a : P.toPoly.Atom) :
    a ∈ selAtoms' P w ↔ P.toPoly.selectedAtom w a := by
  rw [selAtoms', Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    exact h.1 i

/-- **Output existence on an arbitrary word**: sort the (finite) selected
atoms by `≺`. -/
theorem exists_isOutput' (P : WRP.Presentation Step Step) (hV : P.Valid)
    (w : List Step) :
    ∃ out, P.IsOutput w out := by
  set L := (selAtoms' P w).toList with hLdef
  have hLnd : L.Nodup := Finset.nodup_toList _
  have hLmem : ∀ a, a ∈ L ↔ P.toPoly.selectedAtom w a := by
    intro a
    rw [hLdef, Finset.mem_toList, mem_selAtoms']
  obtain ⟨sorted, hsnd, hsmem, hspair⟩ :=
    SliceProfileDischarge.exists_sorted_of_nodup (P.wrpOrd w) L.length L
      (le_refl _) hLnd
      (fun a ha b hb => hV.trichot _ a b ((hLmem a).mp ha) ((hLmem b).mp hb))
      (fun a ha b hb c hc => hV.trans _ a b c ((hLmem a).mp ha) ((hLmem b).mp hb)
        ((hLmem c).mp hc))
  refine ⟨sorted.map (P.toPoly.labelOf w), sorted, hsnd, ?_, hspair, rfl⟩
  intro a
  rw [hsmem, hLmem]

/-! ## The counting bridge -/

/-- **Counting bridge on an arbitrary word**: a `countP` over any `Nodup`
enumeration of the selected atoms is the `Σ copies, Σ tuples` double sum. -/
theorem atom_countP_eq_sigmaSum' (P : WRP.Presentation Step Step) (w : List Step)
    (atoms : List P.toPoly.Atom) (hnd : atoms.Nodup)
    (hmem : ∀ a, a ∈ atoms ↔ P.toPoly.selectedAtom w a)
    (Q : P.toPoly.Atom → Prop) :
    atoms.countP (fun a => decide (Q a))
      = ∑ c : Fin P.toPoly.K,
          ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
            Finset.range w.length),
          if P.toPoly.sel c w ī ∧ Q ⟨c, ī⟩ then 1 else 0 := by
  rw [List.countP_eq_length_filter]
  have hfn : (atoms.filter (fun a => decide (Q a))).Nodup := hnd.filter _
  rw [← List.toFinset_card_of_nodup hfn]
  have hset : (atoms.filter (fun a => decide (Q a))).toFinset
      = ((Finset.univ : Finset (Fin P.toPoly.K)).sigma (fun c =>
          Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
            Finset.range w.length))).filter
        (fun a => P.toPoly.selectedAtom w a ∧ Q a) := by
    ext a
    rw [List.mem_toFinset, List.mem_filter, hmem, decide_eq_true_eq,
      Finset.mem_filter, Finset.mem_sigma]
    constructor
    · rintro ⟨hsel, hQ⟩
      refine ⟨⟨Finset.mem_univ _, ?_⟩, hsel, hQ⟩
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range]
      exact hsel.1 i
    · rintro ⟨_, hsel, hQ⟩
      exact ⟨hsel, hQ⟩
  rw [hset, Finset.card_filter]
  refine (Finset.sum_sigma _ _ _).trans ?_
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun ī hī => ?_))
  have hvalid : P.toPoly.validAtom w ⟨c, ī⟩ := by
    intro i
    have := Fintype.mem_piFinset.mp hī i
    rwa [Finset.mem_range] at this
  by_cases hsel : P.toPoly.sel c w ī
  · by_cases hQ : Q ⟨c, ī⟩
    · rw [if_pos ⟨⟨hvalid, hsel⟩, hQ⟩, if_pos ⟨hsel, hQ⟩]
    · rw [if_neg (fun h => hQ h.2), if_neg (fun h => hQ h.2)]
  · rw [if_neg (fun h => hsel h.1.2), if_neg (fun h => hsel h.1)]

/-! ## The pinned first-ascent count -/

/-- **`fasCount'`** — the first-ascent count of an arbitrary word: selected
`U`-atoms that `≺`-precede every selected `D`-atom. -/
noncomputable def fasCount' (P : WRP.Presentation Step Step) (w : List Step) : ℕ :=
  ∑ c : Fin P.toPoly.K,
    ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
      Finset.range w.length),
    if (P.toPoly.sel c w ī
        ∧ P.toPoly.labelOf w ⟨c, ī⟩ = U
        ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom w b →
            (P.toPoly.labelOf w b = U ∨ P.wrpOrd w ⟨c, ī⟩ b)) then 1 else 0

/-- **The semantic bridge on an arbitrary word** (fas half only): any output's
`firstAscent` equals the pinned count. -/
theorem fas_eq_firstAscent_out' (P : WRP.Presentation Step Step) (hV : P.Valid)
    (w : List Step) (out : List Step) (hout : P.IsOutput w out) :
    firstAscent out = fasCount' P w := by
  obtain ⟨atoms, hnd, hmem, hfa⟩ := SliceOutput.firstAscent_eq_countP P hV w out hout
  rw [hfa]
  have hcongr : atoms.countP (fun a => decide (P.toPoly.labelOf w a = U)
        && atoms.all (fun b => decide (P.toPoly.labelOf w b = U)
          || decide (P.wrpOrd w a b)))
      = atoms.countP (fun a => decide (P.toPoly.labelOf w a = U
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom w b →
            (P.toPoly.labelOf w b = U ∨ P.wrpOrd w a b))) := by
    refine List.countP_congr (fun a _ => ?_)
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, List.all_eq_true]
    constructor
    · rintro ⟨hU, hall⟩
      refine ⟨hU, fun b hb => ?_⟩
      have := hall b ((hmem b).mpr hb)
      rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at this
      exact this
    · rintro ⟨hU, hall⟩
      refine ⟨hU, fun b hb => ?_⟩
      rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact hall b ((hmem b).mp hb)
  rw [hcongr, fasCount']
  refine Eq.trans (List.countP_congr (fun a _ => ?_))
    (Eq.trans (atom_countP_eq_sigmaSum' P w atoms hnd hmem
      (fun a => P.toPoly.labelOf w a = U
        ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom w b →
          (P.toPoly.labelOf w b = U ∨ P.wrpOrd w a b)))
      (Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
        (fun ī _ => by
          by_cases h : P.toPoly.sel c w ī
              ∧ P.toPoly.labelOf w ⟨c, ī⟩ = U
              ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom w b →
                (P.toPoly.labelOf w b = U ∨ P.wrpOrd w ⟨c, ī⟩ b)
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h]))))
  simp only [decide_eq_true_eq]

/-! ## The copied-slice readings -/

/-- The fibred first-ascent count. -/
noncomputable def fasCountGA_m (P : WRP.Presentation Step Step) (mS n : ℕ) : ℕ :=
  fasCount' P (copiedSlice mS n)

/-- The domain-gated fibred first-ascent count — the fibred agreement target. -/
noncomputable def gatedFasCountGA_m (P : WRP.Presentation Step Step)
    (mS n : ℕ) : ℕ :=
  if P.toPoly.domain (copiedSlice mS n) then fasCountGA_m P mS n else 0

/-! ## The fibred budget supplier -/

/-- **The fibred budget supplier**: `hPT` + growth on the copied slices produce,
at every in-domain copied slice, exactly the per-copy `Nodup`-list bound that
`one_cluster_fibred` and `cells_cover_fibred` consume. -/
theorem hbud_of_hgrow_m (P : WRP.Presentation Step Step) (hV : P.Valid)
    (T : List Step → Option (List Step)) (C : ℕ)
    (hPT : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    (hgrow : ∀ mS n out, T (copiedSlice mS n) = some out →
      out.length ≤ C * (mS + n + 1)) :
    ∀ mS n, P.toPoly.domain (copiedSlice mS n) → ∀ (c : Fin P.toPoly.K)
      (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
      (∀ x ∈ l, P.toPoly.selectedAtom (copiedSlice mS n) ⟨c, x⟩) →
      l.length ≤ C * (mS + n + 1) := by
  intro mS n hdom c l hnd hsel
  obtain ⟨out, hout⟩ := exists_isOutput' P hV (copiedSlice mS n)
  have hTout : T (copiedSlice mS n) = some out := (hPT _ _).mpr ⟨hdom, hout⟩
  have h := SliceGrowthCollapse.one_cluster_hcard_of_output P (copiedSlice mS n)
    out hout C (mS + n) (hgrow mS n out hTout) c l hnd hsel
  exact h

end CopiedDischarge
