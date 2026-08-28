/-
# The §7 profile discharge, general arity — stage 0: the pinned interfaces

The GA build order starts by PINNING the
semantic interfaces every later milestone must agree against:

* `selAtomsGA` / `mem_selAtomsGA` — the selected-atom `Finset` of `W_n` over all
  copies and tuples (`Sigma.eta` replaces the arity-1 `atom_eq` machinery);
* `exists_isOutput_slice_GA` — output existence on the slice for ANY valid
  presentation (no arity hypothesis, no budget): sort the selected atoms by `≺`;
* `atom_countP_eq_sigmaSum` — atom-list counts as `Σ copies, Σ tuples` double sums
  (the GA replacement of the arity-1 `SliceBridge` z/coord machinery, which is
  dropped, not mirrored);
* `fasCountGA` / `tailUCountGA` — THE pinned count shapes (semantic, `C`-free), their
  domain-gated forms `gatedFasCountGA` / `gatedTailUCountGA` (GA-7's agreement
  targets), and the fas/tailU partition;
* `fas_eq_firstAscent_out_GA` — the semantic bridge: any output's `firstAscent` and
  `tailU` equal the pinned counts;
* `hbud_of_hgrow` — THE pinned budget shape: `hPT` + `hgrow` supply, at every
  in-domain slice, exactly the per-copy `Nodup`-list bound that `one_cluster` (and
  everything built on it) consumes.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`): pure finite combinatorics.
-/
import RequestProject.SliceProfileDischarge
import RequestProject.SliceGrowthCollapse

namespace SliceProfileDischargeGA

open WRP Step
open scoped Classical

/-! ## Stage 0.2: the selected-atom Finset -/

/-- The selected atoms of `W_n`, over all copies and all valid tuples. -/
noncomputable def selAtomsGA (P : WRP.Presentation Step Step) (n : ℕ) :
    Finset P.toPoly.Atom :=
  ((Finset.univ : Finset (Fin P.toPoly.K)).sigma (fun c =>
    Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
      Finset.range (wrappedFlat n).length))).filter
    (fun a => P.toPoly.selectedAtom (wrappedFlat n) a)

theorem mem_selAtomsGA (P : WRP.Presentation Step Step) (n : ℕ) (a : P.toPoly.Atom) :
    a ∈ selAtomsGA P n ↔ P.toPoly.selectedAtom (wrappedFlat n) a := by
  rw [selAtomsGA, Finset.mem_filter]
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

/-! ## Stage 0.3: output existence on the slice (no arity hypothesis) -/

/-- **Output existence on the slice, general arity**: sort the (finite) selected
atoms by `≺` (a strict total order on selected atoms by `hV`) and read the labels. -/
theorem exists_isOutput_slice_GA (P : WRP.Presentation Step Step) (hV : P.Valid)
    (n : ℕ) :
    ∃ out, P.IsOutput (wrappedFlat n) out := by
  set L := (selAtomsGA P n).toList with hLdef
  have hLnd : L.Nodup := Finset.nodup_toList _
  have hLmem : ∀ a, a ∈ L ↔ P.toPoly.selectedAtom (wrappedFlat n) a := by
    intro a
    rw [hLdef, Finset.mem_toList, mem_selAtomsGA]
  obtain ⟨sorted, hsnd, hsmem, hspair⟩ :=
    SliceProfileDischarge.exists_sorted_of_nodup (P.wrpOrd (wrappedFlat n)) L.length L
      (le_refl _) hLnd
      (fun a ha b hb => hV.trichot _ a b ((hLmem a).mp ha) ((hLmem b).mp hb))
      (fun a ha b hb c hc => hV.trans _ a b c ((hLmem a).mp ha) ((hLmem b).mp hb)
        ((hLmem c).mp hc))
  refine ⟨sorted.map (P.toPoly.labelOf (wrappedFlat n)), sorted, hsnd, ?_, hspair, rfl⟩
  intro a
  rw [hsmem, hLmem]

/-! ## Stage 0.4: atom counts as sigma double sums -/

/-- **Counting bridge**: a `countP` over any `Nodup` enumeration of the selected
atoms is the `Σ copies, Σ tuples` double sum of its indicator. -/
theorem atom_countP_eq_sigmaSum (P : WRP.Presentation Step Step) (n : ℕ)
    (atoms : List P.toPoly.Atom) (hnd : atoms.Nodup)
    (hmem : ∀ a, a ∈ atoms ↔ P.toPoly.selectedAtom (wrappedFlat n) a)
    (Q : P.toPoly.Atom → Prop) :
    atoms.countP (fun a => decide (Q a))
      = ∑ c : Fin P.toPoly.K,
          ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
            Finset.range (wrappedFlat n).length),
          if P.toPoly.sel c (wrappedFlat n) ī ∧ Q ⟨c, ī⟩ then 1 else 0 := by
  rw [List.countP_eq_length_filter]
  have hfn : (atoms.filter (fun a => decide (Q a))).Nodup := hnd.filter _
  rw [← List.toFinset_card_of_nodup hfn]
  have hset : (atoms.filter (fun a => decide (Q a))).toFinset
      = ((Finset.univ : Finset (Fin P.toPoly.K)).sigma (fun c =>
          Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
            Finset.range (wrappedFlat n).length))).filter
        (fun a => P.toPoly.selectedAtom (wrappedFlat n) a ∧ Q a) := by
    ext a
    rw [List.mem_toFinset, List.mem_filter, hmem, decide_eq_true_eq, Finset.mem_filter,
      Finset.mem_sigma]
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
  have hvalid : P.toPoly.validAtom (wrappedFlat n) ⟨c, ī⟩ := by
    intro i
    have := Fintype.mem_piFinset.mp hī i
    rwa [Finset.mem_range] at this
  by_cases hsel : P.toPoly.sel c (wrappedFlat n) ī
  · by_cases hQ : Q ⟨c, ī⟩
    · rw [if_pos ⟨⟨hvalid, hsel⟩, hQ⟩, if_pos ⟨hsel, hQ⟩]
    · rw [if_neg (fun h => hQ h.2), if_neg (fun h => hQ h.2)]
  · rw [if_neg (fun h => hsel h.1.2), if_neg (fun h => hsel h.1)]

/-! ## Stage 0.5: the pinned count shapes -/

/-- **`fasCountGA`** — the first-ascent count, general arity: selected `U`-atoms that
`≺`-precede every selected `D`-atom, as a `Σ copies, Σ tuples` double sum.  THE pinned
shape GA-7 must agree against. -/
noncomputable def fasCountGA (P : WRP.Presentation Step Step) (n : ℕ) : ℕ :=
  ∑ c : Fin P.toPoly.K,
    ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
      Finset.range (wrappedFlat n).length),
    if (P.toPoly.sel c (wrappedFlat n) ī
        ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
        ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
            (P.toPoly.labelOf (wrappedFlat n) b = U
              ∨ P.wrpOrd (wrappedFlat n) ⟨c, ī⟩ b)) then 1 else 0

/-- **`tailUCountGA`** — the complementary `U`-count. -/
noncomputable def tailUCountGA (P : WRP.Presentation Step Step) (n : ℕ) : ℕ :=
  ∑ c : Fin P.toPoly.K,
    ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
      Finset.range (wrappedFlat n).length),
    if (P.toPoly.sel c (wrappedFlat n) ī
        ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
        ∧ ¬ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
            (P.toPoly.labelOf (wrappedFlat n) b = U
              ∨ P.wrpOrd (wrappedFlat n) ⟨c, ī⟩ b)) then 1 else 0

/-- The domain-gated first-ascent count — GA-7's agreement target. -/
noncomputable def gatedFasCountGA (P : WRP.Presentation Step Step) (n : ℕ) : ℕ :=
  if P.toPoly.domain (wrappedFlat n) then fasCountGA P n else 0

/-- The domain-gated tail count — GA-7's agreement target. -/
noncomputable def gatedTailUCountGA (P : WRP.Presentation Step Step) (n : ℕ) : ℕ :=
  if P.toPoly.domain (wrappedFlat n) then tailUCountGA P n else 0

/-- **The fas/tailU partition, general arity.** -/
theorem totalSelectedU_eq_fas_add_tail_GA (P : WRP.Presentation Step Step) (n : ℕ) :
    (∑ c : Fin P.toPoly.K,
      ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
        Finset.range (wrappedFlat n).length),
      if (P.toPoly.sel c (wrappedFlat n) ī
          ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U) then 1 else 0)
      = fasCountGA P n + tailUCountGA P n := by
  rw [fasCountGA, tailUCountGA, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ī _ => ?_)
  by_cases h1 : P.toPoly.sel c (wrappedFlat n) ī
      ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
  · by_cases h2 : ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
        (P.toPoly.labelOf (wrappedFlat n) b = U ∨ P.wrpOrd (wrappedFlat n) ⟨c, ī⟩ b)
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2, h2⟩, if_neg (fun h => h.2.2 h2), add_zero]
    · rw [if_pos h1, if_neg (fun h => h2 h.2.2), if_pos ⟨h1.1, h1.2, h2⟩, zero_add]
  · rw [if_neg h1, if_neg (fun h => h1 ⟨h.1, h.2.1⟩), if_neg (fun h => h1 ⟨h.1, h.2.1⟩),
      add_zero]

/-! ## Stage 0.6: the semantic bridge -/

/-- **The semantic bridge, general arity**: any output's `firstAscent` and `tailU`
equal the pinned counts. -/
theorem fas_eq_firstAscent_out_GA (P : WRP.Presentation Step Step) (hV : P.Valid)
    (n : ℕ) (out : List Step) (hout : P.IsOutput (wrappedFlat n) out) :
    firstAscent out = fasCountGA P n ∧ tailU out = tailUCountGA P n := by
  obtain ⟨atoms, hnd, hmem, hfa⟩ := SliceOutput.firstAscent_eq_countP P hV
    (wrappedFlat n) out hout
  -- the fas predicate, in `decide`-form
  have hfa' : firstAscent out = fasCountGA P n := by
    rw [hfa]
    have hcongr : atoms.countP (fun a => decide (P.toPoly.labelOf (wrappedFlat n) a = U)
          && atoms.all (fun b => decide (P.toPoly.labelOf (wrappedFlat n) b = U)
            || decide (P.wrpOrd (wrappedFlat n) a b)))
        = atoms.countP (fun a => decide (P.toPoly.labelOf (wrappedFlat n) a = U
            ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
              (P.toPoly.labelOf (wrappedFlat n) b = U
                ∨ P.wrpOrd (wrappedFlat n) a b))) := by
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
    rw [hcongr, fasCountGA]
    refine Eq.trans (List.countP_congr (fun a _ => ?_))
      (Eq.trans (atom_countP_eq_sigmaSum P n atoms hnd hmem
        (fun a => P.toPoly.labelOf (wrappedFlat n) a = U
          ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
            (P.toPoly.labelOf (wrappedFlat n) b = U ∨ P.wrpOrd (wrappedFlat n) a b)))
        (Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
          (fun ī _ => by
            by_cases h : P.toPoly.sel c (wrappedFlat n) ī
                ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
                ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
                  (P.toPoly.labelOf (wrappedFlat n) b = U
                    ∨ P.wrpOrd (wrappedFlat n) ⟨c, ī⟩ b)
            · rw [if_pos h, if_pos h]
            · rw [if_neg h, if_neg h]))))
    simp only [decide_eq_true_eq]
  refine ⟨hfa', ?_⟩
  -- the U-count as the total selected-U sum
  obtain ⟨atoms', hnd', hmem', _, hmap'⟩ := hout
  have hcU : out.count U
      = ∑ c : Fin P.toPoly.K,
          ∑ ī ∈ Fintype.piFinset (fun _ : Fin (P.toPoly.arity c) =>
            Finset.range (wrappedFlat n).length),
          if (P.toPoly.sel c (wrappedFlat n) ī
              ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U) then 1 else 0 := by
    rw [hmap', List.count_eq_countP, List.countP_map]
    have hcongr : atoms'.countP ((fun x => x == U) ∘ P.toPoly.labelOf (wrappedFlat n))
        = atoms'.countP (fun a => decide (P.toPoly.labelOf (wrappedFlat n) a = U)) := by
      refine List.countP_congr (fun a _ => ?_)
      show (P.toPoly.labelOf (wrappedFlat n) a == U) = true ↔ _
      rw [beq_iff_eq, decide_eq_true_eq]
    rw [hcongr]
    refine Eq.trans (List.countP_congr (fun a _ => ?_))
      (Eq.trans (atom_countP_eq_sigmaSum P n atoms' hnd' hmem'
        (fun a => P.toPoly.labelOf (wrappedFlat n) a = U))
        (Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
          (fun ī _ => by
            by_cases h : P.toPoly.sel c (wrappedFlat n) ī
                ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
            · rw [if_pos h, if_pos h]
            · rw [if_neg h, if_neg h]))))
    simp only [decide_eq_true_eq]
  rw [tailU, hcU, hfa', totalSelectedU_eq_fas_add_tail_GA]
  omega

/-! ## Stage 0.7: the pinned budget shape -/

/-- **The budget supplier**: `hPT` + `hgrow` produce, at every in-domain slice,
exactly the per-copy `Nodup`-list bound that `one_cluster` (and everything built on
it) consumes. -/
theorem hbud_of_hgrow (P : WRP.Presentation Step Step) (hV : P.Valid)
    (T : List Step → Option (List Step)) (C : ℕ)
    (hPT : ∀ w out, T w = some out ↔ (P.toPoly.domain w ∧ P.IsOutput w out))
    (hgrow : ∀ n out, T (wrappedFlat n) = some out → out.length ≤ C * (n + 1)) :
    ∀ n, P.toPoly.domain (wrappedFlat n) → ∀ (c : Fin P.toPoly.K)
      (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
      (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
      l.length ≤ C * (n + 1) := by
  intro n hdom c l hnd hsel
  obtain ⟨out, hout⟩ := exists_isOutput_slice_GA P hV n
  have hTout : T (wrappedFlat n) = some out := (hPT _ _).mpr ⟨hdom, hout⟩
  exact SliceGrowthCollapse.one_cluster_hcard_of_output P _ out hout C n
    (hgrow n out hTout) c l hnd hsel

end SliceProfileDischargeGA
