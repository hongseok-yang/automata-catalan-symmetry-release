/-
# The §7 fas-profile discharge (arity-1): output existence and the semantic bridge

The final assembly of the arity-1 §7 slice theorem discharge.  This file builds the *semantic*
prerequisites of the capstone `wrp_slice_profile_affine_arity1`:

* `exists_sorted_of_nodup` — a generic selection-sort: a finite `Nodup` list carrying a
  strict total order admits a `Pairwise`-sorted reordering (via repeated min-extraction
  with `SliceDstar.exists_min_of_list`).
* `exists_isOutput_slice` — every valid arity-1 presentation has an output on `W_n`
  (sort the selected atoms of `W_n` by `≺` and read off their labels).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`): pure finite combinatorics.
-/
import RequestProject.SliceDstar
import RequestProject.SliceOutput

namespace SliceProfileDischarge

open WRP Step SliceDstar
open scoped Classical

/-- **Generic min-extraction sort.**  A finite `Nodup` list whose elements carry a
trichotomous, transitive relation `R` admits a `Pairwise R` reordering with the same
membership.  Proved by bounded induction on the length, repeatedly pulling the `R`-minimum
(`exists_min_of_list`) to the front and recursing on the erasure. -/
theorem exists_sorted_of_nodup {α : Type*} (R : α → α → Prop) :
    ∀ (N : ℕ) (l : List α), l.length ≤ N → l.Nodup →
      (∀ a ∈ l, ∀ b ∈ l, R a b ∨ a = b ∨ R b a) →
      (∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, R a b → R b c → R a c) →
      ∃ sorted : List α, sorted.Nodup ∧ (∀ a, a ∈ sorted ↔ a ∈ l) ∧ sorted.Pairwise R := by
  intro N
  induction N with
  | zero =>
      intro l hl _ _ _
      have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
      exact ⟨[], by simp, by simp [hnil], by simp⟩
  | succ N ih =>
      intro l hl hnd htri htr
      by_cases hl0 : l = []
      · exact ⟨[], by simp, by simp [hl0], by simp⟩
      · obtain ⟨m, hmmem, hmmin⟩ := exists_min_of_list R l hl0 htri htr
        have hlerase : (l.erase m).length ≤ N := by
          rw [List.length_erase_of_mem hmmem]; omega
        obtain ⟨sorted', hnd', hmem', hpair'⟩ := ih (l.erase m) hlerase (hnd.erase m)
          (fun a ha b hb => htri a (List.mem_of_mem_erase ha) b (List.mem_of_mem_erase hb))
          (fun a ha b hb c hc => htr a (List.mem_of_mem_erase ha) b (List.mem_of_mem_erase hb)
            c (List.mem_of_mem_erase hc))
        refine ⟨m :: sorted', ?_, ?_, ?_⟩
        · rw [List.nodup_cons]
          refine ⟨?_, hnd'⟩
          rw [hmem']
          intro hc; exact (List.Nodup.mem_erase_iff hnd).mp hc |>.1 rfl
        · intro a
          rw [List.mem_cons, hmem']
          constructor
          · rintro (rfl | ha)
            · exact hmmem
            · exact List.mem_of_mem_erase ha
          · intro ha
            by_cases h : a = m
            · exact Or.inl h
            · exact Or.inr ((List.Nodup.mem_erase_iff hnd).mpr ⟨h, ha⟩)
        · rw [List.pairwise_cons]
          refine ⟨fun b hb => ?_, hpair'⟩
          rw [hmem'] at hb
          have hbl : b ∈ l := List.mem_of_mem_erase hb
          have hbne : b ≠ m := ((List.Nodup.mem_erase_iff hnd).mp hb).1
          rcases hmmin b hbl with heq | hr
          · exact absurd heq.symm hbne
          · exact hr

/-- The list of all selected atoms of `W_n` (arity-1, enumerated by `(copy, position)`),
the all-labels analogue of `SliceDstar.selDList`. -/
noncomputable def selList (P : WRP.Presentation Step Step) (n : ℕ) : List P.toPoly.Atom :=
  ((List.finRange P.toPoly.K).flatMap (fun c =>
    (List.range (wrappedFlat n).length).map (fun p => (⟨c, fun _ => p⟩ : P.toPoly.Atom)))).filter
    (fun a => decide (P.toPoly.selectedAtom (wrappedFlat n) a))

theorem mem_selList (P : WRP.Presentation Step Step) (harity : ∀ c, P.toPoly.arity c = 1)
    (n : ℕ) (a : P.toPoly.Atom) :
    a ∈ selList P n ↔ P.toPoly.selectedAtom (wrappedFlat n) a := by
  rw [selList, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hsel⟩; exact hsel
  · intro hsel
    refine ⟨?_, hsel⟩
    rw [List.mem_flatMap]
    refine ⟨a.1, List.mem_finRange _, ?_⟩
    rw [List.mem_map]
    refine ⟨a.2 (SliceBridge.z P.toPoly harity a.1), ?_,
      (SliceBridge.atom_eq P.toPoly harity a).symm⟩
    rw [List.mem_range]
    exact (SliceBridge.valid_iff P.toPoly harity a.1 _ (wrappedFlat n)).mp
      (by rw [← SliceBridge.atom_eq P.toPoly harity a]; exact hsel.1)

/-- **Output existence on the slice.**  Every valid arity-1 presentation has an output on
`W_n`: sort the (finite) selected atoms by `≺` (a strict total order on selected atoms by
`hV`) and map to their labels. -/
theorem exists_isOutput_slice (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity : ∀ c, P.toPoly.arity c = 1) (n : ℕ) :
    ∃ out, P.IsOutput (wrappedFlat n) out := by
  set L := (selList P n).dedup with hLdef
  have hLnd : L.Nodup := List.nodup_dedup _
  have hLmem : ∀ a, a ∈ L ↔ P.toPoly.selectedAtom (wrappedFlat n) a := by
    intro a; rw [hLdef, List.mem_dedup, mem_selList P harity n]
  obtain ⟨sorted, hsnd, hsmem, hspair⟩ :=
    exists_sorted_of_nodup (P.wrpOrd (wrappedFlat n)) L.length L (le_refl _) hLnd
      (fun a ha b hb => hV.trichot _ a b ((hLmem a).mp ha) ((hLmem b).mp hb))
      (fun a ha b hb c hc => hV.trans _ a b c ((hLmem a).mp ha) ((hLmem b).mp hb) ((hLmem c).mp hc))
  refine ⟨sorted.map (P.toPoly.labelOf (wrappedFlat n)), sorted, hsnd, ?_, hspair, rfl⟩
  intro a; rw [hsmem, hLmem]

/-- **`fasCount`** — the first-ascent count as a `(copy, position)` double sum: selected
`U`-atoms that `≺`-precede every selected `D`-atom.  This is exactly the RHS of
`SliceBridge.firstAscent_eq_selectedCount`, so `firstAscent out = fasCount P n` for any
output `out` (the `D`-collapse to `d*` is deferred to the affineness proof). -/
noncomputable def fasCount (P : WRP.Presentation Step Step) (n : ℕ) : ℕ :=
  ∑ c : Fin P.toPoly.K, ∑ p ∈ Finset.range (wrappedFlat n).length,
    if (P.toPoly.sel c (wrappedFlat n) (fun _ => p)
        ∧ P.toPoly.label c (wrappedFlat n) (fun _ => p) = U
        ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
            (P.toPoly.label b.1 (wrappedFlat n) b.2 = U
              ∨ P.wrpOrd (wrappedFlat n) ⟨c, fun _ => p⟩ b)) then 1 else 0

/-- **`tailUCount`** — the dual count: selected `U`-atoms that do NOT precede every selected
`D`-atom (equivalently `d* ≺ a`).  Counted directly (the complement cell), so it is a
genuine `card` with non-negative slopes. -/
noncomputable def tailUCount (P : WRP.Presentation Step Step) (n : ℕ) : ℕ :=
  ∑ c : Fin P.toPoly.K, ∑ p ∈ Finset.range (wrappedFlat n).length,
    if (P.toPoly.sel c (wrappedFlat n) (fun _ => p)
        ∧ P.toPoly.label c (wrappedFlat n) (fun _ => p) = U
        ∧ ¬ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
            (P.toPoly.label b.1 (wrappedFlat n) b.2 = U
              ∨ P.wrpOrd (wrappedFlat n) ⟨c, fun _ => p⟩ b)) then 1 else 0

/-- **The fas/tailU partition.**  `totalSelectedU = fasCount + tailUCount` (every selected
`U`-atom either precedes every selected `D`-atom or not). -/
theorem totalSelectedU_eq_fas_add_tail (P : WRP.Presentation Step Step) (n : ℕ) :
    (∑ c : Fin P.toPoly.K, ∑ p ∈ Finset.range (wrappedFlat n).length,
      if (P.toPoly.sel c (wrappedFlat n) (fun _ => p)
          ∧ P.toPoly.label c (wrappedFlat n) (fun _ => p) = U) then 1 else 0)
      = fasCount P n + tailUCount P n := by
  rw [fasCount, tailUCount, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h1 : P.toPoly.sel c (wrappedFlat n) (fun _ => p)
      ∧ P.toPoly.label c (wrappedFlat n) (fun _ => p) = U
  · by_cases h2 : ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
        (P.toPoly.label b.1 (wrappedFlat n) b.2 = U ∨ P.wrpOrd (wrappedFlat n) ⟨c, fun _ => p⟩ b)
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2, h2⟩, if_neg (fun h => h.2.2 h2), add_zero]
    · rw [if_pos h1, if_neg (fun h => h2 h.2.2), if_pos ⟨h1.1, h1.2, h2⟩, zero_add]
  · rw [if_neg h1, if_neg (fun h => h1 ⟨h.1, h.2.1⟩), if_neg (fun h => h1 ⟨h.1, h.2.1⟩), add_zero]

/-- **The semantic bridge** (lemma #12).  For any output of `W_n`, `firstAscent` and
`tailU` equal the counting definitions `fasCount`/`tailUCount`. -/
theorem fas_eq_firstAscent_out (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity : ∀ c, P.toPoly.arity c = 1) (n : ℕ) (out : List Step)
    (hout : P.IsOutput (wrappedFlat n) out) :
    firstAscent out = fasCount P n ∧ tailU out = tailUCount P n := by
  have hfa : firstAscent out = fasCount P n :=
    SliceBridge.firstAscent_eq_selectedCount P hV harity (wrappedFlat n) out hout
  refine ⟨hfa, ?_⟩
  obtain ⟨atoms, hnd, hmem, _, hmap⟩ := hout
  have hcU : out.count U = ∑ c : Fin P.toPoly.K, ∑ p ∈ Finset.range (wrappedFlat n).length,
      if (P.toPoly.sel c (wrappedFlat n) (fun _ => p)
          ∧ P.toPoly.label c (wrappedFlat n) (fun _ => p) = U) then 1 else 0 :=
    SliceBridge.count_U_eq_totalSelectedU P.toPoly harity (wrappedFlat n) out atoms hnd hmem hmap
  rw [tailU, hcU, hfa, totalSelectedU_eq_fas_add_tail]
  omega

end SliceProfileDischarge
