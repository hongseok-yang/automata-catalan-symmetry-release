/-
# The §7 fas-profile discharge (arity-1): the sorting prerequisite

`exists_sorted_of_nodup` — a generic selection sort: a finite `Nodup` list carrying a strict total
order admits a `Pairwise`-sorted reordering, via repeated min-extraction with
`SliceDstar.exists_min_of_list`.  It is what turns the selected atoms of a slice, ordered by `≺`,
into the output word.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`): pure finite combinatorics.
-/import RequestProject.SliceDstar

namespace SliceProfileDischarge

open SliceDstar
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

end SliceProfileDischarge
