/-
# Output semantics on the slice: `firstAscent` / `tailU` as selected-atom counts

The WRP output `out = (selected atoms, sorted by `≺`).map labelOf`.  The discharge needs
`firstAscent out` and `tailU out` as counts over the selected atoms, so they can be shown
affine-on-residues.  The combinatorial core is a pure list fact: in a list that is
`Pairwise R` for a strict (asymmetric) order `R`, the leading run of `p`-elements has the
same length as the count of `p`-elements that `R`-precede **every** non-`p` element
(`takeWhile_length_eq_countP`).  Applied with `R = wrpOrd` and `p = (label = U)` this says
`firstAscent out = #{ selected U-atoms a : a ≺ every selected D-atom }` — exactly the `fas`
the counting machinery computes.

This file builds the list core first.  Axiom-clean.
-/
import RequestProject.WRP
import RequestProject.DyckPath

namespace SliceOutput

open WRP Step
open scoped Classical

/-- **The sorted-list leading-run count.**  For an `r`-`Pairwise` list with `r`
asymmetric on its elements, the leading run of `p`-elements has length equal to the
count of elements that are `p` and for which every list element is either `p` or
`r`-after them (i.e. that `r`-precede every non-`p` element). -/
theorem takeWhile_length_eq_countP {α : Type*} (r : α → α → Bool) (p : α → Bool) :
    ∀ (l : List α), l.Pairwise (fun a b => r a b = true) →
      (∀ a ∈ l, ∀ b ∈ l, r a b = true → r b a = false) →
      (l.takeWhile p).length = l.countP (fun a => p a && l.all (fun b => p b || r a b)) := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons x xs ih =>
      intro hpw hasym
      rw [List.pairwise_cons] at hpw
      obtain ⟨hxhead, hpwxs⟩ := hpw
      have hxs : ∀ a ∈ xs, r x a = true := fun a ha => hxhead a ha
      have ihxs := ih hpwxs (fun a ha b hb => hasym a (List.mem_cons_of_mem _ ha)
        b (List.mem_cons_of_mem _ hb))
      by_cases hpx : p x = true
      · rw [List.takeWhile_cons_of_pos hpx, List.length_cons, List.countP_cons]
        have hcondx : (p x && (x :: xs).all (fun b => p b || r x b)) = true := by
          rw [Bool.and_eq_true]
          refine ⟨hpx, List.all_eq_true.mpr (fun b hb => ?_)⟩
          rcases List.mem_cons.mp hb with rfl | hb'
          · simp [hpx]
          · simp [hxs b hb']
        have hcong : xs.countP (fun a => p a && (x :: xs).all (fun b => p b || r a b))
            = xs.countP (fun a => p a && xs.all (fun b => p b || r a b)) := by
          refine List.countP_congr (fun a ha => ?_)
          simp only [List.all_cons]
          rw [show (p x || r a x) = true from by simp [hpx]]
          simp
        rw [hcong, ← ihxs, hcondx]
        simp
      · simp only [Bool.not_eq_true] at hpx
        rw [List.takeWhile_cons_of_neg (by simp [hpx]), List.length_nil, List.countP_cons]
        have hcondx : (p x && (x :: xs).all (fun b => p b || r x b)) = false := by
          simp [hpx]
        have hzero : xs.countP (fun a => p a && (x :: xs).all (fun b => p b || r a b)) = 0 := by
          rw [List.countP_eq_zero]
          intro a ha
          have hax : r a x = false := hasym x (by simp) a
            (List.mem_cons_of_mem _ ha) (hxs a ha)
          simp [List.all_cons, hpx, hax]
        rw [hzero, hcondx]
        simp

/-- **`firstAscent` of a WRP output as a selected-atom count.**  From `IsOutput` (the
output is the `≺`-sorted selected atoms' labels) and `Valid` (so `≺` is asymmetric on
selected atoms), `firstAscent out` counts the selected atoms that are `U`-labelled and
`≺`-precede every selected `D`-atom. -/
theorem firstAscent_eq_countP {Alpha : Type*} (P : Presentation Alpha Step) (hV : P.Valid)
    (w : List Alpha) (out : List Step) (hout : P.IsOutput w out) :
    ∃ atoms : List P.toPoly.Atom, atoms.Nodup ∧ (∀ a, a ∈ atoms ↔ P.toPoly.selectedAtom w a) ∧
      firstAscent out = atoms.countP (fun a => decide (P.toPoly.labelOf w a = U) &&
        atoms.all (fun b => decide (P.toPoly.labelOf w b = U) || decide (P.wrpOrd w a b))) := by
  obtain ⟨atoms, hnd, hmem, hpair, hmap⟩ := hout
  refine ⟨atoms, hnd, hmem, ?_⟩
  have hasym : ∀ a ∈ atoms, ∀ b ∈ atoms,
      decide (P.wrpOrd w a b) = true → decide (P.wrpOrd w b a) = false := by
    intro a ha b hb hab
    rw [decide_eq_true_eq] at hab
    rw [decide_eq_false_iff_not]
    intro hba
    exact hV.irrefl w a ((hmem a).mp ha)
      (hV.trans w a b a ((hmem a).mp ha) ((hmem b).mp hb) ((hmem a).mp ha) hab hba)
  have hpair' : atoms.Pairwise (fun a b => decide (P.wrpOrd w a b) = true) :=
    hpair.imp (fun {a b} h => decide_eq_true_eq.mpr h)
  unfold firstAscent
  rw [hmap, List.takeWhile_map, List.length_map]
  simp only [Function.comp_def]
  exact takeWhile_length_eq_countP (fun a b => decide (P.wrpOrd w a b))
    (fun a => decide (P.toPoly.labelOf w a = U)) atoms hpair' hasym

/-- **The ∀-collapse.**  When `dstar` is the `≺`-minimal selected `D`-atom, the
condition "`a` precedes every selected `D`-atom" (the `fas` membership predicate)
collapses to the single comparison `a ≺ dstar`.  Pure order theory on `Valid`. -/
theorem fas_inner_collapse {Alpha : Type*} (P : Presentation Alpha Step) (hV : P.Valid)
    (w : List Alpha) (dstar : P.toPoly.Atom) (hdsel : P.toPoly.selectedAtom w dstar)
    (hdD : P.toPoly.labelOf w dstar = D)
    (hdmin : ∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = D →
      dstar = b ∨ P.wrpOrd w dstar b)
    (a : P.toPoly.Atom) (hasel : P.toPoly.selectedAtom w a) :
    (∀ b, P.toPoly.selectedAtom w b → (P.toPoly.labelOf w b = U ∨ P.wrpOrd w a b)) ↔
      P.wrpOrd w a dstar := by
  constructor
  · intro h
    rcases h dstar hdsel with hU | hord
    · rw [hdD] at hU; exact absurd hU (by decide)
    · exact hord
  · intro hadstar b hbsel
    by_cases hbU : P.toPoly.labelOf w b = U
    · exact Or.inl hbU
    · have hbD : P.toPoly.labelOf w b = D := by
        cases hlb : P.toPoly.labelOf w b with
        | U => exact absurd hlb hbU
        | D => rfl
      refine Or.inr ?_
      rcases hdmin b hbsel hbD with rfl | hdb
      · exact hadstar
      · exact hV.trans w a dstar b hasel hdsel hbsel hadstar hdb

/-- **Existence of the `≺`-minimal selected `D`-atom.**  From `IsOutput` (the output is
the `≺`-sorted selected atoms) and the presence of a selected `D`-atom, the first
`D`-labelled atom in the sorted list is selected, `D`-labelled, and `≺`-minimal among
selected `D`-atoms.  (Head of the `D`-filtered, still-`Pairwise`, nonempty list.) -/
theorem exists_min_D_atom {Alpha : Type*} (P : Presentation Alpha Step) (w : List Alpha)
    (out : List Step) (hout : P.IsOutput w out)
    (hD : ∃ a, P.toPoly.selectedAtom w a ∧ P.toPoly.labelOf w a = D) :
    ∃ dstar, P.toPoly.selectedAtom w dstar ∧ P.toPoly.labelOf w dstar = D ∧
      ∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = D →
        dstar = b ∨ P.wrpOrd w dstar b := by
  obtain ⟨atoms, _, hmem, hpair, _⟩ := hout
  obtain ⟨a0, ha0sel, ha0D⟩ := hD
  have hmemD : ∀ b, P.toPoly.selectedAtom w b → P.toPoly.labelOf w b = D →
      b ∈ atoms.filter (fun a => decide (P.toPoly.labelOf w a = D)) := by
    intro b hbsel hbD
    rw [List.mem_filter]
    exact ⟨(hmem b).mpr hbsel, by simp [hbD]⟩
  have hne : atoms.filter (fun a => decide (P.toPoly.labelOf w a = D)) ≠ [] :=
    List.ne_nil_of_mem (hmemD a0 ha0sel ha0D)
  obtain ⟨d, rest, hDeq⟩ := List.exists_cons_of_ne_nil hne
  have hdmem : d ∈ atoms.filter (fun a => decide (P.toPoly.labelOf w a = D)) := by
    rw [hDeq]; simp
  rw [List.mem_filter] at hdmem
  have hp : (d :: rest).Pairwise (P.wrpOrd w) := by
    rw [← hDeq]; exact List.Pairwise.filter (fun a => decide (P.toPoly.labelOf w a = D)) hpair
  rw [List.pairwise_cons] at hp
  refine ⟨d, (hmem d).mp hdmem.1, by simpa using hdmem.2, ?_⟩
  intro b hbsel hbD
  have hbmem := hmemD b hbsel hbD
  rw [hDeq, List.mem_cons] at hbmem
  rcases hbmem with rfl | hbtail
  · exact Or.inl rfl
  · exact Or.inr (hp.1 b hbtail)

end SliceOutput

