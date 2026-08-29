/-
# d*-rank core: the lex-min over a finite EP-comparable
family of `AffineOnResiduesZ`-coordinate vector sequences is `AffineOnResiduesZ`
per coordinate.

This is the COMBINATORIAL HEART of the (WIP) arity-1 `fas` discharge piece (A)
`dstarRank_coord_affineOnResiduesZ`.

The `d*`-rank on `W_n` is the `≺`-min (lex on rank, tie by `χ`; on the rank layer
just the lex-min of the rank vectors) over the SELECTED `D`-atoms.  Each
(copy, region) family contributes, per residue class of the loop-index, a per-class
boundary rank vector whose every coordinate is `AffineOnResiduesZ` in `n`, and
selectedness is convolution-shaped hence constant per cell.  The cross-family/cross-residue
lex-min is then a finite fold (`lexMinList_coord_affineOnResiduesZ`) of the pairwise
`lexMin2_coord_aff`, each comparison `EventuallyPeriodic` (the hypothesis the caller supplies
per residue via `lexLt_eventuallyPeriodic`).

This file VERIFIES that fold: given a nonempty list of vector families `Fs`, each
coordinate `AffineOnResiduesZ`, and the pairwise-`lexLt`-EP hypothesis, the
coordinatewise lex-min `lexMinList Fs` has every coordinate `AffineOnResiduesZ`.
The KEY auxiliary `EP_lexMin_left` (the comparison of a fixed `F` against a running
lex-min is itself EP) is proved by the same fold, using the pointwise identity
`lexLt F (lexMin2 G H) ↔ (if lexLt G H then lexLt F G else lexLt F H)`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
import RequestProject.SliceVectorLexMin

namespace SliceDstarCore

open SliceThreshold SliceOrder SliceVectorLexMin
open scoped Classical

variable {d : ℕ}

/-- Coordinatewise lex-min of two vector families. -/
noncomputable def lexMin2 (U V : ℕ → Fin d → ℤ) : ℕ → Fin d → ℤ :=
  fun n i => if WRP.lexLt (U n) (V n) then U n i else V n i

/-- Running coordinatewise lex-min over a nonempty list of families: fold `lexMin2`. -/
noncomputable def lexMinList : List (ℕ → Fin d → ℤ) → ℕ → Fin d → ℤ
  | []        => fun _ _ => 0
  | [F]       => F
  | F :: rest => lexMin2 F (lexMinList rest)

@[simp] theorem lexMinList_singleton (F : ℕ → Fin d → ℤ) : lexMinList [F] = F := rfl

theorem lexMinList_cons_cons (F G : ℕ → Fin d → ℤ) (rest : List (ℕ → Fin d → ℤ)) :
    lexMinList (F :: G :: rest) = lexMin2 F (lexMinList (G :: rest)) := rfl

/-- **The fold step preserves `AffineOnResiduesZ` per coordinate.**  This is exactly
`lexMin2_coord_affineOnResiduesZ`, restated for `lexMin2`. -/
theorem lexMin2_coord_aff (U V : ℕ → Fin d → ℤ) {p : ℕ} (hp : 1 ≤ p)
    (hEP : EventuallyPeriodic (fun n => WRP.lexLt (U n) (V n)) p)
    (hU : ∀ i : Fin d, AffineOnResiduesZ (fun n => U n i))
    (hV : ∀ i : Fin d, AffineOnResiduesZ (fun n => V n i)) (i : Fin d) :
    AffineOnResiduesZ (fun n => lexMin2 U V n i) :=
  lexMin2_coord_affineOnResiduesZ U V hp hEP hU hV i

/-- **Pointwise lex-comparison against a `lexMin2`.**  `lexLt (F n) (lexMin2 G H n)`
holds iff: when `G` wins (`lexLt (G n) (H n)`) then `lexLt (F n) (G n)`, else
`lexLt (F n) (H n)`.  (The vector `lexMin2 G H n` is `G n` or `H n` pointwise, by the
same `if`-flag in EVERY coordinate, so `lexLt` against it is the gated comparison.) -/
theorem lexLt_lexMin2_iff (F G H : ℕ → Fin d → ℤ) (n : ℕ) :
    WRP.lexLt (F n) (lexMin2 G H n) ↔
      (if WRP.lexLt (G n) (H n) then WRP.lexLt (F n) (G n) else WRP.lexLt (F n) (H n)) := by
  unfold lexMin2
  by_cases hgh : WRP.lexLt (G n) (H n)
  · have hvec : (fun i => if WRP.lexLt (G n) (H n) then G n i else H n i) = G n := by
      funext i; rw [if_pos hgh]
    rw [hvec, if_pos hgh]
  · have hvec : (fun i => if WRP.lexLt (G n) (H n) then G n i else H n i) = H n := by
      funext i; rw [if_neg hgh]
    rw [hvec, if_neg hgh]

/-- Negation of an EP predicate is EP. -/
theorem EP_not {Pr : ℕ → Prop} {p : ℕ} (h : EventuallyPeriodic Pr p) :
    EventuallyPeriodic (fun n => ¬ Pr n) p := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, fun n hn => by simp only; rw [hm n hn]⟩

/-- **EP of the comparison `F ≺ lexMinList rest`.**  By induction on `rest`: the
single-element case is `hEPF`; the cons step rewrites via `lexLt_lexMin2_iff` to an
EP-gated `if` (`affineOnResiduesZ_ite`-style on Props) of the head comparison and the
IH tail comparison, all EP. -/
theorem EP_lexMin_left (F : ℕ → Fin d → ℤ) (rest : List (ℕ → Fin d → ℤ)) {p : ℕ}
    (hp : 1 ≤ p)
    (hEPF : ∀ V ∈ rest, EventuallyPeriodic (fun n => WRP.lexLt (F n) (V n)) p)
    (hEPrest : ∀ U ∈ rest, ∀ V ∈ rest,
        EventuallyPeriodic (fun n => WRP.lexLt (U n) (V n)) p)
    (hne : rest ≠ []) :
    EventuallyPeriodic (fun n => WRP.lexLt (F n) (lexMinList rest n)) p := by
  match rest, hne with
  | [G], _ =>
      simpa [lexMinList] using hEPF G (by simp)
  | G :: G' :: rest'', _ =>
      rw [lexMinList_cons_cons]
      -- pointwise: lexLt F (lexMin2 G (lexMinList (G'::rest''))) is the gated `if`
      have hEPgh : EventuallyPeriodic
          (fun n => WRP.lexLt (G n) (lexMinList (G' :: rest'') n)) p := by
        apply EP_lexMin_left G (G' :: rest'') hp
        · exact fun V hV => hEPrest G (by simp) V (List.mem_cons_of_mem _ hV)
        · exact fun U hU V hV => hEPrest U (List.mem_cons_of_mem _ hU)
            V (List.mem_cons_of_mem _ hV)
        · simp
      have hEPFG : EventuallyPeriodic (fun n => WRP.lexLt (F n) (G n)) p :=
        hEPF G (by simp)
      have hEPFrest : EventuallyPeriodic
          (fun n => WRP.lexLt (F n) (lexMinList (G' :: rest'') n)) p := by
        apply EP_lexMin_left F (G' :: rest'') hp
        · exact fun V hV => hEPF V (List.mem_cons_of_mem _ hV)
        · exact fun U hU V hV => hEPrest U (List.mem_cons_of_mem _ hU)
            V (List.mem_cons_of_mem _ hV)
        · simp
      -- EP of an EP-gated disjunction of EP predicates
      have hgate : EventuallyPeriodic
          (fun n => (WRP.lexLt (G n) (lexMinList (G' :: rest'') n) ∧
                      WRP.lexLt (F n) (G n)) ∨
                    (¬ WRP.lexLt (G n) (lexMinList (G' :: rest'') n) ∧
                      WRP.lexLt (F n) (lexMinList (G' :: rest'') n))) p :=
        (hEPgh.and hEPFG).or ((EP_not hEPgh).and hEPFrest)
      refine hgate.congr (fun n => ?_)
      rw [lexLt_lexMin2_iff F G (lexMinList (G' :: rest'')) n]
      by_cases hgh : WRP.lexLt (G n) (lexMinList (G' :: rest'') n)
      · simp [hgh]
      · simp [hgh]
  termination_by rest.length

/-- **The lex-min over a finite family is `AffineOnResiduesZ` per coordinate.**

Hypotheses:
* `hp : 1 ≤ p` — a single common period (the lcm of all rank periods + iterate
  periods, aligned across families and residue classes);
* `haff` — every family in `Fs` has every coordinate `AffineOnResiduesZ`;
* `hEPpair` — every ORDERED pair of families from `Fs` has eventually-periodic
  `lexLt` comparison with period `p` (supplied by `lexLt_eventuallyPeriodic` per
  residue class, since on a fixed residue class each rank coordinate has a CONSTANT
  slope).

Conclusion: every coordinate of `lexMinList Fs` is `AffineOnResiduesZ`.

Proof: induction on `Fs`.  The cons step folds `lexMin2_coord_aff` against the IH on
the tail (its coordinates are `AffineOnResiduesZ` by IH and its comparison with the
head is `EP_lexMin_left`).  The single-element base case is the family itself. -/
theorem lexMinList_coord_affineOnResiduesZ
    (Fs : List (ℕ → Fin d → ℤ)) {p : ℕ} (hp : 1 ≤ p)
    (haff : ∀ F ∈ Fs, ∀ i : Fin d, AffineOnResiduesZ (fun n => F n i))
    (hEPpair : ∀ U ∈ Fs, ∀ V ∈ Fs,
        EventuallyPeriodic (fun n => WRP.lexLt (U n) (V n)) p)
    (hne : Fs ≠ []) :
    ∀ i : Fin d, AffineOnResiduesZ (fun n => lexMinList Fs n i) := by
  induction Fs with
  | nil => exact absurd rfl hne
  | cons F rest ih =>
      cases rest with
      | nil =>
          intro i; simpa [lexMinList] using haff F (by simp) i
      | cons G rest' =>
          intro i
          rw [lexMinList_cons_cons]
          have haffrest : ∀ H ∈ (G :: rest'), ∀ j : Fin d,
              AffineOnResiduesZ (fun n => H n j) :=
            fun H hH j => haff H (List.mem_cons_of_mem _ hH) j
          have hEPrest : ∀ U ∈ (G :: rest'), ∀ V ∈ (G :: rest'),
              EventuallyPeriodic (fun n => WRP.lexLt (U n) (V n)) p :=
            fun U hU V hV => hEPpair U (List.mem_cons_of_mem _ hU)
              V (List.mem_cons_of_mem _ hV)
          have ihrest : ∀ j : Fin d,
              AffineOnResiduesZ (fun n => lexMinList (G :: rest') n j) :=
            ih haffrest hEPrest (by simp)
          have hEPcompare : EventuallyPeriodic
              (fun n => WRP.lexLt (F n) (lexMinList (G :: rest') n)) p := by
            apply EP_lexMin_left F (G :: rest') hp
            · exact fun V hV => hEPpair F (by simp) V (List.mem_cons_of_mem _ hV)
            · exact hEPrest
            · simp
          have hF : ∀ j : Fin d, AffineOnResiduesZ (fun n => F n j) :=
            fun j => haff F (by simp) j
          exact lexMin2_coord_aff F (lexMinList (G :: rest')) hp hEPcompare hF ihrest i

end SliceDstarCore
