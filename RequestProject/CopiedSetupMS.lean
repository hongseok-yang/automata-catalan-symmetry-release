/-
# mS-direction eventual periodicity (§9 tower, Stage F-mS — foundation)

The fibred tie count needs the equal-rank cell finsets to be *eventually periodic in the
boundary width* `mS` (not mS-invariant — that is FALSE — but
periodic with an mS-free period `q_U`).  The whole mS-dependence flows through the post-prefix
automaton state `δ*(q₀, U^mS)` and the rank accumulated over the `U^mS` prefix and `D^mS` suffix.

This file lays the **cornerstone**: reading a uniform letter run `x^{mS}` through any finite-state
`RankSource` automaton, the post-run STATE is eventually periodic in `mS`.  This is the mS-direction
twin of `SliceAutomata.iterate_eventuallyPeriodic` (used everywhere for the `n` direction), specialised
to the `foldl … (List.replicate mS x)` form in which the rank engine reads the `U^mS` prefix
(`CopiedRank.summand_copied_block_eq`) and the `D^mS` suffix.  The period/threshold are hoisted BEFORE
`mS`, matching the discipline the §9 tower requires.
-/
import RequestProject.CopiedRank
import RequestProject.CopiedAffineAt
import RequestProject.CopiedLandmark
import RequestProject.CopiedGateEP

namespace CopiedSetupMS

open Step CopiedRank CopiedLandmark CopiedCells SliceFamilyCell

/-- **Iterate period-multiple**: from one-step eventual periodicity `f^[j+p] = f^[j]`
(for `j ≥ m`), any multiple `f^[j + p*k] q₀ = f^[j] q₀`. -/
theorem iterate_period_mul {Q : Type*} (f : Q → Q) (q₀ : Q) (m p : ℕ)
    (hper : ∀ j, m ≤ j → f^[j + p] q₀ = f^[j] q₀) (k j : ℕ) (hj : m ≤ j) :
    f^[j + p * k] q₀ = f^[j] q₀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show j + p * (k + 1) = (j + p * k) + p by ring, hper (j + p * k) (by omega)]
    exact ih

/-- **Endofunction-level eventual periodicity (period-multiple form)**: for a finite-state `h`,
the iterate sequence `h^[·]` is eventually periodic *as a function* — `h^[a + p*k] = h^[a]` for all
start states at once, past a threshold `m`.  This uniform-over-start-states form is needed for the
suffix run of `gateF` EP-in-mS, whose base state itself moves with `mS`. -/
theorem endofunction_EP_mul {Q : Type*} [Finite Q] (h : Q → Q) :
    ∃ m p, 1 ≤ p ∧ ∀ k a, m ≤ a → h^[a + p * k] = h^[a] := by
  have key : ∀ a, (fun g : Q → Q => h ∘ g)^[a] id = h^[a] := by
    intro a; induction a with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih]
      exact (Function.iterate_succ' h n).symm
  obtain ⟨m, p, hp, hper⟩ := SliceAutomata.iterate_eventuallyPeriodic (fun g : Q → Q => h ∘ g) id
  refine ⟨m, p, hp, fun k a ha => ?_⟩
  have := iterate_period_mul (fun g : Q → Q => h ∘ g) id m p hper k a ha
  rw [key, key] at this
  exact this

/-- **The PREFIX-stretch summand formula↔eval bridge** (d3.4 prefix-engine, the mirror of
`summand_copied_sufStretch_eq`).  For a coordinate at a prefix position `q < mS-1` (where
`posAt (.prefIdx q) = q` is mS-FREE), `s.eval` reads the first `q` letters `U^q` (a pure `δ_U` run).
STRICTLY SIMPLER than the suffix twin: no `U^mS ++ (UD)^n` pre-blocks and no growing tail — just `U^q`,
and the formula is mS-FREE and n-FREE.  This is what makes the prefix engine cheap (no `reverseComplement`
needed) — the deep-PREFIX analog of the d3.3 suffix collapse. -/
theorem summand_copied_prefStretch_eq {k : ℕ} (s : Summand Step d k)
    (mS q : ℕ) (hq : q < mS - 1) (n : ℕ) :
    s.eval (copiedSlice mS n) (fun _ => q) =
      s.coeff • s.A.prefixRank (List.replicate q U) (List.replicate q U).length
        + s.β (List.foldl s.A.δ s.A.q0 (List.replicate q U)) U := by
  have hm : 1 ≤ mS := by omega
  have hget : (copiedSlice mS n)[q]? = some U :=
    copiedSlice_getElem?_pref mS n q hm (by omega)
  have hpref : s.A.prefixRank (copiedSlice mS n) q
      = s.A.prefixRank (List.replicate q U) (List.replicate q U).length := by
    rw [List.length_replicate]
    exact SliceRankAtom.prefixRank_prefix_stable s.A _ _ q
      (by rw [copiedSlice_take_U mS q n hm (by omega), List.take_replicate, Nat.min_self])
  have hstate : s.A.stateBefore (copiedSlice mS n) q
      = List.foldl s.A.δ s.A.q0 (List.replicate q U) := by
    unfold RankSource.stateBefore
    rw [copiedSlice_take_U mS q n hm (by omega)]
  unfold Summand.eval
  funext c
  rw [hget, Option.elim_some, hpref, hstate]
  simp

open SliceRankAtom in
/-- **The PREFIX-stretch summand formula is `RankAffine` in the prefix depth `q`** (d3.4 prefix-engine,
the mirror of the suffix-stretch recurrence).  EVEN SIMPLER than the suffix: empty pre-blocks and NO
`+1` shift (the run is exactly `U^q`).  PART A `prefixRank(U^q)` via `prefixRank_pre_blocks_tail_rankAffine`
with empty pre/suf; PART B `s.β(δ_U^q q0) U` via `rankAffine_of_iterate` from the bare start `q0`. -/
theorem prefStretch_formula_rankAffine_q {k : ℕ} (s : Summand Step d k) :
    RankAffine (fun q =>
      s.coeff • s.A.prefixRank (List.replicate q U) (List.replicate q U).length
        + s.β (List.foldl s.A.δ s.A.q0 (List.replicate q U)) U) := by
  have := s.A.fintypeQ
  refine RankAffine.add (RankAffine.smul s.coeff ?_) ?_
  · refine RankAffine.congr (fun q => ?_)
      (prefixRank_pre_blocks_tail_rankAffine s.A [] [U] [])
    simp only [List.nil_append, List.append_nil, flatten_replicate_singleton]
  · refine RankAffine.congr (fun q => ?_)
      (rankAffine_of_iterate (fun st => s.A.δ st U) s.A.q0 (fun st => s.β st U))
    rw [foldl_replicate_iterate s.A.δ U]

/-- **Mixed cell descriptor (deep-suffix candidate set).**  Each coordinate is either a fixed
wrapped-flat / stretch descriptor (`inl r : RegionSpecF B`) or a DEEP-suffix offset
(`inr i_off`, `i_off ≥ 1`) standing for the moving descriptor `sufIdx (mS-1-i_off)` whose `D`-run
`D^{mS-i_off}` grows with `mS`.  A fixed `RegionSpecF B` cannot reach the deep-suffix region (its
`sufIdx l` carries a fixed `l`), so the deep case needs this separate `inr` marker. -/
def mixedPosAt {B : ℕ} (ds : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) (mS t n : ℕ) : ℕ :=
  match ds with
  | .inl r => r.posAt mS t n
  | .inr (.inl i_off) => mS + 2 * n + 1 + (mS - 1 - i_off)
  | .inr (.inr i_off) => mS - 1 - i_off

/-! ## d3.2b-enum: the bounded mS-free shape enumeration -/

/-- **The bounded mS-free shape enumeration** for one coordinate (d3.2b-enum): the finite set of
candidate `RegionSpecF B ⊕ (ℕ ⊕ ℕ)` descriptors — `inl (core r)` for any wrapped-flat region, `inl (prefIdx q)`
for `q < q_U`, `inl (sufIdx l)` for the SHALLOW suffix depths `l < q_D`, and `inr i_off` for the DEEP
suffix depths `1 ≤ i_off ≤ q_D` (encoding `sufIdx (mS-1-i_off)`).  The l-monotonicity (d3.3) collapses all
other suffix depths to these boundaries; `q_U`/`q_D` are the U-prefix / D-suffix automaton cycle lengths. -/
def coordCands (B q_U q_D : ℕ) : Finset (RegionSpecF B ⊕ (ℕ ⊕ ℕ)) :=
  (Finset.univ.image (fun r : RegionSpec B => Sum.inl (RegionSpecF.core r)))
  ∪ ((Finset.range q_U).image (fun q => Sum.inl (RegionSpecF.prefIdx q)))
  ∪ ((Finset.range q_D).image (fun l => Sum.inl (RegionSpecF.sufIdx l)))
  ∪ ((Finset.Icc 1 q_D).image (fun i_off => Sum.inr (Sum.inl i_off)))
  ∪ ((Finset.Icc 1 q_U).image (fun i_off => Sum.inr (Sum.inr i_off)))

/-- Membership characterization of `coordCands`. -/
theorem mem_coordCands {B q_U q_D : ℕ} (x : RegionSpecF B ⊕ (ℕ ⊕ ℕ)) :
    x ∈ coordCands B q_U q_D ↔
      (∃ r : RegionSpec B, x = Sum.inl (RegionSpecF.core r))
      ∨ (∃ q, q < q_U ∧ x = Sum.inl (RegionSpecF.prefIdx q))
      ∨ (∃ l, l < q_D ∧ x = Sum.inl (RegionSpecF.sufIdx l))
      ∨ (∃ i_off, 1 ≤ i_off ∧ i_off ≤ q_D ∧ x = Sum.inr (Sum.inl i_off))
      ∨ (∃ i_off, 1 ≤ i_off ∧ i_off ≤ q_U ∧ x = Sum.inr (Sum.inr i_off)) := by
  simp only [coordCands, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ((((⟨r, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨l, hl, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
    · exact Or.inl ⟨r, rfl⟩
    · exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨l, hl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi.1, hi.2, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi.1, hi.2, rfl⟩)))
  · rintro (⟨r, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨l, hl, rfl⟩ | ⟨i, hi1, hi2, rfl⟩ | ⟨i, hi1, hi2, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨r, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨l, hl, rfl⟩))
    · exact Or.inl (Or.inr ⟨i, ⟨hi1, hi2⟩, rfl⟩)
    · exact Or.inr ⟨i, ⟨hi1, hi2⟩, rfl⟩

end CopiedSetupMS
