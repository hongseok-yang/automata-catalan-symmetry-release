/-
# The lex-below count: counting loop-indices whose rank is `≺`-below a moving threshold

The rank-comparison heart of the arity-1 `fas` count.  An atom at loop-index `j` has
rank `rank(j)` (a `RankAffine` `ℤ^d`-vector); the moving `d*`-threshold is
`AffineOnResiduesZ` in `n`.  `fas` counts the `j < n` with `lexLt (rank j) (thr n)`.

This file builds that count purely from the `SliceThreshold` kernel (no MSO):

* `indicator_{lt,le,eq,dvd}` — the `{0,1}` indicator of an `AffineOnResiduesZ`
  comparison is `AffineOnResidues` (via `toNat`/`min`/`affineOnResidues_mul_bddOne`);
* (next) the single-variable lex indicator and the two-variable lex-below count, by
  induction on the coordinate list, reducing the head-strict case to
  `countLtThreshold` and the head-equal case to a pinned-`t` indicator.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
import RequestProject.SliceThreshold
import RequestProject.WRP

namespace SliceLexCount

open SliceThreshold SliceAffine
open scoped Classical

/-- The indicator of `F n < G n` (two `AffineOnResiduesZ` sequences) is `AffineOnResidues`. -/
theorem indicator_lt {F G : ℕ → ℤ} (hF : AffineOnResiduesZ F) (hG : AffineOnResiduesZ G) :
    AffineOnResidues (fun n => if F n < G n then 1 else 0) := by
  have heq : (fun n => if F n < G n then 1 else 0) = (fun n => (min 1 (G n - F n)).toNat) := by
    funext n; by_cases h : F n < G n
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  rw [heq]; exact ((AffineOnResiduesZ.const 1).min (hG.sub hF)).toNat

/-- The indicator of `F n ≤ G n` is `AffineOnResidues`. -/
theorem indicator_le {F G : ℕ → ℤ} (hF : AffineOnResiduesZ F) (hG : AffineOnResiduesZ G) :
    AffineOnResidues (fun n => if F n ≤ G n then 1 else 0) := by
  have heq : (fun n => if F n ≤ G n then 1 else 0)
      = (fun n => (min 1 (G n - F n + 1)).toNat) := by
    funext n; by_cases h : F n ≤ G n
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  rw [heq]
  exact ((AffineOnResiduesZ.const 1).min ((hG.sub hF).add (AffineOnResiduesZ.const 1))).toNat

/-- The indicator of `F n = G n` is `AffineOnResidues` (product of the two `≤`-indicators). -/
theorem indicator_eq {F G : ℕ → ℤ} (hF : AffineOnResiduesZ F) (hG : AffineOnResiduesZ G) :
    AffineOnResidues (fun n => if F n = G n then 1 else 0) := by
  have heq : (fun n => if F n = G n then 1 else 0)
      = (fun n => (if F n ≤ G n then 1 else 0) * (if G n ≤ F n then 1 else 0)) := by
    funext n
    rcases lt_trichotomy (F n) (G n) with h | h | h
    · rw [if_neg (ne_of_lt h), if_pos (le_of_lt h), if_neg (not_le.mpr h)]
    · rw [if_pos h, if_pos (le_of_eq h), if_pos (le_of_eq h.symm)]
    · rw [if_neg (ne_of_gt h), if_neg (not_le.mpr h), if_pos (le_of_lt h)]
  rw [heq]
  exact affineOnResidues_mul_bddOne (indicator_le hF hG) (indicator_le hG hF)
    (fun n => by by_cases h : G n ≤ F n <;> simp [h])

/-- The indicator of `q ∣ H n` (fixed `q ≥ 1`, `H` `AffineOnResiduesZ`) is
`AffineOnResidues`: per residue class mod `p·q` the divisibility is constant. -/
theorem indicator_dvd (q : ℕ) (hq : 1 ≤ q) {H : ℕ → ℤ} (hH : AffineOnResiduesZ H) :
    AffineOnResidues (fun n => if (q : ℤ) ∣ H n then 1 else 0) := by
  obtain ⟨m, p, s, hp, hrec⟩ := hH
  refine affineOnResidues_of_period (m := m) (p := p * q) (fun _ => 0)
    (Nat.mul_pos hp (by omega)) ?_
  intro r _ k
  show (if (q : ℤ) ∣ H (m + r + p * q * k) then 1 else 0)
      = (if (q : ℤ) ∣ H (m + r) then 1 else 0) + k * 0
  rw [Nat.mul_zero, Nat.add_zero, show m + r + p * q * k = m + r + p * (q * k) from by ring,
    hrec r (q * k)]
  have hdvd : (q : ℤ) ∣ (↑(q * k)) * s r := ⟨↑k * s r, by push_cast; ring⟩
  by_cases h : (q : ℤ) ∣ H (m + r)
  · rw [if_pos h, if_pos (dvd_add h hdvd)]
  · rw [if_neg h, if_neg (fun hc => h ((dvd_add_right hdvd).mp (by rwa [add_comm] at hc)))]

/-- List-recursive lexicographic order on `ℤ`-lists. -/
def lexLtL : List ℤ → List ℤ → Prop
  | [], _ => False
  | _ :: _, [] => False
  | x :: xs, y :: ys => x < y ∨ (x = y ∧ lexLtL xs ys)

/-- **Bridge.**  `WRP.lexLt` on `Fin d → ℤ` vectors equals `lexLtL` on their
`List.ofFn`, by induction on `d` (the head/tail decomposition of the `Fin`-lex order). -/
theorem lexLt_iff_lexLtL : ∀ {d : ℕ} (x y : Fin d → ℤ),
    WRP.lexLt x y ↔ lexLtL (List.ofFn x) (List.ofFn y)
  | 0, x, y => by
      constructor
      · rintro ⟨i, _⟩; exact i.elim0
      · intro h; simp [List.ofFn, lexLtL] at h
  | d + 1, x, y => by
      rw [List.ofFn_succ, List.ofFn_succ]
      simp only [lexLtL]
      rw [← lexLt_iff_lexLtL (fun i => x i.succ) (fun i => y i.succ)]
      constructor
      · rintro ⟨i, hlt, hi⟩
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exact Or.inl hi
        · exact Or.inr ⟨hlt 0 (Fin.succ_pos j),
            ⟨j, fun k hk => hlt k.succ (Fin.succ_lt_succ_iff.mpr hk), hi⟩⟩
      · rintro (h | ⟨h0, ⟨j, hlt', hi'⟩⟩)
        · exact ⟨0, fun k hk => absurd hk (Fin.not_lt_zero k), h⟩
        · refine ⟨j.succ, fun k hk => ?_, hi'⟩
          rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
          · exact h0
          · exact hlt' k' (Fin.succ_lt_succ_iff.mp hk)

/-- **Single-variable lex indicator.**  For two lists of `AffineOnResiduesZ` sequences,
the indicator of `lexLtL (As n) (Bs n)` is `AffineOnResidues` in `n`. -/
theorem lexLtL_indicator (As Bs : List (ℕ → ℤ))
    (hA : ∀ f ∈ As, AffineOnResiduesZ f) (hB : ∀ f ∈ Bs, AffineOnResiduesZ f) :
    AffineOnResidues (fun n =>
      if lexLtL (As.map (fun f => f n)) (Bs.map (fun f => f n)) then 1 else 0) := by
  induction As generalizing Bs with
  | nil => simpa [lexLtL] using AffineOnResidues.zero
  | cons a As' ih =>
      cases Bs with
      | nil => simpa [lexLtL] using AffineOnResidues.zero
      | cons b Bs' =>
          have ha := hA a (by simp)
          have hb := hB b (by simp)
          have ihrest := ih Bs' (fun f hf => hA f (List.mem_cons_of_mem _ hf))
            (fun f hf => hB f (List.mem_cons_of_mem _ hf))
          have heq : (fun n => if lexLtL ((a :: As').map (fun f => f n))
                ((b :: Bs').map (fun f => f n)) then 1 else 0)
              = (fun n => (if a n < b n then 1 else 0)
                  + (if a n = b n then 1 else 0)
                    * (if lexLtL (As'.map (fun f => f n)) (Bs'.map (fun f => f n))
                        then 1 else 0)) := by
            funext n
            simp only [List.map_cons, lexLtL]
            by_cases h1 : a n < b n
            · simp [h1, ne_of_lt h1]
            · by_cases h2 : a n = b n
              · simp [h2]
              · simp [h1, h2]
          rw [heq]
          exact (indicator_lt ha hb).add
            (affineOnResidues_mul_bddOne (indicator_eq ha hb) ihrest (fun n => by split <;> simp))

/-- **Pinned-`t` count.**  When the head slope `p ≠ 0`, the equality `b + t·p = c` pins
`t` to a single value, so the count of `t ∈ [0,N)` also satisfying a predicate `Q` is a
`{0,1}` indicator of (divisibility ∧ non-negativity ∧ in-range ∧ `Q` at the pinned `t`). -/
theorem pinned_count (b p c : ℤ) (hp : p ≠ 0) (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ((Finset.range N).filter (fun t : ℕ => b + (t : ℤ) * p = c ∧ Q t)).card
      = if (p ∣ (c - b) ∧ 0 ≤ (c - b) / p ∧ ((c - b) / p).toNat < N ∧ Q ((c - b) / p).toNat)
          then 1 else 0 := by
  by_cases hcond : (p ∣ (c - b) ∧ 0 ≤ (c - b) / p ∧ ((c - b) / p).toNat < N
      ∧ Q ((c - b) / p).toNat)
  · rw [if_pos hcond]
    obtain ⟨hdvd, hnn, hlt, hQ⟩ := hcond
    have hsingle : (Finset.range N).filter (fun t : ℕ => b + (t : ℤ) * p = c ∧ Q t)
        = {((c - b) / p).toNat} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨hlt, ?_, hQ⟩
        rw [Int.toNat_of_nonneg hnn, Int.ediv_mul_cancel hdvd]; ring
      · intro t ht
        rw [Finset.mem_filter, Finset.mem_range] at ht
        obtain ⟨-, heq, -⟩ := ht
        have hmul : (t : ℤ) * p = ((c - b) / p) * p := by
          rw [Int.ediv_mul_cancel hdvd]; linarith
        have ht' : (t : ℤ) = (c - b) / p := mul_right_cancel₀ hp hmul
        omega
    rw [hsingle, Finset.card_singleton]
  · rw [if_neg hcond, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t ht hpred
    rw [Finset.mem_range] at ht
    obtain ⟨heq, hQt⟩ := hpred
    have hmul : (t : ℤ) * p = c - b := by linarith
    have hdvd : p ∣ (c - b) := ⟨t, by rw [← hmul]; ring⟩
    have hquot : (c - b) / p = (t : ℤ) := by rw [← hmul]; exact Int.mul_ediv_cancel _ hp
    exact hcond ⟨hdvd, by rw [hquot]; exact Int.natCast_nonneg t,
      by rw [hquot]; simpa using ht, by rw [hquot]; simpa using hQt⟩

/-- `{0,1}` indicator of a conjunction is the product of the indicators. -/
theorem ite_and_mul (A B : Prop) [Decidable A] [Decidable B] :
    (if (A ∧ B) then (1 : ℕ) else 0) = (if A then 1 else 0) * (if B then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

/-- **The two-variable lex-below count.**  For a line spec `L` (base/slope pairs) and a
threshold `T` (`AffineOnResiduesZ` coords), the count of `t < U n` whose affine line
`lineAt t` is `lexLtL`-below `T n` is `AffineOnResidues` in `n`.  By induction on the
coordinate list: the head-strict case goes to `countLtThreshold`, the head-equal case to
`pinned_count` (`p≠0`) or an `indicator_eq`-gated tail count (`p=0`). -/
theorem countLexL (L : List (ℤ × ℤ)) (T : List (ℕ → ℤ)) (hT : ∀ f ∈ T, AffineOnResiduesZ f)
    (U : ℕ → ℕ) (hU : AffineOnResidues U) :
    AffineOnResidues (fun n => ((Finset.range (U n)).filter
      (fun t : ℕ => lexLtL (L.map (fun bp => bp.1 + (t : ℤ) * bp.2))
        (T.map (fun f => f n)))).card) := by
  induction L generalizing T with
  | nil =>
      have h0 : (fun n => ((Finset.range (U n)).filter (fun t : ℕ =>
            lexLtL (([] : List (ℤ × ℤ)).map (fun bp => bp.1 + (t : ℤ) * bp.2))
              (T.map (fun f => f n)))).card) = fun _ => 0 := by
        funext n; simp [lexLtL]
      rw [h0]; exact AffineOnResidues.zero
  | cons bp L' ih =>
      obtain ⟨b, p⟩ := bp
      cases T with
      | nil =>
          have h0 : (fun n => ((Finset.range (U n)).filter (fun t : ℕ =>
                lexLtL (((b, p) :: L').map (fun bp => bp.1 + (t : ℤ) * bp.2))
                  (([] : List (ℕ → ℤ)).map (fun f => f n)))).card) = fun _ => 0 := by
            funext n; simp [lexLtL]
          rw [h0]; exact AffineOnResidues.zero
      | cons c T' =>
          have hc : AffineOnResiduesZ c := hT c (by simp)
          have hT' : ∀ f ∈ T', AffineOnResiduesZ f := fun f hf => hT f (by simp [hf])
          have ihrest := ih T' hT'
          -- split the head disjunction into strict + tie
          have hsplit : (fun n => ((Finset.range (U n)).filter (fun t : ℕ =>
                lexLtL (((b, p) :: L').map (fun bp => bp.1 + (t : ℤ) * bp.2))
                  ((c :: T').map (fun f => f n)))).card)
              = (fun n => ((Finset.range (U n)).filter
                    (fun t : ℕ => b + (t : ℤ) * p < c n)).card
                  + ((Finset.range (U n)).filter (fun t : ℕ => b + (t : ℤ) * p = c n ∧
                      lexLtL (L'.map (fun bp => bp.1 + (t : ℤ) * bp.2))
                        (T'.map (fun f => f n)))).card) := by
            funext n
            have hfc : (Finset.range (U n)).filter (fun t : ℕ =>
                  lexLtL (((b, p) :: L').map (fun bp => bp.1 + (t : ℤ) * bp.2))
                    ((c :: T').map (fun f => f n)))
                = (Finset.range (U n)).filter (fun t : ℕ => (b + (t : ℤ) * p < c n) ∨
                    (b + (t : ℤ) * p = c n ∧ lexLtL (L'.map (fun bp => bp.1 + (t : ℤ) * bp.2))
                      (T'.map (fun f => f n)))) :=
              Finset.filter_congr (fun t _ => by simp only [List.map_cons, lexLtL])
            have hdisj : Disjoint
                ((Finset.range (U n)).filter (fun t : ℕ => b + (t : ℤ) * p < c n))
                ((Finset.range (U n)).filter (fun t : ℕ => b + (t : ℤ) * p = c n ∧
                  lexLtL (L'.map (fun bp => bp.1 + (t : ℤ) * bp.2)) (T'.map (fun f => f n)))) := by
              apply Finset.disjoint_left.mpr
              intro t h1 h2
              rw [Finset.mem_filter] at h1 h2
              exact absurd h2.2.1 (ne_of_lt h1.2)
            rw [hfc, Finset.filter_or, Finset.card_union_of_disjoint hdisj]
          rw [hsplit]
          refine AffineOnResidues.add ?_ ?_
          · -- strict term = countLtThreshold p (c - b) U
            refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_)
              (countLtThreshold p (hc.sub (AffineOnResiduesZ.const b)) hU)
            apply congrArg Finset.card
            apply Finset.filter_congr
            intro t _
            rw [show p * (t : ℤ) = (t : ℤ) * p from mul_comm _ _]; omega
          · -- tie term
            by_cases hp0 : p = 0
            · subst hp0
              have heq : (fun n => ((Finset.range (U n)).filter (fun t : ℕ =>
                    b + (t : ℤ) * 0 = c n ∧ lexLtL (L'.map (fun bp => bp.1 + (t : ℤ) * bp.2))
                      (T'.map (fun f => f n)))).card)
                  = (fun n => ((Finset.range (U n)).filter (fun t : ℕ =>
                      lexLtL (L'.map (fun bp => bp.1 + (t : ℤ) * bp.2))
                        (T'.map (fun f => f n)))).card * (if b = c n then 1 else 0)) := by
                funext n
                by_cases hbc : b = c n
                · rw [if_pos hbc, Nat.mul_one]
                  apply congrArg Finset.card; apply Finset.filter_congr
                  intro t _; constructor
                  · rintro ⟨-, hr⟩; exact hr
                  · intro hr; exact ⟨by rw [hbc]; ring, hr⟩
                · rw [if_neg hbc, Nat.mul_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                  rintro t - ⟨he, -⟩; exact hbc (by simpa using he)
              rw [heq]
              exact affineOnResidues_mul_bddOne ihrest
                (indicator_eq (AffineOnResiduesZ.const b) hc) (fun n => by split <;> simp)
            · -- p ≠ 0 : pinned count = product of four indicators
              have key : (fun n => ((Finset.range (U n)).filter (fun t : ℕ =>
                    b + (t : ℤ) * p = c n ∧ lexLtL (L'.map (fun bp => bp.1 + (t : ℤ) * bp.2))
                      (T'.map (fun f => f n)))).card)
                  = (fun n => (if (p : ℤ) ∣ (c n - b) then 1 else 0)
                      * (if 0 ≤ (c n - b) / p then 1 else 0)
                      * (if ((c n - b) / p).toNat < U n then 1 else 0)
                      * (if lexLtL (L'.map (fun bp => bp.1 + ((c n - b) / p) * bp.2))
                          (T'.map (fun f => f n)) then 1 else 0)) := by
                funext n
                rw [pinned_count b p (c n) hp0 (U n)
                  (fun t => lexLtL (L'.map (fun bp => bp.1 + (t : ℤ) * bp.2))
                    (T'.map (fun f => f n))),
                  ite_and_mul, ite_and_mul, ite_and_mul]
                by_cases hB : 0 ≤ (c n - b) / p
                · have htoNat : (((c n - b) / p).toNat : ℤ) = (c n - b) / p :=
                    Int.toNat_of_nonneg hB
                  rw [show (L'.map (fun bp => bp.1 + (((c n - b) / p).toNat : ℤ) * bp.2))
                        = (L'.map (fun bp => bp.1 + ((c n - b) / p) * bp.2)) from
                      List.map_congr_left (fun bp _ => by rw [htoNat])]
                  ring
                · rw [if_neg hB]; ring
              rw [key]
              have hpnat : 1 ≤ p.natAbs := by omega
              have hediv : AffineOnResiduesZ (fun n => (c n - b) / p) :=
                (hc.sub (AffineOnResiduesZ.const b)).ediv p hp0
              have hI_A : AffineOnResidues (fun n => if (p : ℤ) ∣ (c n - b) then 1 else 0) := by
                refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_)
                  (indicator_dvd p.natAbs hpnat (hc.sub (AffineOnResiduesZ.const b)))
                exact if_congr Int.natAbs_dvd.symm rfl rfl
              have hI_B : AffineOnResidues (fun n => if 0 ≤ (c n - b) / p then 1 else 0) :=
                indicator_le (AffineOnResiduesZ.const 0) hediv
              have hI_C : AffineOnResidues (fun n => if ((c n - b) / p).toNat < U n then 1 else 0) := by
                refine AffineOnResidues.congr_eventually (N := 0) (fun n _ => ?_)
                  (indicator_lt hediv.toNatCast (AffineOnResiduesZ.of_natCast hU))
                exact if_congr Nat.cast_lt.symm rfl rfl
              have hI_D : AffineOnResidues (fun n =>
                  if lexLtL (L'.map (fun bp => bp.1 + ((c n - b) / p) * bp.2))
                    (T'.map (fun f => f n)) then 1 else 0) :=
                (lexLtL_indicator (L'.map (fun bp => fun n => bp.1 + ((c n - b) / p) * bp.2)) T'
                  (by intro f hf; simp only [List.mem_map] at hf; obtain ⟨bp, -, rfl⟩ := hf
                      exact (AffineOnResiduesZ.const bp.1).add
                        ((hediv.smul bp.2).congr (fun n => mul_comm bp.2 ((c n - b) / p))))
                  hT').congr_eventually (N := 0)
                  (fun n _ => by simp only [List.map_map, Function.comp_def])
              exact affineOnResidues_mul_bddOne
                (affineOnResidues_mul_bddOne
                  (affineOnResidues_mul_bddOne hI_A hI_B (fun n => by split <;> simp))
                  hI_C (fun n => by split <;> simp))
                hI_D (fun n => by split <;> simp)

end SliceLexCount
