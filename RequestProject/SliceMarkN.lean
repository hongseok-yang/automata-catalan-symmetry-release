/-
# The `m`-marked slice word: blocks form and unmarked-segment folds (route GA-2, foundation)

The general-arity discharge analyses per-atom predicates through `m`-mark DFAs
(`MSOMarkN`).  On the slice `W_n = U(UD)^nD` every loop block is the SAME two-letter
word, so an `m`-marked slice word decomposes canonically — no sorting of the marks is
needed — as

  `pre-letter :: (block letters)_{j<n} ++ [suffix letter]`,

with block `j` contributing the two letters at positions `1+2j`, `1+2j+1`, each carrying
the bit-vector of marks that land on it.  This file provides that **blocks form**
(`markAtN_wrappedFlat`), via an offset-generalised recursive marker `markSeg` that
distributes over `++` and over `flatten ∘ replicate`, together with the run-side
primitives: the unmarked single step `fStepN`, the unmarked block map `bFN`, and the
**unmarked-segment fold** (`foldl_blocks_unmarked`): folding the DFA over a run of
mark-free blocks is the `bFN` iterate.  These are the GA-2 ingredients for the
separated-group shift lemma (`acceptsN_moveGroup` below), which drives the growth
collapse (GA-3).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`): pure list/automaton algebra.
-/
import RequestProject.MSOMarkN

namespace SliceMarkN

open Step MSOMarkN

/-! ## The offset-generalised marker -/

/-- The mark bit-vector carried by position `q` for the coordinate tuple `ī`. -/
def bitsAt (m : ℕ) (ī : Fin m → ℕ) (q : ℕ) : Fin m → Bool :=
  fun i => decide (q = ī i)

/-- The marked segment contributed by `w` when it sits at offset `off` of the full
word: the letter of `w` at relative position `j` carries mark `i` exactly when
`off + j = ī i`. -/
def markSeg (m : ℕ) : List Step → (Fin m → ℕ) → ℕ → List (MarkedN m)
  | [], _, _ => []
  | a :: w, ī, off => mkLetter m a (bitsAt m ī off) :: markSeg m w ī (off + 1)

@[simp] theorem markSeg_nil (m : ℕ) (ī : Fin m → ℕ) (off : ℕ) :
    markSeg m [] ī off = [] := rfl

theorem markSeg_cons (m : ℕ) (a : Step) (w : List Step) (ī : Fin m → ℕ) (off : ℕ) :
    markSeg m (a :: w) ī off
      = mkLetter m a (bitsAt m ī off) :: markSeg m w ī (off + 1) := rfl

@[simp] theorem markSeg_length (m : ℕ) (w : List Step) (ī : Fin m → ℕ) :
    ∀ off, (markSeg m w ī off).length = w.length := by
  induction w with
  | nil => intro off; rfl
  | cons a w ih =>
      intro off
      rw [markSeg_cons, List.length_cons, List.length_cons, ih (off + 1)]

/-- `markAtN` is the offset-`0` marked segment. -/
theorem markAtN_eq_markSeg (m : ℕ) (w : List Step) (ī : Fin m → ℕ) :
    markAtN m w ī = markSeg m w ī 0 := by
  apply List.ext_getElem
  · rw [markAtN_length, markSeg_length]
  · intro j h1 h2
    have hjw : j < w.length := by rwa [markAtN_length] at h1
    -- the `markAtN` side
    have hL : (markAtN m w ī)[j] = mkLetter m w[j] (fun i => decide (j = ī i)) := by
      have := markAtN_getElem? m w ī j hjw
      rw [List.getElem?_eq_getElem h1] at this
      exact Option.some.inj this
    -- the `markSeg` side, by induction with a generalised offset
    have hR : ∀ (w : List Step) (off j : ℕ) (hj : j < w.length),
        (markSeg m w ī off)[j]'(by rw [markSeg_length]; exact hj)
          = mkLetter m w[j] (bitsAt m ī (off + j)) := by
      intro w
      induction w with
      | nil => intro off j hj; exact absurd hj (by simp)
      | cons a w ih =>
          intro off j hj
          cases j with
          | zero =>
              show mkLetter m a (bitsAt m ī off) = mkLetter m a (bitsAt m ī (off + 0))
              rw [Nat.add_zero]
          | succ j =>
              have hj' : j < w.length := by simpa using hj
              simp only [markSeg_cons, List.getElem_cons_succ]
              rw [ih (off + 1) j hj']
              have harg : off + 1 + j = off + (j + 1) := by omega
              rw [harg]
    rw [hL, hR w 0 j hjw]
    congr 1
    funext i
    show decide (j = ī i) = decide (0 + j = ī i)
    rw [Nat.zero_add]

theorem markSeg_append (m : ℕ) (w₁ w₂ : List Step) (ī : Fin m → ℕ) :
    ∀ off, markSeg m (w₁ ++ w₂) ī off
      = markSeg m w₁ ī off ++ markSeg m w₂ ī (off + w₁.length) := by
  induction w₁ with
  | nil => intro off; simp
  | cons a w₁ ih =>
      intro off
      rw [List.cons_append, markSeg_cons, markSeg_cons, ih (off + 1), List.cons_append]
      have harg : off + 1 + w₁.length = off + (a :: w₁).length := by
        rw [List.length_cons]
        omega
      rw [harg]

theorem markSeg_replicate_flatten (m : ℕ) (l : List Step) (ī : Fin m → ℕ) :
    ∀ (n off : ℕ),
      markSeg m ((List.replicate n l).flatten) ī off
        = (List.range n).flatMap (fun j => markSeg m l ī (off + j * l.length))
  | 0, off => by simp
  | (n + 1), off => by
      rw [List.replicate_succ, List.flatten_cons, markSeg_append,
        markSeg_replicate_flatten m l ī n (off + l.length),
        List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      congr 1
      · congr 1
        omega
      · refine List.flatMap_congr (fun j _ => ?_)
        congr 1
        rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul]
        omega

/-! ## The blocks form of the marked slice word -/

/-- **The blocks form**: the `m`-marked slice word is the pre letter, then per block
`j < n` the two letters at positions `1+2j` and `1+2j+1`, then the suffix letter —
each carrying its mark bit-vector. -/
theorem markAtN_wrappedFlat (m n : ℕ) (ī : Fin m → ℕ) :
    markAtN m (wrappedFlat n) ī
      = mkLetter m U (bitsAt m ī 0)
        :: ((List.range n).flatMap (fun j =>
              [mkLetter m U (bitsAt m ī (1 + 2 * j)),
               mkLetter m D (bitsAt m ī (1 + 2 * j + 1))]))
        ++ [mkLetter m D (bitsAt m ī (1 + 2 * n))] := by
  rw [markAtN_eq_markSeg, wrappedFlat, markSeg_append, markSeg_append,
    markSeg_replicate_flatten]
  have hofflen : 0 + ([U] ++ (List.replicate n [U, D]).flatten).length = 1 + 2 * n := by
    simp only [List.length_append, List.length_flatten, List.map_replicate,
      List.sum_replicate, List.length_cons, List.length_nil, smul_eq_mul]
    omega
  rw [hofflen]
  rw [show markSeg m [U] ī 0 = [mkLetter m U (bitsAt m ī 0)] from rfl,
    show markSeg m [D] ī (1 + 2 * n) = [mkLetter m D (bitsAt m ī (1 + 2 * n))] from rfl]
  rw [List.singleton_append, List.cons_append]
  congr 1
  congr 1
  refine List.flatMap_congr (fun j _ => ?_)
  show markSeg m [U, D] ī (0 + [U].length + j * [U, D].length)
      = [mkLetter m U (bitsAt m ī (1 + 2 * j)), mkLetter m D (bitsAt m ī (1 + 2 * j + 1))]
  have harg : 0 + [U].length + j * [U, D].length = 1 + 2 * j := by
    simp only [List.length_cons, List.length_nil]
    ring
  rw [harg]
  rfl

/-! ## The unmarked block map and unmarked-segment folds -/

variable {m : ℕ} (M : SliceMSO.DetAuto (MarkedN m))

/-- The unmarked single step: read `a` with every mark track off. -/
def fStepN (q : M.Q) (a : Step) : M.Q := M.δ q (mkLetter m a (fun _ => false))

/-- The unmarked block map: read one mark-free block `UD`. -/
def bFN (q : M.Q) : M.Q := fStepN M (fStepN M q U) D

/-- A position carrying no marks yields the all-false bit-vector. -/
theorem bitsAt_eq_false (ī : Fin m → ℕ) (q : ℕ) (h : ∀ i, ī i ≠ q) :
    bitsAt m ī q = fun _ => false := by
  funext i
  exact decide_eq_false (fun hc => h i hc.symm)

/-- **Unmarked-segment fold**: folding the DFA over the blocks `[a, a+len)` when no
mark lands in them is the `bFN`-iterate. -/
theorem foldl_blocks_unmarked (ī : Fin m → ℕ) :
    ∀ (len a : ℕ) (q : M.Q),
      (∀ j, a ≤ j → j < a + len → ∀ i, ī i ≠ 1 + 2 * j ∧ ī i ≠ 1 + 2 * j + 1) →
      List.foldl M.δ q ((List.range' a len).flatMap (fun j =>
          [mkLetter m U (bitsAt m ī (1 + 2 * j)),
           mkLetter m D (bitsAt m ī (1 + 2 * j + 1))]))
        = (bFN M)^[len] q
  | 0, a, q, _ => by simp
  | (len + 1), a, q, h => by
      rw [List.range'_succ, List.flatMap_cons, List.foldl_append]
      have hU : bitsAt m ī (1 + 2 * a) = fun _ => false :=
        bitsAt_eq_false ī _ (fun i => (h a (le_refl a) (by omega) i).1)
      have hD : bitsAt m ī (1 + 2 * a + 1) = fun _ => false :=
        bitsAt_eq_false ī _ (fun i => (h a (le_refl a) (by omega) i).2)
      have hblock : List.foldl M.δ q
          [mkLetter m U (bitsAt m ī (1 + 2 * a)),
           mkLetter m D (bitsAt m ī (1 + 2 * a + 1))] = bFN M q := by
        rw [hU, hD]
        rfl
      rw [hblock, foldl_blocks_unmarked ī len (a + 1) (bFN M q)
        (fun j hj1 hj2 i => h j (by omega) (by omega) i),
        ← Function.iterate_succ_apply]

/-- Acceptance through the blocks form. -/
theorem acceptsN_blocks (n : ℕ) (ī : Fin m → ℕ) :
    M.accepts (markAtN m (wrappedFlat n) ī) ↔
      M.accept (List.foldl M.δ
        (M.δ M.q0 (mkLetter m U (bitsAt m ī 0)))
        (((List.range n).flatMap (fun j =>
            [mkLetter m U (bitsAt m ī (1 + 2 * j)),
             mkLetter m D (bitsAt m ī (1 + 2 * j + 1))]))
          ++ [mkLetter m D (bitsAt m ī (1 + 2 * n))])) := by
  simp only [SliceMSO.DetAuto.accepts]
  rw [markAtN_wrappedFlat, List.cons_append, List.foldl_cons]

/-! ## The separated-group shift lemma (GA-2) -/

/-- The iterate FUNCTION `bFN^[g]` is eventually periodic in `g` (`M.Q → M.Q` is
finite) — the `bFN` twin of `bF_func_iterate_eventuallyPeriodic`. -/
theorem bFN_func_iterate_eventuallyPeriodic :
    ∃ mv pv : ℕ, 1 ≤ pv ∧ ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g] := by
  have := M.fintypeQ
  obtain ⟨mv, pv, hpv, hper⟩ :=
    SliceAutomata.iterate_eventuallyPeriodic (fun g : M.Q → M.Q => bFN M ∘ g) id
  have key : ∀ k, (fun g : M.Q → M.Q => bFN M ∘ g)^[k] id = (bFN M)^[k] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, ← Function.iterate_succ']
  exact ⟨mv, pv, hpv, fun g hg => by rw [← key, ← key]; exact hper g hg⟩

/-- Shift the coordinates lying in the group window `[1+2b, 1+2c)` right by `δ`
blocks (`2δ` positions); the others stay. -/
def shiftGroup (m : ℕ) (ī : Fin m → ℕ) (b c δ : ℕ) : Fin m → ℕ :=
  fun i => if 1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c then ī i + 2 * δ else ī i

/-- Off both group windows the mark bits are unchanged by the shift. -/
theorem shiftGroup_bitsAt_outside {m : ℕ} (ī : Fin m → ℕ) (b c δ q : ℕ)
    (hq1 : ¬ (1 + 2 * b ≤ q ∧ q < 1 + 2 * c))
    (hq2 : ¬ (1 + 2 * (b + δ) ≤ q ∧ q < 1 + 2 * (c + δ))) :
    bitsAt m (shiftGroup m ī b c δ) q = bitsAt m ī q := by
  funext i
  unfold bitsAt shiftGroup
  by_cases hcond : 1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c
  · rw [if_pos hcond]
    show decide (q = ī i + 2 * δ) = decide (q = ī i)
    rw [decide_eq_false (fun h => hq2 ⟨by omega, by omega⟩),
      decide_eq_false (fun h => hq1 ⟨by omega, by omega⟩)]
  · rw [if_neg hcond]

/-- Inside the group window the shifted bits at the shifted position match the
original bits, provided every non-group coordinate avoids the enlarged window. -/
theorem shiftGroup_bitsAt_inside {m : ℕ} (ī : Fin m → ℕ) (b c δ q : ℕ)
    (hq1 : 1 + 2 * b ≤ q) (hq2 : q < 1 + 2 * c)
    (havoid : ∀ i, (1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c)
      ∨ ī i < 1 + 2 * b ∨ 1 + 2 * (c + δ) ≤ ī i) :
    bitsAt m (shiftGroup m ī b c δ) (q + 2 * δ) = bitsAt m ī q := by
  funext i
  unfold bitsAt shiftGroup
  rcases havoid i with hin | hlow | hhigh
  · rw [if_pos hin]
    show decide (q + 2 * δ = ī i + 2 * δ) = decide (q = ī i)
    exact decide_eq_decide.mpr (by omega)
  · rw [if_neg (by omega)]
    show decide (q + 2 * δ = ī i) = decide (q = ī i)
    rw [decide_eq_false (by omega), decide_eq_false (by omega)]
  · rw [if_neg (by omega)]
    show decide (q + 2 * δ = ī i) = decide (q = ī i)
    rw [decide_eq_false (by omega), decide_eq_false (by omega)]

/-- **The separated-group shift lemma** (route GA-2).  If the marks of `ī` split into
a LEFT part (positions `< 1+2a`), a GROUP (positions in `[1+2b, 1+2c)`), and a RIGHT
part (positions `≥ 1+2d`), with `a ≤ b ≤ c`, `c + δ ≤ d ≤ n`, then shifting the group
right by `δ` blocks preserves acceptance, provided the `bFN`-iterates of the two gap
lengths agree (`hiter1`/`hiter2` — supplied by eventual periodicity when the gaps are
beyond the threshold and `δ` is a multiple of the period). -/
theorem acceptsN_moveGroup (n : ℕ) (ī : Fin m → ℕ) (a b c d δ : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c + δ ≤ d) (hdn : d ≤ n)
    (hclass : ∀ i, ī i < 1 + 2 * a ∨ (1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c)
      ∨ 1 + 2 * d ≤ ī i)
    (hiter1 : (bFN M)^[b + δ - a] = (bFN M)^[b - a])
    (hiter2 : (bFN M)^[d - (c + δ)] = (bFN M)^[d - c]) :
    M.accepts (markAtN m (wrappedFlat n) (shiftGroup m ī b c δ))
      ↔ M.accepts (markAtN m (wrappedFlat n) ī) := by
  have havoid : ∀ i, (1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c)
      ∨ ī i < 1 + 2 * b ∨ 1 + 2 * (c + δ) ≤ ī i := by
    intro i
    rcases hclass i with h | h | h
    · right; left; omega
    · left; exact h
    · right; right; omega
  rw [acceptsN_blocks, acceptsN_blocks]
  -- the pre and suffix letters agree
  have hpre : bitsAt m (shiftGroup m ī b c δ) 0 = bitsAt m ī 0 :=
    shiftGroup_bitsAt_outside ī b c δ 0 (by omega) (by omega)
  have hsuf : bitsAt m (shiftGroup m ī b c δ) (1 + 2 * n) = bitsAt m ī (1 + 2 * n) :=
    shiftGroup_bitsAt_outside ī b c δ (1 + 2 * n) (by omega) (by omega)
  rw [hpre, hsuf]
  rw [List.foldl_append, List.foldl_append]
  -- it remains to identify the two block folds
  set s0 : M.Q := M.δ M.q0 (mkLetter m U (bitsAt m ī 0)) with hs0
  have hkey : List.foldl M.δ s0 ((List.range n).flatMap (fun j =>
        [mkLetter m U (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * j)),
         mkLetter m D (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * j + 1))]))
      = List.foldl M.δ s0 ((List.range n).flatMap (fun j =>
        [mkLetter m U (bitsAt m ī (1 + 2 * j)),
         mkLetter m D (bitsAt m ī (1 + 2 * j + 1))])) := by
    -- split each side into its five segments
    have hsplitR : List.range n
        = List.range' 0 a ++ (List.range' a (b - a) ++ (List.range' b (c - b)
            ++ (List.range' c (d - c) ++ List.range' d (n - d)))) := by
      rw [List.range_eq_range']
      conv_lhs => rw [show n = a + ((b - a) + ((c - b) + ((d - c) + (n - d))))
        from by omega]
      rw [← List.range'_append_1, ← List.range'_append_1, ← List.range'_append_1,
        ← List.range'_append_1,
        show (0 : ℕ) + a = a from by omega,
        show a + (b - a) = b from by omega,
        show b + (c - b) = c from by omega,
        show c + (d - c) = d from by omega]
    have hsplitL : List.range n
        = List.range' 0 a ++ (List.range' a (b + δ - a) ++ (List.range' (b + δ) (c - b)
            ++ (List.range' (c + δ) (d - (c + δ)) ++ List.range' d (n - d)))) := by
      rw [List.range_eq_range']
      conv_lhs => rw [show n = a + ((b + δ - a) + ((c - b) + ((d - (c + δ)) + (n - d))))
        from by omega]
      rw [← List.range'_append_1, ← List.range'_append_1, ← List.range'_append_1,
        ← List.range'_append_1,
        show (0 : ℕ) + a = a from by omega,
        show a + (b + δ - a) = b + δ from by omega,
        show b + δ + (c - b) = c + δ from by omega,
        show c + δ + (d - (c + δ)) = d from by omega]
    conv_lhs => rw [hsplitL]
    conv_rhs => rw [hsplitR]
    simp only [List.flatMap_append, List.foldl_append]
    -- segment 0: `[0, a)` — bits agree
    have hseg0 : ((List.range' 0 a).flatMap (fun j =>
          [mkLetter m U (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * j)),
           mkLetter m D (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * j + 1))]))
        = ((List.range' 0 a).flatMap (fun j =>
          [mkLetter m U (bitsAt m ī (1 + 2 * j)),
           mkLetter m D (bitsAt m ī (1 + 2 * j + 1))])) := by
      refine List.flatMap_congr (fun j hj => ?_)
      have hja : j < a := by
        have := List.mem_range'_1.mp hj
        omega
      rw [shiftGroup_bitsAt_outside ī b c δ (1 + 2 * j) (by omega) (by omega),
        shiftGroup_bitsAt_outside ī b c δ (1 + 2 * j + 1) (by omega) (by omega)]
    rw [hseg0]
    -- segment 4: `[d, n)` — bits agree
    have hseg4 : ((List.range' d (n - d)).flatMap (fun j =>
          [mkLetter m U (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * j)),
           mkLetter m D (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * j + 1))]))
        = ((List.range' d (n - d)).flatMap (fun j =>
          [mkLetter m U (bitsAt m ī (1 + 2 * j)),
           mkLetter m D (bitsAt m ī (1 + 2 * j + 1))])) := by
      refine List.flatMap_congr (fun j hj => ?_)
      have hjd : d ≤ j := by
        have := List.mem_range'_1.mp hj
        omega
      rw [shiftGroup_bitsAt_outside ī b c δ (1 + 2 * j) (by omega) (by omega),
        shiftGroup_bitsAt_outside ī b c δ (1 + 2 * j + 1) (by omega) (by omega)]
    rw [hseg4]
    -- segment 2: the group, reindexed by `+δ`
    have hseg2 : ((List.range' (b + δ) (c - b)).flatMap (fun j =>
          [mkLetter m U (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * j)),
           mkLetter m D (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * j + 1))]))
        = ((List.range' b (c - b)).flatMap (fun j =>
          [mkLetter m U (bitsAt m ī (1 + 2 * j)),
           mkLetter m D (bitsAt m ī (1 + 2 * j + 1))])) := by
      rw [List.range'_eq_map_range, List.range'_eq_map_range,
        List.flatMap_map, List.flatMap_map]
      refine List.flatMap_congr (fun t ht => ?_)
      have htc : t < c - b := List.mem_range.mp ht
      have e1 : 1 + 2 * (b + δ + t) = 1 + 2 * (b + t) + 2 * δ := by omega
      have e2 : 1 + 2 * (b + t) + 2 * δ + 1 = (1 + 2 * (b + t) + 1) + 2 * δ := by omega
      show [mkLetter m U (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * (b + δ + t))),
            mkLetter m D (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * (b + δ + t) + 1))]
          = [mkLetter m U (bitsAt m ī (1 + 2 * (b + t))),
             mkLetter m D (bitsAt m ī (1 + 2 * (b + t) + 1))]
      rw [e1, e2,
        shiftGroup_bitsAt_inside ī b c δ (1 + 2 * (b + t)) (by omega) (by omega) havoid,
        shiftGroup_bitsAt_inside ī b c δ (1 + 2 * (b + t) + 1) (by omega) (by omega)
          havoid]
    rw [hseg2]
    -- segments 1 and 3: unmarked gaps fold to `bFN`-iterates
    have hgapL : ∀ (q : M.Q), List.foldl M.δ q ((List.range' a (b + δ - a)).flatMap
        (fun j => [mkLetter m U (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * j)),
                   mkLetter m D (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * j + 1))]))
        = (bFN M)^[b + δ - a] q := by
      intro q
      refine foldl_blocks_unmarked M _ _ _ _ (fun j hj1 hj2 i => ?_)
      unfold shiftGroup
      by_cases hcond : 1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c
      · rw [if_pos hcond]
        omega
      · rw [if_neg hcond]
        rcases hclass i with h | h | h
        · omega
        · exact absurd h hcond
        · omega
    have hgapL' : ∀ (q : M.Q), List.foldl M.δ q ((List.range' a (b - a)).flatMap
        (fun j => [mkLetter m U (bitsAt m ī (1 + 2 * j)),
                   mkLetter m D (bitsAt m ī (1 + 2 * j + 1))]))
        = (bFN M)^[b - a] q := by
      intro q
      refine foldl_blocks_unmarked M _ _ _ _ (fun j hj1 hj2 i => ?_)
      rcases hclass i with h | h | h
      · omega
      · omega
      · omega
    have hgapR : ∀ (q : M.Q), List.foldl M.δ q ((List.range' (c + δ) (d - (c + δ))).flatMap
        (fun j => [mkLetter m U (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * j)),
                   mkLetter m D (bitsAt m (shiftGroup m ī b c δ) (1 + 2 * j + 1))]))
        = (bFN M)^[d - (c + δ)] q := by
      intro q
      refine foldl_blocks_unmarked M _ _ _ _ (fun j hj1 hj2 i => ?_)
      unfold shiftGroup
      by_cases hcond : 1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c
      · rw [if_pos hcond]
        omega
      · rw [if_neg hcond]
        rcases hclass i with h | h | h
        · omega
        · exact absurd h hcond
        · omega
    have hgapR' : ∀ (q : M.Q), List.foldl M.δ q ((List.range' c (d - c)).flatMap
        (fun j => [mkLetter m U (bitsAt m ī (1 + 2 * j)),
                   mkLetter m D (bitsAt m ī (1 + 2 * j + 1))]))
        = (bFN M)^[d - c] q := by
      intro q
      refine foldl_blocks_unmarked M _ _ _ _ (fun j hj1 hj2 i => ?_)
      rcases hclass i with h | h | h
      · omega
      · omega
      · omega
    rw [hgapL, hgapL', hgapR, hgapR', hiter1, hiter2]
  rw [hkey]

end SliceMarkN
