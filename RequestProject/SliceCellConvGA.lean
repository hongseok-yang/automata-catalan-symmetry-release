/-
# GA-7.0 — the cell-tuple convolution form (`SliceFasCountGA` namespace, part 1/3)

The foundation of the general-arity counting layer.  The marked-DFA acceptance of a CELL TUPLE decomposes, on the bulk
window, as fixed boundary data around two unmarked-block `bFN`-iterates:

* the hit-functions and the five per-segment letter identifications;
* the per-cell `clusterWidth` and the width-exact gap lemma;
* `acceptsN_cellTuple_conv` (uniform window) and `acceptsN_cellTuple_convW`
  (the width-exact form on the FULL canonical bulk window `Z ≤ t`, `t+W+Z ≤ n`);
* the EP corollaries `acceptsN_cellTuple_baseZ_EP` / `acceptsN_clusterFree_EP`.

Axiom-clean: pure word combinatorics over the landed `SliceMarkN` blocks form.
All three parts share the `SliceFasCountGA` namespace.
-/
import RequestProject.SliceFasSelectorGA

namespace SliceFasCountGA

open WRP Step SliceFamilyCell SliceDstarGA SliceDstarGateGA SliceFasGatesGA
  SliceThreshold SliceAffine SliceOrder MSOMarkN SliceMarkN SliceFasSelectorGA
open scoped Classical

/-! ## The hit-functions: which coordinate fires where, `(t, n)`-free -/

/-- The coordinate fires at the pre position `0`. -/
def hitPre {Z : ℕ} (r : RegionSpec Z) : Bool :=
  match r with
  | .pre => true
  | _ => false

/-- The coordinate fires at the front position `1 + 2j + e` (`j < Z`). -/
def hitFront {Z : ℕ} (r : RegionSpec Z) (j : ℕ) (e : Bool) : Bool :=
  match r with
  | .front f e' => decide (f.1 = j ∧ e' = e)
  | _ => false

/-- The coordinate fires at the cluster position `1 + 2(t + δ) + e` (`δ < Z`). -/
def hitCluster {Z : ℕ} (r : RegionSpec Z) (δ : ℕ) (e : Bool) : Bool :=
  match r with
  | .cluster δ' e' => decide (δ'.1 = δ ∧ e' = e)
  | _ => false

/-- The coordinate fires at the back position `1 + 2(n - Z + a) + e` (`a < Z`,
relative pattern: back pin `l` sits at `a = Z - 1 - l`). -/
def hitBack {Z : ℕ} (r : RegionSpec Z) (a : ℕ) (e : Bool) : Bool :=
  match r with
  | .back l e' => decide (l.1 = Z - 1 - a ∧ e' = e)
  | _ => false

/-- The coordinate fires at the suffix position `1 + 2n`. -/
def hitSuf {Z : ℕ} (r : RegionSpec Z) : Bool :=
  match r with
  | .suf => true
  | _ => false

/-! ## The per-cell cluster width -/

section WidthDefs

variable {Z k : ℕ}

/-- The cluster width of a descriptor tuple: one past the largest cluster offset
(`0` for cluster-free tuples). -/
noncomputable def clusterWidth (rs : Fin k → RegionSpec Z) : ℕ :=
  Finset.univ.sup (fun i => match rs i with
    | RegionSpec.cluster δ _ => δ.1 + 1
    | _ => 0)

theorem cluster_lt_width (rs : Fin k → RegionSpec Z) (i : Fin k) (δ : Fin Z)
    (e : Bool) (h : rs i = .cluster δ e) : δ.1 < clusterWidth rs := by
  have hle := Finset.le_sup (f := fun i => match rs i with
    | RegionSpec.cluster δ _ => δ.1 + 1
    | _ => 0) (Finset.mem_univ i)
  rw [h] at hle
  exact hle

theorem clusterWidth_le (rs : Fin k → RegionSpec Z) : clusterWidth rs ≤ Z := by
  refine Finset.sup_le (fun i _ => ?_)
  rcases hri : rs i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;> simp only []
  · omega
  · omega
  · omega
  · omega
  · have := δ.isLt
    omega

end WidthDefs

/-! ## The per-segment letter identifications -/

section BitLemmas

variable {Z k : ℕ} (rs : Fin k → RegionSpec Z)

/-- The pre letter is fixed. -/
theorem bits_pre (t n : ℕ) (_hZt : Z ≤ t) (_htn : t + Z ≤ n) :
    bitsAt k (cellTuple rs t n) 0 = fun i => hitPre (rs i) := by
  funext i
  show decide (0 = (rs i).posAt t n) = hitPre (rs i)
  rcases hri : rs i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    simp only [RegionSpec.posAt, hitPre]
  · simp
  · exact decide_eq_false (by omega)
  · exact decide_eq_false (by rcases e with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · exact decide_eq_false (by rcases e with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · exact decide_eq_false (by rcases e with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)

/-- The front letters are fixed: position `1 + 2j + e.toNat` for `j < Z`. -/
theorem bits_front (t n j : ℕ) (hj : j < Z) (e : Bool) (hZt : Z ≤ t)
    (htn : t + Z ≤ n) :
    bitsAt k (cellTuple rs t n) (1 + 2 * j + e.toNat)
      = fun i => hitFront (rs i) j e := by
  funext i
  show decide (1 + 2 * j + e.toNat = (rs i).posAt t n) = hitFront (rs i) j e
  rcases hri : rs i with _ | _ | ⟨f, e'⟩ | ⟨l, e'⟩ | ⟨δ, e'⟩ <;>
    simp only [RegionSpec.posAt, hitFront]
  · exact decide_eq_false (by rcases e with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · exact decide_eq_false (by rcases e with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · refine decide_eq_decide.mpr ?_
    have hf := f.isLt
    rcases e with _ | _ <;> rcases e' with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true]
    · constructor
      · intro h
        exact ⟨by omega, by trivial⟩
      · rintro ⟨h1, -⟩
        omega
    · constructor
      · intro h
        exact absurd h (by omega)
      · rintro ⟨-, h2⟩
        exact absurd h2 (by simp)
    · constructor
      · intro h
        exact absurd h (by omega)
      · rintro ⟨-, h2⟩
        exact absurd h2 (by simp)
    · constructor
      · intro h
        exact ⟨by omega, by trivial⟩
      · rintro ⟨h1, -⟩
        omega
  · exact decide_eq_false (by
      have hl := l.isLt
      rcases e with _ | _ <;> rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · exact decide_eq_false (by
      have hδ := δ.isLt
      rcases e with _ | _ <;> rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)

/-- The cluster letters are fixed relative to the base: position
`1 + 2(t + δ) + e.toNat` for `δ < Z`. -/
theorem bits_cluster (t n δ : ℕ) (hδ : δ < Z) (e : Bool) (hZt : Z ≤ t)
    (hδn : t + δ + Z + 1 ≤ n) :
    bitsAt k (cellTuple rs t n) (1 + 2 * (t + δ) + e.toNat)
      = fun i => hitCluster (rs i) δ e := by
  funext i
  show decide (1 + 2 * (t + δ) + e.toNat = (rs i).posAt t n)
    = hitCluster (rs i) δ e
  rcases hri : rs i with _ | _ | ⟨f, e'⟩ | ⟨l, e'⟩ | ⟨δ', e'⟩ <;>
    simp only [RegionSpec.posAt, hitCluster]
  · exact decide_eq_false (by rcases e with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · exact decide_eq_false (by rcases e with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · exact decide_eq_false (by
      have hf := f.isLt
      rcases e with _ | _ <;> rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · exact decide_eq_false (by
      have hl := l.isLt
      rcases e with _ | _ <;> rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · refine decide_eq_decide.mpr ?_
    have hδ' := δ'.isLt
    rcases e with _ | _ <;> rcases e' with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true]
    · constructor
      · intro h
        exact ⟨by omega, by trivial⟩
      · rintro ⟨h1, -⟩
        omega
    · constructor
      · intro h
        exact absurd h (by omega)
      · rintro ⟨-, h2⟩
        exact absurd h2 (by simp)
    · constructor
      · intro h
        exact absurd h (by omega)
      · rintro ⟨-, h2⟩
        exact absurd h2 (by simp)
    · constructor
      · intro h
        exact ⟨by omega, by trivial⟩
      · rintro ⟨h1, -⟩
        omega

/-- The back letters are fixed RELATIVE patterns: position
`1 + 2(n - Z + a) + e.toNat` for `a < Z`. -/
theorem bits_back (t n a : ℕ) (ha : a < Z) (e : Bool) (hZt : Z ≤ t)
    (hwin : t + clusterWidth rs + Z ≤ n) :
    bitsAt k (cellTuple rs t n) (1 + 2 * (n - Z + a) + e.toNat)
      = fun i => hitBack (rs i) a e := by
  funext i
  show decide (1 + 2 * (n - Z + a) + e.toNat = (rs i).posAt t n)
    = hitBack (rs i) a e
  rcases hri : rs i with _ | _ | ⟨f, e'⟩ | ⟨l, e'⟩ | ⟨δ, e'⟩ <;>
    simp only [RegionSpec.posAt, hitBack]
  · exact decide_eq_false (by rcases e with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · exact decide_eq_false (by rcases e with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · exact decide_eq_false (by
      have hf := f.isLt
      rcases e with _ | _ <;> rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · refine decide_eq_decide.mpr ?_
    have hl := l.isLt
    rcases e with _ | _ <;> rcases e' with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true]
    · constructor
      · intro h
        exact ⟨by omega, by trivial⟩
      · rintro ⟨h1, -⟩
        omega
    · constructor
      · intro h
        exact absurd h (by omega)
      · rintro ⟨-, h2⟩
        exact absurd h2 (by simp)
    · constructor
      · intro h
        exact absurd h (by omega)
      · rintro ⟨-, h2⟩
        exact absurd h2 (by simp)
    · constructor
      · intro h
        exact ⟨by omega, by trivial⟩
      · rintro ⟨h1, -⟩
        omega
  · exact decide_eq_false (by
      have hδ := cluster_lt_width rs i δ e' hri
      have hWZ := clusterWidth_le rs
      rcases e with _ | _ <;> rcases e' with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)

/-- The suffix letter is fixed. -/
theorem bits_suf (t n : ℕ) (_hZt : Z ≤ t) (htn : t + Z ≤ n) :
    bitsAt k (cellTuple rs t n) (1 + 2 * n) = fun i => hitSuf (rs i) := by
  funext i
  show decide (1 + 2 * n = (rs i).posAt t n) = hitSuf (rs i)
  rcases hri : rs i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    simp only [RegionSpec.posAt, hitSuf]
  · exact decide_eq_false (by omega)
  · simp
  · exact decide_eq_false (by
      have hf := f.isLt
      rcases e with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · exact decide_eq_false (by
      have hl := l.isLt
      rcases e with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)
  · exact decide_eq_false (by
      have hδ := δ.isLt
      rcases e with _ | _ <;>
        simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)

/-- The two unmarked gaps avoid every coordinate. -/
theorem bits_gap (t n j : ℕ) (hZt : Z ≤ t) (htn : t + 2 * Z + 1 ≤ n)
    (hgap : (Z ≤ j ∧ j < t) ∨ (t + Z ≤ j ∧ j < n - Z)) :
    ∀ i, cellTuple rs t n i ≠ 1 + 2 * j ∧ cellTuple rs t n i ≠ 1 + 2 * j + 1 := by
  intro i
  show (rs i).posAt t n ≠ 1 + 2 * j ∧ (rs i).posAt t n ≠ 1 + 2 * j + 1
  rcases hri : rs i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    simp only [RegionSpec.posAt]
  · constructor <;> omega
  · constructor <;> omega
  · have hf := f.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;>
      constructor <;> omega
  · have hl := l.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;>
      constructor <;> omega
  · have hδ := δ.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;>
      constructor <;> omega

end BitLemmas

/-! ## GA-7.0: the cell-tuple convolution decomposition -/

section CellConv

variable {Z k : ℕ} (M : SliceMSO.DetAuto (MarkedN k)) (rs : Fin k → RegionSpec Z)

/-- The fixed pre+front prefix state. -/
noncomputable def cellQ0 : M.Q :=
  List.foldl M.δ (M.δ M.q0 (mkLetter k U (fun i => hitPre (rs i))))
    ((List.range Z).flatMap (fun j =>
      [mkLetter k U (fun i => hitFront (rs i) j false),
       mkLetter k D (fun i => hitFront (rs i) j true)]))

/-- The fixed cluster-window map. -/
noncomputable def cellGcl (q : M.Q) : M.Q :=
  List.foldl M.δ q ((List.range Z).flatMap (fun d =>
    [mkLetter k U (fun i => hitCluster (rs i) d false),
     mkLetter k D (fun i => hitCluster (rs i) d true)]))

/-- The fixed back+suffix acceptance. -/
def cellAcc (q : M.Q) : Prop :=
  M.accept (M.δ (List.foldl M.δ q ((List.range Z).flatMap (fun a =>
      [mkLetter k U (fun i => hitBack (rs i) a false),
       mkLetter k D (fun i => hitBack (rs i) a true)])))
    (mkLetter k D (fun i => hitSuf (rs i))))

/-- **The cell-tuple convolution form** (GA-7.0): on the bulk window, the marked
acceptance of the cell at base `t` is the fixed boundary data around the two
`bFN`-iterate gaps. -/
theorem acceptsN_cellTuple_conv (t n : ℕ) (hZt : Z ≤ t) (htn : t + 2 * Z + 1 ≤ n) :
    M.accepts (markAtN k (wrappedFlat n) (cellTuple rs t n)) ↔
      cellAcc M rs ((bFN M)^[n - 2 * Z - t]
        (cellGcl M rs ((bFN M)^[t - Z] (cellQ0 M rs)))) := by
  rw [acceptsN_blocks]
  -- the five-segment split
  have hsplit : List.range n
      = List.range' 0 Z ++ (List.range' Z (t - Z) ++ (List.range' t Z
          ++ (List.range' (t + Z) (n - 2 * Z - t) ++ List.range' (n - Z) Z))) := by
    rw [List.range_eq_range']
    conv_lhs => rw [show n = Z + ((t - Z) + (Z + ((n - 2 * Z - t) + Z)))
      from by omega]
    rw [← List.range'_append_1, ← List.range'_append_1, ← List.range'_append_1,
      ← List.range'_append_1,
      show (0 : ℕ) + Z = Z from by omega,
      show Z + (t - Z) = t from by omega,
      show t + Z + (n - 2 * Z - t) = n - Z from by omega]
  rw [hsplit]
  simp only [List.flatMap_append, List.foldl_append]
  -- the pre letter
  rw [show bitsAt k (cellTuple rs t n) 0 = fun i => hitPre (rs i)
    from bits_pre rs t n hZt (by omega)]
  -- segment 1: the front blocks
  have hseg1 : ((List.range' 0 Z).flatMap (fun j =>
        [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * j)),
         mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * j + 1))]))
      = ((List.range Z).flatMap (fun j =>
        [mkLetter k U (fun i => hitFront (rs i) j false),
         mkLetter k D (fun i => hitFront (rs i) j true)])) := by
    rw [show List.range' 0 Z = List.range Z from List.range_eq_range'.symm]
    refine List.flatMap_congr (fun j hj => ?_)
    have hjZ : j < Z := List.mem_range.mp hj
    have h1 := bits_front rs t n j hjZ false hZt (by omega)
    have h2 := bits_front rs t n j hjZ true hZt (by omega)
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at h1 h2
    rw [h1, h2]
  rw [hseg1]
  -- segment 2: the left unmarked gap
  have hgapL : ∀ q : M.Q, List.foldl M.δ q
      ((List.range' Z (t - Z)).flatMap (fun j =>
        [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * j)),
         mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * j + 1))]))
      = (bFN M)^[t - Z] q := by
    intro q
    exact foldl_blocks_unmarked M (cellTuple rs t n) (t - Z) Z q
      (fun j hj1 hj2 i => bits_gap rs t n j hZt htn (Or.inl ⟨hj1, by omega⟩) i)
  rw [hgapL]
  -- segment 3: the cluster window
  have hseg3 : ((List.range' t Z).flatMap (fun j =>
        [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * j)),
         mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * j + 1))]))
      = ((List.range Z).flatMap (fun d =>
        [mkLetter k U (fun i => hitCluster (rs i) d false),
         mkLetter k D (fun i => hitCluster (rs i) d true)])) := by
    rw [List.range'_eq_map_range, List.flatMap_map]
    refine List.flatMap_congr (fun d hd => ?_)
    have hdZ : d < Z := List.mem_range.mp hd
    show [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * (t + d))),
          mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * (t + d) + 1))] = _
    have h1 := bits_cluster rs t n d hdZ false hZt (by omega)
    have h2 := bits_cluster rs t n d hdZ true hZt (by omega)
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at h1 h2
    rw [h1, h2]
  rw [hseg3]
  -- segment 4: the right unmarked gap
  have hgapR : ∀ q : M.Q, List.foldl M.δ q
      ((List.range' (t + Z) (n - 2 * Z - t)).flatMap (fun j =>
        [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * j)),
         mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * j + 1))]))
      = (bFN M)^[n - 2 * Z - t] q := by
    intro q
    exact foldl_blocks_unmarked M (cellTuple rs t n) (n - 2 * Z - t) (t + Z) q
      (fun j hj1 hj2 i => bits_gap rs t n j hZt htn (Or.inr ⟨hj1, by omega⟩) i)
  rw [hgapR]
  -- segment 5: the back blocks
  have hseg5 : ((List.range' (n - Z) Z).flatMap (fun j =>
        [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * j)),
         mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * j + 1))]))
      = ((List.range Z).flatMap (fun a =>
        [mkLetter k U (fun i => hitBack (rs i) a false),
         mkLetter k D (fun i => hitBack (rs i) a true)])) := by
    rw [List.range'_eq_map_range, List.flatMap_map]
    refine List.flatMap_congr (fun a ha => ?_)
    have haZ : a < Z := List.mem_range.mp ha
    show [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * (n - Z + a))),
          mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * (n - Z + a) + 1))] = _
    have h1 := bits_back rs t n a haZ false hZt
      (by have := clusterWidth_le rs; omega)
    have h2 := bits_back rs t n a haZ true hZt
      (by have := clusterWidth_le rs; omega)
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at h1 h2
    rw [h1, h2]
  rw [hseg5]
  -- the suffix letter
  rw [show bitsAt k (cellTuple rs t n) (1 + 2 * n) = fun i => hitSuf (rs i)
    from bits_suf rs t n hZt (by omega)]
  -- assemble
  rw [cellAcc, cellGcl, cellQ0]
  simp only [List.foldl_cons, List.foldl_nil]

/-- **Boundary-base EP**: the acceptance at the fixed base `Z` is eventually
periodic in `n`. -/
theorem acceptsN_cellTuple_baseZ_EP :
    ∃ p, 1 ≤ p ∧ EventuallyPeriodic
      (fun n => M.accepts (markAtN k (wrappedFlat n) (cellTuple rs Z n))) p := by
  obtain ⟨mv, pv, hpv, hEP⟩ := bFN_func_iterate_eventuallyPeriodic M
  refine ⟨pv, hpv, mv + 3 * Z + 2, fun n hn => ?_⟩
  simp only []
  rw [acceptsN_cellTuple_conv M rs Z (n + pv) le_rfl (by omega),
    acceptsN_cellTuple_conv M rs Z n le_rfl (by omega)]
  have hiter : (bFN M)^[n + pv - 2 * Z - Z] = (bFN M)^[n - 2 * Z - Z] := by
    rw [show n + pv - 2 * Z - Z = (n - 2 * Z - Z) + pv from by omega]
    exact hEP _ (by omega)
  rw [hiter]

/-- **Frozen-cell EP**: the acceptance of a cluster-free cell at ANY fixed base is
eventually periodic in `n`. -/
theorem acceptsN_clusterFree_EP (hcf : ∀ i, clusterFree (rs i)) (t0 : ℕ) :
    ∃ p, 1 ≤ p ∧ EventuallyPeriodic
      (fun n => M.accepts (markAtN k (wrappedFlat n) (cellTuple rs t0 n))) p := by
  obtain ⟨p, hp, m, hEP⟩ := acceptsN_cellTuple_baseZ_EP M rs
  refine ⟨p, hp, m, fun n hn => ?_⟩
  simp only []
  rw [SliceDstarBridgeGA.cellTuple_clusterFree_base rs hcf t0 Z (n + p),
    SliceDstarBridgeGA.cellTuple_clusterFree_base rs hcf t0 Z n]
  exact hEP n hn

end CellConv



/-! ## The per-cell cluster width and the width-exact convolution form -/

section Width

variable {Z k : ℕ}

/-- The two width-exact unmarked gaps avoid every coordinate. -/
theorem bits_gapW (rs : Fin k → RegionSpec Z) (t n j : ℕ) (hZt : Z ≤ t)
    (hwin : t + clusterWidth rs + Z ≤ n)
    (hgap : (Z ≤ j ∧ j < t) ∨ (t + clusterWidth rs ≤ j ∧ j < n - Z)) :
    ∀ i, cellTuple rs t n i ≠ 1 + 2 * j ∧ cellTuple rs t n i ≠ 1 + 2 * j + 1 := by
  intro i
  show (rs i).posAt t n ≠ 1 + 2 * j ∧ (rs i).posAt t n ≠ 1 + 2 * j + 1
  rcases hri : rs i with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    simp only [RegionSpec.posAt]
  · constructor <;> omega
  · constructor <;> omega
  · have hf := f.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;>
      constructor <;> omega
  · have hl := l.isLt
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;>
      constructor <;> omega
  · have hδ := cluster_lt_width rs i δ e hri
    rcases e with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;>
      constructor <;> omega

variable (M : SliceMSO.DetAuto (MarkedN k))

/-- The width-exact cluster-window map. -/
noncomputable def cellGclW (rs : Fin k → RegionSpec Z) (q : M.Q) : M.Q :=
  List.foldl M.δ q ((List.range (clusterWidth rs)).flatMap (fun d =>
    [mkLetter k U (fun i => hitCluster (rs i) d false),
     mkLetter k D (fun i => hitCluster (rs i) d true)]))

/-- **The width-exact convolution form**: valid on the FULL canonical bulk window
`Z ≤ t`, `t + clusterWidth rs + Z ≤ n`. -/
theorem acceptsN_cellTuple_convW (rs : Fin k → RegionSpec Z) (t n : ℕ) (hZt : Z ≤ t)
    (htn : t + clusterWidth rs + Z ≤ n) :
    M.accepts (markAtN k (wrappedFlat n) (cellTuple rs t n)) ↔
      cellAcc M rs ((bFN M)^[n - Z - clusterWidth rs - t]
        (cellGclW M rs ((bFN M)^[t - Z] (cellQ0 M rs)))) := by
  have hWZ := clusterWidth_le rs
  rw [acceptsN_blocks]
  have hsplit : List.range n
      = List.range' 0 Z ++ (List.range' Z (t - Z) ++ (List.range' t (clusterWidth rs)
          ++ (List.range' (t + clusterWidth rs) (n - Z - clusterWidth rs - t)
            ++ List.range' (n - Z) Z))) := by
    rw [List.range_eq_range']
    conv_lhs => rw [show n = Z + ((t - Z) + (clusterWidth rs
      + ((n - Z - clusterWidth rs - t) + Z))) from by omega]
    rw [← List.range'_append_1, ← List.range'_append_1, ← List.range'_append_1,
      ← List.range'_append_1,
      show (0 : ℕ) + Z = Z from by omega,
      show Z + (t - Z) = t from by omega,
      show t + clusterWidth rs + (n - Z - clusterWidth rs - t) = n - Z from by omega]
  rw [hsplit]
  simp only [List.flatMap_append, List.foldl_append]
  rw [show bitsAt k (cellTuple rs t n) 0 = fun i => hitPre (rs i)
    from bits_pre rs t n hZt (by omega)]
  have hseg1 : ((List.range' 0 Z).flatMap (fun j =>
        [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * j)),
         mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * j + 1))]))
      = ((List.range Z).flatMap (fun j =>
        [mkLetter k U (fun i => hitFront (rs i) j false),
         mkLetter k D (fun i => hitFront (rs i) j true)])) := by
    rw [show List.range' 0 Z = List.range Z from List.range_eq_range'.symm]
    refine List.flatMap_congr (fun j hj => ?_)
    have hjZ : j < Z := List.mem_range.mp hj
    have h1 := bits_front rs t n j hjZ false hZt (by omega)
    have h2 := bits_front rs t n j hjZ true hZt (by omega)
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at h1 h2
    rw [h1, h2]
  rw [hseg1]
  have hgapL : ∀ q : M.Q, List.foldl M.δ q
      ((List.range' Z (t - Z)).flatMap (fun j =>
        [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * j)),
         mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * j + 1))]))
      = (bFN M)^[t - Z] q := by
    intro q
    exact foldl_blocks_unmarked M (cellTuple rs t n) (t - Z) Z q
      (fun j hj1 hj2 i => bits_gapW rs t n j hZt htn (Or.inl ⟨hj1, by omega⟩) i)
  rw [hgapL]
  have hseg3 : ((List.range' t (clusterWidth rs)).flatMap (fun j =>
        [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * j)),
         mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * j + 1))]))
      = ((List.range (clusterWidth rs)).flatMap (fun d =>
        [mkLetter k U (fun i => hitCluster (rs i) d false),
         mkLetter k D (fun i => hitCluster (rs i) d true)])) := by
    rw [List.range'_eq_map_range, List.flatMap_map]
    refine List.flatMap_congr (fun d hd => ?_)
    have hdW : d < clusterWidth rs := List.mem_range.mp hd
    show [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * (t + d))),
          mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * (t + d) + 1))] = _
    have h1 := bits_cluster rs t n d (by omega) false hZt (by omega)
    have h2 := bits_cluster rs t n d (by omega) true hZt (by omega)
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at h1 h2
    rw [h1, h2]
  rw [hseg3]
  have hgapR : ∀ q : M.Q, List.foldl M.δ q
      ((List.range' (t + clusterWidth rs) (n - Z - clusterWidth rs - t)).flatMap
        (fun j =>
          [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * j)),
           mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * j + 1))]))
      = (bFN M)^[n - Z - clusterWidth rs - t] q := by
    intro q
    exact foldl_blocks_unmarked M (cellTuple rs t n)
      (n - Z - clusterWidth rs - t) (t + clusterWidth rs) q
      (fun j hj1 hj2 i => bits_gapW rs t n j hZt htn (Or.inr ⟨hj1, by omega⟩) i)
  rw [hgapR]
  have hseg5 : ((List.range' (n - Z) Z).flatMap (fun j =>
        [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * j)),
         mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * j + 1))]))
      = ((List.range Z).flatMap (fun a =>
        [mkLetter k U (fun i => hitBack (rs i) a false),
         mkLetter k D (fun i => hitBack (rs i) a true)])) := by
    rw [List.range'_eq_map_range, List.flatMap_map]
    refine List.flatMap_congr (fun a ha => ?_)
    have haZ : a < Z := List.mem_range.mp ha
    show [mkLetter k U (bitsAt k (cellTuple rs t n) (1 + 2 * (n - Z + a))),
          mkLetter k D (bitsAt k (cellTuple rs t n) (1 + 2 * (n - Z + a) + 1))] = _
    have h1 := bits_back rs t n a haZ false hZt (by omega)
    have h2 := bits_back rs t n a haZ true hZt (by omega)
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at h1 h2
    rw [h1, h2]
  rw [hseg5]
  rw [show bitsAt k (cellTuple rs t n) (1 + 2 * n) = fun i => hitSuf (rs i)
    from bits_suf rs t n hZt (by omega)]
  rw [cellAcc, cellGclW, cellQ0]
  simp only [List.foldl_cons, List.foldl_nil]

end Width

end SliceFasCountGA
