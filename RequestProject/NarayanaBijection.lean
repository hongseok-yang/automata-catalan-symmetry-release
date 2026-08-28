/-
# The height sweep is a bijection on `D_n`, and the Narayana symmetry

Completes components (b) and (d) of the paper's `thm:narayana-sweep`
(§`sec:narayana-sweep`), on top of the proved swap identities
(`NarayanaSweep.lean`) and the WRP membership (`NarayanaWRP.lean`):

* `heightSweep_bijOn` — `H` restricts to a bijection `D_n → D_n`;
* `narayana_symmetry_card` — the card-level Narayana symmetry
  `#{P ∈ D_n : (val, dr) = (j, k)} = #{P ∈ D_n : (val, dr) = (k, j)}`.

The route (design artifact `NARAYANA_BIJ_DESIGN.json`): injectivity of `H` on
Dyck paths by the LEVEL-COUNTING reconstruction — the sorted sweep word
determines, level by level, the per-level `U`/`D` counts of the source (the
crossing identity is the existing `belowU_eq_atMostD`; each positive level of
the sweep opens with a `D` by the `matchD` rightmost-step argument), and then
the per-position rank lemma pins every letter of the source.  Surjectivity is
free from finiteness, exactly as in the paper ("an injection between finite
sets of the same size is onto").

Trust base for the headline theorems: `[propext, Classical.choice, Quot.sound]`.
-/
import RequestProject.NarayanaSweep

open Step

/-! ## SECTION A — enumeration infrastructure -/

instance decidableIsDyckPath : DecidablePred IsDyckPath := fun P =>
  decidable_of_iff
    ((∀ k : ℕ, k ≤ P.length → 0 ≤ height P k) ∧ height P P.length = 0)
    Iff.rfl

/-- All step words of length `L`. -/
def stepWords (L : ℕ) : Finset (List Step) :=
  (Finset.univ : Finset (Fin L → Step)).image List.ofFn

theorem mem_stepWords {L : ℕ} {P : List Step} :
    P ∈ stepWords L ↔ P.length = L := by
  constructor
  · intro h
    rw [stepWords, Finset.mem_image] at h
    obtain ⟨f, -, rfl⟩ := h
    simp
  · intro h
    subst h
    rw [stepWords, Finset.mem_image]
    exact ⟨fun i => P[i], Finset.mem_univ _, List.ofFn_getElem⟩

theorem card_stepWords (L : ℕ) : (stepWords L).card = 2 ^ L := by
  rw [stepWords, Finset.card_image_of_injective _ List.ofFn_injective,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    show Fintype.card Step = 2 from rfl]

/-- The Dyck paths of semilength `n`, as a `Finset`. -/
def dyckFinset (n : ℕ) : Finset (List Step) :=
  (stepWords (2 * n)).filter IsDyckPath

theorem mem_dyckFinset {n : ℕ} {P : List Step} :
    P ∈ dyckFinset n ↔ P ∈ DyckPath n := by
  rw [dyckFinset, Finset.mem_filter, mem_stepWords]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem coe_dyckFinset (n : ℕ) : (dyckFinset n : Set (List Step)) = DyckPath n :=
  Set.ext fun _ => mem_dyckFinset

example : (dyckFinset 2).card = 2 := by decide
example : (dyckFinset 3).card = 5 := by decide

theorem semilength_of_mem_dyckFinset {n : ℕ} {P : List Step}
    (h : P ∈ dyckFinset n) : semilength P = n := by
  rw [mem_dyckFinset] at h
  rw [semilength, h.2, Nat.mul_div_cancel_left n (by norm_num)]

/-- `H` maps `D_n` into `D_n`. -/
theorem heightSweep_mapsTo (n : ℕ) :
    Set.MapsTo heightSweep (DyckPath n) (DyckPath n) := fun P hP =>
  ⟨isDyckPath_heightSweep P hP.1, by rw [length_heightSweep]; exact hP.2⟩

/-- On the finite set `D_n`, injectivity already yields the bijection. -/
theorem heightSweep_bijOn_of_injOn (n : ℕ)
    (hinj : Set.InjOn heightSweep (DyckPath n)) :
    Set.BijOn heightSweep (DyckPath n) (DyckPath n) := by
  refine ⟨heightSweep_mapsTo n, hinj, ?_⟩
  rw [← coe_dyckFinset]
  exact Finset.surjOn_of_injOn_of_card_le _
    (by rw [coe_dyckFinset]; exact heightSweep_mapsTo n)
    (by rw [coe_dyckFinset]; exact hinj) le_rfl

/-! ## SECTION D — hypothesis-free swap wrappers -/

theorem eq_nil_of_isDyckPath_semilength_zero {P : List Step}
    (hP : IsDyckPath P) (h : semilength P = 0) : P = [] := by
  have h1 := count_U_add_count_D P
  have h2 := count_U_eq_count_D_of_isDyckPath P hP
  rw [semilength] at h
  have hlen : P.length = 0 := by omega
  exact List.eq_nil_of_length_eq_zero hlen

/-- The valley/double-rise swap, with no semilength hypothesis. -/
theorem heightSweep_nil : heightSweep [] = [] := by
  unfold heightSweep
  simp

theorem valleys_heightSweep (P : List Step) (hP : IsDyckPath P) :
    valleys (heightSweep P) = doubleRises P := by
  by_cases h : semilength P = 0
  · rw [eq_nil_of_isDyckPath_semilength_zero hP h, heightSweep_nil]
    rfl
  · exact valleys_heightSweep_eq_doubleRises P hP (by omega)

/-- The double-rise/valley swap, with no semilength hypothesis. -/
theorem doubleRises_heightSweep (P : List Step) (hP : IsDyckPath P) :
    doubleRises (heightSweep P) = valleys P := by
  by_cases h : semilength P = 0
  · rw [eq_nil_of_isDyckPath_semilength_zero hP h, heightSweep_nil]
    rfl
  · exact doubleRises_heightSweep_eq_valleys P hP (by omega)

/-! ## SECTION B — injectivity of the height sweep on Dyck paths -/

/-! ### B1: the level boundary in the sorted sweep -/

/-- The number of sweep entries of height `≤ t` — the boundary index of the
level-`t` block in the sorted sweep. -/
def levelBoundary (P : List Step) (t : ℤ) : ℕ :=
  (sweepIdx P).countP (fun z => decide (z.1 ≤ t))

theorem levelBoundary_le (P : List Step) (t : ℤ) :
    levelBoundary P t ≤ P.length := by
  rw [levelBoundary, ← length_sweepIdx P]
  exact List.countP_le_length

/-- The sorted sweep's heights are nondecreasing. -/
theorem sweep_height_mono (P : List Step) {i j : ℕ}
    (hi : i < ((sweepIdx P).mergeSort cmpHS').length)
    (hj : j < ((sweepIdx P).mergeSort cmpHS').length) (hij : i ≤ j) :
    ((sweepIdx P).mergeSort cmpHS')[i].1 ≤ ((sweepIdx P).mergeSort cmpHS')[j].1 := by
  rcases Nat.lt_or_ge i j with h | h
  · have := klt_getElem P hi hj h
    unfold klt at this
    omega
  · have : i = j := by omega
    subst this
    exact le_refl _

theorem levelBoundary_eq_sorted_countP (P : List Step) (t : ℤ) :
    levelBoundary P t
      = ((sweepIdx P).mergeSort cmpHS').countP (fun z => decide (z.1 ≤ t)) :=
  (List.Perm.countP_eq _ (List.mergeSort_perm _ _)).symm

/-- **The boundary dichotomy**: index `a` of the sorted sweep lies before the
level-`t` boundary exactly when its height is `≤ t`. -/
theorem getElem_boundary_iff (P : List Step) (t : ℤ) {a : ℕ}
    (ha : a < ((sweepIdx P).mergeSort cmpHS').length) :
    a < levelBoundary P t ↔ ((sweepIdx P).mergeSort cmpHS')[a].1 ≤ t := by
  rw [levelBoundary_eq_sorted_countP]
  constructor
  · intro hlt
    by_contra hgt
    have hdrop : (((sweepIdx P).mergeSort cmpHS').drop a).countP
        (fun z => decide (z.1 ≤ t)) = 0 := by
      rw [List.countP_eq_zero]
      intro z hz
      obtain ⟨k, hk, hzk⟩ := List.getElem_of_mem hz
      rw [List.getElem_drop] at hzk
      have hklen : a + k < ((sweepIdx P).mergeSort cmpHS').length := by
        rw [List.length_drop] at hk
        omega
      have hmono := sweep_height_mono P ha hklen (by omega)
      rw [hzk] at hmono
      simp only [decide_eq_true_eq]
      omega
    have hsplit : ((sweepIdx P).mergeSort cmpHS').countP (fun z => decide (z.1 ≤ t))
        = (((sweepIdx P).mergeSort cmpHS').take a).countP (fun z => decide (z.1 ≤ t))
          + (((sweepIdx P).mergeSort cmpHS').drop a).countP
              (fun z => decide (z.1 ≤ t)) := by
      rw [← List.countP_append, List.take_append_drop]
    have htake : (((sweepIdx P).mergeSort cmpHS').take a).countP
        (fun z => decide (z.1 ≤ t)) ≤ a := by
      calc (((sweepIdx P).mergeSort cmpHS').take a).countP (fun z => decide (z.1 ≤ t))
          ≤ (((sweepIdx P).mergeSort cmpHS').take a).length := List.countP_le_length
        _ ≤ a := by rw [List.length_take]; omega
    omega
  · intro hle
    have htake : (((sweepIdx P).mergeSort cmpHS').take (a + 1)).countP
        (fun z => decide (z.1 ≤ t))
        = (((sweepIdx P).mergeSort cmpHS').take (a + 1)).length := by
      rw [List.countP_eq_length]
      intro z hz
      obtain ⟨k, hk, hzk⟩ := List.getElem_of_mem hz
      rw [List.getElem_take] at hzk
      have hklen : k < ((sweepIdx P).mergeSort cmpHS').length := by
        rw [List.length_take] at hk
        omega
      have hka : k ≤ a := by
        rw [List.length_take] at hk
        omega
      have hmono := sweep_height_mono P hklen ha hka
      rw [hzk] at hmono
      simp only [decide_eq_true_eq]
      omega
    have hlen : (((sweepIdx P).mergeSort cmpHS').take (a + 1)).length = a + 1 := by
      rw [List.length_take]
      omega
    have hsub : (((sweepIdx P).mergeSort cmpHS').take (a + 1)).countP
        (fun z => decide (z.1 ≤ t))
        ≤ ((sweepIdx P).mergeSort cmpHS').countP (fun z => decide (z.1 ≤ t)) :=
      (List.take_sublist _ _).countP_le
    omega

/-! ### B2: prefix counts at the boundary -/

/-- Elements of the boundary prefix have height `≤ t`; elements beyond have
height `> t`. -/
theorem mem_take_boundary_height {P : List Step} {t : ℤ} {z : ℤ × ℕ × Step}
    (hz : z ∈ ((sweepIdx P).mergeSort cmpHS').take (levelBoundary P t)) :
    z.1 ≤ t := by
  obtain ⟨k, hk, hzk⟩ := List.getElem_of_mem hz
  rw [List.getElem_take] at hzk
  have hklen : k < ((sweepIdx P).mergeSort cmpHS').length := by
    rw [List.length_take] at hk
    omega
  have hkB : k < levelBoundary P t := by
    rw [List.length_take] at hk
    omega
  have := (getElem_boundary_iff P t hklen).mp hkB
  rw [hzk] at this
  exact this

theorem mem_drop_boundary_height {P : List Step} {t : ℤ} {z : ℤ × ℕ × Step}
    (hz : z ∈ ((sweepIdx P).mergeSort cmpHS').drop (levelBoundary P t)) :
    t < z.1 := by
  obtain ⟨k, hk, hzk⟩ := List.getElem_of_mem hz
  rw [List.getElem_drop] at hzk
  have hklen : levelBoundary P t + k < ((sweepIdx P).mergeSort cmpHS').length := by
    rw [List.length_drop] at hk
    omega
  have hnot : ¬ (levelBoundary P t + k < levelBoundary P t) := by omega
  rw [getElem_boundary_iff P t hklen, hzk] at hnot
  omega

/-- The generic boundary-prefix count: counting letter `s` in the boundary prefix
of the sweep equals counting `(height ≤ t, letter s)` over all triples. -/
theorem count_take_boundary (P : List Step) (t : ℤ) (s : Step) :
    ((heightSweep P).take (levelBoundary P t)).count s
      = (sweepIdx P).countP (fun z => decide (z.1 ≤ t ∧ z.2.2 = s)) := by
  have h1 : ((heightSweep P).take (levelBoundary P t)).count s
      = ((((sweepIdx P).mergeSort cmpHS').take (levelBoundary P t)).map (·.2.2)).count s := by
    rw [heightSweep_eq', List.map_take]
  rw [h1, List.count_eq_countP, List.countP_map]
  have h2 : (((sweepIdx P).mergeSort cmpHS').take (levelBoundary P t)).countP
        ((fun x => x == s) ∘ (·.2.2))
      = (((sweepIdx P).mergeSort cmpHS').take (levelBoundary P t)).countP
        (fun z => decide (z.1 ≤ t ∧ z.2.2 = s)) := by
    apply List.countP_congr
    intro z hz
    have hht := mem_take_boundary_height hz
    simp only [Function.comp_apply, beq_iff_eq, decide_eq_true_eq]
    tauto
  rw [h2]
  have hdrop : (((sweepIdx P).mergeSort cmpHS').drop (levelBoundary P t)).countP
      (fun z => decide (z.1 ≤ t ∧ z.2.2 = s)) = 0 := by
    rw [List.countP_eq_zero]
    intro z hz
    have := mem_drop_boundary_height hz
    simp only [decide_eq_true_eq]
    omega
  have hsplit : ((sweepIdx P).mergeSort cmpHS').countP
        (fun z => decide (z.1 ≤ t ∧ z.2.2 = s))
      = (((sweepIdx P).mergeSort cmpHS').take (levelBoundary P t)).countP
          (fun z => decide (z.1 ≤ t ∧ z.2.2 = s))
        + (((sweepIdx P).mergeSort cmpHS').drop (levelBoundary P t)).countP
            (fun z => decide (z.1 ≤ t ∧ z.2.2 = s)) := by
    rw [← List.countP_append, List.take_append_drop]
  have hperm : ((sweepIdx P).mergeSort cmpHS').countP
        (fun z => decide (z.1 ≤ t ∧ z.2.2 = s))
      = (sweepIdx P).countP (fun z => decide (z.1 ≤ t ∧ z.2.2 = s)) :=
    List.Perm.countP_eq _ (List.mergeSort_perm _ _)
  omega

/-- The `D`-count of the boundary prefix is the global count of `D`-steps at
height `≤ t`. -/
theorem count_D_take_boundary (P : List Step) (t : ℤ) :
    ((heightSweep P).take (levelBoundary P t)).count D
      = atMostDpre P P.length t := by
  rw [count_take_boundary, atMostDpre_eq_count]

/-- The `U`-count of the boundary prefix is the global count of `U`-steps at
height `< t + 1`. -/
theorem count_U_take_boundary (P : List Step) (t : ℤ) :
    ((heightSweep P).take (levelBoundary P t)).count U
      = belowUpre P P.length (t + 1) := by
  rw [count_take_boundary, belowUpre_eq_count]
  apply List.countP_congr
  intro z _
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨by omega, h.2⟩
  · intro h
    exact ⟨by omega, h.2⟩

/-! ### B3: discrete intermediate values and the boundary height -/

/-- Discrete IVT upward: every value between `0` and `height P b` is attained. -/
theorem exists_height_eq (P : List Step) {v : ℤ} {b : ℕ} (h0 : 0 ≤ v)
    (hv : v ≤ height P b) : ∃ j, j ≤ b ∧ height P j = v := by
  induction b with
  | zero =>
    refine ⟨0, le_refl 0, ?_⟩
    rw [height_zero] at hv ⊢
    omega
  | succ b ih =>
    by_cases hb : v ≤ height P b
    · obtain ⟨j, hj, hjv⟩ := ih hb
      exact ⟨j, by omega, hjv⟩
    · push Not at hb
      by_cases hlen : b < P.length
      · have hone := height_succ_le_height_add_one P b hlen
        exact ⟨b + 1, le_refl _, by omega⟩
      · push Not at hlen
        rw [height_of_length_le P (b + 1) (by omega),
          ← height_of_length_le P b hlen] at hv
        omega

/-- **The boundary entry sits exactly one level up**: at a non-final boundary the
sorted sweep's entry has height `t + 1`. -/
theorem boundary_height (P : List Step) (_hP : IsDyckPath P) (t : ℤ) (ht : 0 ≤ t)
    (hlt : levelBoundary P t < ((sweepIdx P).mergeSort cmpHS').length) :
    ((sweepIdx P).mergeSort cmpHS')[levelBoundary P t].1 = t + 1 := by
  have hgt : ¬ (((sweepIdx P).mergeSort cmpHS')[levelBoundary P t].1 ≤ t) := by
    rw [← getElem_boundary_iff P t hlt]
    omega
  push Not at hgt
  by_contra hne
  have hge : t + 2 ≤ ((sweepIdx P).mergeSort cmpHS')[levelBoundary P t].1 := by omega
  have hmem : ((sweepIdx P).mergeSort cmpHS')[levelBoundary P t] ∈ sweepIdx P :=
    (List.mergeSort_perm _ _).subset (List.getElem_mem hlt)
  have hplt : ((sweepIdx P).mergeSort cmpHS')[levelBoundary P t].2.1 < P.length :=
    sweepIdx_pos_lt P hmem
  have hph : ((sweepIdx P).mergeSort cmpHS')[levelBoundary P t].1
      = height P (((sweepIdx P).mergeSort cmpHS')[levelBoundary P t].2.1) :=
    sweep_height_at P _ hplt hmem rfl
  obtain ⟨j, hj, hjv⟩ := exists_height_eq P (v := t + 1)
    (b := ((sweepIdx P).mergeSort cmpHS')[levelBoundary P t].2.1)
    (by omega) (by omega)
  have hjlt : j < P.length := by omega
  have hjmemT : tripleAt P j hjlt ∈ (sweepIdx P).mergeSort cmpHS' :=
    List.mem_mergeSort.mpr (tripleAt_mem P j hjlt)
  obtain ⟨m, hm, hmeq⟩ := List.getElem_of_mem hjmemT
  have hklt : klt ((sweepIdx P).mergeSort cmpHS')[m]
      ((sweepIdx P).mergeSort cmpHS')[levelBoundary P t] := by
    rw [hmeq]
    left
    show (tripleAt P j hjlt).1 < _
    rw [show (tripleAt P j hjlt).1 = height P j from rfl, hjv]
    omega
  have hmB : m < levelBoundary P t := lt_of_klt_getElem P hm hlt hklt
  have hmle := (getElem_boundary_iff P t hm).mp hmB
  rw [hmeq] at hmle
  have : height P j ≤ t := hmle
  omega

/-! ### B4: every positive level of the sweep opens with a `D` -/

/-- The rightmost step at a positive height is a `D` (else its matching
down-step would sit at the same height further right). -/
theorem rightmost_at_height_isD (P : List Step) (hP : IsDyckPath P) {t : ℤ}
    (ht : 0 < t) {p : ℕ} (hp : p < P.length) (hh : height P p = t)
    (hmax : ∀ q, q < P.length → height P q = t → q ≤ p) : P[p] = D := by
  rcases hU : P[p] with _ | _
  · exfalso
    have hm := matchD_props P hP p hp hU
    have hmgt := (matchD_mem P hP p hp).1
    by_cases hq : matchD P p + 1 < P.length
    · have := hmax (matchD P p + 1) hq (by rw [hm.2.2, hh])
      omega
    · push Not at hq
      have h0 : height P (matchD P p + 1) = 0 := by
        rw [height_of_length_le P _ (by omega), hP.2]
      rw [hm.2.2, hh] at h0
      omega
  · rfl

/-- **Each level opens with a `D`**: the boundary entry of a positive level is a
`D`-step. -/
theorem boundary_getElem_D (P : List Step) (hP : IsDyckPath P) (t : ℤ) (ht : 0 ≤ t)
    (hlt : levelBoundary P t < ((sweepIdx P).mergeSort cmpHS').length) :
    (heightSweep P)[levelBoundary P t]? = some D := by
  have hmem : ((sweepIdx P).mergeSort cmpHS')[levelBoundary P t] ∈ sweepIdx P :=
    (List.mergeSort_perm _ _).subset (List.getElem_mem hlt)
  have hbh := boundary_height P hP t ht hlt
  have hplt : ((sweepIdx P).mergeSort cmpHS')[levelBoundary P t].2.1 < P.length :=
    sweepIdx_pos_lt P hmem
  have hph : ((sweepIdx P).mergeSort cmpHS')[levelBoundary P t].1
      = height P (((sweepIdx P).mergeSort cmpHS')[levelBoundary P t].2.1) :=
    sweep_height_at P _ hplt hmem rfl
  have hmax : ∀ q, q < P.length → height P q = t + 1
      → q ≤ ((sweepIdx P).mergeSort cmpHS')[levelBoundary P t].2.1 := by
    intro q hq hqh
    by_contra hgt
    push Not at hgt
    have hqmemT : tripleAt P q hq ∈ (sweepIdx P).mergeSort cmpHS' :=
      List.mem_mergeSort.mpr (tripleAt_mem P q hq)
    obtain ⟨m, hm, hmeq⟩ := List.getElem_of_mem hqmemT
    have hklt : klt ((sweepIdx P).mergeSort cmpHS')[m]
        ((sweepIdx P).mergeSort cmpHS')[levelBoundary P t] := by
      rw [hmeq]
      right
      constructor
      · show (tripleAt P q hq).1 = _
        rw [show (tripleAt P q hq).1 = height P q from rfl, hqh, hbh]
      · show _ < (tripleAt P q hq).2.1
        rw [show (tripleAt P q hq).2.1 = q from rfl]
        exact hgt
    have hmB : m < levelBoundary P t := lt_of_klt_getElem P hm hlt hklt
    have hmle := (getElem_boundary_iff P t hm).mp hmB
    rw [hmeq] at hmle
    have : height P q ≤ t := hmle
    omega
  have hD := rightmost_at_height_isD P hP (t := t + 1) (by omega) hplt
    (by rw [← hph, hbh]) hmax
  rw [heightSweep_getElem?, List.getElem?_eq_getElem hlt]
  simp only [Option.map_some]
  rw [sweep_step_at P _ hplt hmem rfl, hD]

/-! ### B5: boundary uniqueness as a pure word lemma -/

theorem boundary_unique_aux {w : List Step} {c m1 m2 : ℕ}
    (h2 : m2 ≤ w.length) (hlt : m1 < m2)
    (hc1 : (w.take m1).count D = c) (hc2 : (w.take m2).count D = c)
    (hd1 : m1 = w.length ∨ w[m1]? = some D) : False := by
  have hm1lt : m1 < w.length := by omega
  have hd1' : w[m1]? = some D := by
    rcases hd1 with h' | h'
    · omega
    · exact h'
  have hstep : (w.take (m1 + 1)).count D = (w.take m1).count D + 1 := by
    rw [List.take_add_one, hd1', List.count_append]
    simp
  have hmono : (w.take (m1 + 1)).count D ≤ (w.take m2).count D := by
    have htt : w.take (m1 + 1) = (w.take m2).take (m1 + 1) := by
      rw [List.take_take]
      congr 1
      omega
    rw [htt]
    exact (List.take_sublist _ _).count_le _
  omega

/-- A boundary index is determined by its prefix `D`-count, provided the word
continues with a `D` there (or ends). -/
theorem boundary_unique {w : List Step} {c m1 m2 : ℕ}
    (h1 : m1 ≤ w.length) (h2 : m2 ≤ w.length)
    (hc1 : (w.take m1).count D = c) (hc2 : (w.take m2).count D = c)
    (hd1 : m1 = w.length ∨ w[m1]? = some D)
    (hd2 : m2 = w.length ∨ w[m2]? = some D) : m1 = m2 := by
  rcases Nat.lt_trichotomy m1 m2 with h | h | h
  · exact absurd (boundary_unique_aux h2 h hc1 hc2 hd1) (fun f => f)
  · exact h
  · exact absurd (boundary_unique_aux h1 h hc2 hc1 hd2) (fun f => f)

/-! ### B6: the level data of the source is determined by the sweep word -/

/-- Boundaries agree once the `D`-counts agree (over the SAME sweep word). -/
theorem levelBoundary_eq_of_agree {P Q : List Step} (hP : IsDyckPath P)
    (hQ : IsDyckPath Q) (hw : heightSweep P = heightSweep Q) {t : ℤ} (ht : 0 ≤ t)
    (hD : atMostDpre P P.length t = atMostDpre Q Q.length t) :
    levelBoundary P t = levelBoundary Q t := by
  refine boundary_unique (w := heightSweep P) (c := atMostDpre P P.length t)
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [length_heightSweep]
    exact levelBoundary_le P t
  · rw [hw, length_heightSweep]
    exact levelBoundary_le Q t
  · exact count_D_take_boundary P t
  · rw [hw, count_D_take_boundary Q t, hD]
  · by_cases hend : levelBoundary P t < ((sweepIdx P).mergeSort cmpHS').length
    · exact Or.inr (boundary_getElem_D P hP t ht hend)
    · push Not at hend
      rw [List.length_mergeSort, length_sweepIdx] at hend
      left
      rw [length_heightSweep]
      exact le_antisymm (levelBoundary_le P t) hend
  · by_cases hend : levelBoundary Q t < ((sweepIdx Q).mergeSort cmpHS').length
    · exact Or.inr (by rw [hw]; exact boundary_getElem_D Q hQ t ht hend)
    · push Not at hend
      rw [List.length_mergeSort, length_sweepIdx] at hend
      left
      rw [hw, length_heightSweep]
      exact le_antisymm (levelBoundary_le Q t) hend

/-- **The level data propagates**: two Dyck paths with the same sweep word have
the same per-level `U`-counts and the same level boundaries, at every level. -/
theorem level_data_eq_of_heightSweep_eq {P Q : List Step}
    (hP : IsDyckPath P) (hQ : IsDyckPath Q)
    (hw : heightSweep P = heightSweep Q) (t : ℕ) :
    belowUpre P P.length (t : ℤ) = belowUpre Q Q.length (t : ℤ)
      ∧ levelBoundary P (t : ℤ) = levelBoundary Q (t : ℤ) := by
  induction t with
  | zero =>
    have hbU : ∀ (R : List Step), IsDyckPath R →
        belowUpre R R.length ((0 : ℕ) : ℤ) = 0 := by
      intro R hR
      rw [belowUpre]
      apply List.countP_eq_zero.mpr
      intro i hi
      rw [List.mem_range] at hi
      simp only [decide_eq_true_eq]
      intro hcon
      have := hR.1 i (by omega)
      omega
    refine ⟨by rw [hbU P hP, hbU Q hQ], ?_⟩
    refine levelBoundary_eq_of_agree hP hQ hw (by norm_num) ?_
    rw [show ((0 : ℕ) : ℤ) = (0 : ℤ) from by norm_num] at hbU ⊢
    rw [← belowU_eq_atMostD P hP 0 le_rfl, ← belowU_eq_atMostD Q hQ 0 le_rfl,
      hbU P hP, hbU Q hQ]
  | succ t ih =>
    obtain ⟨ihU, ihB⟩ := ih
    have hU1 : belowUpre P P.length ((t : ℤ) + 1)
        = belowUpre Q Q.length ((t : ℤ) + 1) := by
      rw [← count_U_take_boundary P (t : ℤ), ← count_U_take_boundary Q (t : ℤ),
        ihB, hw]
    have hcast : (((t + 1 : ℕ)) : ℤ) = (t : ℤ) + 1 := by push_cast; ring
    refine ⟨by rw [hcast]; exact hU1, ?_⟩
    rw [hcast]
    refine levelBoundary_eq_of_agree hP hQ hw (by omega) ?_
    rw [← belowU_eq_atMostD P hP _ (by omega), ← belowU_eq_atMostD Q hQ _ (by omega)]
    exact hU1

/-! ### B7: the rank of a triple in the sorted sweep -/

instance : DecidableRel klt := fun a b => by unfold klt; infer_instance

/-- A triple sits in the sorted sweep exactly at its `klt`-rank. -/
theorem getElem_rank (P : List Step) {z : ℤ × ℕ × Step} (hz : z ∈ sweepIdx P) :
    ((sweepIdx P).mergeSort cmpHS')[(sweepIdx P).countP fun z' => decide (klt z' z)]?
      = some z := by
  have hzT : z ∈ (sweepIdx P).mergeSort cmpHS' := List.mem_mergeSort.mpr hz
  obtain ⟨m, hm, hmeq⟩ := List.getElem_of_mem hzT
  have hcount : (sweepIdx P).countP (fun z' => decide (klt z' z)) = m := by
    rw [← List.Perm.countP_eq _ (List.mergeSort_perm _ _)]
    have hsplit : ((sweepIdx P).mergeSort cmpHS').countP (fun z' => decide (klt z' z))
        = (((sweepIdx P).mergeSort cmpHS').take m).countP (fun z' => decide (klt z' z))
          + (((sweepIdx P).mergeSort cmpHS').drop m).countP
              (fun z' => decide (klt z' z)) := by
      rw [← List.countP_append, List.take_append_drop]
    have htake : (((sweepIdx P).mergeSort cmpHS').take m).countP
        (fun z' => decide (klt z' z))
        = (((sweepIdx P).mergeSort cmpHS').take m).length := by
      rw [List.countP_eq_length]
      intro y hy
      obtain ⟨k, hk, hyk⟩ := List.getElem_of_mem hy
      rw [List.getElem_take] at hyk
      have hklen : k < ((sweepIdx P).mergeSort cmpHS').length := by
        rw [List.length_take] at hk
        omega
      have hkm : k < m := by
        rw [List.length_take] at hk
        omega
      have := klt_getElem P hklen hm hkm
      rw [hyk, hmeq] at this
      simpa using this
    have hdrop : (((sweepIdx P).mergeSort cmpHS').drop m).countP
        (fun z' => decide (klt z' z)) = 0 := by
      rw [List.countP_eq_zero]
      intro y hy
      obtain ⟨k, hk, hyk⟩ := List.getElem_of_mem hy
      rw [List.getElem_drop] at hyk
      have hklen : m + k < ((sweepIdx P).mergeSort cmpHS').length := by
        rw [List.length_drop] at hk
        omega
      simp only [decide_eq_true_eq]
      intro hcon
      have hlt : m + k < m := by
        apply lt_of_klt_getElem P hklen hm
        rw [hyk, hmeq]
        exact hcon
      omega
    have hlen : (((sweepIdx P).mergeSort cmpHS').take m).length = m := by
      rw [List.length_take]
      omega
    rw [hsplit, htake, hdrop, hlen]
    omega
  rw [hcount, List.getElem?_eq_getElem hm, hmeq]

/-! ### B8: the rank is determined by the level data and the prefix -/

/-- Heights along a common prefix agree. -/
theorem height_eq_of_take_eq {P Q : List Step} {i : ℕ}
    (htake : P.take i = Q.take i) {j : ℕ} (hj : j ≤ i) :
    height P j = height Q j := by
  unfold height
  rw [show P.take j = (P.take i).take j from by rw [List.take_take]; congr 1; omega,
    show Q.take j = (Q.take i).take j from by rw [List.take_take]; congr 1; omega,
    htake]

/-- The rank of the position-`i` triple, in position-count terms. -/
theorem rank_tripleAt (P : List Step) (i : ℕ) (hi : i < P.length) :
    (sweepIdx P).countP (fun z' => decide (klt z' (tripleAt P i hi)))
      = (List.range P.length).countP (fun j => decide (height P j < height P i
          ∨ (height P j = height P i ∧ i < j))) := by
  unfold sweepIdx
  rw [List.range_eq_range', ← List.zipIdx_map_snd (l := P) (i := 0),
    List.countP_map, List.countP_map]
  apply List.countP_congr
  intro x hx
  obtain ⟨hj, hs⟩ := List.mem_zipIdx' hx
  simp only [Function.comp_apply, decide_eq_true_eq]
  unfold klt tripleAt
  simp only []

/-- Generic disjoint-or split for `countP`. -/
theorem countP_split_or {α} (l : List α) (p q1 q2 : α → Bool)
    (h : ∀ x ∈ l, (p x = true ↔ (q1 x = true ∨ q2 x = true)))
    (hdisj : ∀ x ∈ l, ¬ (q1 x = true ∧ q2 x = true)) :
    l.countP p = l.countP q1 + l.countP q2 := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons,
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))
        (fun x hx => hdisj x (List.mem_cons_of_mem a hx))]
    have ha := h a List.mem_cons_self
    have hd := hdisj a List.mem_cons_self
    by_cases h1 : q1 a = true <;> by_cases h2 : q2 a = true <;>
      simp_all <;> omega

/-- The `<h` position count in `belowUpre`/`atMostDpre` terms. -/
theorem count_lt_height (P : List Step) (h : ℤ) :
    (List.range P.length).countP (fun j => decide (height P j < h))
      = belowUpre P P.length h
        + (List.range P.length).countP
            (fun j => decide (height P j ≤ h - 1 ∧ P[j]? = some D)) := by
  rw [belowUpre]
  refine countP_split_or _ _ _ _ ?_ ?_
  · intro j hj
    rw [List.mem_range] at hj
    simp only [decide_eq_true_eq]
    constructor
    · intro hlt
      rw [List.getElem?_eq_getElem hj]
      rcases hU : P[j] with _ | _
      · exact Or.inl ⟨hlt, rfl⟩
      · exact Or.inr ⟨by omega, rfl⟩
    · rintro (⟨hlt, -⟩ | ⟨hle, -⟩)
      · exact hlt
      · omega
  · intro j hj
    simp only [decide_eq_true_eq]
    rintro ⟨⟨-, hU⟩, ⟨-, hD⟩⟩
    rw [hU] at hD
    exact absurd (Option.some.inj hD) (by simp)

/-- The `≤ h-1`-and-`D` count is `atMostDpre` at `h - 1`. -/
theorem count_le_D (P : List Step) (h : ℤ) :
    (List.range P.length).countP
        (fun j => decide (height P j ≤ h - 1 ∧ P[j]? = some D))
      = atMostDpre P P.length (h - 1) := by
  rw [atMostDpre]

/-- `atMostDpre` at a negative threshold is zero on a Dyck path. -/
theorem atMostDpre_neg (P : List Step) (hP : IsDyckPath P) {t : ℤ} (ht : t < 0) :
    atMostDpre P P.length t = 0 := by
  rw [atMostDpre]
  apply List.countP_eq_zero.mpr
  intro j hj
  rw [List.mem_range] at hj
  simp only [decide_eq_true_eq]
  intro hcon
  have := hP.1 j (by omega)
  omega

/-- **The rank-count agreement**: with the same sweep word and the same prefix,
the position-`i` triple has the same rank in both paths. -/
theorem rank_count_eq_of_agree {P Q : List Step} (hP : IsDyckPath P)
    (hQ : IsDyckPath Q) (hw : heightSweep P = heightSweep Q) {i : ℕ}
    (hiP : i < P.length) (hiQ : i < Q.length) (htake : P.take i = Q.take i) :
    (List.range P.length).countP (fun j => decide (height P j < height P i
        ∨ (height P j = height P i ∧ i < j)))
      = (List.range Q.length).countP (fun j => decide (height Q j < height Q i
        ∨ (height Q j = height Q i ∧ i < j))) := by
  have hlen : P.length = Q.length := by
    have hp := length_heightSweep P
    have hq := length_heightSweep Q
    rw [hw] at hp
    omega
  have hh : height P i = height Q i := height_eq_of_take_eq htake (le_refl i)
  have hh0 : 0 ≤ height P i := hP.1 i (by omega)
  -- agreement of belowUpre at every nonnegative integer level
  have hbelow : ∀ t : ℤ, 0 ≤ t →
      belowUpre P P.length t = belowUpre Q Q.length t := by
    intro t ht
    have hcast : t = ((t.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg ht).symm
    rw [hcast]
    exact (level_data_eq_of_heightSweep_eq hP hQ hw t.toNat).1
  have hatmost : ∀ t : ℤ, atMostDpre P P.length t = atMostDpre Q Q.length t := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · rw [atMostDpre_neg P hP ht, atMostDpre_neg Q hQ ht]
    · rw [← belowU_eq_atMostD P hP t ht, ← belowU_eq_atMostD Q hQ t ht]
      exact hbelow t ht
  -- the `< h` counts agree (for any h)
  have hcountlt : ∀ h : ℤ,
      (List.range P.length).countP (fun j => decide (height P j < h))
        = (List.range Q.length).countP (fun j => decide (height Q j < h)) := by
    intro h
    rcases le_or_gt h 0 with hle | hpos
    · -- both zero: Dyck heights are ≥ 0
      have hzero : ∀ (R : List Step), IsDyckPath R →
          (List.range R.length).countP (fun j => decide (height R j < h)) = 0 := by
        intro R hR
        apply List.countP_eq_zero.mpr
        intro j hj
        rw [List.mem_range] at hj
        simp only [decide_eq_true_eq]
        intro hcon
        have := hR.1 j (by omega)
        omega
      rw [hzero P hP, hzero Q hQ]
    · rw [count_lt_height P h, count_lt_height Q h, count_le_D, count_le_D,
        hbelow h (by omega), hatmost (h - 1)]
  -- the `≤ i`-restricted equal-height count agrees (prefix-determined)
  have hcountle : (List.range P.length).countP
        (fun j => decide (height P j = height P i ∧ j ≤ i))
      = (List.range Q.length).countP
        (fun j => decide (height Q j = height Q i ∧ j ≤ i)) := by
    have hsplitrange : ∀ (R : List Step) (hiR : i < R.length),
        (List.range R.length).countP
            (fun j => decide (height R j = height R i ∧ j ≤ i))
          = (List.range (i + 1)).countP
            (fun j => decide (height R j = height R i)) := by
      intro R hiR
      have hr : R.length = (i + 1) + (R.length - (i + 1)) := by omega
      rw [hr, List.range_add, List.countP_append]
      have h2 : ((List.range (R.length - (i + 1))).map (i + 1 + ·)).countP
          (fun j => decide (height R j = height R i ∧ j ≤ i)) = 0 := by
        rw [List.countP_eq_zero]
        intro j hj
        rw [List.mem_map] at hj
        obtain ⟨k, -, rfl⟩ := hj
        simp only [decide_eq_true_eq]
        omega
      rw [h2, Nat.add_zero]
      apply List.countP_congr
      intro j hj
      rw [List.mem_range] at hj
      simp only [decide_eq_true_eq]
      constructor
      · intro hcon
        exact hcon.1
      · intro hcon
        exact ⟨hcon, by omega⟩
    rw [hsplitrange P hiP, hsplitrange Q hiQ]
    apply List.countP_congr
    intro j hj
    rw [List.mem_range] at hj
    simp only [decide_eq_true_eq]
    rw [height_eq_of_take_eq htake (by omega : j ≤ i), hh]
  -- the additive key identity, per path: klt-count + (=h ∧ ≤i) = (<h) + (=h)
  have hkey : ∀ (R : List Step), IsDyckPath R → ∀ (hiR : i < R.length),
      (List.range R.length).countP (fun j => decide (height R j < height R i
          ∨ (height R j = height R i ∧ i < j)))
        + (List.range R.length).countP
            (fun j => decide (height R j = height R i ∧ j ≤ i))
      = (List.range R.length).countP (fun j => decide (height R j < height R i))
        + (List.range R.length).countP
            (fun j => decide (height R j = height R i)) := by
    intro R hR hiR
    have hL : (List.range R.length).countP (fun j => decide ((height R j < height R i
          ∨ (height R j = height R i ∧ i < j)) ∨ (height R j = height R i ∧ j ≤ i)))
        = (List.range R.length).countP (fun j => decide (height R j < height R i
            ∨ (height R j = height R i ∧ i < j)))
          + (List.range R.length).countP
              (fun j => decide (height R j = height R i ∧ j ≤ i)) := by
      exact countP_split_or _ _ _ _
        (fun j _ => by simp only [decide_eq_true_eq])
        (fun j _ => by simp only [decide_eq_true_eq]; omega)
    have hR' : (List.range R.length).countP (fun j => decide ((height R j < height R i
          ∨ (height R j = height R i ∧ i < j)) ∨ (height R j = height R i ∧ j ≤ i)))
        = (List.range R.length).countP (fun j => decide (height R j < height R i
            ∨ height R j = height R i)) := by
      apply List.countP_congr
      intro j _
      simp only [decide_eq_true_eq]
      omega
    have hsplit2 : (List.range R.length).countP
        (fun j => decide (height R j < height R i ∨ height R j = height R i))
        = (List.range R.length).countP (fun j => decide (height R j < height R i))
          + (List.range R.length).countP
              (fun j => decide (height R j = height R i)) := by
      exact countP_split_or _ _ _ _
        (fun j _ => by simp only [decide_eq_true_eq])
        (fun j _ => by simp only [decide_eq_true_eq]; omega)
    rw [← hL, hR', hsplit2]
  -- the `= h` counts agree, from `< h` at h and h+1
  have hcounteq : (List.range P.length).countP
        (fun j => decide (height P j = height P i))
      = (List.range Q.length).countP
        (fun j => decide (height Q j = height Q i)) := by
    have hstep : ∀ (R : List Step) (h : ℤ),
        (List.range R.length).countP (fun j => decide (height R j < h + 1))
          = (List.range R.length).countP (fun j => decide (height R j < h))
            + (List.range R.length).countP (fun j => decide (height R j = h)) := by
      intro R h
      exact countP_split_or _ _ _ _
        (fun j _ => by simp only [decide_eq_true_eq]; omega)
        (fun j _ => by simp only [decide_eq_true_eq]; omega)
    have h1 := hstep P (height P i)
    have h2 := hstep Q (height Q i)
    have h3 := hcountlt (height P i)
    have h4 := hcountlt (height P i + 1)
    rw [← hh] at h2 ⊢
    omega
  have hkP := hkey P hP hiP
  have hkQ := hkey Q hQ hiQ
  have h3 := hcountlt (height P i)
  rw [← hh] at hkQ hcountle hcounteq ⊢
  omega

/-! ### B9: injectivity of the height sweep on Dyck paths -/

/-- **The keystone**: Dyck paths with the same height sweep are equal. -/
theorem heightSweep_injective_isDyckPath {P Q : List Step}
    (hP : IsDyckPath P) (hQ : IsDyckPath Q)
    (hw : heightSweep P = heightSweep Q) : P = Q := by
  have hlen : P.length = Q.length := by
    have hp := length_heightSweep P
    have hq := length_heightSweep Q
    rw [hw] at hp
    omega
  have hpoint : ∀ i : ℕ, P[i]? = Q[i]? := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
    by_cases hiP : i < P.length
    · have hiQ : i < Q.length := by omega
      have htake : P.take i = Q.take i := by
        apply List.ext_getElem?
        intro j
        by_cases hj : j < i
        · rw [List.getElem?_take_of_lt hj, List.getElem?_take_of_lt hj]
          exact ih j hj
        · rw [List.getElem?_eq_none (by rw [List.length_take]; omega),
            List.getElem?_eq_none (by rw [List.length_take]; omega)]
      have hrank := rank_count_eq_of_agree hP hQ hw hiP hiQ htake
      have hgP := getElem_rank P (tripleAt_mem P i hiP)
      have hgQ := getElem_rank Q (tripleAt_mem Q i hiQ)
      have hsP : (heightSweep P)[(sweepIdx P).countP
          fun z' => decide (klt z' (tripleAt P i hiP))]? = some (P[i]'hiP) := by
        rw [heightSweep_getElem?, hgP]
        rfl
      have hsQ : (heightSweep Q)[(sweepIdx Q).countP
          fun z' => decide (klt z' (tripleAt Q i hiQ))]? = some (Q[i]'hiQ) := by
        rw [heightSweep_getElem?, hgQ]
        rfl
      have hreq : (sweepIdx P).countP (fun z' => decide (klt z' (tripleAt P i hiP)))
          = (sweepIdx Q).countP (fun z' => decide (klt z' (tripleAt Q i hiQ))) := by
        rw [rank_tripleAt P i hiP, rank_tripleAt Q i hiQ]
        exact hrank
      rw [hreq, hw] at hsP
      rw [List.getElem?_eq_getElem hiP, List.getElem?_eq_getElem hiQ]
      exact hsP.symm.trans hsQ
    · push Not at hiP
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  exact List.ext_getElem? hpoint

/-! ## SECTION C — the bijection -/

theorem heightSweep_injOn (n : ℕ) : Set.InjOn heightSweep (DyckPath n) :=
  fun _P hP _Q hQ h => heightSweep_injective_isDyckPath hP.1 hQ.1 h

/-- **`thm:narayana-sweep`, component (b)**: the height sweep restricts to a
bijection `D_n → D_n`. -/
theorem heightSweep_bijOn (n : ℕ) :
    Set.BijOn heightSweep (DyckPath n) (DyckPath n) :=
  heightSweep_bijOn_of_injOn n (heightSweep_injOn n)

/-- Existence form: every Dyck path is a height sweep. -/
theorem exists_heightSweep_eq {n : ℕ} {Q : List Step} (hQ : Q ∈ DyckPath n) :
    ∃ P ∈ DyckPath n, heightSweep P = Q :=
  (heightSweep_bijOn n).surjOn hQ

/-! ## SECTION E — the Narayana symmetry -/

theorem narayana_fiber_card_le (n j k : ℕ) :
    ((dyckFinset n).filter fun P => valleys P = j ∧ doubleRises P = k).card ≤
      ((dyckFinset n).filter fun P => valleys P = k ∧ doubleRises P = j).card := by
  apply Finset.card_le_card_of_injOn heightSweep
  · intro P hP
    rw [Finset.mem_coe, Finset.mem_filter] at hP
    obtain ⟨hPD, hval, hdr⟩ := hP
    have hP' := (mem_dyckFinset.mp hPD).1
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_dyckFinset]
      exact heightSweep_mapsTo n (mem_dyckFinset.mp hPD)
    · rw [valleys_heightSweep P hP', hdr]
    · rw [doubleRises_heightSweep P hP', hval]
  · apply (heightSweep_injOn n).mono
    rw [← coe_dyckFinset]
    exact_mod_cast Finset.filter_subset _ _

/-- **`thm:narayana-sweep`, component (d), card form**: the joint
`(val, dr)`-distribution over `D_n` is symmetric — the Narayana symmetry
`Nar_n(q, t) = Nar_n(t, q)` at the level of coefficient counts. -/
theorem narayana_symmetry_card (n j k : ℕ) :
    ((dyckFinset n).filter fun P => valleys P = j ∧ doubleRises P = k).card =
      ((dyckFinset n).filter fun P => valleys P = k ∧ doubleRises P = j).card :=
  Nat.le_antisymm (narayana_fiber_card_le n j k) (narayana_fiber_card_le n k j)

/-! ## Examples -/

example : ((dyckFinset 4).filter
    fun P => valleys P = 1 ∧ doubleRises P = 2).card = 6 := by native_decide

example : ((dyckFinset 4).filter
    fun P => valleys P = 2 ∧ doubleRises P = 1).card = 6 := by native_decide
