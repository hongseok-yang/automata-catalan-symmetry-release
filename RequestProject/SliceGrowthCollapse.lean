/-
# Growth collapse: the one-cluster property of selected atoms (route GA-3)

The general-arity discharge uses the growth hypothesis `|T(W_n)| ≤ C(n+1)`
STRUCTURALLY: a selected atom whose marks form two bulk clusters admits, by composed
`SliceMarkN.acceptsN_moveGroup_step` moves, a `Θ((n/p)²)`-sized orbit of distinct
selected atoms — contradicting linear growth for large `n`.  Hence eventually every
selected atom has the ONE-CLUSTER property (all block coordinates within `[0,B) ∪
(n−B, n) ∪ [t−B, t+B]` for a single base `t`), and the selected-atom set is a finite
union of 0/1-parameter families on which the arity-1 tower applies.

This file starts the GA-3 build with its self-contained combinatorial pieces:

* `exists_unmarked_gap` — the pigeonhole gap-finder: there are at most `m` marks, so
  any `(m+1)·G` consecutive blocks contain a fully unmarked run of `G` blocks.  This
  is what locates the flanking gaps required by the shift lemma inside any stretch
  between two far-apart bulk coordinates.
* `shiftGroup_ne` — distinct shift amounts give distinct tuples (the orbit members
  are pairwise distinct atoms), provided the group window is inhabited.

Still to come (the refined GA-3 plan, `FAS_DESIGN.md`): the canonical-configuration
reachability (park both bulk clusters left by monotone move sequences, then place
them at arbitrary grid targets), the orbit count, and the contradiction against the
`IsOutput` length bound.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
import RequestProject.SliceMarkN
import RequestProject.WRP
import RequestProject.WrappedFlat

namespace SliceGrowthCollapse

open MSO Step MSOMarkN SliceMarkN

/-- **Pigeonhole gap-finder.**  There are at most `m` marks, so among any `m + 1`
consecutive chunks of `G` blocks some chunk is fully unmarked. -/
theorem exists_unmarked_gap {m : ℕ} (ī : Fin m → ℕ) (G lo : ℕ) :
    ∃ s, lo ≤ s ∧ s + G ≤ lo + (m + 1) * G ∧
      ∀ j, s ≤ j → j < s + G → ∀ i, ī i ≠ 1 + 2 * j ∧ ī i ≠ 1 + 2 * j + 1 := by
  by_cases hex : ∃ t : Fin (m + 1), ∀ j, lo + t.val * G ≤ j → j < lo + t.val * G + G →
      ∀ i, ī i ≠ 1 + 2 * j ∧ ī i ≠ 1 + 2 * j + 1
  · obtain ⟨t, ht⟩ := hex
    have htm : t.val + 1 ≤ m + 1 := t.isLt
    have hmul : (t.val + 1) * G ≤ (m + 1) * G := Nat.mul_le_mul_right G htm
    have hmul' : t.val * G + G = (t.val + 1) * G := by ring
    exact ⟨lo + t.val * G, by omega, by omega, ht⟩
  · exfalso
    push Not at hex
    -- every chunk contains a mark; pick its mark index, get `Fin (m+1) ↪ Fin m`
    have hf : ∀ t : Fin (m + 1), ∃ i : Fin m, ∃ j, lo + t.val * G ≤ j ∧
        j < lo + t.val * G + G ∧ (ī i = 1 + 2 * j ∨ ī i = 1 + 2 * j + 1) := by
      intro t
      obtain ⟨j, hj1, hj2, i, hi⟩ := hex t
      refine ⟨i, j, hj1, hj2, ?_⟩
      by_cases h1 : ī i = 1 + 2 * j
      · exact Or.inl h1
      · exact Or.inr (hi h1)
    choose f j hj1 hj2 hjor using hf
    -- two chunks share a mark index; their blocks are disjoint — contradiction
    have key : ∀ t t' : Fin (m + 1), t.val < t'.val → f t = f t' → False := by
      intro t t' hlt heq
      have hsucc : t.val + 1 ≤ t'.val := hlt
      have hmul : (t.val + 1) * G ≤ t'.val * G := Nat.mul_le_mul_right G hsucc
      have hmul' : t.val * G + G = (t.val + 1) * G := by ring
      have hsep : lo + t.val * G + G ≤ lo + t'.val * G := by omega
      have h1 := hj1 t
      have h2 := hj2 t
      have h1' := hj1 t'
      have h2' := hj2 t'
      have hv := hjor t
      have hv' := hjor t'
      rw [heq] at hv
      rcases hv with hv | hv <;> rcases hv' with hv' | hv' <;> omega
    obtain ⟨t, t', htne, hteq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt f (by simp)
    have hvalne : t.val ≠ t'.val := fun h => htne (Fin.ext h)
    rcases Nat.lt_or_ge t.val t'.val with hlt | hge
    · exact key t t' hlt hteq
    · exact key t' t (by omega) hteq.symm

/-- Distinct shift amounts give distinct tuples, as soon as the group window is
inhabited: the orbit members of the move sequence are pairwise distinct atoms. -/
theorem shiftGroup_ne {m : ℕ} (ī : Fin m → ℕ) (b c δ δ' : ℕ) (hne : δ ≠ δ')
    (hin : ∃ i, 1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c) :
    shiftGroup m ī b c δ ≠ shiftGroup m ī b c δ' := by
  obtain ⟨i, hi⟩ := hin
  intro heq
  have h := congrFun heq i
  unfold shiftGroup at h
  rw [if_pos hi, if_pos hi] at h
  omega

/-- Iterate-function periodicity extends to arbitrary multiples of the period. -/
theorem bFN_iterate_period_mul {m : ℕ} (M : SliceMSO.DetAuto (MarkedN m)) (mv pv : ℕ)
    (hEP : ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g]) :
    ∀ (k g : ℕ), mv ≤ g → (bFN M)^[g + k * pv] = (bFN M)^[g]
  | 0, g, _ => by rw [Nat.zero_mul, Nat.add_zero]
  | (k + 1), g, hg => by
      have h1 : (bFN M)^[g + k * pv + pv] = (bFN M)^[g + k * pv] := hEP _ (by omega)
      have h2 := bFN_iterate_period_mul M mv pv hEP k g hg
      rw [show g + (k + 1) * pv = g + k * pv + pv from by ring, h1, h2]

/-- **Multi-period move**: a group with start left gap `≥ mv` and end right gap
`≥ mv` may move right by ANY multiple of the period in a single application —
there are no intermediate configurations to certify. -/
theorem acceptsN_moveGroup_multi {m : ℕ} (M : SliceMSO.DetAuto (MarkedN m)) (mv pv : ℕ)
    (hEP : ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g])
    (n : ℕ) (ī : Fin m → ℕ) (a b c d k : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hdn : d ≤ n)
    (hgapL : mv ≤ b - a) (hgapR : mv + k * pv ≤ d - c)
    (hclass : ∀ i, ī i < 1 + 2 * a ∨ (1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c)
      ∨ 1 + 2 * d ≤ ī i) :
    M.accepts (markAtN m (wrappedFlat n) (shiftGroup m ī b c (k * pv)))
      ↔ M.accepts (markAtN m (wrappedFlat n) ī) := by
  refine acceptsN_moveGroup M n ī a b c d (k * pv) hab hbc (by omega) hdn hclass ?_ ?_
  · rw [show b + k * pv - a = (b - a) + k * pv from by omega]
    exact bFN_iterate_period_mul M mv pv hEP k (b - a) hgapL
  · have h := bFN_iterate_period_mul M mv pv hEP k (d - c - k * pv) (by omega)
    rw [show d - c - k * pv + k * pv = d - c from by omega] at h
    rw [show d - (c + k * pv) = d - c - k * pv from by omega]
    exact h.symm

/-- **Counting bridge**: an injective family of valid accepted tuples indexed by a
finite set of lattice points is bounded by the growth budget. -/
theorem card_le_of_injOn_accepted {m : ℕ} (M : SliceMSO.DetAuto (MarkedN m))
    (C n : ℕ) (S : Finset (ℕ × ℕ)) (f : ℕ × ℕ → (Fin m → ℕ))
    (hinj : Set.InjOn f S)
    (hacc : ∀ p ∈ S, (∀ i, f p i < (wrappedFlat n).length) ∧
      M.accepts (markAtN m (wrappedFlat n) (f p)))
    (hcard : ∀ l : List (Fin m → ℕ), l.Nodup →
      (∀ ī ∈ l, (∀ i, ī i < (wrappedFlat n).length) ∧
        M.accepts (markAtN m (wrappedFlat n) ī)) →
      l.length ≤ C * (n + 1)) :
    S.card ≤ C * (n + 1) := by
  have hnodup : (S.toList.map f).Nodup := by
    refine List.Nodup.map_on ?_ S.nodup_toList
    intro x hx y hy hxy
    exact hinj (by simpa using hx) (by simpa using hy) hxy
  have hmem : ∀ ī ∈ S.toList.map f, (∀ i, ī i < (wrappedFlat n).length) ∧
      M.accepts (markAtN m (wrappedFlat n) ī) := by
    intro ī hī
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hī
    exact hacc p (by simpa using hp)
  have hl := hcard (S.toList.map f) hnodup hmem
  rwa [List.length_map, Finset.length_toList] at hl


/-- **Per-copy growth bound from `IsOutput`**: a `Nodup` list of selected tuples of one
copy embeds into the output's atom list, so its length is at most the output length. -/
theorem nodup_selected_length_le {Alpha Gamma : Type*} (P : WRP.Presentation Alpha Gamma)
    (w : List Alpha) (out : List Gamma) (hout : P.IsOutput w out)
    (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)) (hnd : l.Nodup)
    (hsel : ∀ ī ∈ l, P.toPoly.selectedAtom w ⟨c, ī⟩) :
    l.length ≤ out.length := by
  obtain ⟨atoms, _, hmem, _, houteq⟩ := hout
  have hndmap : (l.map (fun ī => (⟨c, ī⟩ : P.toPoly.Atom))).Nodup := by
    refine List.Nodup.map ?_ hnd
    intro x y hxy
    injection hxy
  have hsub : (l.map (fun ī => (⟨c, ī⟩ : P.toPoly.Atom))) ⊆ atoms := by
    intro a ha
    obtain ⟨ī, hī, rfl⟩ := List.mem_map.mp ha
    exact (hmem _).mpr (hsel ī hī)
  have hle := (List.subperm_of_subset hndmap hsub).length_le
  rw [List.length_map] at hle
  rw [houteq, List.length_map]
  exact hle

/-- **The per-copy selectedness DFA**: on valid tuples, an `arity c`-mark DFA decides
the selection relation of copy `c` (from `selDef` via `markedDFAN_exists`). -/
theorem exists_selDFA (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K) :
    ∃ M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)),
      ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        (M.accepts (markAtN (P.toPoly.arity c) w ī) ↔ P.toPoly.sel c w ī) := by
  obtain ⟨φ, hφ⟩ := P.toPoly.selDef c
  obtain ⟨M, hM⟩ := MSOMarkN.markedDFAN_exists (P.toPoly.arity c) φ
  exact ⟨M, fun w ī hval => (hM w ī hval).trans (hφ w ī).symm⟩


/-- The zero shift is the identity. -/
theorem shiftGroup_zero {m : ℕ} (ī : Fin m → ℕ) (b c : ℕ) :
    shiftGroup m ī b c 0 = ī := by
  funext i
  unfold shiftGroup
  split <;> omega

/-- Shifted tuples remain valid positions of `W_n` when the moved window stays inside
the blocks. -/
theorem shiftGroup_valid {m : ℕ} (ī : Fin m → ℕ) (b c δ n : ℕ) (hcd : c + δ ≤ n)
    (hval : ∀ i, ī i < (wrappedFlat n).length) :
    ∀ i, shiftGroup m ī b c δ i < (wrappedFlat n).length := by
  intro i
  have hlen := length_wrappedFlat n
  have hv := hval i
  unfold shiftGroup
  by_cases hcond : 1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c
  · rw [if_pos hcond]
    omega
  · rw [if_neg hcond]
    exact hv


/-- An unmarked block window excludes all mark positions: every coordinate lies
strictly left or strictly right of it. -/
theorem unmarked_window_excludes {m : ℕ} (ī : Fin m → ℕ) (s t : ℕ)
    (h : ∀ jj, s ≤ jj → jj < t → ∀ i, ī i ≠ 1 + 2 * jj ∧ ī i ≠ 1 + 2 * jj + 1) :
    ∀ i, ī i < 1 + 2 * s ∨ 1 + 2 * t ≤ ī i := by
  intro i
  by_contra hcon
  push Not at hcon
  have := h ((ī i - 1) / 2) (by omega) (by omega) i
  omega

/-- Evaluation of `shiftGroup` inside the window. -/
theorem shiftGroup_apply_in {m : ℕ} (ī : Fin m → ℕ) (b c δ : ℕ) (i : Fin m)
    (h : 1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c) :
    shiftGroup m ī b c δ i = ī i + 2 * δ := by
  unfold shiftGroup
  exact if_pos h

/-- Evaluation of `shiftGroup` outside the window. -/
theorem shiftGroup_apply_out {m : ℕ} (ī : Fin m → ℕ) (b c δ : ℕ) (i : Fin m)
    (h : ¬ (1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c)) :
    shiftGroup m ī b c δ i = ī i := by
  unfold shiftGroup
  exact if_neg h

/-- **The rightward two-move quadratic family.**  If a selected atom has witness
marks in two windows separated by an unmarked `G`-gap, with another unmarked
`G`-gap on the far left and a long unmarked run on the far right, then sliding
the right group into the big run (parameter `v`) and the left group into the
vacated space (parameter `u < h ≤ v`) yields `h²` distinct selected atoms —
contradicting the growth budget. -/
theorem no_two_bulk_groups_right {m : ℕ} (M : SliceMSO.DetAuto (MarkedN m))
    (mv pv G : ℕ) (hpv : 1 ≤ pv) (hG : G = mv + pv)
    (hEP : ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g])
    (C n : ℕ)
    (hcard : ∀ l : List (Fin m → ℕ), l.Nodup →
      (∀ ī ∈ l, (∀ i, ī i < (wrappedFlat n).length) ∧
        M.accepts (markAtN m (wrappedFlat n) ī)) →
      l.length ≤ C * (n + 1))
    (ī : Fin m → ℕ) (hval : ∀ i, ī i < (wrappedFlat n).length)
    (hacc : M.accepts (markAtN m (wrappedFlat n) ī))
    (s₁ s₂ σ L h : ℕ)
    (hg₁ : ∀ jj, s₁ ≤ jj → jj < s₁ + G → ∀ i, ī i ≠ 1 + 2 * jj ∧ ī i ≠ 1 + 2 * jj + 1)
    (hg₂ : ∀ jj, s₂ ≤ jj → jj < s₂ + G → ∀ i, ī i ≠ 1 + 2 * jj ∧ ī i ≠ 1 + 2 * jj + 1)
    (hgL : ∀ jj, σ ≤ jj → jj < σ + L → ∀ i, ī i ≠ 1 + 2 * jj ∧ ī i ≠ 1 + 2 * jj + 1)
    (hw₁ : ∃ i, 1 + 2 * (s₁ + G) ≤ ī i ∧ ī i < 1 + 2 * s₂)
    (hw₂ : ∃ i, 1 + 2 * (s₂ + G) ≤ ī i ∧ ī i < 1 + 2 * σ)
    (hLn : σ + L ≤ n)
    (hroom : mv + 2 * h * pv ≤ L)
    (hcount : C * (n + 1) < h * h) :
    False := by
  obtain ⟨i₁, hi₁⟩ := hw₁
  obtain ⟨i₂, hi₂⟩ := hw₂
  have hord₁ : s₁ + G < s₂ := by omega
  have hord₂ : s₂ + G < σ := by omega
  have hex₁ := unmarked_window_excludes ī s₁ (s₁ + G) hg₁
  have hex₂ := unmarked_window_excludes ī s₂ (s₂ + G) hg₂
  have hexL := unmarked_window_excludes ī σ (σ + L) hgL
  set f : ℕ × ℕ → (Fin m → ℕ) := fun p =>
    shiftGroup m (shiftGroup m ī (s₂ + G) σ (p.2 * pv)) (s₁ + G) s₂ (p.1 * pv) with hfdef
  set S : Finset (ℕ × ℕ) := (Finset.range h) ×ˢ (Finset.Ico h (2 * h)) with hSdef
  have hSmem : ∀ p ∈ S, p.1 < h ∧ h ≤ p.2 ∧ p.2 < 2 * h := by
    intro p hp
    rw [hSdef, Finset.mem_product, Finset.mem_range, Finset.mem_Ico] at hp
    exact ⟨hp.1, hp.2.1, hp.2.2⟩
  have hmulv : ∀ v : ℕ, v < 2 * h → v * pv ≤ 2 * h * pv := fun v hv =>
    Nat.mul_le_mul_right pv (by omega)
  have hmuluv : ∀ u v : ℕ, u ≤ v → u * pv ≤ v * pv := fun u v huv =>
    Nat.mul_le_mul_right pv huv
  -- move 1: the right group slides into the long run
  have hinner : ∀ v : ℕ, v < 2 * h →
      (M.accepts (markAtN m (wrappedFlat n) (shiftGroup m ī (s₂ + G) σ (v * pv)))
        ↔ M.accepts (markAtN m (wrappedFlat n) ī)) := by
    intro v hv
    have hvpv := hmulv v hv
    refine acceptsN_moveGroup_multi M mv pv hEP n ī s₂ (s₂ + G) σ (σ + L) v
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
    intro i
    rcases hex₂ i with h2 | h2
    · left; exact h2
    · rcases hexL i with hL | hL
      · right; left; omega
      · right; right; omega
  -- move 2: the left group slides into the vacated space
  have houter : ∀ u v : ℕ, u < h → h ≤ v → v < 2 * h →
      (M.accepts (markAtN m (wrappedFlat n) (f (u, v)))
        ↔ M.accepts (markAtN m (wrappedFlat n)
            (shiftGroup m ī (s₂ + G) σ (v * pv)))) := by
    intro u v hu hhv hv
    have hvpv := hmulv v hv
    have huv := hmuluv u v (by omega)
    refine acceptsN_moveGroup_multi M mv pv hEP n
      (shiftGroup m ī (s₂ + G) σ (v * pv)) s₁ (s₁ + G) s₂ (s₂ + G + v * pv) u
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
    intro i
    by_cases hcond : 1 + 2 * (s₂ + G) ≤ ī i ∧ ī i < 1 + 2 * σ
    · rw [shiftGroup_apply_in ī (s₂ + G) σ (v * pv) i hcond]
      right; right; omega
    · rw [shiftGroup_apply_out ī (s₂ + G) σ (v * pv) i hcond]
      rcases hex₂ i with h2 | h2
      · rcases hex₁ i with h1 | h1
        · left; exact h1
        · right; left; omega
      · rcases hexL i with hL | hL
        · exact absurd ⟨by omega, by omega⟩ hcond
        · right; right; omega
  -- validity of the family members
  have hfvalid : ∀ u v : ℕ, u < h → v < 2 * h →
      ∀ i, f (u, v) i < (wrappedFlat n).length := by
    intro u v hu hv
    have hvpv := hmulv v hv
    have hupv : u * pv ≤ 2 * h * pv := hmulv u (by omega)
    exact shiftGroup_valid (shiftGroup m ī (s₂ + G) σ (v * pv)) (s₁ + G) s₂ (u * pv) n
      (by omega)
      (shiftGroup_valid ī (s₂ + G) σ (v * pv) n (by omega) hval)
  have hfacc : ∀ p ∈ S, (∀ i, f p i < (wrappedFlat n).length) ∧
      M.accepts (markAtN m (wrappedFlat n) (f p)) := by
    intro p hp
    obtain ⟨hu, hhv, hv⟩ := hSmem p hp
    refine ⟨hfvalid p.1 p.2 hu hv, ?_⟩
    rw [show f p = f (p.1, p.2) from rfl, houter p.1 p.2 hu hhv hv, hinner p.2 hv]
    exact hacc
  -- the two witnesses read off the parameters
  have hread₁ : ∀ u v : ℕ, f (u, v) i₁ = ī i₁ + 2 * (u * pv) := by
    intro u v
    show shiftGroup m (shiftGroup m ī (s₂ + G) σ (v * pv)) (s₁ + G) s₂ (u * pv) i₁
      = ī i₁ + 2 * (u * pv)
    have hin : shiftGroup m ī (s₂ + G) σ (v * pv) i₁ = ī i₁ :=
      shiftGroup_apply_out ī (s₂ + G) σ (v * pv) i₁ (by omega)
    rw [shiftGroup_apply_in (shiftGroup m ī (s₂ + G) σ (v * pv)) (s₁ + G) s₂ (u * pv) i₁
      (by rw [hin]; exact hi₁), hin]
  have hread₂ : ∀ u v : ℕ, f (u, v) i₂ = ī i₂ + 2 * (v * pv) := by
    intro u v
    show shiftGroup m (shiftGroup m ī (s₂ + G) σ (v * pv)) (s₁ + G) s₂ (u * pv) i₂
      = ī i₂ + 2 * (v * pv)
    have hin : shiftGroup m ī (s₂ + G) σ (v * pv) i₂ = ī i₂ + 2 * (v * pv) :=
      shiftGroup_apply_in ī (s₂ + G) σ (v * pv) i₂ hi₂
    rw [shiftGroup_apply_out (shiftGroup m ī (s₂ + G) σ (v * pv)) (s₁ + G) s₂ (u * pv) i₂
      (by rw [hin]; omega), hin]
  have hinj : Set.InjOn f S := by
    intro p hp q hq hpq
    have h1 := congrFun hpq i₁
    have h2 := congrFun hpq i₂
    rw [show f p = f (p.1, p.2) from rfl, show f q = f (q.1, q.2) from rfl] at h1 h2
    rw [hread₁ p.1 p.2, hread₁ q.1 q.2] at h1
    rw [hread₂ p.1 p.2, hread₂ q.1 q.2] at h2
    have hu : p.1 * pv = q.1 * pv := by omega
    have hv : p.2 * pv = q.2 * pv := by omega
    have hu' : p.1 = q.1 := Nat.eq_of_mul_eq_mul_right (by omega) hu
    have hv' : p.2 = q.2 := Nat.eq_of_mul_eq_mul_right (by omega) hv
    exact Prod.ext hu' hv'
  have hbound := card_le_of_injOn_accepted M C n S f hinj hfacc hcard
  have hScard : S.card = h * h := by
    rw [hSdef, Finset.card_product, Finset.card_range, Nat.card_Ico]
    congr 1
    omega
  omega

/-! ## The leftward move (route GA-3, L1) -/

/-- Leftward window shift: coordinates in `[1+2b, 1+2c)` move LEFT by `δ` blocks. -/
def shiftGroupLeft (m : ℕ) (ī : Fin m → ℕ) (b c δ : ℕ) : Fin m → ℕ :=
  fun i => if 1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c then ī i - 2 * δ else ī i

theorem shiftGroupLeft_apply_in {m : ℕ} (ī : Fin m → ℕ) (b c δ : ℕ) (i : Fin m)
    (h : 1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c) :
    shiftGroupLeft m ī b c δ i = ī i - 2 * δ := by
  unfold shiftGroupLeft
  exact if_pos h

theorem shiftGroupLeft_apply_out {m : ℕ} (ī : Fin m → ℕ) (b c δ : ℕ) (i : Fin m)
    (h : ¬ (1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c)) :
    shiftGroupLeft m ī b c δ i = ī i := by
  unfold shiftGroupLeft
  exact if_neg h

/-- Leftward shifts only decrease coordinates, so validity is free. -/
theorem shiftGroupLeft_valid {m : ℕ} (ī : Fin m → ℕ) (b c δ n : ℕ)
    (hval : ∀ i, ī i < (wrappedFlat n).length) :
    ∀ i, shiftGroupLeft m ī b c δ i < (wrappedFlat n).length := by
  intro i
  unfold shiftGroupLeft
  by_cases hcond : 1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c
  · rw [if_pos hcond]
    have := hval i
    omega
  · rw [if_neg hcond]
    exact hval i

/-- **The leftward multi-period move** (adjudicated L1): a group may move LEFT by any
multiple of the period, provided the TARGET left gap and the ORIGINAL right gap are
`≥ mv`.  Proved by exhibiting the original tuple as the rightward shift of the
left-shifted one and reading `acceptsN_moveGroup_multi` backwards. -/
theorem acceptsN_moveGroup_left {m : ℕ} (M : SliceMSO.DetAuto (MarkedN m))
    (mv pv : ℕ) (hEP : ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g])
    (n : ℕ) (ī : Fin m → ℕ) (a b c d k : ℕ)
    (hab : a + mv + k * pv ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hdn : d ≤ n)
    (hgapR : mv ≤ d - c)
    (hclass : ∀ i, ī i < 1 + 2 * a ∨ (1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c)
      ∨ 1 + 2 * d ≤ ī i) :
    M.accepts (markAtN m (wrappedFlat n) (shiftGroupLeft m ī b c (k * pv)))
      ↔ M.accepts (markAtN m (wrappedFlat n) ī) := by
  have hre : shiftGroup m (shiftGroupLeft m ī b c (k * pv))
      (b - k * pv) (c - k * pv) (k * pv) = ī := by
    funext i
    by_cases hB : 1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c
    · have hp := shiftGroupLeft_apply_in ī b c (k * pv) i hB
      rw [shiftGroup_apply_in (shiftGroupLeft m ī b c (k * pv))
        (b - k * pv) (c - k * pv) (k * pv) i
        (by rw [hp]; constructor <;> omega), hp]
      omega
    · have hp := shiftGroupLeft_apply_out ī b c (k * pv) i hB
      rw [shiftGroup_apply_out (shiftGroupLeft m ī b c (k * pv))
        (b - k * pv) (c - k * pv) (k * pv) i
        (by rw [hp]
            rcases hclass i with h1 | h1 | h1
            · intro hcon; omega
            · exact absurd h1 hB
            · intro hcon; omega), hp]
  have hmove := acceptsN_moveGroup_multi M mv pv hEP n
    (shiftGroupLeft m ī b c (k * pv)) a (b - k * pv) (c - k * pv) d k
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  · rw [hre] at hmove
    exact hmove.symm
  · intro i
    by_cases hB : 1 + 2 * b ≤ ī i ∧ ī i < 1 + 2 * c
    · rw [shiftGroupLeft_apply_in ī b c (k * pv) i hB]
      right; left
      constructor <;> omega
    · rw [shiftGroupLeft_apply_out ī b c (k * pv) i hB]
      rcases hclass i with h1 | h1 | h1
      · left; exact h1
      · exact absurd h1 hB
      · right; right; omega


/-- **The inward two-move quadratic family** (adjudicated L2): the long unmarked run
lies BETWEEN the two witness groups; the left group slides rightward into it
(parameter `u`) and the right group leftward into it (parameter `v`); the two
consumptions stay apart on the square, so `h²` distinct selected atoms arise. -/
theorem no_two_bulk_groups_between {m : ℕ} (M : SliceMSO.DetAuto (MarkedN m))
    (mv pv G : ℕ) (hpv : 1 ≤ pv) (hG : G = mv + pv)
    (hEP : ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g])
    (C n : ℕ)
    (hcard : ∀ l : List (Fin m → ℕ), l.Nodup →
      (∀ ī ∈ l, (∀ i, ī i < (wrappedFlat n).length) ∧
        M.accepts (markAtN m (wrappedFlat n) ī)) →
      l.length ≤ C * (n + 1))
    (ī : Fin m → ℕ) (hval : ∀ i, ī i < (wrappedFlat n).length)
    (hacc : M.accepts (markAtN m (wrappedFlat n) ī))
    (s₁ σ L s₂ h : ℕ)
    (hg₁ : ∀ jj, s₁ ≤ jj → jj < s₁ + G → ∀ i, ī i ≠ 1 + 2 * jj ∧ ī i ≠ 1 + 2 * jj + 1)
    (hgL : ∀ jj, σ ≤ jj → jj < σ + L → ∀ i, ī i ≠ 1 + 2 * jj ∧ ī i ≠ 1 + 2 * jj + 1)
    (hg₂ : ∀ jj, s₂ ≤ jj → jj < s₂ + G → ∀ i, ī i ≠ 1 + 2 * jj ∧ ī i ≠ 1 + 2 * jj + 1)
    (hw₁ : ∃ i, 1 + 2 * (s₁ + G) ≤ ī i ∧ ī i < 1 + 2 * σ)
    (hw₂ : ∃ i, 1 + 2 * (σ + L) ≤ ī i ∧ ī i < 1 + 2 * s₂)
    (hn : s₂ + G ≤ n)
    (hroom : mv + 2 * h * pv ≤ L)
    (hcount : C * (n + 1) < h * h) :
    False := by
  obtain ⟨i₁, hi₁⟩ := hw₁
  obtain ⟨i₂, hi₂⟩ := hw₂
  have hord₁ : s₁ + G < σ := by omega
  have hord₂ : σ + L < s₂ := by omega
  have hex₁ := unmarked_window_excludes ī s₁ (s₁ + G) hg₁
  have hexL := unmarked_window_excludes ī σ (σ + L) hgL
  have hex₂ := unmarked_window_excludes ī s₂ (s₂ + G) hg₂
  set f : ℕ × ℕ → (Fin m → ℕ) := fun p =>
    shiftGroupLeft m (shiftGroup m ī (s₁ + G) σ (p.1 * pv)) (σ + L) s₂ (p.2 * pv)
    with hfdef
  set S : Finset (ℕ × ℕ) := (Finset.range h) ×ˢ (Finset.range h) with hSdef
  have hSmem : ∀ p ∈ S, p.1 < h ∧ p.2 < h := by
    intro p hp
    rw [hSdef, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    exact hp
  have hmul : ∀ v : ℕ, v < h → v * pv + pv ≤ h * pv := by
    intro v hv
    have h1 : (v + 1) * pv ≤ h * pv := Nat.mul_le_mul_right pv (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    exact h1
  have h2hpv : 2 * h * pv = h * pv + h * pv := by ring
  -- step 1: slide the left group rightward into the run
  have hinner : ∀ u : ℕ, u < h →
      (M.accepts (markAtN m (wrappedFlat n) (shiftGroup m ī (s₁ + G) σ (u * pv)))
        ↔ M.accepts (markAtN m (wrappedFlat n) ī)) := by
    intro u hu
    have hupv := hmul u hu
    refine acceptsN_moveGroup_multi M mv pv hEP n ī s₁ (s₁ + G) σ (σ + L) u
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
    intro i
    rcases hex₁ i with h1 | h1
    · left; exact h1
    · rcases hexL i with hL | hL
      · right; left; omega
      · right; right; omega
  -- step 2: slide the right group leftward into the remaining run
  have houter : ∀ u v : ℕ, u < h → v < h →
      (M.accepts (markAtN m (wrappedFlat n) (f (u, v)))
        ↔ M.accepts (markAtN m (wrappedFlat n)
            (shiftGroup m ī (s₁ + G) σ (u * pv)))) := by
    intro u v hu hv
    have hupv := hmul u hu
    have hvpv := hmul v hv
    refine acceptsN_moveGroup_left M mv pv hEP n
      (shiftGroup m ī (s₁ + G) σ (u * pv)) (σ + u * pv) (σ + L) s₂ (s₂ + G) v
      (by omega) (by omega) (by omega) (by omega) (by omega) ?_
    intro i
    by_cases hA : 1 + 2 * (s₁ + G) ≤ ī i ∧ ī i < 1 + 2 * σ
    · rw [shiftGroup_apply_in ī (s₁ + G) σ (u * pv) i hA]
      left; omega
    · rw [shiftGroup_apply_out ī (s₁ + G) σ (u * pv) i hA]
      rcases hexL i with hL | hL
      · left; omega
      · rcases hex₂ i with h2 | h2
        · right; left; omega
        · right; right; omega
  -- validity
  have hfvalid : ∀ u v : ℕ, u < h → v < h →
      ∀ i, f (u, v) i < (wrappedFlat n).length := by
    intro u v hu hv
    have hupv := hmul u hu
    exact shiftGroupLeft_valid _ (σ + L) s₂ (v * pv) n
      (shiftGroup_valid ī (s₁ + G) σ (u * pv) n (by omega) hval)
  have hfacc : ∀ p ∈ S, (∀ i, f p i < (wrappedFlat n).length) ∧
      M.accepts (markAtN m (wrappedFlat n) (f p)) := by
    intro p hp
    obtain ⟨hu, hv⟩ := hSmem p hp
    refine ⟨hfvalid p.1 p.2 hu hv, ?_⟩
    rw [show f p = f (p.1, p.2) from rfl, houter p.1 p.2 hu hv, hinner p.1 hu]
    exact hacc
  -- parameter readback
  have hread₁ : ∀ u v : ℕ, u < h → f (u, v) i₁ = ī i₁ + 2 * (u * pv) := by
    intro u v hu
    have hupv := hmul u hu
    show shiftGroupLeft m (shiftGroup m ī (s₁ + G) σ (u * pv)) (σ + L) s₂ (v * pv) i₁
      = ī i₁ + 2 * (u * pv)
    have hin : shiftGroup m ī (s₁ + G) σ (u * pv) i₁ = ī i₁ + 2 * (u * pv) :=
      shiftGroup_apply_in ī (s₁ + G) σ (u * pv) i₁ hi₁
    rw [shiftGroupLeft_apply_out (shiftGroup m ī (s₁ + G) σ (u * pv)) (σ + L) s₂
      (v * pv) i₁ (by rw [hin]; intro hcon; omega), hin]
  have hread₂ : ∀ u v : ℕ, f (u, v) i₂ = ī i₂ - 2 * (v * pv) := by
    intro u v
    show shiftGroupLeft m (shiftGroup m ī (s₁ + G) σ (u * pv)) (σ + L) s₂ (v * pv) i₂
      = ī i₂ - 2 * (v * pv)
    have hin : shiftGroup m ī (s₁ + G) σ (u * pv) i₂ = ī i₂ :=
      shiftGroup_apply_out ī (s₁ + G) σ (u * pv) i₂ (by omega)
    rw [shiftGroupLeft_apply_in (shiftGroup m ī (s₁ + G) σ (u * pv)) (σ + L) s₂
      (v * pv) i₂ (by rw [hin]; exact hi₂), hin]
  have hinj : Set.InjOn f S := by
    intro p hp q hq hpq
    obtain ⟨hpu, hpv2⟩ := hSmem p hp
    obtain ⟨hqu, hqv2⟩ := hSmem q hq
    have hppv := hmul p.2 hpv2
    have hqpv := hmul q.2 hqv2
    have h1 := congrFun hpq i₁
    have h2 := congrFun hpq i₂
    rw [show f p = f (p.1, p.2) from rfl, show f q = f (q.1, q.2) from rfl] at h1 h2
    rw [hread₁ p.1 p.2 hpu, hread₁ q.1 q.2 hqu] at h1
    rw [hread₂ p.1 p.2, hread₂ q.1 q.2] at h2
    have hu : p.1 * pv = q.1 * pv := by omega
    have hv : p.2 * pv = q.2 * pv := by omega
    have hu' : p.1 = q.1 := Nat.eq_of_mul_eq_mul_right (by omega) hu
    have hv' : p.2 = q.2 := Nat.eq_of_mul_eq_mul_right (by omega) hv
    exact Prod.ext hu' hv'
  have hbound := card_le_of_injOn_accepted M C n S f hinj hfacc hcard
  have hScard : S.card = h * h := by
    rw [hSdef, Finset.card_product, Finset.card_range]
  omega


/-- **The leftward two-move quadratic family** (adjudicated L3): the long unmarked run
lies LEFT of both witness groups; the left group parks into it (parameter
`u ∈ [h, 2h)`) and the right group follows into the vacated middle gap (parameter
`v < h ≤ u`), giving `h²` distinct selected atoms. -/
theorem no_two_bulk_groups_left {m : ℕ} (M : SliceMSO.DetAuto (MarkedN m))
    (mv pv G : ℕ) (hpv : 1 ≤ pv) (hG : G = mv + pv)
    (hEP : ∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g])
    (C n : ℕ)
    (hcard : ∀ l : List (Fin m → ℕ), l.Nodup →
      (∀ ī ∈ l, (∀ i, ī i < (wrappedFlat n).length) ∧
        M.accepts (markAtN m (wrappedFlat n) ī)) →
      l.length ≤ C * (n + 1))
    (ī : Fin m → ℕ) (hval : ∀ i, ī i < (wrappedFlat n).length)
    (hacc : M.accepts (markAtN m (wrappedFlat n) ī))
    (σ L s₁ s₂ h : ℕ)
    (hgL : ∀ jj, σ ≤ jj → jj < σ + L → ∀ i, ī i ≠ 1 + 2 * jj ∧ ī i ≠ 1 + 2 * jj + 1)
    (hg₁ : ∀ jj, s₁ ≤ jj → jj < s₁ + G → ∀ i, ī i ≠ 1 + 2 * jj ∧ ī i ≠ 1 + 2 * jj + 1)
    (hg₂ : ∀ jj, s₂ ≤ jj → jj < s₂ + G → ∀ i, ī i ≠ 1 + 2 * jj ∧ ī i ≠ 1 + 2 * jj + 1)
    (hw₁ : ∃ i, 1 + 2 * (σ + L) ≤ ī i ∧ ī i < 1 + 2 * s₁)
    (hw₂ : ∃ i, 1 + 2 * (s₁ + G) ≤ ī i ∧ ī i < 1 + 2 * s₂)
    (hn : s₂ + G ≤ n)
    (hroom : mv + 2 * h * pv ≤ L)
    (hcount : C * (n + 1) < h * h) :
    False := by
  obtain ⟨i₁, hi₁⟩ := hw₁
  obtain ⟨i₂, hi₂⟩ := hw₂
  have hord₁ : σ + L < s₁ := by omega
  have hord₂ : s₁ + G < s₂ := by omega
  have hexL := unmarked_window_excludes ī σ (σ + L) hgL
  have hex₁ := unmarked_window_excludes ī s₁ (s₁ + G) hg₁
  have hex₂ := unmarked_window_excludes ī s₂ (s₂ + G) hg₂
  set f : ℕ × ℕ → (Fin m → ℕ) := fun p =>
    shiftGroupLeft m (shiftGroupLeft m ī (σ + L) s₁ (p.1 * pv)) (s₁ + G) s₂ (p.2 * pv)
    with hfdef
  set S : Finset (ℕ × ℕ) := (Finset.Ico h (2 * h)) ×ˢ (Finset.range h) with hSdef
  have hSmem : ∀ p ∈ S, (h ≤ p.1 ∧ p.1 < 2 * h) ∧ p.2 < h := by
    intro p hp
    rw [hSdef, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hp
    exact hp
  have hmul2 : ∀ u : ℕ, u < 2 * h → u * pv + pv ≤ 2 * h * pv := by
    intro u hu
    have h1 : (u + 1) * pv ≤ 2 * h * pv := Nat.mul_le_mul_right pv (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    exact h1
  have hmuluv : ∀ v u : ℕ, v ≤ u → v * pv ≤ u * pv := fun v u hvu =>
    Nat.mul_le_mul_right pv hvu
  -- step 1: the left group parks into the long run
  have hinner : ∀ u : ℕ, u < 2 * h →
      (M.accepts (markAtN m (wrappedFlat n) (shiftGroupLeft m ī (σ + L) s₁ (u * pv)))
        ↔ M.accepts (markAtN m (wrappedFlat n) ī)) := by
    intro u hu
    have hupv := hmul2 u hu
    refine acceptsN_moveGroup_left M mv pv hEP n ī σ (σ + L) s₁ (s₁ + G) u
      (by omega) (by omega) (by omega) (by omega) (by omega) ?_
    intro i
    rcases hexL i with hL | hL
    · left; exact hL
    · rcases hex₁ i with h1 | h1
      · right; left; omega
      · right; right; omega
  -- step 2: the right group follows into the vacated middle gap
  have houter : ∀ u v : ℕ, h ≤ u → u < 2 * h → v < h →
      (M.accepts (markAtN m (wrappedFlat n) (f (u, v)))
        ↔ M.accepts (markAtN m (wrappedFlat n)
            (shiftGroupLeft m ī (σ + L) s₁ (u * pv)))) := by
    intro u v hhu hu hv
    have hupv := hmul2 u hu
    have hvu := hmuluv v u (by omega)
    refine acceptsN_moveGroup_left M mv pv hEP n
      (shiftGroupLeft m ī (σ + L) s₁ (u * pv)) (s₁ - u * pv) (s₁ + G) s₂ (s₂ + G) v
      (by omega) (by omega) (by omega) (by omega) (by omega) ?_
    intro i
    by_cases hA : 1 + 2 * (σ + L) ≤ ī i ∧ ī i < 1 + 2 * s₁
    · rw [shiftGroupLeft_apply_in ī (σ + L) s₁ (u * pv) i hA]
      left; omega
    · rw [shiftGroupLeft_apply_out ī (σ + L) s₁ (u * pv) i hA]
      rcases hexL i with hL | hL
      · left; omega
      · rcases hex₁ i with h1 | h1
        · exact absurd ⟨by omega, by omega⟩ hA
        · rcases hex₂ i with h2 | h2
          · right; left; omega
          · right; right; omega
  -- validity (leftward shifts only decrease)
  have hfvalid : ∀ u v : ℕ, ∀ i, f (u, v) i < (wrappedFlat n).length := by
    intro u v
    exact shiftGroupLeft_valid _ (s₁ + G) s₂ (v * pv) n
      (shiftGroupLeft_valid ī (σ + L) s₁ (u * pv) n hval)
  have hfacc : ∀ p ∈ S, (∀ i, f p i < (wrappedFlat n).length) ∧
      M.accepts (markAtN m (wrappedFlat n) (f p)) := by
    intro p hp
    obtain ⟨⟨hhu, hu⟩, hv⟩ := hSmem p hp
    refine ⟨hfvalid p.1 p.2, ?_⟩
    rw [show f p = f (p.1, p.2) from rfl, houter p.1 p.2 hhu hu hv, hinner p.1 hu]
    exact hacc
  -- parameter readback
  have hread₁ : ∀ u v : ℕ, u < 2 * h → f (u, v) i₁ = ī i₁ - 2 * (u * pv) := by
    intro u v hu
    have hupv := hmul2 u hu
    show shiftGroupLeft m (shiftGroupLeft m ī (σ + L) s₁ (u * pv)) (s₁ + G) s₂
      (v * pv) i₁ = ī i₁ - 2 * (u * pv)
    have hin : shiftGroupLeft m ī (σ + L) s₁ (u * pv) i₁ = ī i₁ - 2 * (u * pv) :=
      shiftGroupLeft_apply_in ī (σ + L) s₁ (u * pv) i₁ hi₁
    rw [shiftGroupLeft_apply_out (shiftGroupLeft m ī (σ + L) s₁ (u * pv)) (s₁ + G) s₂
      (v * pv) i₁ (by rw [hin]; intro hcon; omega), hin]
  have hread₂ : ∀ u v : ℕ, f (u, v) i₂ = ī i₂ - 2 * (v * pv) := by
    intro u v
    show shiftGroupLeft m (shiftGroupLeft m ī (σ + L) s₁ (u * pv)) (s₁ + G) s₂
      (v * pv) i₂ = ī i₂ - 2 * (v * pv)
    have hin : shiftGroupLeft m ī (σ + L) s₁ (u * pv) i₂ = ī i₂ :=
      shiftGroupLeft_apply_out ī (σ + L) s₁ (u * pv) i₂ (by omega)
    rw [shiftGroupLeft_apply_in (shiftGroupLeft m ī (σ + L) s₁ (u * pv)) (s₁ + G) s₂
      (v * pv) i₂ (by rw [hin]; exact hi₂), hin]
  have hinj : Set.InjOn f S := by
    intro p hp q hq hpq
    obtain ⟨⟨hpuh, hpu⟩, hpv2⟩ := hSmem p hp
    obtain ⟨⟨hquh, hqu⟩, hqv2⟩ := hSmem q hq
    have hppv := hmul2 p.1 hpu
    have hqpv := hmul2 q.1 hqu
    have hpv2' := hmuluv p.2 p.1 (by omega)
    have hqv2' := hmuluv q.2 q.1 (by omega)
    have h1 := congrFun hpq i₁
    have h2 := congrFun hpq i₂
    rw [show f p = f (p.1, p.2) from rfl, show f q = f (q.1, q.2) from rfl] at h1 h2
    rw [hread₁ p.1 p.2 hpu, hread₁ q.1 q.2 hqu] at h1
    rw [hread₂ p.1 p.2, hread₂ q.1 q.2] at h2
    have hu : p.1 * pv = q.1 * pv := by omega
    have hv : p.2 * pv = q.2 * pv := by omega
    have hu' : p.1 = q.1 := Nat.eq_of_mul_eq_mul_right (by omega) hu
    have hv' : p.2 = q.2 := Nat.eq_of_mul_eq_mul_right (by omega) hv
    exact Prod.ext hu' hv'
  have hbound := card_le_of_injOn_accepted M C n S f hinj hfacc hcard
  have hScard : S.card = h * h := by
    rw [hSdef, Finset.card_product, Finset.card_range, Nat.card_Ico]
    congr 1
    omega
  omega


/-- **Quadratic beats linear** (adjudicated L4): beyond an explicit threshold, the
square of `(n / D - E) / (2p)` exceeds `C * (n + 1)`. -/
theorem quadratic_beats_linear (C D E p : ℕ) (hp : 1 ≤ p) (hD : 1 ≤ D) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      C * (n + 1) < ((n / D - E) / (2 * p)) * ((n / D - E) / (2 * p)) := by
  refine ⟨D * (2 * p * (2*C*D*p + C*D*(2*p+E+1) + C + 1) + E), fun n hn => ?_⟩
  set H : ℕ := 2*C*D*p + C*D*(2*p+E+1) + C + 1 with hH
  set h : ℕ := (n / D - E) / (2 * p) with hh
  set r : ℕ := (n / D - E) % (2 * p) with hr
  set s : ℕ := n % D with hs
  have e1 : n = D * (n / D) + s := by
    rw [hs]
    exact (Nat.div_add_mod n D).symm
  have e2 : s < D := by
    rw [hs]
    exact Nat.mod_lt n (by omega)
  have e3 : n / D - E = 2 * p * h + r := by
    rw [hh, hr]
    exact (Nat.div_add_mod (n / D - E) (2 * p)).symm
  have e4 : r < 2 * p := by
    rw [hr]
    exact Nat.mod_lt _ (by omega)
  have h5 : 2 * p * H + E ≤ n / D := by
    rw [Nat.le_div_iff_mul_le (show 0 < D by omega)]
    have hc := Nat.mul_comm (2 * p * H + E) D
    omega
  have h6 : H ≤ h := by
    rw [hh, Nat.le_div_iff_mul_le (show 0 < 2 * p by omega)]
    have hc := Nat.mul_comm H (2 * p)
    omega
  have b1 : C * (n + 1) ≤ C*D*(n / D) + C*D := by
    have hb : n + 1 ≤ D * (n / D) + D := by omega
    calc C * (n + 1) ≤ C * (D * (n / D) + D) := Nat.mul_le_mul_left C hb
      _ = C*D*(n / D) + C*D := by ring
  have b2 : C*D*(n / D) ≤ C*D*(2 * p * h + r + E) :=
    Nat.mul_le_mul_left (C*D) (by omega)
  have b3 : C*D*(2 * p * h + r + E) = (2*C*D*p)*h + C*D*(r+E) := by ring
  have b4 : C*D*(r+E) ≤ C*D*(2*p+E) := Nat.mul_le_mul_left (C*D) (by omega)
  have q1 : H * h ≤ h * h := Nat.mul_le_mul_right h h6
  have q2 : H * h = (2*C*D*p)*h + (C*D*(2*p+E+1))*h + C*h + h := by
    rw [hH]
    ring
  have q3 : C*D*(2*p+E) + C*D + 1 ≤ (C*D*(2*p+E+1))*h + C*h + h := by
    have hh1 : 1 ≤ h := by omega
    have t1 : C*D*(2*p+E+1) * 1 ≤ (C*D*(2*p+E+1)) * h :=
      Nat.mul_le_mul_left _ hh1
    rw [Nat.mul_one] at t1
    have t2 : C*D*(2*p+E+1) = C*D*(2*p+E) + C*D := by ring
    omega
  omega


/-- **The bad-pair collapse** (adjudicated L5, tuple level): for any per-atom DFA `M`
and growth budget `C`, beyond explicit thresholds `B, N` no accepted valid tuple has
two block coordinates that are `B`-deep in the bulk and `B`-separated — the long-run
trichotomy dispatches to the three two-move quadratic families. -/
theorem bad_pair_collapse {m : ℕ} (M : SliceMSO.DetAuto (MarkedN m)) (C : ℕ) :
    ∃ B N : ℕ, 1 ≤ B ∧ ∀ n, N ≤ n → ∀ ī : Fin m → ℕ,
      (∀ i, ī i < (wrappedFlat n).length) →
      M.accepts (markAtN m (wrappedFlat n) ī) →
      (∀ l : List (Fin m → ℕ), l.Nodup →
        (∀ x ∈ l, (∀ i, x i < (wrappedFlat n).length) ∧
          M.accepts (markAtN m (wrappedFlat n) x)) →
        l.length ≤ C * (n + 1)) →
      ∀ (i₁ i₂ : Fin m) (j j' : ℕ),
        (ī i₁ = 1 + 2 * j ∨ ī i₁ = 1 + 2 * j + 1) →
        (ī i₂ = 1 + 2 * j' ∨ ī i₂ = 1 + 2 * j' + 1) →
        B ≤ j → j + B ≤ j' → j' + B ≤ n → False := by
  obtain ⟨mv, pv, hpv, hEP⟩ := bFN_func_iterate_eventuallyPeriodic M
  set G : ℕ := mv + pv with hGdef
  obtain ⟨N₀, hN₀⟩ := quadratic_beats_linear C (m + 1) mv pv hpv (by omega)
  have hBlin : (m + 2) * G + 2 = (m + 1) * G + G + 2 := by ring
  refine ⟨(m + 2) * G + 2, N₀, by omega, ?_⟩
  intro n hn ī hval hacc hcard i₁ i₂ j j' hbj hbj' hBj hjj' hj'n
  -- the long run
  set G' : ℕ := n / (m + 1) with hG'def
  obtain ⟨σ, hσ0, hσtop, hbig⟩ := exists_unmarked_gap ī G' 0
  have hG'n : (m + 1) * G' ≤ n := by
    rw [hG'def]
    have hd := Nat.div_mul_le_self n (m + 1)
    have hc := Nat.mul_comm (n / (m + 1)) (m + 1)
    omega
  have hσn : σ + G' ≤ n := by omega
  set h : ℕ := (G' - mv) / (2 * pv) with hhdef
  have hcount : C * (n + 1) < h * h := by
    rw [hhdef, hG'def]
    exact hN₀ n hn
  have hroom : mv + 2 * h * pv ≤ G' := by
    have hh1 : 1 ≤ h := by
      rcases Nat.eq_zero_or_pos h with h0 | h1
      · rw [h0] at hcount
        omega
      · exact h1
    have hdm : h * (2 * pv) ≤ G' - mv := by
      rw [hhdef]
      exact Nat.div_mul_le_self (G' - mv) (2 * pv)
    have hge : 1 * (2 * pv) ≤ h * (2 * pv) := Nat.mul_le_mul_right (2 * pv) hh1
    rw [Nat.one_mul] at hge
    have hc : 2 * h * pv = h * (2 * pv) := by ring
    omega
  -- the run avoids the two marked blocks
  have hjout : ¬ (σ ≤ j ∧ j < σ + G') := by
    rintro ⟨h1, h2⟩
    have := hbig j h1 h2 i₁
    omega
  have hj'out : ¬ (σ ≤ j' ∧ j' < σ + G') := by
    rintro ⟨h1, h2⟩
    have := hbig j' h1 h2 i₂
    omega
  have htri : σ + G' ≤ j ∨ (j < σ ∧ σ + G' ≤ j') ∨ j' < σ := by omega
  rcases htri with hcase | hcase | hcase
  · -- the run is LEFT of both groups
    obtain ⟨sA, hsAlo, hsAtop, hgapA⟩ := exists_unmarked_gap ī G (j + 1)
    obtain ⟨sB, hsBlo, hsBtop, hgapB⟩ := exists_unmarked_gap ī G (j' + 1)
    exact no_two_bulk_groups_left M mv pv G hpv hGdef hEP C n hcard ī hval hacc
      σ G' sA sB h hbig hgapA hgapB
      ⟨i₁, by omega⟩ ⟨i₂, by omega⟩ (by omega) hroom hcount
  · -- the run is BETWEEN the groups
    obtain ⟨sA, hsAlo, hsAtop, hgapA⟩ := exists_unmarked_gap ī G (j - (m + 1) * G)
    obtain ⟨sB, hsBlo, hsBtop, hgapB⟩ := exists_unmarked_gap ī G (j' + 1)
    exact no_two_bulk_groups_between M mv pv G hpv hGdef hEP C n hcard ī hval hacc
      sA σ G' sB h hgapA hbig hgapB
      ⟨i₁, by omega⟩ ⟨i₂, by omega⟩ (by omega) hroom hcount
  · -- the run is RIGHT of both groups
    obtain ⟨sA, hsAlo, hsAtop, hgapA⟩ := exists_unmarked_gap ī G (j - (m + 1) * G)
    obtain ⟨sB, hsBlo, hsBtop, hgapB⟩ := exists_unmarked_gap ī G (j + 1)
    exact no_two_bulk_groups_right M mv pv G hpv hGdef hEP C n hcard ī hval hacc
      sA sB σ G' h hgapA hgapB hbig
      ⟨i₁, by omega⟩ ⟨i₂, by omega⟩ hσn hroom hcount


/-- **The bad-pair collapse, pinned and machine-quantified** (§9 tower,
Stage D): the depth constant is the EXPLICIT `(m+2)·(mv+pv)+2` and the
threshold `N` is chosen from `(C, mv, pv)` alone — BEFORE the machine.  Every
machine sharing the period data (in particular every re-rooted/pulled-back
machine, whose `bFN` is literally the original's) is covered by the same
`B` and `N`.  This is the worker behind the fibred one-cluster property. -/
theorem bad_pair_collapse_pinned {m : ℕ} (mv pv : ℕ) (hpv : 1 ≤ pv) (C : ℕ) :
    ∃ N : ℕ, ∀ (M : SliceMSO.DetAuto (MarkedN m)),
      (∀ g, mv ≤ g → (bFN M)^[g + pv] = (bFN M)^[g]) →
      ∀ n, N ≤ n → ∀ ī : Fin m → ℕ,
      (∀ i, ī i < (wrappedFlat n).length) →
      M.accepts (markAtN m (wrappedFlat n) ī) →
      (∀ l : List (Fin m → ℕ), l.Nodup →
        (∀ x ∈ l, (∀ i, x i < (wrappedFlat n).length) ∧
          M.accepts (markAtN m (wrappedFlat n) x)) →
        l.length ≤ C * (n + 1)) →
      ∀ (i₁ i₂ : Fin m) (j j' : ℕ),
        (ī i₁ = 1 + 2 * j ∨ ī i₁ = 1 + 2 * j + 1) →
        (ī i₂ = 1 + 2 * j' ∨ ī i₂ = 1 + 2 * j' + 1) →
        (m + 2) * (mv + pv) + 2 ≤ j → j + (m + 2) * (mv + pv) + 2 ≤ j' →
        j' + (m + 2) * (mv + pv) + 2 ≤ n → False := by
  obtain ⟨N₀, hN₀⟩ := quadratic_beats_linear C (m + 1) mv pv hpv (by omega)
  refine ⟨N₀, fun M hEP => ?_⟩
  set G : ℕ := mv + pv with hGdef
  have hBlin : (m + 2) * G + 2 = (m + 1) * G + G + 2 := by ring
  intro n hn ī hval hacc hcard i₁ i₂ j j' hbj hbj' hBj hjj' hj'n
  rw [hGdef] at hBj hjj' hj'n
  have hBj' : (m + 2) * (mv + pv) + 2 ≤ j := hBj
  have hjj'' : j + ((m + 2) * (mv + pv) + 2) ≤ j' := by omega
  have hj'n' : j' + ((m + 2) * (mv + pv) + 2) ≤ n := by omega
  rw [← hGdef] at hBj' hjj'' hj'n'
  clear hBj hjj' hj'n
  rename' hBj' => hBj, hjj'' => hjj', hj'n' => hj'n
  -- the long run
  set G' : ℕ := n / (m + 1) with hG'def
  obtain ⟨σ, hσ0, hσtop, hbig⟩ := exists_unmarked_gap ī G' 0
  have hG'n : (m + 1) * G' ≤ n := by
    rw [hG'def]
    have hd := Nat.div_mul_le_self n (m + 1)
    have hc := Nat.mul_comm (n / (m + 1)) (m + 1)
    omega
  have hσn : σ + G' ≤ n := by omega
  set h : ℕ := (G' - mv) / (2 * pv) with hhdef
  have hcount : C * (n + 1) < h * h := by
    rw [hhdef, hG'def]
    exact hN₀ n hn
  have hroom : mv + 2 * h * pv ≤ G' := by
    have hh1 : 1 ≤ h := by
      rcases Nat.eq_zero_or_pos h with h0 | h1
      · rw [h0] at hcount
        omega
      · exact h1
    have hdm : h * (2 * pv) ≤ G' - mv := by
      rw [hhdef]
      exact Nat.div_mul_le_self (G' - mv) (2 * pv)
    have hge : 1 * (2 * pv) ≤ h * (2 * pv) := Nat.mul_le_mul_right (2 * pv) hh1
    rw [Nat.one_mul] at hge
    have hc : 2 * h * pv = h * (2 * pv) := by ring
    omega
  -- the run avoids the two marked blocks
  have hjout : ¬ (σ ≤ j ∧ j < σ + G') := by
    rintro ⟨h1, h2⟩
    have := hbig j h1 h2 i₁
    omega
  have hj'out : ¬ (σ ≤ j' ∧ j' < σ + G') := by
    rintro ⟨h1, h2⟩
    have := hbig j' h1 h2 i₂
    omega
  have htri : σ + G' ≤ j ∨ (j < σ ∧ σ + G' ≤ j') ∨ j' < σ := by omega
  rcases htri with hcase | hcase | hcase
  · -- the run is LEFT of both groups
    obtain ⟨sA, hsAlo, hsAtop, hgapA⟩ := exists_unmarked_gap ī G (j + 1)
    obtain ⟨sB, hsBlo, hsBtop, hgapB⟩ := exists_unmarked_gap ī G (j' + 1)
    exact no_two_bulk_groups_left M mv pv G hpv hGdef hEP C n hcard ī hval hacc
      σ G' sA sB h hbig hgapA hgapB
      ⟨i₁, by omega⟩ ⟨i₂, by omega⟩ (by omega) hroom hcount
  · -- the run is BETWEEN the groups
    obtain ⟨sA, hsAlo, hsAtop, hgapA⟩ := exists_unmarked_gap ī G (j - (m + 1) * G)
    obtain ⟨sB, hsBlo, hsBtop, hgapB⟩ := exists_unmarked_gap ī G (j' + 1)
    exact no_two_bulk_groups_between M mv pv G hpv hGdef hEP C n hcard ī hval hacc
      sA σ G' sB h hgapA hbig hgapB
      ⟨i₁, by omega⟩ ⟨i₂, by omega⟩ (by omega) hroom hcount
  · -- the run is RIGHT of both groups
    obtain ⟨sA, hsAlo, hsAtop, hgapA⟩ := exists_unmarked_gap ī G (j - (m + 1) * G)
    obtain ⟨sB, hsBlo, hsBtop, hgapB⟩ := exists_unmarked_gap ī G (j + 1)
    exact no_two_bulk_groups_right M mv pv G hpv hGdef hEP C n hcard ī hval hacc
      sA sB σ G' h hgapA hgapB hbig
      ⟨i₁, by omega⟩ ⟨i₂, by omega⟩ hσn hroom hcount


/-- The budget-hoisted corollary: `B` before `C`. -/
theorem bad_pair_collapse_hoisted {m : ℕ} (M : SliceMSO.DetAuto (MarkedN m)) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ C : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ∀ ī : Fin m → ℕ,
      (∀ i, ī i < (wrappedFlat n).length) →
      M.accepts (markAtN m (wrappedFlat n) ī) →
      (∀ l : List (Fin m → ℕ), l.Nodup →
        (∀ x ∈ l, (∀ i, x i < (wrappedFlat n).length) ∧
          M.accepts (markAtN m (wrappedFlat n) x)) →
        l.length ≤ C * (n + 1)) →
      ∀ (i₁ i₂ : Fin m) (j j' : ℕ),
        (ī i₁ = 1 + 2 * j ∨ ī i₁ = 1 + 2 * j + 1) →
        (ī i₂ = 1 + 2 * j' ∨ ī i₂ = 1 + 2 * j' + 1) →
        B ≤ j → j + B ≤ j' → j' + B ≤ n → False := by
  obtain ⟨mv, pv, hpv, hEP⟩ := bFN_func_iterate_eventuallyPeriodic M
  refine ⟨(m + 2) * (mv + pv) + 2, by omega, fun C => ?_⟩
  obtain ⟨N, hN⟩ := bad_pair_collapse_pinned mv pv hpv C (m := m)
  exact ⟨N, fun n hn ī hval hacc hcard i₁ i₂ j j' hbj hbj' hBj hjj' hj'n =>
    hN M hEP n hn ī hval hacc hcard i₁ i₂ j j' hbj hbj'
      hBj (by omega) (by omega)⟩

/-- **The one-cluster property** (adjudicated L6, the GA-3 capstone): for a WRP
presentation and growth budget `C` there are thresholds `B, N` such that for all
`n ≥ N`, no selected atom of any copy whose per-copy selected-tuple counts respect
the budget has two block coordinates `B`-deep in the bulk and `B`-separated.
Eventually every selected atom is one bounded bulk cluster plus boundary-pinned
decorations — the arity-1 geometry. -/
theorem one_cluster (P : WRP.Presentation Step Step) (C : ℕ) :
    ∃ B N : ℕ, 1 ≤ B ∧ ∀ n, N ≤ n → ∀ c : Fin P.toPoly.K,
      ∀ ī : Fin (P.toPoly.arity c) → ℕ,
      P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩ →
      (∀ l : List (Fin (P.toPoly.arity c) → ℕ), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) →
      ∀ (i₁ i₂ : Fin (P.toPoly.arity c)) (j j' : ℕ),
        (ī i₁ = 1 + 2 * j ∨ ī i₁ = 1 + 2 * j + 1) →
        (ī i₂ = 1 + 2 * j' ∨ ī i₂ = 1 + 2 * j' + 1) →
        B ≤ j → j + B ≤ j' → j' + B ≤ n → False := by
  have hMs := fun c => exists_selDFA P c
  choose M hM using hMs
  have hbps := fun c => bad_pair_collapse (M c) C
  choose Bc Nc hBc1 hbp using hbps
  refine ⟨max 1 (Finset.univ.sup Bc), Finset.univ.sup Nc, le_max_left 1 _, ?_⟩
  intro n hn c ī hsel hcard i₁ i₂ j j' hbj hbj' hBj hjj' hj'n
  have hsupB : Bc c ≤ max 1 (Finset.univ.sup Bc) :=
    le_trans (Finset.le_sup (f := Bc) (Finset.mem_univ c)) (le_max_right _ _)
  have hsupN : Nc c ≤ Finset.univ.sup Nc :=
    Finset.le_sup (f := Nc) (Finset.mem_univ c)
  have hvalid : ∀ i, ī i < (wrappedFlat n).length := fun i => hsel.1 i
  refine hbp c n (by omega) ī hvalid
    ((hM c (wrappedFlat n) ī hvalid).mpr hsel.2) ?_ i₁ i₂ j j' hbj hbj'
    (by omega) (by omega) (by omega)
  intro l hnd hmem
  refine hcard l hnd (fun x hx => ?_)
  exact ⟨(hmem x hx).1, ((hM c (wrappedFlat n) x (hmem x hx).1).mp (hmem x hx).2)⟩


/-- The growth-budget hypothesis of `one_cluster`, supplied at in-domain slices by
any output of length `≤ C(n+1)` (downstream: from `hPT` and `hgrow`). -/
theorem one_cluster_hcard_of_output {Alpha Gamma : Type*} (P : WRP.Presentation Alpha Gamma)
    (w : List Alpha) (out : List Gamma) (hout : P.IsOutput w out) (C n : ℕ)
    (hlen : out.length ≤ C * (n + 1)) (c : Fin P.toPoly.K) :
    ∀ l : List (Fin (P.toPoly.arity c) → ℕ), l.Nodup →
      (∀ x ∈ l, P.toPoly.selectedAtom w ⟨c, x⟩) →
      l.length ≤ C * (n + 1) :=
  fun l hnd hsel => le_trans (nodup_selected_length_le P w out hout c l hnd hsel) hlen


/-! ## The cells form (the GA-4 interface) -/

/-- Position `q` lies in block `j` of the slice. -/
def inBlock (q j : ℕ) : Prop := q = 1 + 2 * j ∨ q = 1 + 2 * j + 1

/-- Per-coordinate classification of a valid slice position: the pre letter, the
suffix letter, or a block position with its block index. -/
theorem position_cases (q n : ℕ) (hq : q < 2 * (n + 1)) :
    q = 0 ∨ q = 1 + 2 * n ∨ ((q - 1) / 2 < n ∧ inBlock q ((q - 1) / 2)) := by
  unfold inBlock
  omega

/-- **The cells form** (adjudicated L7, the GA-4 interface): beyond the thresholds,
every budget-respecting selected atom splits per coordinate as pre `0` / suffix
`1+2n` / front-pinned (block `< B`) / back-pinned (block `n−e`, `1 ≤ e < B`) /
member of ONE bulk cluster at a shared base `t` (block `t+δ`, `δ < B`,
`B ≤ t`, `t+B ≤ n`), with the base attained by some coordinate. -/
theorem one_cluster_cells (P : WRP.Presentation Step Step) (C : ℕ) :
    ∃ B N : ℕ, 1 ≤ B ∧ ∀ n, N ≤ n → ∀ c : Fin P.toPoly.K,
      ∀ ī : Fin (P.toPoly.arity c) → ℕ,
      P.toPoly.selectedAtom (wrappedFlat n) ⟨c, ī⟩ →
      (∀ l : List (Fin (P.toPoly.arity c) → ℕ), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) →
      (∀ i, ī i = 0 ∨ ī i = 1 + 2 * n
          ∨ (∃ f, f < B ∧ inBlock (ī i) f)
          ∨ (∃ e, 1 ≤ e ∧ e < B ∧ inBlock (ī i) (n - e)))
        ∨ (∃ t, B ≤ t ∧ t + B ≤ n ∧ (∃ i₀, inBlock (ī i₀) t) ∧
            ∀ i, ī i = 0 ∨ ī i = 1 + 2 * n
              ∨ (∃ f, f < B ∧ inBlock (ī i) f)
              ∨ (∃ e, 1 ≤ e ∧ e < B ∧ inBlock (ī i) (n - e))
              ∨ (∃ δ, δ < B ∧ inBlock (ī i) (t + δ))) := by
  classical
  obtain ⟨B, N, hB1, hoc⟩ := one_cluster P C
  refine ⟨B, max N (3 * B + 1), hB1, ?_⟩
  intro n hn c ī hsel hcard
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn3B : 3 * B + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hval : ∀ i, ī i < 2 * (n + 1) := by
    intro i
    have := hsel.1 i
    rwa [length_wrappedFlat] at this
  set S : Finset ℕ := (Finset.range n).filter
    (fun j => B ≤ j ∧ j + B ≤ n ∧ ∃ i, inBlock (ī i) j) with hSdef
  have hSmem : ∀ j, j ∈ S ↔ (j < n ∧ B ≤ j ∧ j + B ≤ n ∧ ∃ i, inBlock (ī i) j) := by
    intro j
    rw [hSdef, Finset.mem_filter, Finset.mem_range]
  by_cases hSne : S.Nonempty
  · -- a bulk cluster exists; its least block is the base
    right
    set t := S.min' hSne with htdef
    have htS := S.min'_mem hSne
    rw [hSmem] at htS
    obtain ⟨htn, htB, htBn, i₀, hi₀⟩ := htS
    refine ⟨t, htB, htBn, ⟨i₀, hi₀⟩, ?_⟩
    intro i
    rcases position_cases (ī i) n (hval i) with h0 | hsuf | ⟨hjn, hblk⟩
    · left; exact h0
    · right; left; exact hsuf
    · set j := (ī i - 1) / 2 with hjdef
      by_cases hf : j < B
      · right; right; left; exact ⟨j, hf, hblk⟩
      · by_cases hb : j + B ≤ n
        · have hjS : j ∈ S := (hSmem j).mpr ⟨hjn, by omega, hb, ⟨i, hblk⟩⟩
          have htj : t ≤ j := S.min'_le j hjS
          have hjt : j < t + B := by
            by_contra hcon
            push Not at hcon
            exact hoc n hnN c ī hsel hcard i₀ i t j hi₀ hblk htB hcon (by omega)
          right; right; right; right
          refine ⟨j - t, by omega, ?_⟩
          have harg : t + (j - t) = j := by omega
          rw [harg]
          exact hblk
        · right; right; right; left
          refine ⟨n - j, by omega, by omega, ?_⟩
          have harg : n - (n - j) = j := by omega
          rw [harg]
          exact hblk
  · -- no bulk coordinate at all
    left
    intro i
    rcases position_cases (ī i) n (hval i) with h0 | hsuf | ⟨hjn, hblk⟩
    · left; exact h0
    · right; left; exact hsuf
    · set j := (ī i - 1) / 2 with hjdef
      by_cases hf : j < B
      · right; right; left; exact ⟨j, hf, hblk⟩
      · by_cases hb : j + B ≤ n
        · exact absurd ⟨j, (hSmem j).mpr ⟨hjn, by omega, hb, ⟨i, hblk⟩⟩⟩ hSne
        · right; right; right
          refine ⟨n - j, by omega, by omega, ?_⟩
          have harg : n - (n - j) = j := by omega
          rw [harg]
          exact hblk


end SliceGrowthCollapse
