/-
# The d*-rank on the slice is affine-on-residues per coordinate (§7 arity-1 discharge)

The arity-1 `fas` discharge's rank threshold is the `d*`-rank: the rank vector of the
`≺`-minimal selected `D`-atom of `W_n` (equivalently, the lex-minimum of the rank vectors
over the selected `D`-atoms, since `≺` compares ranks lexicographically first).  `fas`
counts the selected atoms `a` with `a ≺ d*`, so the strict part needs `d*`-rank(n) as an
`AffineOnResiduesZ` threshold per coordinate.

This file builds, in order:
* the supporting `lexMinList` minimality (`lexMinList_le`), the generic finite-min
  extraction `exists_min_of_list`, and the D-existence EP gate
  (`Dpresent_eventuallyPeriodic`);
* the selected-restricted per-class lex-boundary engine `selBvec_lex_is_lex_min` and its
  coordinate affineness `selBvecCoord_affineOnResiduesZ`;
* the BIG-dominated gated lex-min `gated_lexMin_affine`: a lex-minimum over EP-gated
  candidates is affine-on-residues.
-/
import RequestProject.SliceCountSlice
import RequestProject.SliceDstarCore
import RequestProject.SliceLexOrder
import RequestProject.SliceOutput
import RequestProject.SliceSelect

namespace SliceDstar

open WRP Step SliceThreshold SliceAffine SliceOrder SliceLexOrder SliceDstarCore
  SliceBoundaryMinCore SliceVectorLexMin
open scoped Classical

variable {d : ℕ}

/-- **`lexMinList` is the lex-minimum of its (nonempty) family.**  Nothing in the list
lex-precedes `lexMinList Fs n`, and it is attained by some member.  (`SliceDstarCore`
shows `lexMinList` is `AffineOnResiduesZ` per coordinate but proves no minimality.) -/
theorem lexMinList_le (Fs : List (ℕ → Fin d → ℤ)) (hne : Fs ≠ []) (n : ℕ) :
    (∀ F ∈ Fs, ¬ WRP.lexLt (F n) (lexMinList Fs n)) ∧ (∃ F ∈ Fs, lexMinList Fs n = F n) := by
  induction Fs with
  | nil => exact absurd rfl hne
  | cons F rest ih =>
      cases rest with
      | nil =>
          refine ⟨fun G hG => ?_, ⟨F, by simp, rfl⟩⟩
          rw [List.mem_singleton] at hG
          rw [hG, lexMinList_singleton]
          exact lexLt_irrefl (F n)
      | cons G rest' =>
          obtain ⟨hmin, K, hKmem, hKeq⟩ := ih (by simp)
          rw [lexMinList_cons_cons]
          set H := lexMinList (G :: rest') with hHdef
          by_cases hflag : WRP.lexLt (F n) (H n)
          · have hvec : lexMin2 F H n = F n := by funext i; simp only [lexMin2]; rw [if_pos hflag]
            refine ⟨fun L hL => ?_, ⟨F, by simp, hvec⟩⟩
            rw [hvec]
            rcases List.mem_cons.mp hL with rfl | hLrest
            · exact lexLt_irrefl (L n)
            · exact fun hLF => hmin L hLrest (lexLt_trans (L n) (F n) (H n) hLF hflag)
          · have hvec : lexMin2 F H n = H n := by funext i; simp only [lexMin2]; rw [if_neg hflag]
            refine ⟨fun L hL => ?_, ⟨K, List.mem_cons_of_mem F hKmem, by rw [hvec]; exact hKeq⟩⟩
            rw [hvec]
            rcases List.mem_cons.mp hL with rfl | hLrest
            · exact hflag
            · exact hmin L hLrest

/-- **Existence of a selected `D`-atom is eventually periodic in `n`.**  The D-empty/D-present
dichotomy gate, repackaged from `SliceSelect.selectedLabel_exists_slice_eventuallyPeriodic`. -/
theorem Dpresent_eventuallyPeriodic (P : WRP.Presentation Step Step) :
    ∃ p : ℕ, 1 ≤ p ∧ EventuallyPeriodic
      (fun n => ∃ a : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) a ∧
        P.toPoly.labelOf (wrappedFlat n) a = D) p := by
  obtain ⟨m, p, hp, hper⟩ := SliceSelect.selectedLabel_exists_slice_eventuallyPeriodic P.toPoly D
  exact ⟨p, hp, m, hper⟩

/-! ## Finite-min extraction for the `≺`-minimal selected `D`-atom -/

/-- **Generic finite-min for a strict total order on a list.**  Given trichotomy and
transitivity of `R` on a nonempty list, some element `R`-precedes (or equals) every
element.  (No `LinearOrder` instance / no sort; just the min.) -/
theorem exists_min_of_list {α : Type*} (R : α → α → Prop) :
    ∀ (l : List α), l ≠ [] →
      (∀ a ∈ l, ∀ b ∈ l, R a b ∨ a = b ∨ R b a) →
      (∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, R a b → R b c → R a c) →
      ∃ m ∈ l, ∀ b ∈ l, m = b ∨ R m b := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons x xs ih =>
      intro _ htri htr
      cases xs with
      | nil =>
          exact ⟨x, by simp, fun b hb => Or.inl (by rw [List.mem_singleton] at hb; exact hb.symm)⟩
      | cons y ys =>
          obtain ⟨m', hm'mem, hm'min⟩ := ih (by simp)
            (fun a ha b hb => htri a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))
            (fun a ha b hb c hc => htr a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb)
              c (List.mem_cons_of_mem x hc))
          have hxmem : x ∈ x :: y :: ys := by simp
          have hm'mem' : m' ∈ x :: y :: ys := List.mem_cons_of_mem x hm'mem
          rcases htri x hxmem m' hm'mem' with hxm | hxm | hxm
          · refine ⟨x, hxmem, fun b hb => ?_⟩
            rcases List.mem_cons.mp hb with rfl | hbxs
            · exact Or.inl rfl
            · rcases hm'min b hbxs with rfl | hrb
              · exact Or.inr hxm
              · exact Or.inr (htr x hxmem m' hm'mem' b (List.mem_cons_of_mem x hbxs) hxm hrb)
          · refine ⟨x, hxmem, fun b hb => ?_⟩
            rcases List.mem_cons.mp hb with rfl | hbxs
            · exact Or.inl rfl
            · rcases hm'min b hbxs with heq | hrb
              · exact Or.inl (hxm.trans heq)
              · exact Or.inr (by rw [hxm]; exact hrb)
          · refine ⟨m', hm'mem', fun b hb => ?_⟩
            rcases List.mem_cons.mp hb with rfl | hbxs
            · exact Or.inr hxm
            · exact hm'min b hbxs

/-! ## The selected-restricted per-class lex-boundary engine -/

/-- The selected per-class lex-boundary vector: `F(m+r)` shifted by the lex-extremal
*selected* step (`lastSel` if the slope `P` is lex-decreasing, else `firstSel`). -/
noncomputable def selBvecVal {d : ℕ} (F : ℕ → Fin d → ℤ) (m r : ℕ) (P : Fin d → ℤ)
    (takeLast : Bool) (firstSel lastSel : ℕ) : Fin d → ℤ :=
  fun i => if takeLast then F (m + r) i + (lastSel : ℤ) * P i
           else F (m + r) i + (firstSel : ℤ) * P i

/-- **Selected-restricted per-class lex-min** (the selected analogue of
`SliceVectorBoundaryAttain.bvec_lex_is_lex_min`).  Among the *selected* steps `k` of
residue class `r`, the boundary vector `selBvecVal` (at the first selected step when the
slope is lex-increasing, the last when lex-decreasing) lex-dominates every selected member
and is attained.  The slope-sign arithmetic is identical to the unselected case; only the
boundary index changes from `0`/`numReps-1` to `firstSel`/`lastSel`. -/
theorem selBvec_lex_is_lex_min {d : ℕ} (F : ℕ → Fin d → ℤ) {m p : ℕ} (P : Fin d → ℤ)
    (takeLast : Bool) (sel : ℕ → Prop)
    (hrec : ∀ (i : Fin d) (r k : ℕ), F (m + r + p * k) i = F (m + r) i + k * P i)
    (hflag : takeLast = true ↔ WRP.lexLt P (fun _ => 0))
    (r N firstSel lastSel : ℕ)
    (hfs : firstSel < numReps m p r N ∧ sel firstSel ∧ ∀ k, k < firstSel → ¬ sel k)
    (hls : lastSel < numReps m p r N ∧ sel lastSel ∧
      ∀ k, lastSel < k → k < numReps m p r N → ¬ sel k) :
    (∀ k, k < numReps m p r N → sel k →
        ¬ WRP.lexLt (F (m + r + p * k)) (selBvecVal F m r P takeLast firstSel lastSel))
    ∧ (∃ k, k < numReps m p r N ∧ sel k ∧
        selBvecVal F m r P takeLast firstSel lastSel = F (m + r + p * k)) := by
  cases takeLast with
  | false =>
      have hnotP : ¬ WRP.lexLt P (fun _ => 0) := fun hh => Bool.false_ne_true (hflag.mpr hh)
      have hbv : ∀ i, selBvecVal F m r P false firstSel lastSel i
          = F (m + r) i + (firstSel : ℤ) * P i := by
        intro i; simp only [selBvecVal, Bool.false_eq_true, if_false]
      refine ⟨fun k hk hsk => ?_, ⟨firstSel, hfs.1, hfs.2.1, ?_⟩⟩
      · rw [lexLt_sub_zero]
        have heq : (fun i => F (m + r + p * k) i - selBvecVal F m r P false firstSel lastSel i)
            = (fun i => ((k : ℤ) - (firstSel : ℤ)) * P i) := by
          funext i; rw [hrec i r k, hbv i]; ring
        rw [heq, lexLt_smul_iff]
        rintro (⟨_, hP⟩ | ⟨hc, _⟩)
        · exact hnotP hP
        · have hge : firstSel ≤ k := by
            by_contra hlt; push Not at hlt; exact hfs.2.2 k hlt hsk
          omega
      · funext i; rw [hbv i, hrec i r firstSel]
  | true =>
      have hPlt : WRP.lexLt P (fun _ => 0) := hflag.mp rfl
      have hbv : ∀ i, selBvecVal F m r P true firstSel lastSel i
          = F (m + r) i + (lastSel : ℤ) * P i := by
        intro i; simp only [selBvecVal, if_true]
      refine ⟨fun k hk hsk => ?_, ⟨lastSel, hls.1, hls.2.1, ?_⟩⟩
      · rw [lexLt_sub_zero]
        have heq : (fun i => F (m + r + p * k) i - selBvecVal F m r P true firstSel lastSel i)
            = (fun i => ((k : ℤ) - (lastSel : ℤ)) * P i) := by
          funext i; rw [hrec i r k, hbv i]; ring
        rw [heq, lexLt_smul_iff]
        rintro (⟨hc, _⟩ | ⟨_, hP⟩)
        · have hle : k ≤ lastSel := by
            by_contra hlt; push Not at hlt; exact hls.2.2 k hlt hk hsk
          omega
        · exact lexLt_irrefl (fun _ => 0) (lexLt_trans (fun _ => 0) P (fun _ => 0) hP hPlt)
      · funext i; rw [hbv i, hrec i r lastSel]

/-- **`selBvecVal` is `AffineOnResiduesZ` per coordinate** when the selected boundary
indices `firstSel`/`lastSel` are `AffineOnResidues`-in-`N` (the base `F (m+r) i` is a fixed
integer; the slope rides on the boundary index). -/
theorem selBvecCoord_affineOnResiduesZ {d : ℕ} (F : ℕ → Fin d → ℤ) (m r : ℕ) (P : Fin d → ℤ)
    (takeLast : Bool) (firstSel lastSel : ℕ → ℕ) (hfs : AffineOnResidues firstSel)
    (hls : AffineOnResidues lastSel) (i : Fin d) :
    AffineOnResiduesZ (fun N => selBvecVal F m r P takeLast (firstSel N) (lastSel N) i) := by
  cases takeLast with
  | false =>
      refine AffineOnResiduesZ.congr (fun N => ?_)
        ((AffineOnResiduesZ.const (F (m + r) i)).add ((AffineOnResiduesZ.of_natCast hfs).smul (P i)))
      simp only [selBvecVal, Bool.false_eq_true, if_false]; ring
  | true =>
      refine AffineOnResiduesZ.congr (fun N => ?_)
        ((AffineOnResiduesZ.const (F (m + r) i)).add ((AffineOnResiduesZ.of_natCast hls).smul (P i)))
      simp only [selBvecVal, if_true]; ring

/-! ## The BIG-dominated gated lex-min: lex-min over EP-gated candidates is affine -/

/-- `lexLt` is asymmetric. -/
theorem lexLt_asymm {d : ℕ} (a b : Fin d → ℤ) (h : WRP.lexLt a b) : ¬ WRP.lexLt b a :=
  fun hba => lexLt_irrefl a (lexLt_trans a b a h hba)

/-- `n ↦ (n - c) / d` is `AffineOnResidues` (slope `1` per class beyond `c`).  This is the
bulk-end step count `k_end n` for the bulk `d*`-candidate. -/
theorem affineOnResidues_natSubDiv (c d : ℕ) (hd : 1 ≤ d) :
    AffineOnResidues (fun n => (n - c) / d) := by
  refine affineOnResidues_of_period (m := c) (p := d) (fun _ => 1) hd (fun r _ k => ?_)
  show (c + r + d * k - c) / d = (c + r - c) / d + k * 1
  rw [show c + r + d * k - c = r + d * k from by omega, show c + r - c = r from by omega,
    Nat.add_mul_div_left r k hd, Nat.mul_one]

/-- Eventual periodicity lifts to any multiple of the period. -/
theorem EP_of_dvd {Pr : ℕ → Prop} {p p' : ℕ} (h : EventuallyPeriodic Pr p) (hdvd : p ∣ p') :
    EventuallyPeriodic Pr p' := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨k, rfl⟩ := hdvd
  refine ⟨m, fun n hn => ?_⟩
  have key : ∀ t, Pr (n + p * t) ↔ Pr n := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        rw [show n + p * (t + 1) = (n + p * t) + p from by ring, hm _ (by omega)]; exact ih
  exact key k

/-- The pointwise `foldr max 0` over a finite list of `AffineOnResiduesZ` sequences is
`AffineOnResiduesZ` (used to build the dominating `BIG`). -/
theorem affineOnResiduesZ_listMax (l : List (ℕ → ℤ)) (h : ∀ f ∈ l, AffineOnResiduesZ f) :
    AffineOnResiduesZ (fun n => (l.map (fun f => f n)).foldr max 0) := by
  induction l with
  | nil => simpa using AffineOnResiduesZ.const 0
  | cons f l ih =>
      have hf := h f (by simp)
      have ihl := ih (fun g hg => h g (by simp [hg]))
      simpa using hf.max ihl

/-- **Gated lex-min is `AffineOnResiduesZ` per coordinate.**  Given finitely many candidate
vector-families, each `AffineOnResiduesZ` per coord, with an eventually-periodic selection gate
and pairwise eventually-periodic `lexLt` comparisons, and a `BIG` family that lex-dominates every
candidate at every `n`: the lex-min of `BIG` together with the *gated* candidates (each replaced by
`BIG` when its gate is off) is `AffineOnResiduesZ` per coord.  (The domination makes off-candidates
never win, so this is the lex-min over the on-candidates whenever any is on.) -/
theorem gated_lexMin_affine {d : ℕ} (cands : List ((ℕ → Prop) × (ℕ → Fin d → ℤ))) {p : ℕ}
    (hp : 1 ≤ p) (hgate : ∀ gf ∈ cands, EventuallyPeriodic gf.1 p)
    (haff : ∀ gf ∈ cands, ∀ i, AffineOnResiduesZ (fun n => gf.2 n i))
    (hpair : ∀ gf ∈ cands, ∀ gf' ∈ cands,
      EventuallyPeriodic (fun n => WRP.lexLt (gf.2 n) (gf'.2 n)) p)
    (BIG : ℕ → Fin d → ℤ) (hBIGaff : ∀ i, AffineOnResiduesZ (fun n => BIG n i))
    (hdom : ∀ gf ∈ cands, ∀ n, WRP.lexLt (gf.2 n) (BIG n)) (i : Fin d) :
    AffineOnResiduesZ (fun n => lexMinList
      (BIG :: cands.map (fun gf => fun n => if gf.1 n then gf.2 n else BIG n)) n i) := by
  set gat := fun (gf : (ℕ → Prop) × (ℕ → Fin d → ℤ)) (n : ℕ) =>
    if gf.1 n then gf.2 n else BIG n with hgatdef
  refine lexMinList_coord_affineOnResiduesZ (BIG :: cands.map gat) hp ?_ ?_ (by simp) i
  · -- coordinate affineness of every family in the list
    intro F hF j
    rcases List.mem_cons.mp hF with rfl | hFm
    · exact hBIGaff j
    · rw [List.mem_map] at hFm
      obtain ⟨gf, hgf, rfl⟩ := hFm
      refine AffineOnResiduesZ.congr (fun n => by simp only [hgatdef]; split <;> rfl)
        (affineOnResiduesZ_ite_of_EP hp (hgate gf hgf) (haff gf hgf j) (hBIGaff j))
  · -- pairwise lexLt EP
    intro U hU V hV
    obtain hUeq | hUm := List.mem_cons.mp hU
    · obtain hVeq | hVm := List.mem_cons.mp hV
      · -- U = BIG, V = BIG
        rw [hUeq, hVeq]
        exact EventuallyPeriodic.of_eventually_false ⟨0, fun n _ => lexLt_irrefl (BIG n)⟩
      · -- U = BIG, V = gat gf'
        rw [List.mem_map] at hVm; obtain ⟨gf', hgf', rfl⟩ := hVm
        rw [hUeq]
        refine EventuallyPeriodic.of_eventually_false ⟨0, fun n _ => ?_⟩
        simp only [hgatdef]; split
        · exact lexLt_asymm _ _ (hdom gf' hgf' n)
        · exact lexLt_irrefl (BIG n)
    · obtain hVeq | hVm := List.mem_cons.mp hV
      · -- U = gat gf, V = BIG
        rw [List.mem_map] at hUm; obtain ⟨gf, hgf, rfl⟩ := hUm
        rw [hVeq]
        refine EventuallyPeriodic.congr (fun n => ?_) (hgate gf hgf)
        simp only [hgatdef]; by_cases hg : gf.1 n
        · simp only [if_pos hg]; exact ⟨fun _ => hdom gf hgf n, fun _ => hg⟩
        · simp only [if_neg hg]
          exact ⟨fun h => absurd h hg, fun h => absurd h (lexLt_irrefl (BIG n))⟩
      · -- U = gat gf, V = gat gf'
        rw [List.mem_map] at hUm hVm
        obtain ⟨gf, hgf, rfl⟩ := hUm
        obtain ⟨gf', hgf', rfl⟩ := hVm
        refine EventuallyPeriodic.congr (fun n => ?_)
          (((hgate gf hgf).and ((hgate gf' hgf').and (hpair gf hgf gf' hgf'))).or
            ((hgate gf hgf).and (EP_not (hgate gf' hgf'))))
        simp only [hgatdef]
        by_cases hg : gf.1 n <;> by_cases hg' : gf'.1 n
        · simp [hg, hg']
        · simp only [if_pos hg, if_neg hg']
          exact ⟨fun _ => hdom gf hgf n, fun _ => Or.inr ⟨hg, hg'⟩⟩
        · simp only [if_neg hg, if_pos hg']
          refine ⟨fun h => (by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h hg),
            fun h => absurd h (lexLt_asymm _ _ (hdom gf' hgf' n))⟩
        · simp only [if_neg hg, if_neg hg']
          refine ⟨fun h => (by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h hg),
            fun h => absurd h (lexLt_irrefl (BIG n))⟩

end SliceDstar
