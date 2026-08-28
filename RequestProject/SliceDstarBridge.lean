/-
# The d*-rank bridge: common-period setup (`dstar_setup`)

The first stage of the §7 arity-1 discharge's dominant-risk lemma
`dstarRank_affineOnResiduesZ`: the **common-period fold**.  Across all copies it produces a
single threshold `m` and period `p` at which simultaneously (i) every copy's blockD- and
suf-rank families have a *global* slope (`PB`/`PS`), and (ii) every copy's selectedness DFA's
forward iterate `(bF)^[·] q_pre` and backward iterate function `(bF)^[·]` are periodic — the
prerequisite (one shared `p`) for the candidate-family lex-min in the next stage.

Rests on the textbook Büchi axiom (via the selectedness gates).
-/
import RequestProject.SliceDstar
import RequestProject.SliceFasGates
import RequestProject.SliceFasBridges
import RequestProject.SliceRankRegions
import RequestProject.SliceRankThreshold

namespace SliceDstarBridge

open WRP Step SliceThreshold SliceAffine SliceOrder SliceLexOrder SliceDstar
  SliceCount MSOMark SliceMSO SliceRankAtom SliceDstarCore SliceBoundaryMinCore
open scoped Classical

/-- **The common-period setup.**  A single `(m, p)` at which all copies' rank families have a
global slope and all copies' selectedness-DFA iterates are periodic, with the per-copy
selectedness gate DFAs `Mc`. -/
theorem dstar_setup (P : WRP.Presentation Step Step) (harity : ∀ c, P.toPoly.arity c = 1) :
    ∃ (m p : ℕ) (Mc : Fin P.toPoly.K → DetAuto (Step × Bool))
      (PU PB PS PP : Fin P.toPoly.K → Fin P.d → ℤ),
      1 ≤ p ∧
      (∀ c n q, q < (wrappedFlat n).length →
        ((P.toPoly.selectedAtom (wrappedFlat n) ⟨c, fun _ => q⟩ ∧
          P.toPoly.labelOf (wrappedFlat n) ⟨c, fun _ => q⟩ = D)
         ↔ (Mc c).accepts (markAt (wrappedFlat n) q))) ∧
      (∀ c j, m ≤ j → (bF (Mc c))^[j + p] (qpre (Mc c)) = (bF (Mc c))^[j] (qpre (Mc c))) ∧
      (∀ c j, m ≤ j → (bF (Mc c))^[j + p] = (bF (Mc c))^[j]) ∧
      (∀ c n, m ≤ n →
        P.rank c (wrappedFlat (n + p + 1)) (fun _ => 1 + 2 * (n + p))
          = P.rank c (wrappedFlat (n + 1)) (fun _ => 1 + 2 * n) + PU c) ∧
      (∀ c n, m ≤ n →
        P.rank c (wrappedFlat (n + p + 1)) (fun _ => 1 + 2 * (n + p) + 1)
          = P.rank c (wrappedFlat (n + 1)) (fun _ => 1 + 2 * n + 1) + PB c) ∧
      (∀ c n, m ≤ n →
        P.rank c (wrappedFlat (n + p)) (fun _ => 1 + 2 * (n + p))
          = P.rank c (wrappedFlat n) (fun _ => 1 + 2 * n) + PS c) ∧
      (∀ c n, m ≤ n →
        P.rank c (wrappedFlat (n + p)) (fun _ => 0)
          = P.rank c (wrappedFlat n) (fun _ => 0) + PP c) := by
  classical
  set RU : Fin P.toPoly.K → ℕ → Fin P.d → ℤ :=
    fun c j => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j) with hRUdef
  set RB : Fin P.toPoly.K → ℕ → Fin P.d → ℤ :=
    fun c j => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1) with hRBdef
  set RS : Fin P.toPoly.K → ℕ → Fin P.d → ℤ :=
    fun c n => P.rank c (wrappedFlat n) (fun _ => 1 + 2 * n) with hRSdef
  set RP : Fin P.toPoly.K → ℕ → Fin P.d → ℤ :=
    fun c n => P.rank c (wrappedFlat n) (fun _ => 0) with hRPdef
  have hRU : ∀ c, RankAffine (RU c) := fun c => rank_block_rankAffine P c
  have hRB : ∀ c, RankAffine (RB c) := fun c => rank_blockD_rankAffine P c
  have hRS : ∀ c, RankAffine (RS c) := fun c => rank_suf_rankAffine P c
  have hRP : ∀ c, RankAffine (RP c) := fun c => rank_pre_rankAffine P c
  obtain ⟨mR, pR, hpR, halign⟩ := SliceFasBridges.rankAffine_align_common_period
    ((List.finRange P.toPoly.K).flatMap (fun c => [RU c, RB c, RS c, RP c]))
    (by
      intro F hF
      rw [List.mem_flatMap] at hF
      obtain ⟨c, _, hF⟩ := hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact hRU c
      · rw [List.mem_cons] at hF; rcases hF with rfl | hF
        · exact hRB c
        · rw [List.mem_cons] at hF; rcases hF with rfl | hF
          · exact hRS c
          · rw [List.mem_cons] at hF; rcases hF with rfl | hF
            · exact hRP c
            · exact absurd hF (by simp))
  have hslopes : ∀ c, ∃ PU PB PS PP : Fin P.d → ℤ,
      (∀ n, mR ≤ n → RU c (n + pR) = RU c n + PU) ∧
      (∀ n, mR ≤ n → RB c (n + pR) = RB c n + PB) ∧
      (∀ n, mR ≤ n → RS c (n + pR) = RS c n + PS) ∧
      (∀ n, mR ≤ n → RP c (n + pR) = RP c n + PP) := by
    intro c
    obtain ⟨PU, hPU⟩ := halign (RU c)
      (by rw [List.mem_flatMap]; exact ⟨c, List.mem_finRange c, by simp⟩)
    obtain ⟨PB, hPB⟩ := halign (RB c)
      (by rw [List.mem_flatMap]; exact ⟨c, List.mem_finRange c, by simp⟩)
    obtain ⟨PS, hPS⟩ := halign (RS c)
      (by rw [List.mem_flatMap]; exact ⟨c, List.mem_finRange c, by simp⟩)
    obtain ⟨PP, hPP⟩ := halign (RP c)
      (by rw [List.mem_flatMap]; exact ⟨c, List.mem_finRange c, by simp⟩)
    exact ⟨PU, PB, PS, PP, hPU, hPB, hPS, hPP⟩
  choose PU PB PS PP hPUc hPBc hPSc hPPc using hslopes
  have hdata : ∀ c : Fin P.toPoly.K, ∃ (Mc : DetAuto (Step × Bool)) (mu pu mv pv : ℕ),
      1 ≤ pu ∧ 1 ≤ pv ∧
      (∀ n q, q < (wrappedFlat n).length →
        ((P.toPoly.selectedAtom (wrappedFlat n) ⟨c, fun _ => q⟩ ∧
          P.toPoly.labelOf (wrappedFlat n) ⟨c, fun _ => q⟩ = D)
         ↔ Mc.accepts (markAt (wrappedFlat n) q))) ∧
      (∀ j, mu ≤ j → (bF Mc)^[j + pu] (qpre Mc) = (bF Mc)^[j] (qpre Mc)) ∧
      (∀ j, mv ≤ j → (bF Mc)^[j + pv] = (bF Mc)^[j]) := by
    intro c
    obtain ⟨Mc, hMc⟩ := SliceFasGates.selectedD_gate P c harity
    obtain ⟨mu, pu, hpu, hfwd⟩ := SliceCount.bF_iterate_eventuallyPeriodic Mc
    obtain ⟨mv, pv, hpv, hbwd⟩ := SliceCount.bF_func_iterate_eventuallyPeriodic Mc
    exact ⟨Mc, mu, pu, mv, pv, hpu, hpv, hMc, hfwd, hbwd⟩
  choose Mc muc puc mvc pvc hpuc hpvc hMc hfwdc hbwdc using hdata
  set p : ℕ := pR * (∏ c : Fin P.toPoly.K, puc c * pvc c) with hpdef
  have hprodpos : 0 < ∏ c : Fin P.toPoly.K, puc c * pvc c :=
    Finset.prod_pos (fun c _ => Nat.mul_pos (hpuc c) (hpvc c))
  have hp : 1 ≤ p := by rw [hpdef]; exact Nat.mul_pos hpR hprodpos
  have hpRdvd : pR ∣ p := by rw [hpdef]; exact dvd_mul_right pR _
  have hpucdvd : ∀ c, puc c ∣ p := by
    intro c
    have h1 : puc c * pvc c ∣ ∏ c : Fin P.toPoly.K, puc c * pvc c :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
    rw [hpdef]; exact Dvd.dvd.mul_left (dvd_trans (dvd_mul_right _ _) h1) pR
  have hpvcdvd : ∀ c, pvc c ∣ p := by
    intro c
    have h1 : puc c * pvc c ∣ ∏ c : Fin P.toPoly.K, puc c * pvc c :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
    rw [hpdef]; exact Dvd.dvd.mul_left (dvd_trans (dvd_mul_left _ _) h1) pR
  -- common threshold
  set m : ℕ := mR ⊔ Finset.univ.sup (fun c => muc c ⊔ mvc c) with hmdef
  have hsup : ∀ c, muc c ⊔ mvc c ≤ Finset.univ.sup (fun c => muc c ⊔ mvc c) :=
    fun c => Finset.le_sup (f := fun c => muc c ⊔ mvc c) (Finset.mem_univ c)
  have hmmuc : ∀ c, muc c ≤ m := by
    intro c; rw [hmdef]
    exact le_trans (le_trans (le_max_left (muc c) (mvc c)) (hsup c)) (le_max_right mR _)
  have hmmvc : ∀ c, mvc c ≤ m := by
    intro c; rw [hmdef]
    exact le_trans (le_trans (le_max_right (muc c) (mvc c)) (hsup c)) (le_max_right mR _)
  have hmmR : mR ≤ m := by rw [hmdef]; exact le_max_left _ _
  refine ⟨m, p, Mc, (fun c => (p / pR) • PU c), (fun c => (p / pR) • PB c),
    (fun c => (p / pR) • PS c), (fun c => (p / pR) • PP c), hp, hMc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- forward iterate periodic at p
    intro c j hj
    obtain ⟨t, ht⟩ := hpucdvd c
    rw [ht]
    exact fn_period_mul (fun j => (bF (Mc c))^[j] (qpre (Mc c))) (hfwdc c) j t
      (le_trans (hmmuc c) hj)
  · -- backward iterate periodic at p
    intro c j hj
    obtain ⟨t, ht⟩ := hpvcdvd c
    rw [ht]
    exact fn_period_mul (fun j => (bF (Mc c))^[j]) (hbwdc c) j t (le_trans (hmmvc c) hj)
  · -- RU recurrence at p
    intro c n hn
    show RU c (n + p) = RU c n + (p / pR) • PU c
    obtain ⟨t, ht⟩ := hpRdvd
    rw [ht, Nat.mul_div_cancel_left t hpR]
    exact RankAffine.iterate (hPUc c) n t (le_trans hmmR hn)
  · -- RB recurrence at p
    intro c n hn
    show RB c (n + p) = RB c n + (p / pR) • PB c
    obtain ⟨t, ht⟩ := hpRdvd
    rw [ht, Nat.mul_div_cancel_left t hpR]
    exact RankAffine.iterate (hPBc c) n t (le_trans hmmR hn)
  · -- RS recurrence at p
    intro c n hn
    show RS c (n + p) = RS c n + (p / pR) • PS c
    obtain ⟨t, ht⟩ := hpRdvd
    rw [ht, Nat.mul_div_cancel_left t hpR]
    exact RankAffine.iterate (hPSc c) n t (le_trans hmmR hn)
  · -- RP recurrence at p
    intro c n hn
    show RP c (n + p) = RP c n + (p / pR) • PP c
    obtain ⟨t, ht⟩ := hpRdvd
    rw [ht, Nat.mul_div_cancel_left t hpR]
    exact RankAffine.iterate (hPPc c) n t (le_trans hmmR hn)

/-- An arity-1 atom is determined by its single position: `a = ⟨a.1, fun _ => a.2 ⟨0,_⟩⟩`. -/
theorem atom_arity_one_eq {Alpha Gamma : Type*} {Q : Polyreg.Presentation Alpha Gamma}
    (harity : ∀ c, Q.arity c = 1) (a : Q.Atom) (h0 : 0 < Q.arity a.1) :
    a = ⟨a.1, fun _ => a.2 ⟨0, h0⟩⟩ := by
  obtain ⟨c, f⟩ := a
  refine congrArg (Sigma.mk c) ?_
  funext i
  have hi : (i : ℕ) = 0 := by have h1 := i.isLt; have h2 := harity c; omega
  exact congrArg f (Fin.ext hi)

/-- **The class boundary lex-dominates every member** (the `sel := True` specialization of
`selBvec_lex_is_lex_min`, extracted as a standalone lemma so the `dstarC_exists` bulk leaves do
not re-elaborate the heavy proof inline — avoids heartbeat timeouts).  The boundary vector with
`firstSel = 0`, `lastSel = numReps - 1` lex-dominates `F (m+r+p·kd)` for every `kd < numReps`. -/
theorem selBvec_le_member {d : ℕ} (F : ℕ → Fin d → ℤ) {m p : ℕ} (P : Fin d → ℤ) (takeLast : Bool)
    (hrec : ∀ (i : Fin d) (r k : ℕ), F (m + r + p * k) i = F (m + r) i + k * P i)
    (hflag : takeLast = true ↔ WRP.lexLt P (fun _ => 0))
    (r N kd : ℕ) (hkd : kd < numReps m p r N) :
    ¬ WRP.lexLt (F (m + r + p * kd))
      (selBvecVal F m r P takeLast 0 (numReps m p r N - 1)) :=
  (selBvec_lex_is_lex_min F P takeLast (fun _ => True) hrec hflag r N 0 (numReps m p r N - 1)
    ⟨by omega, trivial, fun k hk => (by omega : False).elim⟩
    ⟨by omega, trivial, fun k h1 h2 => (by omega : False).elim⟩).1 kd hkd trivial

/-- Every member of a `ℤ`-list is `≤` its `foldr max 0`. -/
theorem le_foldr_max {x : ℤ} : ∀ {l : List ℤ}, x ∈ l → x ≤ l.foldr max 0 := by
  intro l hx
  induction l with
  | nil => exact absurd hx (by simp)
  | cons a l ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact le_max_left _ _
      · exact le_trans (ih hx') (le_max_right _ _)

set_option maxHeartbeats 1000000 in
/-- **The constructive `d*`-rank exists.**  There is an `AffineOnResiduesZ`-per-coord sequence
`dstarC` equal to `dstarRank` on every `D`-present slice past a threshold. -/
theorem dstarC_exists (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity : ∀ c, P.toPoly.arity c = 1) :
    ∃ (dstarC : ℕ → Fin P.d → ℤ) (N0 : ℕ),
      (∀ i, AffineOnResiduesZ (fun n => dstarC n i)) ∧
      (∀ n, N0 ≤ n →
        (∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧ P.toPoly.labelOf (wrappedFlat n) a = D) →
        dstarRank P hV harity n = dstarC n) := by
  classical
  rcases Nat.eq_zero_or_pos P.d with hd0 | hd
  · exact ⟨fun _ _ => 0, 0, fun i => (hd0 ▸ i).elim0,
      fun n _ _ => funext (fun i => (hd0 ▸ i).elim0)⟩
  obtain ⟨m, p, Mc, PU, PB, PS, PP, hp, hMc, hfwd, hbwd, hRUrec, hRBrec, hRSrec, hRPrec⟩ :=
    dstar_setup P harity
  set RU : Fin P.toPoly.K → ℕ → Fin P.d → ℤ :=
    fun c j => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j) with hRUdef
  set RB : Fin P.toPoly.K → ℕ → Fin P.d → ℤ :=
    fun c j => P.rank c (wrappedFlat (j + 1)) (fun _ => 1 + 2 * j + 1) with hRBdef
  set RS : Fin P.toPoly.K → ℕ → Fin P.d → ℤ :=
    fun c n => P.rank c (wrappedFlat n) (fun _ => 1 + 2 * n) with hRSdef
  set RP : Fin P.toPoly.K → ℕ → Fin P.d → ℤ :=
    fun c n => P.rank c (wrappedFlat n) (fun _ => 0) with hRPdef
  have hRU : ∀ c, RankAffine (RU c) := fun c => rank_block_rankAffine P c
  have hRB : ∀ c, RankAffine (RB c) := fun c => rank_blockD_rankAffine P c
  have hRS : ∀ c, RankAffine (RS c) := fun c => rank_suf_rankAffine P c
  have hRP : ∀ c, RankAffine (RP c) := fun c => rank_pre_rankAffine P c
  have hRUrec' : ∀ c n, m ≤ n → RU c (n + p) = RU c n + PU c := hRUrec
  have hRBrec' : ∀ c n, m ≤ n → RB c (n + p) = RB c n + PB c := hRBrec
  have hRSrec' : ∀ c n, m ≤ n → RS c (n + p) = RS c n + PS c := hRSrec
  have hRPrec' : ∀ c n, m ≤ n → RP c (n + p) = RP c n + PP c := hRPrec
  set tlU : Fin P.toPoly.K → Bool := fun c => decide (WRP.lexLt (PU c) (fun _ => 0)) with htlUdef
  set tlD : Fin P.toPoly.K → Bool := fun c => decide (WRP.lexLt (PB c) (fun _ => 0)) with htlDdef
  -- candidate list: per copy, pre / blockU(front,back,bulk) / blockD(front,back,bulk) / suf
  set cands : List ((ℕ → Prop) × (ℕ → Fin P.d → ℤ)) :=
    (List.finRange P.toPoly.K).flatMap (fun c =>
      [(fun n => (Mc c).accepts (markAt (wrappedFlat n) 0), fun n => RP c n)] ++
      (List.range m).map (fun j =>
        (fun n => (Mc c).accepts (markAt (wrappedFlat n) (1 + 2 * j)), fun _ => RU c j)) ++
      (List.range m).map (fun l =>
        (fun n => (Mc c).accepts (markAt (wrappedFlat n) (1 + 2 * (n - 1 - l))),
          fun n => RU c (n - 1 - l))) ++
      (List.range p).map (fun r =>
        (fun n => (Mc c).accepts (markAt (wrappedFlat n) (1 + 2 * (m + r))),
          fun n => SliceDstar.selBvecVal (RU c) m r (PU c) (tlU c) 0 ((n - (1 + 2 * m + r)) / p))) ++
      (List.range m).map (fun j =>
        (fun n => (Mc c).accepts (markAt (wrappedFlat n) (1 + 2 * j + 1)), fun _ => RB c j)) ++
      (List.range m).map (fun l =>
        (fun n => (Mc c).accepts (markAt (wrappedFlat n) (1 + 2 * (n - 1 - l) + 1)),
          fun n => RB c (n - 1 - l))) ++
      (List.range p).map (fun r =>
        (fun n => (Mc c).accepts (markAt (wrappedFlat n) (1 + 2 * (m + r) + 1)),
          fun n => SliceDstar.selBvecVal (RB c) m r (PB c) (tlD c) 0 ((n - (1 + 2 * m + r)) / p))) ++
      [(fun n => (Mc c).accepts (markAt (wrappedFlat n) (1 + 2 * n)), fun n => RS c n)])
    with hcandsdef
  set BIG : ℕ → Fin P.d → ℤ := fun n coord =>
    if coord = ⟨0, hd⟩
    then (cands.map (fun gf => gf.2 n ⟨0, hd⟩)).foldr max 0 + 1 else 0 with hBIGdef
  have hgate : ∀ gf ∈ cands, EventuallyPeriodic gf.1 p := by
    intro gf hgf
    rw [hcandsdef, List.mem_flatMap] at hgf
    obtain ⟨c, _, hgf⟩ := hgf
    rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append,
      List.mem_append, List.mem_append] at hgf
    rcases hgf with ((((((hgf | hgf) | hgf) | hgf) | hgf) | hgf) | hgf) | hgf
    · -- pre
      rw [List.mem_singleton] at hgf; subst hgf
      refine ⟨m, fun n hn => ?_⟩
      simp only []
      rw [accepts_markAt_pre (Mc c) (n + p), accepts_markAt_pre (Mc c) n, hbwd c n (by omega)]
    · -- frontU j
      rw [List.mem_map] at hgf; obtain ⟨j, _, rfl⟩ := hgf
      refine ⟨m + j + 1, fun n hn => ?_⟩
      simp only []
      rw [accepts_markAt_blockU (Mc c) (n + p) j (by omega),
        accepts_markAt_blockU (Mc c) n j (by omega),
        show n + p - 1 - j = (n - 1 - j) + p from by omega, hbwd c (n - 1 - j) (by omega)]
    · -- backU l
      rw [List.mem_map] at hgf; obtain ⟨l, _, rfl⟩ := hgf
      refine ⟨m + l + 1, fun n hn => ?_⟩
      simp only []
      rw [accepts_markAt_blockU (Mc c) (n + p) (n + p - 1 - l) (by omega),
        accepts_markAt_blockU (Mc c) n (n - 1 - l) (by omega)]
      have hf : (bF (Mc c))^[n + p - 1 - l] (qpre (Mc c)) = (bF (Mc c))^[n - 1 - l] (qpre (Mc c)) := by
        rw [show n + p - 1 - l = (n - 1 - l) + p from by omega]; exact hfwd c (n - 1 - l) (by omega)
      rw [hf, show n + p - 1 - (n + p - 1 - l) = n - 1 - (n - 1 - l) from by omega]
    · -- bulkU r
      rw [List.mem_map] at hgf; obtain ⟨r, _, rfl⟩ := hgf
      refine ⟨m + (m + r) + 1, fun n hn => ?_⟩
      simp only []
      rw [accepts_markAt_blockU (Mc c) (n + p) (m + r) (by omega),
        accepts_markAt_blockU (Mc c) n (m + r) (by omega),
        show n + p - 1 - (m + r) = (n - 1 - (m + r)) + p from by omega,
        hbwd c (n - 1 - (m + r)) (by omega)]
    · -- frontD j
      rw [List.mem_map] at hgf; obtain ⟨j, _, rfl⟩ := hgf
      refine ⟨m + j + 1, fun n hn => ?_⟩
      simp only []
      rw [accepts_markAt_blockD (Mc c) (n + p) j (by omega),
        accepts_markAt_blockD (Mc c) n j (by omega),
        show n + p - 1 - j = (n - 1 - j) + p from by omega, hbwd c (n - 1 - j) (by omega)]
    · -- backD l
      rw [List.mem_map] at hgf; obtain ⟨l, _, rfl⟩ := hgf
      refine ⟨m + l + 1, fun n hn => ?_⟩
      simp only []
      rw [accepts_markAt_blockD (Mc c) (n + p) (n + p - 1 - l) (by omega),
        accepts_markAt_blockD (Mc c) n (n - 1 - l) (by omega)]
      have hf : (bF (Mc c))^[n + p - 1 - l] (qpre (Mc c)) = (bF (Mc c))^[n - 1 - l] (qpre (Mc c)) := by
        rw [show n + p - 1 - l = (n - 1 - l) + p from by omega]; exact hfwd c (n - 1 - l) (by omega)
      rw [hf, show n + p - 1 - (n + p - 1 - l) = n - 1 - (n - 1 - l) from by omega]
    · -- bulkD r
      rw [List.mem_map] at hgf; obtain ⟨r, _, rfl⟩ := hgf
      refine ⟨m + (m + r) + 1, fun n hn => ?_⟩
      simp only []
      rw [accepts_markAt_blockD (Mc c) (n + p) (m + r) (by omega),
        accepts_markAt_blockD (Mc c) n (m + r) (by omega),
        show n + p - 1 - (m + r) = (n - 1 - (m + r)) + p from by omega,
        hbwd c (n - 1 - (m + r)) (by omega)]
    · -- suf
      rw [List.mem_singleton] at hgf; subst hgf
      refine ⟨m, fun n hn => ?_⟩
      simp only []
      rw [show (1 : ℕ) + 2 * (n + p) = 2 * (n + p) + 1 from by ring, accepts_markAt_suf (Mc c) (n + p),
        show (1 : ℕ) + 2 * n = 2 * n + 1 from by ring, accepts_markAt_suf (Mc c) n,
        hfwd c n (by omega)]
  have hcaff : ∀ gf ∈ cands, ∀ i, AffineOnResiduesZ (fun n => gf.2 n i) := by
    intro gf hgf i
    rw [hcandsdef, List.mem_flatMap] at hgf
    obtain ⟨c, _, hgf⟩ := hgf
    rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append,
      List.mem_append, List.mem_append] at hgf
    rcases hgf with ((((((hgf | hgf) | hgf) | hgf) | hgf) | hgf) | hgf) | hgf
    · rw [List.mem_singleton] at hgf; subst hgf
      exact SliceFasBridges.rankAffine_coord_affineOnResiduesZ (hRP c) i
    · rw [List.mem_map] at hgf; obtain ⟨j, _, rfl⟩ := hgf
      exact AffineOnResiduesZ.const _
    · rw [List.mem_map] at hgf; obtain ⟨l, _, rfl⟩ := hgf
      exact SliceFasBridges.rankAffine_back_coord (hRU c) l i
    · rw [List.mem_map] at hgf; obtain ⟨r, _, rfl⟩ := hgf
      exact SliceDstar.selBvecCoord_affineOnResiduesZ (RU c) m r (PU c) (tlU c)
        (fun _ => 0) (fun n => (n - (1 + 2 * m + r)) / p) (affineOnResidues_of_eventuallyPeriodic
          (m := 0) (p := 1) (le_refl 1) (fun n _ => rfl))
        (affineOnResidues_natSubDiv (1 + 2 * m + r) p hp) i
    · rw [List.mem_map] at hgf; obtain ⟨j, _, rfl⟩ := hgf
      exact AffineOnResiduesZ.const _
    · rw [List.mem_map] at hgf; obtain ⟨l, _, rfl⟩ := hgf
      exact SliceFasBridges.rankAffine_back_coord (hRB c) l i
    · rw [List.mem_map] at hgf; obtain ⟨r, _, rfl⟩ := hgf
      exact SliceDstar.selBvecCoord_affineOnResiduesZ (RB c) m r (PB c) (tlD c)
        (fun _ => 0) (fun n => (n - (1 + 2 * m + r)) / p) (affineOnResidues_of_eventuallyPeriodic
          (m := 0) (p := 1) (le_refl 1) (fun n _ => rfl))
        (affineOnResidues_natSubDiv (1 + 2 * m + r) p hp) i
    · rw [List.mem_singleton] at hgf; subst hgf
      exact SliceFasBridges.rankAffine_coord_affineOnResiduesZ (hRS c) i
  have hcandrec : ∀ gf ∈ cands, ∃ Pf : Fin P.d → ℤ,
      ∀ i n, 2 * m + p + 1 ≤ n → gf.2 (n + p) i = gf.2 n i + Pf i := by
    intro gf hgf
    rw [hcandsdef, List.mem_flatMap] at hgf
    obtain ⟨c, _, hgf⟩ := hgf
    rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append,
      List.mem_append, List.mem_append] at hgf
    rcases hgf with ((((((hgf | hgf) | hgf) | hgf) | hgf) | hgf) | hgf) | hgf
    · rw [List.mem_singleton] at hgf; subst hgf
      refine ⟨PP c, fun i n hn => ?_⟩
      show RP c (n + p) i = RP c n i + PP c i
      rw [hRPrec' c n (by omega), Pi.add_apply]
    · rw [List.mem_map] at hgf; obtain ⟨j, _, rfl⟩ := hgf
      exact ⟨fun _ => 0, fun i n _ => by simp⟩
    · rw [List.mem_map] at hgf; obtain ⟨l, hl, rfl⟩ := hgf
      rw [List.mem_range] at hl
      refine ⟨PU c, fun i n hn => ?_⟩
      show RU c (n + p - 1 - l) i = RU c (n - 1 - l) i + PU c i
      rw [show n + p - 1 - l = (n - 1 - l) + p from by omega, hRUrec' c (n - 1 - l) (by omega),
        Pi.add_apply]
    · rw [List.mem_map] at hgf; obtain ⟨r, hr, rfl⟩ := hgf
      rw [List.mem_range] at hr
      refine ⟨if tlU c then PU c else fun _ => 0, fun i n hn => ?_⟩
      simp only [SliceDstar.selBvecVal]
      have hdiv : (n + p - (1 + 2 * m + r)) / p = (n - (1 + 2 * m + r)) / p + 1 := by
        rw [show n + p - (1 + 2 * m + r) = (n - (1 + 2 * m + r)) + p from by omega,
          Nat.add_div_right _ hp]
      cases htl : tlU c with
      | false => simp
      | true =>
          simp only [if_true]
          rw [hdiv]
          push_cast
          ring
    · rw [List.mem_map] at hgf; obtain ⟨j, _, rfl⟩ := hgf
      exact ⟨fun _ => 0, fun i n _ => by simp⟩
    · rw [List.mem_map] at hgf; obtain ⟨l, hl, rfl⟩ := hgf
      rw [List.mem_range] at hl
      refine ⟨PB c, fun i n hn => ?_⟩
      show RB c (n + p - 1 - l) i = RB c (n - 1 - l) i + PB c i
      rw [show n + p - 1 - l = (n - 1 - l) + p from by omega, hRBrec' c (n - 1 - l) (by omega),
        Pi.add_apply]
    · rw [List.mem_map] at hgf; obtain ⟨r, hr, rfl⟩ := hgf
      rw [List.mem_range] at hr
      refine ⟨if tlD c then PB c else fun _ => 0, fun i n hn => ?_⟩
      simp only [SliceDstar.selBvecVal]
      have hdiv : (n + p - (1 + 2 * m + r)) / p = (n - (1 + 2 * m + r)) / p + 1 := by
        rw [show n + p - (1 + 2 * m + r) = (n - (1 + 2 * m + r)) + p from by omega,
          Nat.add_div_right _ hp]
      cases htl : tlD c with
      | false => simp
      | true =>
          simp only [if_true]
          rw [hdiv]
          push_cast
          ring
    · rw [List.mem_singleton] at hgf; subst hgf
      refine ⟨PS c, fun i n hn => ?_⟩
      show RS c (n + p) i = RS c n i + PS c i
      rw [hRSrec' c n (by omega), Pi.add_apply]
  have hpair : ∀ gf ∈ cands, ∀ gf' ∈ cands,
      EventuallyPeriodic (fun n => WRP.lexLt (gf.2 n) (gf'.2 n)) p := by
    intro gf hgf gf' hgf'
    obtain ⟨Pf, hPf⟩ := hcandrec gf hgf
    obtain ⟨Pg, hPg⟩ := hcandrec gf' hgf'
    exact lexLt_eventuallyPeriodic (gf.2) (gf'.2) (2 * m + p + 1) p hp Pf Pg hPf hPg
  have hBIGaff : ∀ i, AffineOnResiduesZ (fun n => BIG n i) := by
    intro i
    by_cases hi : i = ⟨0, hd⟩
    · have heq : (fun n => BIG n i)
          = (fun n => ((cands.map (fun gf => fun n => gf.2 n ⟨0, hd⟩)).map (fun f => f n)).foldr max 0
              + 1) := by
        funext n
        simp only [hBIGdef, hi, ↓reduceIte, List.map_map, Function.comp_def]
      rw [heq]
      exact (affineOnResiduesZ_listMax (cands.map (fun gf => fun n => gf.2 n ⟨0, hd⟩))
        (fun f hf => by
          rw [List.mem_map] at hf; obtain ⟨gf, hgf, rfl⟩ := hf
          exact hcaff gf hgf ⟨0, hd⟩)).add (AffineOnResiduesZ.const 1)
    · have heq : (fun n => BIG n i) = (fun _ => (0 : ℤ)) := by
        funext n; rw [hBIGdef]; simp only [if_neg hi]
      rw [heq]; exact AffineOnResiduesZ.const 0
  have hdom : ∀ gf ∈ cands, ∀ n, WRP.lexLt (gf.2 n) (BIG n) := by
    intro gf hgf n
    refine ⟨⟨0, hd⟩, fun j hj => absurd (Fin.lt_def.mp hj) (Nat.not_lt_zero _), ?_⟩
    simp only [hBIGdef, ↓reduceIte]
    have hmem : gf.2 n ⟨0, hd⟩ ∈ cands.map (fun gf' => gf'.2 n ⟨0, hd⟩) :=
      List.mem_map.mpr ⟨gf, hgf, rfl⟩
    have := le_foldr_max hmem
    omega
  refine ⟨fun n => lexMinList (BIG :: cands.map
    (fun gf => fun n => if gf.1 n then gf.2 n else BIG n)) n, 2 * m + p + 1, ?_, ?_⟩
  · exact fun i => SliceDstar.gated_lexMin_affine cands hp hgate hcaff hpair BIG hBIGaff hdom i
  · intro n hn hD
    show dstarRank P hV harity n
      = lexMinList (BIG :: cands.map (fun gf => fun n => if gf.1 n then gf.2 n else BIG n)) n
    set L := BIG :: cands.map (fun gf => fun n => if gf.1 n then gf.2 n else BIG n) with hLdef
    have hLne : L ≠ [] := by rw [hLdef]; simp
    obtain ⟨hmin, hattn⟩ := lexMinList_le L hLne n
    obtain ⟨dstar, hdsel, hdD, hdmin, hdrank⟩ := dstarRank_spec P hV harity n hD
    -- DR ≤ₗₑₓ rankOf of every selected D-atom
    have hDRle : ∀ b, P.toPoly.selectedAtom (wrappedFlat n) b →
        P.toPoly.labelOf (wrappedFlat n) b = D →
        ¬ WRP.lexLt (P.rankOf (wrappedFlat n) b) (dstarRank P hV harity n) := by
      intro b hbsel hbD
      rw [hdrank]
      rcases hdmin b hbsel hbD with rfl | hord
      · exact lexLt_irrefl _
      · simp only [WRP.Presentation.wrpOrd] at hord
        rcases hord with hlt | ⟨heqr, _⟩
        · exact fun hcon => lexLt_irrefl _ (lexLt_trans _ _ _ hlt hcon)
        · rw [heqr]; exact lexLt_irrefl _
    -- (II) every on-candidate value is rankOf a selected D-atom
    have hmn : m ≤ n := by omega
    have hOnIsRank : ∀ gf ∈ cands, gf.1 n → ∃ b, P.toPoly.selectedAtom (wrappedFlat n) b ∧
        P.toPoly.labelOf (wrappedFlat n) b = D ∧ gf.2 n = P.rankOf (wrappedFlat n) b := by
      intro gf hgf hon
      rw [hcandsdef, List.mem_flatMap] at hgf
      obtain ⟨c, _, hgf⟩ := hgf
      rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append,
        List.mem_append, List.mem_append] at hgf
      rcases hgf with ((((((hgf | hgf) | hgf) | hgf) | hgf) | hgf) | hgf) | hgf
      · rw [List.mem_singleton] at hgf; subst hgf
        have hsel := (hMc c n 0 (by rw [length_wrappedFlat]; omega)).mpr hon
        exact ⟨⟨c, fun _ => 0⟩, hsel.1, hsel.2, rfl⟩
      · rw [List.mem_map] at hgf; obtain ⟨j, hj, rfl⟩ := hgf
        rw [List.mem_range] at hj
        have hsel := (hMc c n (1 + 2 * j) (by rw [length_wrappedFlat]; omega)).mpr hon
        exact ⟨⟨c, fun _ => 1 + 2 * j⟩, hsel.1, hsel.2,
          (rank_block_prefix_invariant P c n j (by omega)).1.symm⟩
      · rw [List.mem_map] at hgf; obtain ⟨l, hl, rfl⟩ := hgf
        rw [List.mem_range] at hl
        have hsel := (hMc c n (1 + 2 * (n - 1 - l)) (by rw [length_wrappedFlat]; omega)).mpr hon
        exact ⟨⟨c, fun _ => 1 + 2 * (n - 1 - l)⟩, hsel.1, hsel.2,
          (rank_block_prefix_invariant P c n (n - 1 - l) (by omega)).1.symm⟩
      · -- bulkU r
        rw [List.mem_map] at hgf; obtain ⟨r, hr, rfl⟩ := hgf
        rw [List.mem_range] at hr
        obtain ⟨kend, hkenddef⟩ : ∃ k : ℕ, k = (n - (1 + 2 * m + r)) / p := ⟨_, rfl⟩
        obtain ⟨kbd, hkbddef⟩ : ∃ k : ℕ, k = (if tlU c then kend else 0 : ℕ) := ⟨_, rfl⟩
        have hkbd_le : kbd ≤ kend := by rw [hkbddef]; split; exacts [le_refl _, Nat.zero_le _]
        have hpke : p * kend ≤ n - (1 + 2 * m + r) := by
          rw [hkenddef, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
        have h1 : p * kbd ≤ p * kend := Nat.mul_le_mul (le_refl p) hkbd_le
        have hbd_lt : m + r + p * kbd < n := by omega
        have hmr_lt : m + r < n := by omega
        have hsel_eq : SliceDstar.selBvecVal (RU c) m r (PU c) (tlU c) 0 kend
            = RU c (m + r + p * kbd) := by
          funext i
          have hit := congrFun (RankAffine.iterate (hRUrec' c) (m + r) kbd (by omega)) i
          rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at hit
          rw [SliceDstar.selBvecVal, hit, hkbddef]
          by_cases htl : tlU c
          · simp only [if_pos htl]
          · simp only [if_neg htl]
        have hf : (bF (Mc c))^[m + r + p * kbd] (qpre (Mc c))
            = (bF (Mc c))^[m + r] (qpre (Mc c)) :=
          fn_period_mul (fun j => (bF (Mc c))^[j] (qpre (Mc c))) (hfwd c) (m + r) kbd (by omega)
        have hb : (bF (Mc c))^[n - 1 - (m + r + p * kbd)] = (bF (Mc c))^[n - 1 - (m + r)] := by
          rw [show n - 1 - (m + r) = (n - 1 - (m + r + p * kbd)) + p * kbd from by omega]
          exact (fn_period_mul (fun j => (bF (Mc c))^[j]) (hbwd c)
            (n - 1 - (m + r + p * kbd)) kbd (by omega)).symm
        have hacc : (Mc c).accepts (markAt (wrappedFlat n) (1 + 2 * (m + r + p * kbd))) :=
          (selBU_eq_of_iter (Mc c) n (m + r + p * kbd) (m + r) hbd_lt hmr_lt hf hb).mpr hon
        have hsel := (hMc c n (1 + 2 * (m + r + p * kbd))
          (by rw [length_wrappedFlat]; omega)).mpr hacc
        refine ⟨⟨c, fun _ => 1 + 2 * (m + r + p * kbd)⟩, hsel.1, hsel.2, ?_⟩
        show SliceDstar.selBvecVal (RU c) m r (PU c) (tlU c) 0 ((n - (1 + 2 * m + r)) / p)
            = P.rankOf (wrappedFlat n) ⟨c, fun _ => 1 + 2 * (m + r + p * kbd)⟩
        rw [← hkenddef, hsel_eq]
        exact (rank_block_prefix_invariant P c n (m + r + p * kbd) hbd_lt).1.symm
      · rw [List.mem_map] at hgf; obtain ⟨j, hj, rfl⟩ := hgf
        rw [List.mem_range] at hj
        have hsel := (hMc c n (1 + 2 * j + 1) (by rw [length_wrappedFlat]; omega)).mpr hon
        exact ⟨⟨c, fun _ => 1 + 2 * j + 1⟩, hsel.1, hsel.2,
          (rank_block_prefix_invariant P c n j (by omega)).2.symm⟩
      · rw [List.mem_map] at hgf; obtain ⟨l, hl, rfl⟩ := hgf
        rw [List.mem_range] at hl
        have hsel := (hMc c n (1 + 2 * (n - 1 - l) + 1) (by rw [length_wrappedFlat]; omega)).mpr hon
        exact ⟨⟨c, fun _ => 1 + 2 * (n - 1 - l) + 1⟩, hsel.1, hsel.2,
          (rank_block_prefix_invariant P c n (n - 1 - l) (by omega)).2.symm⟩
      · -- bulkD r
        rw [List.mem_map] at hgf; obtain ⟨r, hr, rfl⟩ := hgf
        rw [List.mem_range] at hr
        obtain ⟨kend, hkenddef⟩ : ∃ k : ℕ, k = (n - (1 + 2 * m + r)) / p := ⟨_, rfl⟩
        obtain ⟨kbd, hkbddef⟩ : ∃ k : ℕ, k = (if tlD c then kend else 0 : ℕ) := ⟨_, rfl⟩
        have hkbd_le : kbd ≤ kend := by rw [hkbddef]; split; exacts [le_refl _, Nat.zero_le _]
        have hpke : p * kend ≤ n - (1 + 2 * m + r) := by
          rw [hkenddef, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
        have h1 : p * kbd ≤ p * kend := Nat.mul_le_mul (le_refl p) hkbd_le
        have hbd_lt : m + r + p * kbd < n := by omega
        have hmr_lt : m + r < n := by omega
        have hsel_eq : SliceDstar.selBvecVal (RB c) m r (PB c) (tlD c) 0 kend
            = RB c (m + r + p * kbd) := by
          funext i
          have hit := congrFun (RankAffine.iterate (hRBrec' c) (m + r) kbd (by omega)) i
          rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at hit
          rw [SliceDstar.selBvecVal, hit, hkbddef]
          by_cases htl : tlD c
          · simp only [if_pos htl]
          · simp only [if_neg htl]
        have hf : (bF (Mc c))^[m + r + p * kbd] (qpre (Mc c))
            = (bF (Mc c))^[m + r] (qpre (Mc c)) :=
          fn_period_mul (fun j => (bF (Mc c))^[j] (qpre (Mc c))) (hfwd c) (m + r) kbd (by omega)
        have hb : (bF (Mc c))^[n - 1 - (m + r + p * kbd)] = (bF (Mc c))^[n - 1 - (m + r)] := by
          rw [show n - 1 - (m + r) = (n - 1 - (m + r + p * kbd)) + p * kbd from by omega]
          exact (fn_period_mul (fun j => (bF (Mc c))^[j]) (hbwd c)
            (n - 1 - (m + r + p * kbd)) kbd (by omega)).symm
        have hacc : (Mc c).accepts (markAt (wrappedFlat n) (1 + 2 * (m + r + p * kbd) + 1)) :=
          (selBD_eq_of_iter (Mc c) n (m + r + p * kbd) (m + r) hbd_lt hmr_lt hf hb).mpr hon
        have hsel := (hMc c n (1 + 2 * (m + r + p * kbd) + 1)
          (by rw [length_wrappedFlat]; omega)).mpr hacc
        refine ⟨⟨c, fun _ => 1 + 2 * (m + r + p * kbd) + 1⟩, hsel.1, hsel.2, ?_⟩
        show SliceDstar.selBvecVal (RB c) m r (PB c) (tlD c) 0 ((n - (1 + 2 * m + r)) / p)
            = P.rankOf (wrappedFlat n) ⟨c, fun _ => 1 + 2 * (m + r + p * kbd) + 1⟩
        rw [← hkenddef, hsel_eq]
        exact (rank_block_prefix_invariant P c n (m + r + p * kbd) hbd_lt).2.symm
      · rw [List.mem_singleton] at hgf; subst hgf
        have hsel := (hMc c n (1 + 2 * n) (by rw [length_wrappedFlat]; omega)).mpr hon
        exact ⟨⟨c, fun _ => 1 + 2 * n⟩, hsel.1, hsel.2, rfl⟩
    have hII : ∀ gf ∈ cands, gf.1 n → ¬ WRP.lexLt (gf.2 n) (dstarRank P hV harity n) := by
      intro gf hgf hon
      obtain ⟨b, hbsel, hbD, hbeq⟩ := hOnIsRank gf hgf hon
      rw [hbeq]; exact hDRle b hbsel hbD
    -- (I) dstar's own candidate is on and ≤ₗₑₓ DR
    have hI : ∃ gf ∈ cands, gf.1 n ∧ ¬ WRP.lexLt (dstarRank P hV harity n) (gf.2 n) := by
      clear hII hDRle hOnIsRank hmin hattn hLne hLdef L hdom hBIGaff hcandrec hpair hcaff hgate
        hBIGdef BIG
      have h0 : 0 < P.toPoly.arity dstar.1 := by have := harity dstar.1; omega
      obtain ⟨c0, hc0⟩ : ∃ c, c = dstar.1 := ⟨_, rfl⟩
      obtain ⟨q0, hq0d⟩ : ∃ q, q = dstar.2 ⟨0, h0⟩ := ⟨_, rfl⟩
      have hdeq : dstar = ⟨c0, fun _ => q0⟩ := by
        rw [hc0, hq0d]; exact atom_arity_one_eq harity dstar h0
      have hq0lt : q0 < 2 * (n + 1) := by
        rw [hq0d]; have := hdsel.1 ⟨0, h0⟩; rwa [length_wrappedFlat] at this
      have hdsel' : P.toPoly.selectedAtom (wrappedFlat n) ⟨c0, fun _ => q0⟩ := hdeq ▸ hdsel
      have hdD' : P.toPoly.labelOf (wrappedFlat n) ⟨c0, fun _ => q0⟩ = D := hdeq ▸ hdD
      have hDReq : dstarRank P hV harity n = P.rank c0 (wrappedFlat n) (fun _ => q0) := by
        rw [hdrank, hdeq]; rfl
      have hrecU : ∀ (i : Fin P.d) (r' k : ℕ),
          RU c0 (m + r' + p * k) i = RU c0 (m + r') i + k * PU c0 i := by
        intro i r' k
        have ht := congrFun (RankAffine.iterate (hRUrec' c0) (m + r') k (by omega)) i
        rwa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at ht
      have hrecB : ∀ (i : Fin P.d) (r' k : ℕ),
          RB c0 (m + r' + p * k) i = RB c0 (m + r') i + k * PB c0 i := by
        intro i r' k
        have ht := congrFun (RankAffine.iterate (hRBrec' c0) (m + r') k (by omega)) i
        rwa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at ht
      have hflagU : tlU c0 = true ↔ WRP.lexLt (PU c0) (fun _ => 0) := by
        rw [htlUdef]; exact decide_eq_true_iff
      have hflagB : tlD c0 = true ↔ WRP.lexLt (PB c0) (fun _ => 0) := by
        rw [htlDdef]; exact decide_eq_true_iff
      by_cases hpre : q0 = 0
      · have hmem : (fun n => (Mc c0).accepts (markAt (wrappedFlat n) 0), fun n => RP c0 n) ∈ cands := by
          rw [hcandsdef]
          exact List.mem_flatMap.mpr ⟨c0, List.mem_finRange c0,
            List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_left _ (List.mem_singleton.mpr rfl)))))))⟩
        refine ⟨_, hmem, ?_, ?_⟩
        · exact (hMc c0 n 0 (by rw [length_wrappedFlat]; omega)).mp ⟨hpre ▸ hdsel', hpre ▸ hdD'⟩
        · show ¬ WRP.lexLt (dstarRank P hV harity n) (RP c0 n)
          have heq : dstarRank P hV harity n = RP c0 n := by rw [hDReq, hpre]
          rw [heq]; exact lexLt_irrefl _
      by_cases hsuf : q0 = 2 * n + 1
      · have hmem : (fun n => (Mc c0).accepts (markAt (wrappedFlat n) (1 + 2 * n)),
            fun n => RS c0 n) ∈ cands := by
          rw [hcandsdef]
          exact List.mem_flatMap.mpr ⟨c0, List.mem_finRange c0,
            List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
        refine ⟨_, hmem, ?_, ?_⟩
        · exact (hMc c0 n (1 + 2 * n) (by rw [length_wrappedFlat]; omega)).mp
            (by rw [show (1 : ℕ) + 2 * n = q0 from by omega]; exact ⟨hdsel', hdD'⟩)
        · show ¬ WRP.lexLt (dstarRank P hV harity n) (RS c0 n)
          have heq : dstarRank P hV harity n = RS c0 n := by
            rw [hDReq]; show P.rank c0 (wrappedFlat n) (fun _ => q0) = RS c0 n
            rw [show q0 = 1 + 2 * n from by omega]
          rw [heq]; exact lexLt_irrefl _
      rcases Nat.even_or_odd q0 with ⟨jj, hjj⟩ | ⟨jj, hjj⟩
      · -- even q0 = jj + jj, blockD at j = jj - 1
        have hjlt : jj - 1 < n := by omega
        have hqj : q0 = 1 + 2 * (jj - 1) + 1 := by omega
        by_cases hfront : jj - 1 < m
        · have hmem : (fun n => (Mc c0).accepts (markAt (wrappedFlat n) (1 + 2 * (jj - 1) + 1)),
              fun _ => RB c0 (jj - 1)) ∈ cands := by
            rw [hcandsdef]
            exact List.mem_flatMap.mpr ⟨c0, List.mem_finRange c0,
              List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hfront)))))⟩
          refine ⟨_, hmem, ?_, ?_⟩
          · exact (hMc c0 n (1 + 2 * (jj - 1) + 1) (by rw [length_wrappedFlat]; omega)).mp
              (by rw [← hqj]; exact ⟨hdsel', hdD'⟩)
          · show ¬ WRP.lexLt (dstarRank P hV harity n) (RB c0 (jj - 1))
            have heq : dstarRank P hV harity n = RB c0 (jj - 1) := by
              rw [hDReq]; show P.rank c0 (wrappedFlat n) (fun _ => q0) = RB c0 (jj - 1)
              rw [hqj]; exact (rank_block_prefix_invariant P c0 n (jj - 1) hjlt).2
            rw [heq]; exact lexLt_irrefl _
        by_cases hback : n - 1 - m < jj - 1
        · obtain ⟨l, hl⟩ : ∃ l, l = n - 1 - (jj - 1) := ⟨_, rfl⟩
          have hlm : l < m := by rw [hl]; omega
          have hnl : n - 1 - l = jj - 1 := by rw [hl]; omega
          have hmem : (fun n => (Mc c0).accepts (markAt (wrappedFlat n) (1 + 2 * (n - 1 - l) + 1)),
              fun n => RB c0 (n - 1 - l)) ∈ cands := by
            rw [hcandsdef]
            exact List.mem_flatMap.mpr ⟨c0, List.mem_finRange c0,
              List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hlm))))⟩
          refine ⟨_, hmem, ?_, ?_⟩
          · show (Mc c0).accepts (markAt (wrappedFlat n) (1 + 2 * (n - 1 - l) + 1))
            rw [hnl]
            exact (hMc c0 n (1 + 2 * (jj - 1) + 1) (by rw [length_wrappedFlat]; omega)).mp
              (by rw [← hqj]; exact ⟨hdsel', hdD'⟩)
          · show ¬ WRP.lexLt (dstarRank P hV harity n) (RB c0 (n - 1 - l))
            rw [hnl]
            have heq : dstarRank P hV harity n = RB c0 (jj - 1) := by
              rw [hDReq]; show P.rank c0 (wrappedFlat n) (fun _ => q0) = RB c0 (jj - 1)
              rw [hqj]; exact (rank_block_prefix_invariant P c0 n (jj - 1) hjlt).2
            rw [heq]; exact lexLt_irrefl _
        · -- bulkD
          obtain ⟨r, hrdef⟩ : ∃ rr : ℕ, rr = (jj - 1 - m) % p := ⟨_, rfl⟩
          obtain ⟨kd, hkddef⟩ : ∃ kk : ℕ, kk = (jj - 1 - m) / p := ⟨_, rfl⟩
          obtain ⟨kend, hkenddef⟩ : ∃ kk : ℕ, kk = (n - (1 + 2 * m + r)) / p := ⟨_, rfl⟩
          have hrlt : r < p := by rw [hrdef]; exact Nat.mod_lt _ hp
          have hjeq : m + r + p * kd = jj - 1 := by
            rw [hrdef, hkddef]; have := Nat.mod_add_div (jj - 1 - m) p; omega
          have hpkd : p * kd ≤ n - (1 + 2 * m + r) := by omega
          have hkd_le : kd ≤ kend := by
            rw [hkenddef, Nat.le_div_iff_mul_le hp, Nat.mul_comm]; exact hpkd
          have hN : numReps m p r (n - m) = kend + 1 := by
            unfold numReps; rw [if_pos (by omega), hkenddef,
              show n - m - (m + r) - 1 = n - (1 + 2 * m + r) from by omega]
          have hmem : (fun n => (Mc c0).accepts (markAt (wrappedFlat n) (1 + 2 * (m + r) + 1)),
              fun n => SliceDstar.selBvecVal (RB c0) m r (PB c0) (tlD c0) 0
                ((n - (1 + 2 * m + r)) / p)) ∈ cands := by
            rw [hcandsdef]
            exact List.mem_flatMap.mpr ⟨c0, List.mem_finRange c0,
              List.mem_append_left _ (List.mem_append_right _
                (List.mem_map_of_mem (List.mem_range.mpr hrlt)))⟩
          refine ⟨_, hmem, ?_, ?_⟩
          · have hf : (bF (Mc c0))^[m + r] (qpre (Mc c0)) = (bF (Mc c0))^[jj - 1] (qpre (Mc c0)) := by
              rw [← hjeq]
              exact (fn_period_mul (fun j => (bF (Mc c0))^[j] (qpre (Mc c0))) (hfwd c0) (m + r) kd (by omega)).symm
            have hb : (bF (Mc c0))^[n - 1 - (m + r)] = (bF (Mc c0))^[n - 1 - (jj - 1)] := by
              rw [show n - 1 - (m + r) = (n - 1 - (jj - 1)) + p * kd from by omega]
              exact fn_period_mul (fun j => (bF (Mc c0))^[j]) (hbwd c0) (n - 1 - (jj - 1)) kd (by omega)
            have hacc : (Mc c0).accepts (markAt (wrappedFlat n) (1 + 2 * (jj - 1) + 1)) :=
              (hMc c0 n (1 + 2 * (jj - 1) + 1) (by rw [length_wrappedFlat]; omega)).mp
                (by rw [← hqj]; exact ⟨hdsel', hdD'⟩)
            show (Mc c0).accepts (markAt (wrappedFlat n) (1 + 2 * (m + r) + 1))
            rw [selBD_eq_of_iter (Mc c0) n (m + r) (jj - 1) (by omega) (by omega) hf hb]
            exact hacc
          · show ¬ WRP.lexLt (dstarRank P hV harity n)
              (SliceDstar.selBvecVal (RB c0) m r (PB c0) (tlD c0) 0 ((n - (1 + 2 * m + r)) / p))
            have hDeq : dstarRank P hV harity n = RB c0 (jj - 1) := by
              rw [hDReq]; show P.rank c0 (wrappedFlat n) (fun _ => q0) = RB c0 (jj - 1)
              rw [hqj]; exact (rank_block_prefix_invariant P c0 n (jj - 1) hjlt).2
            rw [show (n - (1 + 2 * m + r)) / p = numReps m p r (n - m) - 1 from by rw [hN]; omega,
              hDeq, ← hjeq]
            exact selBvec_le_member (RB c0) (PB c0) (tlD c0) hrecB hflagB r (n - m) kd
              (by rw [hN]; omega)
      · -- odd q0 = 2 * jj + 1, blockU at j = jj
        have hjlt : jj < n := by omega
        have hqj : q0 = 1 + 2 * jj := by omega
        by_cases hfront : jj < m
        · have hmem : (fun n => (Mc c0).accepts (markAt (wrappedFlat n) (1 + 2 * jj)),
              fun _ => RU c0 jj) ∈ cands := by
            rw [hcandsdef]
            exact List.mem_flatMap.mpr ⟨c0, List.mem_finRange c0,
              List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hfront)))))))) ⟩
          refine ⟨_, hmem, ?_, ?_⟩
          · exact (hMc c0 n (1 + 2 * jj) (by rw [length_wrappedFlat]; omega)).mp
              (by rw [← hqj]; exact ⟨hdsel', hdD'⟩)
          · show ¬ WRP.lexLt (dstarRank P hV harity n) (RU c0 jj)
            have heq : dstarRank P hV harity n = RU c0 jj := by
              rw [hDReq]; show P.rank c0 (wrappedFlat n) (fun _ => q0) = RU c0 jj
              rw [hqj]; exact (rank_block_prefix_invariant P c0 n jj hjlt).1
            rw [heq]; exact lexLt_irrefl _
        by_cases hback : n - 1 - m < jj
        · obtain ⟨l, hl⟩ : ∃ l, l = n - 1 - jj := ⟨_, rfl⟩
          have hlm : l < m := by rw [hl]; omega
          have hnl : n - 1 - l = jj := by rw [hl]; omega
          have hmem : (fun n => (Mc c0).accepts (markAt (wrappedFlat n) (1 + 2 * (n - 1 - l))),
              fun n => RU c0 (n - 1 - l)) ∈ cands := by
            rw [hcandsdef]
            exact List.mem_flatMap.mpr ⟨c0, List.mem_finRange c0,
              List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hlm)))))))⟩
          refine ⟨_, hmem, ?_, ?_⟩
          · show (Mc c0).accepts (markAt (wrappedFlat n) (1 + 2 * (n - 1 - l)))
            rw [hnl]
            exact (hMc c0 n (1 + 2 * jj) (by rw [length_wrappedFlat]; omega)).mp
              (by rw [← hqj]; exact ⟨hdsel', hdD'⟩)
          · show ¬ WRP.lexLt (dstarRank P hV harity n) (RU c0 (n - 1 - l))
            rw [hnl]
            have heq : dstarRank P hV harity n = RU c0 jj := by
              rw [hDReq]; show P.rank c0 (wrappedFlat n) (fun _ => q0) = RU c0 jj
              rw [hqj]; exact (rank_block_prefix_invariant P c0 n jj hjlt).1
            rw [heq]; exact lexLt_irrefl _
        · -- bulkU
          obtain ⟨r, hrdef⟩ : ∃ rr : ℕ, rr = (jj - m) % p := ⟨_, rfl⟩
          obtain ⟨kd, hkddef⟩ : ∃ kk : ℕ, kk = (jj - m) / p := ⟨_, rfl⟩
          obtain ⟨kend, hkenddef⟩ : ∃ kk : ℕ, kk = (n - (1 + 2 * m + r)) / p := ⟨_, rfl⟩
          have hrlt : r < p := by rw [hrdef]; exact Nat.mod_lt _ hp
          have hjeq : m + r + p * kd = jj := by
            rw [hrdef, hkddef]; have := Nat.mod_add_div (jj - m) p; omega
          have hpkd : p * kd ≤ n - (1 + 2 * m + r) := by omega
          have hkd_le : kd ≤ kend := by
            rw [hkenddef, Nat.le_div_iff_mul_le hp, Nat.mul_comm]; exact hpkd
          have hN : numReps m p r (n - m) = kend + 1 := by
            unfold numReps; rw [if_pos (by omega), hkenddef,
              show n - m - (m + r) - 1 = n - (1 + 2 * m + r) from by omega]
          have hmem : (fun n => (Mc c0).accepts (markAt (wrappedFlat n) (1 + 2 * (m + r))),
              fun n => SliceDstar.selBvecVal (RU c0) m r (PU c0) (tlU c0) 0
                ((n - (1 + 2 * m + r)) / p)) ∈ cands := by
            rw [hcandsdef]
            exact List.mem_flatMap.mpr ⟨c0, List.mem_finRange c0,
              List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_left _ (List.mem_append_right _
                (List.mem_map_of_mem (List.mem_range.mpr hrlt))))))⟩
          refine ⟨_, hmem, ?_, ?_⟩
          · have hf : (bF (Mc c0))^[m + r] (qpre (Mc c0)) = (bF (Mc c0))^[jj] (qpre (Mc c0)) := by
              rw [← hjeq]
              exact (fn_period_mul (fun j => (bF (Mc c0))^[j] (qpre (Mc c0))) (hfwd c0) (m + r) kd (by omega)).symm
            have hb : (bF (Mc c0))^[n - 1 - (m + r)] = (bF (Mc c0))^[n - 1 - jj] := by
              rw [show n - 1 - (m + r) = (n - 1 - jj) + p * kd from by omega]
              exact fn_period_mul (fun j => (bF (Mc c0))^[j]) (hbwd c0) (n - 1 - jj) kd (by omega)
            have hacc : (Mc c0).accepts (markAt (wrappedFlat n) (1 + 2 * jj)) :=
              (hMc c0 n (1 + 2 * jj) (by rw [length_wrappedFlat]; omega)).mp
                (by rw [← hqj]; exact ⟨hdsel', hdD'⟩)
            show (Mc c0).accepts (markAt (wrappedFlat n) (1 + 2 * (m + r)))
            rw [selBU_eq_of_iter (Mc c0) n (m + r) jj (by omega) hjlt hf hb]
            exact hacc
          · show ¬ WRP.lexLt (dstarRank P hV harity n)
              (SliceDstar.selBvecVal (RU c0) m r (PU c0) (tlU c0) 0 ((n - (1 + 2 * m + r)) / p))
            have hDeq : dstarRank P hV harity n = RU c0 jj := by
              rw [hDReq]; show P.rank c0 (wrappedFlat n) (fun _ => q0) = RU c0 jj
              rw [hqj]; exact (rank_block_prefix_invariant P c0 n jj hjlt).1
            rw [show (n - (1 + 2 * m + r)) / p = numReps m p r (n - m) - 1 from by rw [hN]; omega,
              hDeq, ← hjeq]
            exact selBvec_le_member (RU c0) (PU c0) (tlU c0) hrecU hflagU r (n - m) kd
              (by rw [hN]; omega)
    obtain ⟨gfd, hgfd, hond, hled⟩ := hI
    set gatedd : ℕ → Fin P.d → ℤ := fun n => if gfd.1 n then gfd.2 n else BIG n with hgddef
    have hgddmem : gatedd ∈ L := by
      rw [hLdef]; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨gfd, hgfd, rfl⟩)
    have hgddval : gatedd n = gfd.2 n := by rw [hgddef]; simp only [if_pos hond]
    have hDCle : ¬ WRP.lexLt (gatedd n) (lexMinList L n) := hmin gatedd hgddmem
    have hIfinal : ¬ WRP.lexLt (dstarRank P hV harity n) (lexMinList L n) := by
      rw [← hgddval] at hled
      exact lexLt_negtrans _ _ _ hled hDCle
    have hDClt : WRP.lexLt (lexMinList L n) (BIG n) := by
      have hgdlt : WRP.lexLt (gatedd n) (BIG n) := by rw [hgddval]; exact hdom gfd hgfd n
      rcases lexLt_trichot (lexMinList L n) (gatedd n) with h | h | h
      · exact lexLt_trans _ _ _ h hgdlt
      · rw [h]; exact hgdlt
      · exact absurd h hDCle
    obtain ⟨F, hFmem, hFeq⟩ := hattn
    have hIIfinal : ¬ WRP.lexLt (lexMinList L n) (dstarRank P hV harity n) := by
      rw [hLdef, List.mem_cons] at hFmem
      rcases hFmem with rfl | hFmem
      · rw [hFeq] at hDClt; exact absurd hDClt (lexLt_irrefl _)
      · rw [List.mem_map] at hFmem; obtain ⟨gf, hgf, rfl⟩ := hFmem
        by_cases hon : gf.1 n
        · have hval : lexMinList L n = gf.2 n := by rw [hFeq]; simp only [if_pos hon]
          rw [hval]; exact hII gf hgf hon
        · have hval : lexMinList L n = BIG n := by rw [hFeq]; simp only [if_neg hon]
          rw [hval] at hDClt; exact absurd hDClt (lexLt_irrefl _)
    rcases lexLt_trichot (dstarRank P hV harity n) (lexMinList L n) with h | h | h
    · exact absurd h hIfinal
    · exact h
    · exact absurd h hIIfinal

/-- **The dominant-risk §7 lemma (arity-1 `d*`-rank is affine-on-residues).**  Each coordinate of
`dstarRank` is `AffineOnResiduesZ` in `n`: it equals the constructive `dstarC` on every `D`-present
slice past the threshold (and `0` on `D`-absent slices, whose set is eventually periodic). -/
theorem dstarRank_affineOnResiduesZ (P : WRP.Presentation Step Step) (hV : P.Valid)
    (harity : ∀ c, P.toPoly.arity c = 1) (i : Fin P.d) :
    AffineOnResiduesZ (fun n => dstarRank P hV harity n i) := by
  obtain ⟨dstarC, N0, haff, hbridge⟩ := dstarC_exists P hV harity
  obtain ⟨pD, hpD, hEPD⟩ := Dpresent_eventuallyPeriodic P
  refine AffineOnResiduesZ.congr_eventually (N := N0) (fun n hn => ?_)
    (SliceVectorLexMin.affineOnResiduesZ_ite_of_EP hpD hEPD (haff i) (AffineOnResiduesZ.const 0))
  by_cases hD : ∃ a, P.toPoly.selectedAtom (wrappedFlat n) a
      ∧ P.toPoly.labelOf (wrappedFlat n) a = D
  · rw [if_pos hD, hbridge n hn hD]
  · rw [if_neg hD]; simp only [dstarRank, dif_neg hD]

end SliceDstarBridge
