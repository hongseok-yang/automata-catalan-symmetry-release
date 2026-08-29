/-
# The general-arity equal-rank cell selector — prerequisites (GA-6.3a/b/c)

The GA-6.3 selector `eqRankD_cell_selector` determines which cells `(c', rs, t)` carry equal-rank
selected `D`-atoms per residue class of `n`.  This file lands it and its support layer:

* `dstarRankGA_lex_min` — no selected `D`-atom's rank lex-precedes the `d*`-rank
  (the minimality input to the Case-A chain forcing);
* `freeze_front_descr` / `freeze_back_descr` — the bundled re-freezes: a cell whose
  base sits in a boundary zone IS a cluster-free cell over the enlarged bound at the
  dummy base `Bh + 1`;
* `clusterFree_regionLift` + `cellTuple_regionLift` — descriptor lifting transport;
* `base_mod_iff` — the base-position residue translation
  `(1+2t) % 2p = (1+2(m'+r)) % 2p ↔ (t−m') % p = r`.

Axiom-clean except where the `d*` spec enters (+`SliceMSO.buchi`).
-/
import RequestProject.SliceFasGatesGA
import RequestProject.SliceDstarBridgeGA
import RequestProject.SliceFasSelector

namespace SliceFasSelectorGA

open WRP Step SliceFamilyCell SliceDstarGA SliceDstarGateGA SliceFasGatesGA
  SliceRankAtom SliceThreshold
open scoped Classical

/-! ## GA-6.3a: the lex-minimality interface -/

/-- **No selected `D`-atom's rank lex-precedes the `d*`-rank** (general arity). -/
theorem dstarRankGA_lex_min (P : WRP.Presentation Step Step) (hV : P.Valid) (n : ℕ)
    (hD : ∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧
      P.toPoly.labelOf (wrappedFlat n) a = D)
    (b : P.toPoly.Atom) (hbsel : P.toPoly.selectedAtom (wrappedFlat n) b)
    (hbD : P.toPoly.labelOf (wrappedFlat n) b = D) :
    ¬ WRP.lexLt (P.rankOf (wrappedFlat n) b) (SliceDstarGA.dstarRankGA P hV n) := by
  obtain ⟨dstar, hdsel, hdD, hdmin, hdrank⟩ := SliceDstarGA.dstarRankGA_spec P hV n hD
  rw [hdrank]
  rcases hdmin b hbsel hbD with rfl | hord
  · exact SliceLexOrder.lexLt_irrefl _
  · simp only [WRP.Presentation.wrpOrd] at hord
    rcases hord with hlt | ⟨heqr, _⟩
    · exact fun hcon => SliceLexOrder.lexLt_irrefl _
        (SliceLexOrder.lexLt_trans _ _ _ hlt hcon)
    · rw [heqr]
      exact SliceLexOrder.lexLt_irrefl _

/-! ## GA-6.3c: the bundled re-freezes -/

/-- A cell whose base sits in the front zone is a cluster-free cell over the enlarged
bound, at the dummy base `Bh + 1`. -/
theorem freeze_front_descr {B Bh k : ℕ} (hBB : B ≤ Bh) (rs : Fin k → RegionSpec B)
    (t n : ℕ) (htB : t + B ≤ Bh) :
    ∃ rs' : Fin k → RegionSpec Bh, (∀ i, clusterFree (rs' i)) ∧
      cellTuple rs t n = cellTuple rs' (Bh + 1) n :=
  ⟨fun i => refreezeFront hBB t htB (rs i),
   fun i => clusterFree_refreezeFront hBB t htB (rs i),
   funext (fun i => (refreezeFront_posAt hBB t htB (rs i) (Bh + 1) n).symm)⟩

/-- A cell whose base sits in the back zone is a cluster-free cell over the enlarged
bound, at the dummy base `Bh + 1`. -/
theorem freeze_back_descr {B Bh k : ℕ} (hBB : B ≤ Bh) (hBh1 : 1 ≤ Bh)
    (rs : Fin k → RegionSpec B) (t n : ℕ) (hback : n ≤ t + Bh) (htn : t + B ≤ n) :
    ∃ rs' : Fin k → RegionSpec Bh, (∀ i, clusterFree (rs' i)) ∧
      cellTuple rs t n = cellTuple rs' (Bh + 1) n :=
  ⟨fun i => refreezeBack hBB hBh1 t n hback (rs i),
   fun i => clusterFree_refreezeBack hBB hBh1 t n hback (rs i),
   funext (fun i =>
     (refreezeBack_posAt hBB hBh1 t n hback htn (rs i) (Bh + 1)).symm)⟩

/-! ## GA-6.3b: glue -/

/-- Lifting preserves cluster-freedom in both directions. -/
theorem clusterFree_regionLift {B B' : ℕ} (h : B ≤ B') (r : RegionSpec B) :
    clusterFree (regionLift h r) ↔ clusterFree r := by
  rcases r with _ | _ | ⟨f, e⟩ | ⟨l, e⟩ | ⟨δ, e⟩ <;>
    simp only [regionLift, clusterFree]

/-- A cell over `B` is the same cell over any larger bound. -/
theorem cellTuple_regionLift {B B' k : ℕ} (h : B ≤ B') (rs : Fin k → RegionSpec B)
    (t n : ℕ) :
    cellTuple (fun i => regionLift h (rs i)) t n = cellTuple rs t n :=
  funext (fun i => regionLift_posAt h (rs i) t n)

/-- **The base-position residue translation**: two odd base positions agree mod `2p`
exactly when the bases agree mod `p` — stated in the selector's `(t − m') % p = r`
form. -/
theorem base_mod_iff (m' p t r : ℕ) (hp : 1 ≤ p) (hr : r < p) (ht : m' ≤ t) :
    ((1 + 2 * t) % (2 * p) = (1 + 2 * (m' + r)) % (2 * p)) ↔ (t - m') % p = r := by
  rw [SliceFasSelector.odd_mod_two_mul t p hp,
    SliceFasSelector.odd_mod_two_mul (m' + r) p hp]
  constructor
  · intro h
    have hmod : t ≡ m' + r [MOD p] := by
      unfold Nat.ModEq
      omega
    have h2 : m' + (t - m') ≡ m' + r [MOD p] := by
      rwa [show m' + (t - m') = t from by omega]
    have h3 : t - m' ≡ r [MOD p] := Nat.ModEq.add_left_cancel' m' h2
    rw [Nat.ModEq] at h3
    rw [h3, Nat.mod_eq_of_lt hr]
  · intro h
    have hmod : t % p = (m' + r) % p := by
      conv_lhs => rw [show t = m' + (t - m') from by omega]
      rw [Nat.add_mod, h]
      conv_rhs => rw [Nat.add_mod]
      rw [Nat.mod_eq_of_lt hr]
    omega

/-! ## GA-6.3e: the equal-rank cell selector -/

/-- **The equal-rank cell selector** (GA-6.3e, the general-arity cell form of the arity-1
position selector).  Parameterized on the GA-5 monolith output
`(dstarC, N0, hCaff, hCagree)`; produces `M := 2p`, `mthr := 2·tBk`, a class period
`p0`, a threshold `N1`, and per-class two-layer data: bulk residue classes `S₁` (the
collinear full classes — both Case-A chain endpoints land in the freeze zones) over
`RegionSpec B`, and the frozen front data `F₂` at the single fixed base position
`1 + 2(Bh+1)` over `RegionSpec Bh`.  On in-domain `D`-present slices `n ≥ N1`, a
selected `D`-atom has `d*`-rank exactly when it lies in the class-`n % p0` cells. -/
theorem eqRankD_cell_selector (P : WRP.Presentation Step Step) (hV : P.Valid) (C : ℕ)
    (hbud : ∀ n, P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1))
    (dstarC : ℕ → Fin P.d → ℤ) (N0 : ℕ)
    (hCaff : ∀ i, AffineOnResiduesZ (fun n => dstarC n i))
    (hCagree : ∀ n, N0 ≤ n → P.toPoly.domain (wrappedFlat n) →
      (∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧
        P.toPoly.labelOf (wrappedFlat n) a = D) →
      SliceDstarGA.dstarRankGA P hV n = dstarC n) :
    ∃ (B Bh M mthr p0 N1 : ℕ)
      (S₁ F₁ K₁ : ℕ → (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → RegionSpec B) → Finset ℕ)
      (S₂ F₂ K₂ : ℕ → (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → RegionSpec Bh) → Finset ℕ),
      1 ≤ p0 ∧ B ≤ Bh ∧ M % 2 = 0 ∧ 2 * Bh + 2 ≤ N1 ∧
      (∀ κ c' rs, ∀ r ∈ S₁ κ c' rs, r < M ∧ r % 2 = 1) ∧
      (∀ κ c' rs, ∀ r ∈ S₂ κ c' rs, r < M ∧ r % 2 = 1) ∧
      (∀ κ c' rs, ∀ f ∈ F₁ κ c' rs, f % 2 = 1) ∧
      (∀ κ c' rs, ∀ f ∈ F₂ κ c' rs, f % 2 = 1) ∧
      (∀ κ c' rs, ∀ k ∈ K₁ κ c' rs, k % 2 = 0) ∧
      (∀ κ c' rs, ∀ k ∈ K₂ κ c' rs, k % 2 = 0) ∧
      ∀ n, N1 ≤ n → P.toPoly.domain (wrappedFlat n) →
        (∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧
          P.toPoly.labelOf (wrappedFlat n) a = D) →
        ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
          P.toPoly.labelOf (wrappedFlat n) b = D →
          (P.rankOf (wrappedFlat n) b = SliceDstarGA.dstarRankGA P hV n ↔
            cfgCellGA B Bh M mthr
              (S₁ (n % p0)) (F₁ (n % p0)) (K₁ (n % p0))
              (S₂ (n % p0)) (F₂ (n % p0)) (K₂ (n % p0)) n b) := by
  classical
  -- S1: setup destructure and constants
  obtain ⟨B, Ncc, hB1, hcells⟩ := SliceFamilyCell.cells_cover P C
  obtain ⟨m, p, Mc, Rcell, Bcell, PR, PBn, hp, hmB, hMc, hbwd, hwineq, hRrec, hBrec⟩ :=
    SliceDstarBridgeGA.dstar_setup_GA P B
  set A0 : ℕ := B + m with hA0def
  set tBk : ℕ := 3 * B + m + p + 2 with htBkdef
  set Bh : ℕ := tBk + B with hBhdef
  have hBB : B ≤ Bh := by omega
  have hBh1 : 1 ≤ Bh := by omega
  choose RcellH BcellH hRAH hBAH heqH using
    fun (c' : Fin P.toPoly.K) (rs' : Fin (P.toPoly.arity c') → RegionSpec Bh) =>
      SliceFamilyRank.rank_cell_decomp (B := Bh) P c' rs'
  have hBcellAff : ∀ (c' : Fin P.toPoly.K)
      (rs : Fin (P.toPoly.arity c') → RegionSpec B), RankAffine (Bcell c' rs) :=
    fun c' rs => ⟨m, p, PBn c' rs, hp, hBrec c' rs⟩
  -- S2: the two EP families against the total dstarC
  choose pBk hpBk hBkEP using
    fun (c' : Fin P.toPoly.K) (rs : Fin (P.toPoly.arity c') → RegionSpec B) (r : ℕ) =>
      SliceFasSelector.affineOnResiduesZ_vec_eq_EP
        (F := fun x => fun i => Rcell c' rs (A0 + r) i + Bcell c' rs x i)
        (G := dstarC)
        (fun i => (AffineOnResiduesZ.const (Rcell c' rs (A0 + r) i)).add
          (SliceFasBridges.rankAffine_coord_affineOnResiduesZ (hBcellAff c' rs) i))
        hCaff
  choose pFz hpFz hFzEP using
    fun (c' : Fin P.toPoly.K) (rs' : Fin (P.toPoly.arity c') → RegionSpec Bh) =>
      SliceFasSelector.affineOnResiduesZ_vec_eq_EP
        (F := fun x => fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' x i)
        (G := dstarC)
        (fun i => (AffineOnResiduesZ.const (RcellH c' rs' (Bh + 1) i)).add
          (SliceFasBridges.rankAffine_coord_affineOnResiduesZ (hBAH c' rs') i))
        hCaff
  choose NBk hNBk using fun c' rs r => hBkEP c' rs r
  choose NFz hNFz using fun c' rs' => hFzEP c' rs'
  -- S3: the common class period
  set p0 : ℕ := p * (Finset.univ.prod (fun c' : Fin P.toPoly.K =>
      Finset.univ.prod (fun rs : Fin (P.toPoly.arity c') → RegionSpec B =>
        (Finset.range p).prod (fun r => pBk c' rs r))))
    * (Finset.univ.prod (fun c' : Fin P.toPoly.K =>
      Finset.univ.prod (fun rs' : Fin (P.toPoly.arity c') → RegionSpec Bh =>
        pFz c' rs'))) with hp0def
  have hprod1 : 0 < Finset.univ.prod (fun c' : Fin P.toPoly.K =>
      Finset.univ.prod (fun rs : Fin (P.toPoly.arity c') → RegionSpec B =>
        (Finset.range p).prod (fun r => pBk c' rs r))) :=
    Finset.prod_pos (fun c' _ => Finset.prod_pos (fun rs _ =>
      Finset.prod_pos (fun r _ => hpBk c' rs r)))
  have hprod2 : 0 < Finset.univ.prod (fun c' : Fin P.toPoly.K =>
      Finset.univ.prod (fun rs' : Fin (P.toPoly.arity c') → RegionSpec Bh =>
        pFz c' rs')) :=
    Finset.prod_pos (fun c' _ => Finset.prod_pos (fun rs' _ => hpFz c' rs'))
  have hp0 : 1 ≤ p0 := by
    rw [hp0def]
    exact Nat.mul_pos (Nat.mul_pos hp hprod1) hprod2
  have hBkdvd : ∀ (c' : Fin P.toPoly.K) (rs : Fin (P.toPoly.arity c') → RegionSpec B)
      (r : ℕ), r < p → pBk c' rs r ∣ p0 := by
    intro c' rs r hr
    have h1 : pBk c' rs r ∣ (Finset.range p).prod (fun r => pBk c' rs r) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hr)
    have h2 : (Finset.range p).prod (fun r => pBk c' rs r) ∣
        Finset.univ.prod (fun rs : Fin (P.toPoly.arity c') → RegionSpec B =>
          (Finset.range p).prod (fun r => pBk c' rs r)) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ rs)
    have h3 : Finset.univ.prod (fun rs : Fin (P.toPoly.arity c') → RegionSpec B =>
        (Finset.range p).prod (fun r => pBk c' rs r)) ∣
        Finset.univ.prod (fun c' : Fin P.toPoly.K =>
          Finset.univ.prod (fun rs : Fin (P.toPoly.arity c') → RegionSpec B =>
            (Finset.range p).prod (fun r => pBk c' rs r))) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ c')
    rw [hp0def]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left ((h1.trans h2).trans h3) p) _
  have hFzdvd : ∀ (c' : Fin P.toPoly.K)
      (rs' : Fin (P.toPoly.arity c') → RegionSpec Bh), pFz c' rs' ∣ p0 := by
    intro c' rs'
    have h1 : pFz c' rs' ∣
        Finset.univ.prod (fun rs' : Fin (P.toPoly.arity c') → RegionSpec Bh =>
          pFz c' rs') :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ rs')
    have h2 : Finset.univ.prod (fun rs' : Fin (P.toPoly.arity c') → RegionSpec Bh =>
        pFz c' rs') ∣
        Finset.univ.prod (fun c' : Fin P.toPoly.K =>
          Finset.univ.prod (fun rs' : Fin (P.toPoly.arity c') → RegionSpec Bh =>
            pFz c' rs')) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ c')
    rw [hp0def]
    exact Dvd.dvd.mul_left (h1.trans h2) _
  -- S4: the threshold
  set NEP : ℕ := (Finset.univ.sup (fun c' : Fin P.toPoly.K =>
      Finset.univ.sup (fun rs : Fin (P.toPoly.arity c') → RegionSpec B =>
        (Finset.range p).sup (fun r => NBk c' rs r))))
    ⊔ (Finset.univ.sup (fun c' : Fin P.toPoly.K =>
      Finset.univ.sup (fun rs' : Fin (P.toPoly.arity c') → RegionSpec Bh =>
        NFz c' rs'))) with hNEPdef
  set N1 : ℕ := (2 * Bh + 2) + Ncc + N0 + NEP with hN1def
  have hN1geo : 2 * Bh + 2 ≤ N1 := by
    rw [hN1def]
    omega
  have hNBkLe : ∀ c' rs r, r < p → NBk c' rs r ≤ N1 := by
    intro c' rs r hr
    have h1 : NBk c' rs r ≤ (Finset.range p).sup (fun r => NBk c' rs r) :=
      Finset.le_sup (f := fun r => NBk c' rs r) (Finset.mem_range.mpr hr)
    have h2 : (Finset.range p).sup (fun r => NBk c' rs r)
        ≤ Finset.univ.sup (fun rs : Fin (P.toPoly.arity c') → RegionSpec B =>
            (Finset.range p).sup (fun r => NBk c' rs r)) :=
      Finset.le_sup (f := fun rs => (Finset.range p).sup (fun r => NBk c' rs r))
        (Finset.mem_univ rs)
    have h3 : Finset.univ.sup (fun rs : Fin (P.toPoly.arity c') → RegionSpec B =>
          (Finset.range p).sup (fun r => NBk c' rs r))
        ≤ Finset.univ.sup (fun c' : Fin P.toPoly.K =>
            Finset.univ.sup (fun rs : Fin (P.toPoly.arity c') → RegionSpec B =>
              (Finset.range p).sup (fun r => NBk c' rs r))) :=
      Finset.le_sup (f := fun c' => Finset.univ.sup
        (fun rs : Fin (P.toPoly.arity c') → RegionSpec B =>
          (Finset.range p).sup (fun r => NBk c' rs r))) (Finset.mem_univ c')
    have h4 : Finset.univ.sup (fun c' : Fin P.toPoly.K =>
        Finset.univ.sup (fun rs : Fin (P.toPoly.arity c') → RegionSpec B =>
          (Finset.range p).sup (fun r => NBk c' rs r))) ≤ NEP := by
      rw [hNEPdef]
      exact le_max_left _ _
    rw [hN1def]
    omega
  have hNFzLe : ∀ c' rs', NFz c' rs' ≤ N1 := by
    intro c' rs'
    have h1 : NFz c' rs' ≤ Finset.univ.sup
        (fun rs' : Fin (P.toPoly.arity c') → RegionSpec Bh => NFz c' rs') :=
      Finset.le_sup (f := fun rs' => NFz c' rs') (Finset.mem_univ rs')
    have h2 : Finset.univ.sup
          (fun rs' : Fin (P.toPoly.arity c') → RegionSpec Bh => NFz c' rs')
        ≤ Finset.univ.sup (fun c' : Fin P.toPoly.K =>
            Finset.univ.sup (fun rs' : Fin (P.toPoly.arity c') → RegionSpec Bh =>
              NFz c' rs')) :=
      Finset.le_sup (f := fun c' => Finset.univ.sup
        (fun rs' : Fin (P.toPoly.arity c') → RegionSpec Bh => NFz c' rs'))
        (Finset.mem_univ c')
    have h3 : Finset.univ.sup (fun c' : Fin P.toPoly.K =>
        Finset.univ.sup (fun rs' : Fin (P.toPoly.arity c') → RegionSpec Bh =>
          NFz c' rs')) ≤ NEP := by
      rw [hNEPdef]
      exact le_max_right _ _
    rw [hN1def]
    omega
  have hNccLe : Ncc ≤ N1 := by
    rw [hN1def]
    omega
  have hN0Le : N0 ≤ N1 := by
    rw [hN1def]
    omega
  -- S5: the representative, the data, the hygiene, the refine
  set rep : ℕ → ℕ := fun κ => N1 * p0 + κ with hrepdef
  set S₁ : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpec B) → Finset ℕ :=
    fun κ c' rs =>
      if (∀ i, clusterFree (rs i)) then ∅
      else ((Finset.range p).filter (fun r =>
        PR c' rs = (fun _ => 0) ∧
        (fun i => Rcell c' rs (A0 + r) i + Bcell c' rs (rep κ) i)
          = dstarC (rep κ))).image
        (fun r => (1 + 2 * (A0 + r)) % (2 * p)) with hS₁def
  set F₂ : ℕ → (c' : Fin P.toPoly.K) →
      (Fin (P.toPoly.arity c') → RegionSpec Bh) → Finset ℕ :=
    fun κ c' rs' =>
      if ((∀ i, clusterFree (rs' i)) ∧
          (fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' (rep κ) i)
            = dstarC (rep κ))
      then {2 * Bh + 3} else ∅ with hF₂def
  have hS₁hyg : ∀ κ c' rs, ∀ x ∈ S₁ κ c' rs, x < 2 * p ∧ x % 2 = 1 := by
    intro κ c' rs x hx
    rw [hS₁def] at hx
    simp only [] at hx
    split at hx
    · exact absurd hx (Finset.notMem_empty x)
    · obtain ⟨r, hrmem, rfl⟩ := Finset.mem_image.mp hx
      rw [SliceFasSelector.odd_mod_two_mul (A0 + r) p hp]
      have := Nat.mod_lt (A0 + r) hp
      omega
  have hF₂hyg : ∀ κ c' rs', ∀ f ∈ F₂ κ c' rs', f % 2 = 1 := by
    intro κ c' rs' f hf
    rw [hF₂def] at hf
    simp only [] at hf
    split at hf
    · rw [Finset.mem_singleton] at hf
      omega
    · exact absurd hf (Finset.notMem_empty f)
  refine ⟨B, Bh, 2 * p, 2 * tBk, p0, N1, S₁, (fun _ _ _ => ∅), (fun _ _ _ => ∅),
    (fun _ _ _ => ∅), F₂, (fun _ _ _ => ∅), hp0, hBB, (by omega), hN1geo, hS₁hyg,
    (fun κ c' rs x hx => absurd hx (Finset.notMem_empty x)),
    (fun κ c' rs f hf => absurd hf (Finset.notMem_empty f)),
    hF₂hyg,
    (fun κ c' rs k hk => absurd hk (Finset.notMem_empty k)),
    (fun κ c' rs k hk => absurd hk (Finset.notMem_empty k)),
    ?_⟩
  -- S6: per-n entry and class facts
  intro n hn hdom hD b hbsel hbD
  obtain ⟨c', ī⟩ := b
  have hagree : SliceDstarGA.dstarRankGA P hV n = dstarC n :=
    hCagree n (by omega) hdom hD
  have hlen : (wrappedFlat n).length = 2 * (n + 1) := length_wrappedFlat n
  set κ : ℕ := n % p0 with hκdef
  have hκlt : κ < p0 := Nat.mod_lt _ hp0
  have hrepmod : rep κ % p0 = κ := by
    rw [hrepdef]
    simp only []
    rw [Nat.mul_comm N1 p0, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hκlt
  have hrepN1 : N1 ≤ rep κ := by
    rw [hrepdef]
    simp only []
    have := Nat.le_mul_of_pos_right N1 hp0
    omega
  have hmodeq : ∀ qf, qf ∣ p0 → n % qf = rep κ % qf := by
    intro qf hqf
    have hbase : n % p0 = rep κ % p0 := by
      rw [hrepmod, hκdef]
    exact Nat.ModEq.of_dvd hqf hbase
  have hrankunfold : P.rankOf (wrappedFlat n) ⟨c', ī⟩ = P.rank c' (wrappedFlat n) ī :=
    rfl
  -- S7: the two transport bundles
  have htransBk : ∀ (rs : Fin (P.toPoly.arity c') → RegionSpec B) (r : ℕ), r < p →
      (((fun i => Rcell c' rs (A0 + r) i + Bcell c' rs n i) = dstarC n) ↔
        ((fun i => Rcell c' rs (A0 + r) i + Bcell c' rs (rep κ) i)
          = dstarC (rep κ))) :=
    fun rs r hr => SliceFasSelector.iff_on_class
      (Pr := fun x => (fun i => Rcell c' rs (A0 + r) i + Bcell c' rs x i) = dstarC x)
      (hpBk c' rs r) (hNBk c' rs r)
      (le_trans (hNBkLe c' rs r hr) hn) (le_trans (hNBkLe c' rs r hr) hrepN1)
      (hmodeq _ (hBkdvd c' rs r hr))
  have htransFz : ∀ rs' : Fin (P.toPoly.arity c') → RegionSpec Bh,
      (((fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' n i) = dstarC n) ↔
        ((fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' (rep κ) i)
          = dstarC (rep κ))) :=
    fun rs' => SliceFasSelector.iff_on_class
      (Pr := fun x =>
        (fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' x i) = dstarC x)
      (hpFz c' rs') (hNFz c' rs')
      (le_trans (hNFzLe c' rs') hn) (le_trans (hNFzLe c' rs') hrepN1)
      (hmodeq _ (hFzdvd c' rs'))
  -- S8: the shared frozen emitter
  have hnBh : 2 * Bh + 2 ≤ n := le_trans hN1geo hn
  have emitFrozen : ∀ rs' : Fin (P.toPoly.arity c') → RegionSpec Bh,
      (∀ i, clusterFree (rs' i)) → ī = cellTuple rs' (Bh + 1) n →
      P.rank c' (wrappedFlat n) ī = dstarC n →
      cfgCellArm Bh (2 * p) (2 * tBk) (fun _ _ => ∅) (F₂ κ) (fun _ _ => ∅) n
        ⟨c', ī⟩ := by
    intro rs' hcf' hcell hrk
    have hrkH : (fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' n i) = dstarC n := by
      have h1 : P.rank c' (wrappedFlat n) (cellTuple rs' (Bh + 1) n)
          = fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' n i :=
        heqH c' rs' (Bh + 1) n le_rfl (by omega)
      rw [← h1, ← hcell]
      exact hrk
    refine ⟨rs', Bh + 1, by rw [hlen]; omega, hcell, Or.inr (Or.inl ?_)⟩
    rw [hF₂def]
    simp only []
    rw [if_pos ⟨hcf', (htransFz rs').mp hrkH⟩,
      show 1 + 2 * (Bh + 1) = 2 * Bh + 3 from by omega]
    exact Finset.mem_singleton_self _
  constructor
  · -- S9: (→) cover, cluster-free short-circuit, zone split
    intro hrank
    have hrkC : P.rank c' (wrappedFlat n) ī = dstarC n := by
      rw [← hrankunfold, hrank, hagree]
    obtain ⟨t, htB, htn, hper⟩ := hcells n (by omega) c' ī hbsel (hbud n hdom c')
    choose rs hrs using hper
    have hcell : ī = cellTuple rs t n := funext hrs
    by_cases hcf : ∀ i, clusterFree (rs i)
    · -- cluster-free: lift to Bh and freeze at the dummy base
      set rs' := fun i => regionLift hBB (rs i) with hrs'def
      have hcf' : ∀ i, clusterFree (rs' i) :=
        fun i => (clusterFree_regionLift hBB _).mpr (hcf i)
      have hch : ī = cellTuple rs' (Bh + 1) n := by
        rw [hcell, ← cellTuple_regionLift hBB rs t n]
        exact SliceDstarBridgeGA.cellTuple_clusterFree_base rs' hcf' t (Bh + 1) n
      exact Or.inr (emitFrozen rs' hcf' hch hrkC)
    · rcases Nat.lt_or_ge t tBk with hfront | htlow
      · -- front zone
        obtain ⟨rs', hcf', heq'⟩ := freeze_front_descr hBB rs t n (by omega)
        exact Or.inr (emitFrozen rs' hcf' (hcell.trans heq') hrkC)
      rcases Nat.lt_or_ge n (t + tBk) with hback | hbulk
      · -- back zone
        obtain ⟨rs', hcf', heq'⟩ := freeze_back_descr hBB hBh1 rs t n (by omega) htn
        exact Or.inr (emitFrozen rs' hcf' (hcell.trans heq') hrkC)
      -- S10/S11: deep bulk
      set r := (t - A0) % p with hrdef
      set kk := (t - A0) / p with hkkdef
      have hr : r < p := by
        rw [hrdef]
        exact Nat.mod_lt _ hp
      have hteq : t = A0 + r + p * kk := by
        rw [hrdef, hkkdef]
        have := Nat.mod_add_div (t - A0) p
        omega
      have hchainval : ∀ k, Rcell c' rs (A0 + r + p * k)
          = Rcell c' rs (A0 + r) + k • PR c' rs :=
        fun k => RankAffine.iterate (fun j hj => hRrec c' rs j hj) (A0 + r) k (by omega)
      by_cases hcol : PR c' rs = (fun _ => 0)
      · -- S10: collinear — emit the bulk residue
        have hchain0 : Rcell c' rs t = Rcell c' rs (A0 + r) := by
          conv_lhs => rw [hteq]
          rw [hchainval kk, hcol]
          funext i
          simp
        have hpredn : (fun i => Rcell c' rs (A0 + r) i + Bcell c' rs n i)
            = dstarC n := by
          rw [← hchain0, ← hwineq c' rs t n (by omega) (by omega), ← hcell]
          exact hrkC
        refine Or.inl ⟨rs, t, by rw [hlen]; omega, hcell,
          Or.inl ⟨by omega, by rw [hlen]; omega, ?_⟩⟩
        rw [hS₁def]
        simp only []
        rw [if_neg hcf]
        refine Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hr, hcol, (htransBk rs r hr).mp hpredn⟩, ?_⟩
        exact ((base_mod_iff A0 p t r hp hr (by omega)).mpr hrdef.symm).symm
      · -- S11: Case-A — both chain endpoints beat the interior member
        exfalso
        have hmc : kk * p = p * kk := Nat.mul_comm kk p
        have hkk1 : 1 ≤ kk := by
          rw [hkkdef, Nat.le_div_iff_mul_le hp]
          omega
        set tl := (n - 3 * B - m - (A0 + r)) / p with htldef
        set jl := A0 + r + p * tl with hjldef
        have hjlub : jl + 3 * B + m ≤ n := by
          rw [hjldef]
          have h1 : p * tl ≤ n - 3 * B - m - (A0 + r) := by
            rw [htldef, Nat.mul_comm]
            exact Nat.div_mul_le_self _ _
          omega
        have hkktl : kk < tl := by
          have hstep : kk + 1 ≤ tl := by
            rw [htldef, Nat.le_div_iff_mul_le hp, Nat.add_mul, Nat.one_mul]
            omega
          omega
        -- selectedness travels along the chain
        have hval_t := SliceDstarGateGA.cellTuple_valid rs t n (by omega)
        have hacc_t : (Mc c').accepts (MSOMarkN.markAtN (P.toPoly.arity c')
            (wrappedFlat n) (cellTuple rs t n)) := by
          refine (hMc c' (wrappedFlat n) _ hval_t).mpr ⟨?_, ?_⟩
          · rw [← hcell]
            exact hbsel.2
          · rw [← hcell]
            exact hbD
        have htr_left := SliceDstarGA.cell_base_transport_left (Mc c') m p (hbwd c')
          rs t n kk (by omega) (by omega) (by omega)
        have hsub : t - kk * p = A0 + r := by omega
        rw [hsub] at htr_left
        have hacc_a := htr_left.mpr hacc_t
        have hmc2 : tl * p = p * tl := Nat.mul_comm tl p
        have htr_right := SliceDstarGA.cell_base_transport_right (Mc c') m p (hbwd c')
          rs (A0 + r) n tl (by omega) (by omega) (by omega)
        have hacc_jl := htr_right.mpr hacc_a
        have hbd : A0 + r + tl * p = jl := by
          rw [hjldef]
          omega
        rw [hbd] at hacc_jl
        have hval_a := SliceDstarGateGA.cellTuple_valid rs (A0 + r) n (by omega)
        have hsl_a := (hMc c' (wrappedFlat n) _ hval_a).mp hacc_a
        have hval_jl := SliceDstarGateGA.cellTuple_valid rs jl n (by omega)
        have hsl_jl := (hMc c' (wrappedFlat n) _ hval_jl).mp hacc_jl
        -- the chain value of dstarC at the interior member
        have hDRn : dstarC n = fun i =>
            (Rcell c' rs (A0 + r) i + Bcell c' rs n i) + (kk : ℤ) * PR c' rs i := by
          have h1 : P.rank c' (wrappedFlat n) ī
              = fun i => Rcell c' rs t i + Bcell c' rs n i := by
            rw [hcell]
            exact hwineq c' rs t n (by omega) (by omega)
          rw [← hrkC, h1]
          funext i
          have h2i := congrFun (hchainval kk) i
          rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at h2i
          rw [show t = A0 + r + p * kk from hteq, h2i]
          ring
        rcases SliceFasSelector.chain_min_endpoint
          (fun i => Rcell c' rs (A0 + r) i + Bcell c' rs n i) (PR c' rs)
          kk tl hkk1 hkktl hcol with hfirst | hlast
        · -- the first member lex-precedes the interior one
          refine dstarRankGA_lex_min P hV n hD ⟨c', cellTuple rs (A0 + r) n⟩
            ⟨hval_a, hsl_a.1⟩ hsl_a.2 ?_
          have hrk_a : P.rankOf (wrappedFlat n) ⟨c', cellTuple rs (A0 + r) n⟩
              = fun i => Rcell c' rs (A0 + r) i + Bcell c' rs n i :=
            hwineq c' rs (A0 + r) n (by omega) (by omega)
          rw [hrk_a, hagree, hDRn]
          exact hfirst
        · -- the last member lex-precedes the interior one
          refine dstarRankGA_lex_min P hV n hD ⟨c', cellTuple rs jl n⟩
            ⟨hval_jl, hsl_jl.1⟩ hsl_jl.2 ?_
          have hrk_jl : P.rankOf (wrappedFlat n) ⟨c', cellTuple rs jl n⟩
              = fun i => Rcell c' rs jl i + Bcell c' rs n i :=
            hwineq c' rs jl n (by omega) (by omega)
          have hjl_chain : (fun i => Rcell c' rs jl i + Bcell c' rs n i)
              = fun i => (Rcell c' rs (A0 + r) i + Bcell c' rs n i)
                + (tl : ℤ) * PR c' rs i := by
            funext i
            have h2i := congrFun (hchainval tl) i
            rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at h2i
            rw [show jl = A0 + r + p * tl from hjldef, h2i]
            ring
          rw [hrk_jl, hjl_chain, hagree, hDRn]
          exact hlast
  · -- S12/S13: (←) the two arms decode back to the rank equation
    rintro (⟨rs, t, hzlt, hcell, hcfg⟩ | ⟨rs', t', hzlt, hcell, hcfg⟩)
    · -- S12: the bulk arm
      rcases hcfg with ⟨hge, hltw, hres⟩ | hf | ⟨k, hk, _⟩
      · have htlow : tBk ≤ t := by omega
        have htup : t + tBk ≤ n := by
          rw [hlen] at hltw
          omega
        rw [hS₁def] at hres
        simp only [] at hres
        by_cases hcf : ∀ i, clusterFree (rs i)
        · rw [if_pos hcf] at hres
          exact absurd hres (Finset.notMem_empty _)
        · rw [if_neg hcf] at hres
          obtain ⟨r, hrmem, hrimg⟩ := Finset.mem_image.mp hres
          obtain ⟨hrR, hcol, hvalrep⟩ := Finset.mem_filter.mp hrmem
          have hr : r < p := Finset.mem_range.mp hrR
          have hmod : (t - A0) % p = r :=
            (base_mod_iff A0 p t r hp hr (by omega)).mp hrimg.symm
          have hteq : t = A0 + r + p * ((t - A0) / p) := by
            have := Nat.mod_add_div (t - A0) p
            omega
          have hchainval : ∀ k, Rcell c' rs (A0 + r + p * k)
              = Rcell c' rs (A0 + r) + k • PR c' rs :=
            fun k => RankAffine.iterate (fun j hj => hRrec c' rs j hj) (A0 + r) k
              (by omega)
          have hchain0 : Rcell c' rs t = Rcell c' rs (A0 + r) := by
            conv_lhs => rw [hteq]
            rw [hchainval ((t - A0) / p), hcol]
            funext i
            simp
          have hcell' : ī = cellTuple rs t n := hcell
          have hfin : P.rank c' (wrappedFlat n) ī = dstarC n := by
            rw [hcell', hwineq c' rs t n (by omega) (by omega), hchain0]
            exact (htransBk rs r hr).mpr hvalrep
          rw [hrankunfold, hagree]
          exact hfin
      · exact absurd hf (Finset.notMem_empty _)
      · exact absurd hk (Finset.notMem_empty _)
    · -- S13: the frozen arm
      rcases hcfg with ⟨_, _, hres⟩ | hf | ⟨k, hk, _⟩
      · exact absurd hres (Finset.notMem_empty _)
      · rw [hF₂def] at hf
        simp only [] at hf
        by_cases hcond : (∀ i, clusterFree (rs' i)) ∧
            ((fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' (rep κ) i)
              = dstarC (rep κ))
        · rw [if_pos hcond] at hf
          have ht' : 1 + 2 * t' = 2 * Bh + 3 := Finset.mem_singleton.mp hf
          have ht'eq : t' = Bh + 1 := by omega
          subst ht'eq
          have hcell' : ī = cellTuple rs' (Bh + 1) n := hcell
          have hfin : P.rank c' (wrappedFlat n) ī = dstarC n := by
            rw [hcell']
            have h1 : P.rank c' (wrappedFlat n) (cellTuple rs' (Bh + 1) n)
                = fun i => RcellH c' rs' (Bh + 1) i + BcellH c' rs' n i :=
              heqH c' rs' (Bh + 1) n le_rfl (by omega)
            rw [h1]
            exact (htransFz rs').mpr hcond.2
          rw [hrankunfold, hagree]
          exact hfin
        · rw [if_neg hcond] at hf
          exact absurd hf (Finset.notMem_empty _)
      · exact absurd hk (Finset.notMem_empty _)

/-- **The self-contained selector** (GA-6.3f): the zero-shim wrapper destructuring the
GA-5 monolith. -/
theorem eqRankD_cell_selector' (P : WRP.Presentation Step Step) (hV : P.Valid) (C : ℕ)
    (hbud : ∀ n, P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) :
    ∃ (B Bh M mthr p0 N1 : ℕ)
      (S₁ F₁ K₁ : ℕ → (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → RegionSpec B) → Finset ℕ)
      (S₂ F₂ K₂ : ℕ → (c' : Fin P.toPoly.K) →
        (Fin (P.toPoly.arity c') → RegionSpec Bh) → Finset ℕ),
      1 ≤ p0 ∧ B ≤ Bh ∧ M % 2 = 0 ∧ 2 * Bh + 2 ≤ N1 ∧
      (∀ κ c' rs, ∀ r ∈ S₁ κ c' rs, r < M ∧ r % 2 = 1) ∧
      (∀ κ c' rs, ∀ r ∈ S₂ κ c' rs, r < M ∧ r % 2 = 1) ∧
      (∀ κ c' rs, ∀ f ∈ F₁ κ c' rs, f % 2 = 1) ∧
      (∀ κ c' rs, ∀ f ∈ F₂ κ c' rs, f % 2 = 1) ∧
      (∀ κ c' rs, ∀ k ∈ K₁ κ c' rs, k % 2 = 0) ∧
      (∀ κ c' rs, ∀ k ∈ K₂ κ c' rs, k % 2 = 0) ∧
      ∀ n, N1 ≤ n → P.toPoly.domain (wrappedFlat n) →
        (∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧
          P.toPoly.labelOf (wrappedFlat n) a = D) →
        ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
          P.toPoly.labelOf (wrappedFlat n) b = D →
          (P.rankOf (wrappedFlat n) b = SliceDstarGA.dstarRankGA P hV n ↔
            cfgCellGA B Bh M mthr
              (S₁ (n % p0)) (F₁ (n % p0)) (K₁ (n % p0))
              (S₂ (n % p0)) (F₂ (n % p0)) (K₂ (n % p0)) n b) := by
  obtain ⟨dstarC, N0, hCaff, hCagree⟩ := SliceDstarBridgeGA.dstarC_exists_GA P hV C hbud
  exact eqRankD_cell_selector P hV C hbud dstarC N0 hCaff hCagree

/-! ## GA-6.4: the TIE point bridge -/

/-- **The TIE point bridge** (GA-6.4, the standalone `hpoint` twin): per-class marked
DFAs `Gdfa` such that on in-domain `D`-present slices past the threshold, the semantic
TIE condition at any valid tuple — selected, labelled `U`, of `d*`-rank, and
`atomOrd`-below every equal-rank selected `D`-atom — is the DFA acceptance conjoined
with the rank equality.  This is the exact shape GA-7's counting assembly consumes. -/
theorem tie_point_bridge_GA (P : WRP.Presentation Step Step) (hV : P.Valid) (C : ℕ)
    (hbud : ∀ n, P.toPoly.domain (wrappedFlat n) →
      ∀ (c : Fin P.toPoly.K) (l : List (Fin (P.toPoly.arity c) → ℕ)), l.Nodup →
        (∀ x ∈ l, P.toPoly.selectedAtom (wrappedFlat n) ⟨c, x⟩) →
        l.length ≤ C * (n + 1)) :
    ∃ (p0 N : ℕ) (Gdfa : ℕ → (c : Fin P.toPoly.K) →
        SliceMSO.DetAuto (MSOMarkN.MarkedN (P.toPoly.arity c))), 1 ≤ p0 ∧
      ∀ n, N ≤ n → P.toPoly.domain (wrappedFlat n) →
        (∃ a, P.toPoly.selectedAtom (wrappedFlat n) a ∧
          P.toPoly.labelOf (wrappedFlat n) a = D) →
        ∀ (c : Fin P.toPoly.K) (ī : Fin (P.toPoly.arity c) → ℕ),
          (∀ i, ī i < (wrappedFlat n).length) →
          ((P.toPoly.sel c (wrappedFlat n) ī
            ∧ P.toPoly.labelOf (wrappedFlat n) ⟨c, ī⟩ = U
            ∧ P.rankOf (wrappedFlat n) ⟨c, ī⟩ = SliceDstarGA.dstarRankGA P hV n
            ∧ ∀ b : P.toPoly.Atom, P.toPoly.selectedAtom (wrappedFlat n) b →
                P.toPoly.labelOf (wrappedFlat n) b = D →
                P.rankOf (wrappedFlat n) b = SliceDstarGA.dstarRankGA P hV n →
                P.toPoly.atomOrd (wrappedFlat n) ⟨c, ī⟩ b)
           ↔ ((Gdfa (n % p0) c).accepts
                (MSOMarkN.markAtN (P.toPoly.arity c) (wrappedFlat n) ī)
              ∧ P.rank c (wrappedFlat n) ī = SliceDstarGA.dstarRankGA P hV n)) := by
  classical
  obtain ⟨B, Bh, M, mthr, p0, N1, S₁, F₁, K₁, S₂, F₂, K₂, hp0, hBB, hM2, hN1geo,
    hS₁, hS₂, hF₁, hF₂, hK₁, hK₂, hsel⟩ := eqRankD_cell_selector' P hV C hbud
  choose Gdfa hGdfa using fun (κ : ℕ) (c : Fin P.toPoly.K) =>
    fasU_atomOrd_cellCfg_gate P c B Bh M mthr (S₁ κ) (F₁ κ) (K₁ κ)
      (S₂ κ) (F₂ κ) (K₂ κ) hBB hM2 (hS₁ κ) (hS₂ κ) (hF₁ κ) (hF₂ κ) (hK₁ κ) (hK₂ κ)
  refine ⟨p0, N1, Gdfa, hp0, ?_⟩
  intro n hn hdom hD c ī hval
  rw [← hGdfa (n % p0) c n ī (by omega) hval]
  constructor
  · rintro ⟨hs, hl, hr, hall⟩
    refine ⟨⟨hs, hl, ?_⟩, hr⟩
    intro b hbsel hbD hbcfg
    exact hall b hbsel hbD ((hsel n hn hdom hD b hbsel hbD).mpr hbcfg)
  · rintro ⟨⟨hs, hl, hall⟩, hr⟩
    refine ⟨hs, hl, hr, ?_⟩
    intro b hbsel hbD hbr
    exact hall b hbsel hbD ((hsel n hn hdom hD b hbsel hbD).mp hbr)

end SliceFasSelectorGA
