/-
# `lem:presburger-counting` in one fibre variable

For a semilinear `S ⊆ ℕ^p × ℕ` whose parameter-fibres are finite and of size at most
`C · (‖x‖_∞ + 1)`, the count graph `{(x, |S_x|)} ⊆ ℕ^(p+1)` is semilinear.

The route is a decomposition into proper linear pieces followed by a residue-class refinement.
By `KernelDichotomy` each fibre of a proper piece is an arithmetic progression whose step does
not depend on the parameter; in one fibre variable this reads as a *natural* progression
`{a + j·E : j < l}` with a fixed positive `E` (`exists_step_progression`).  Taking `D` to be a
common multiple of the finitely many steps and cutting along the `D` residue classes turns each
piece into a *`D`-progression*: a set of naturals in which, between any two members,
membership is exactly divisibility of the offset by `D` (`IsDProg`).  Such a set has
`(max − min)/D + 1` elements, and its minimum and maximum are Presburger-definable, so its
count graph is semilinear (`isSemilinearSet_countGraph_of_isDProg`).

`D`-progressions are closed under intersection, so the count graph of a union of pieces inside
one residue class is reached from the two-set identity `|B ∪ C| + |B ∩ C| = |B| + |C|` by
induction on the number of pieces (`isSemilinearSet_countGraph_biUnion`), using the signed
graph arithmetic of `SemilinearGraphArith`.  Summing the `D` residue classes finishes.

## Main results

* `isSemilinearSet_countGraph_dim_one`: the count graph of a semilinear `S ⊆ ℕ^p × ℕ` with
  finite, linearly bounded fibres is semilinear.
* `count_graph_dim_one`: the same statement in the relational packaging of
  `PresburgerCounting.count_graph_semilinear` at `q = 1`.

All statements are unconditional; no counting input is admitted.
-/
import RequestProject.SemilinearMinMax
import RequestProject.KernelDichotomy
import RequestProject.SemilinearGraphArith
import RequestProject.ProperPieceCount

namespace CountBaseCase

open Set FirstOrder Language

/-! ## Fibres as sets of naturals -/

/-- The fibre of `A ⊆ ℕ^p × ℕ` over the parameter `x`, read as a set of naturals. -/
def fib {p : ℕ} (A : Set (Fin p ⊕ Fin 1 → ℕ)) (x : Fin p → ℕ) : Set ℕ :=
  {n : ℕ | Sum.elim x (fun _ => n) ∈ A}

@[simp] theorem mem_fib {p : ℕ} {A : Set (Fin p ⊕ Fin 1 → ℕ)} {x : Fin p → ℕ} {n : ℕ} :
    n ∈ fib A x ↔ Sum.elim x (fun _ => n) ∈ A := Iff.rfl

/-- The tuple fibre and the natural-number fibre are in bijection. -/
def fibEquiv {p : ℕ} (A : Set (Fin p ⊕ Fin 1 → ℕ)) (x : Fin p → ℕ) :
    {y : Fin 1 → ℕ | Sum.elim x y ∈ A} ≃ fib A x where
  toFun y := ⟨y.1 0, by
    have h : (fun _ : Fin 1 => y.1 0) = y.1 := by funext i; fin_cases i; rfl
    show Sum.elim x (fun _ => y.1 0) ∈ A
    rw [h]; exact y.2⟩
  invFun n := ⟨fun _ => n.1, n.2⟩
  left_inv y := Subtype.ext (by funext i; fin_cases i; rfl)
  right_inv _ := rfl

theorem card_tupleFibre {p : ℕ} (A : Set (Fin p ⊕ Fin 1 → ℕ)) (x : Fin p → ℕ) :
    Nat.card {y : Fin 1 → ℕ | Sum.elim x y ∈ A} = (fib A x).ncard :=
  Nat.card_congr (fibEquiv A x)

theorem finite_fib {p : ℕ} {A : Set (Fin p ⊕ Fin 1 → ℕ)} {x : Fin p → ℕ}
    (h : Set.Finite {y : Fin 1 → ℕ | Sum.elim x y ∈ A}) : (fib A x).Finite := by
  have h' := h.to_subtype
  have : Finite (fib A x) := Finite.of_equiv _ (fibEquiv A x)
  exact Set.toFinite _

theorem finite_tupleFibre {p : ℕ} {A : Set (Fin p ⊕ Fin 1 → ℕ)} {x : Fin p → ℕ}
    (h : (fib A x).Finite) : Set.Finite {y : Fin 1 → ℕ | Sum.elim x y ∈ A} := by
  have h' := h.to_subtype
  have : Finite {y : Fin 1 → ℕ | Sum.elim x y ∈ A} := Finite.of_equiv _ (fibEquiv A x).symm
  exact Set.toFinite _

theorem fib_mono {p : ℕ} {A B : Set (Fin p ⊕ Fin 1 → ℕ)} (h : A ⊆ B) (x : Fin p → ℕ) :
    fib A x ⊆ fib B x := fun _ hn => h hn

theorem finite_fib_biUnion {p : ℕ} {ι : Type*} {A : ι → Set (Fin p ⊕ Fin 1 → ℕ)} (s : Finset ι)
    (hfin : ∀ (i : ι) (x : Fin p → ℕ), (fib (A i) x).Finite) (x : Fin p → ℕ) :
    (fib (⋃ i ∈ s, A i) x).Finite := by
  have h : fib (⋃ i ∈ s, A i) x = ⋃ i ∈ (s : Set ι), fib (A i) x := by
    ext n; simp [fib]
  rw [h]
  exact Set.Finite.biUnion s.finite_toSet (fun i _ => hfin i x)

/-! ## From an integer progression to a natural progression -/

/-- A set of naturals cut out as `{b + j·d : j < len}` inside `ℤ`, with every index realised,
is `{a + j·E : j < l}` for natural data, as soon as `E` is `|d|` (or anything at all when
`d = 0`). -/
private theorem exists_natProg {b d : ℤ} {E len : ℕ} {F : Set ℕ}
    (hE : d = 0 ∨ (E : ℤ) = d ∨ (E : ℤ) = -d)
    (hiff : ∀ n : ℕ, n ∈ F ↔ ∃ j : ℕ, j < len ∧ (n : ℤ) = b + j * d)
    (hreal : ∀ j : ℕ, j < len → ∃ n : ℕ, (n : ℤ) = b + j * d) :
    ∃ a l : ℕ, ∀ n : ℕ, n ∈ F ↔ ∃ j : ℕ, j < l ∧ n = a + j * E := by
  rcases Nat.eq_zero_or_pos len with hlen | hlen
  · refine ⟨0, 0, fun n => ?_⟩
    rw [hiff n]
    constructor
    · rintro ⟨j, hj, -⟩; omega
    · rintro ⟨j, hj, -⟩; omega
  obtain ⟨n₀, hn₀⟩ := hreal 0 hlen
  simp only [Nat.cast_zero, zero_mul, add_zero] at hn₀
  rcases hE with hd | hE
  · -- `d = 0`: the fibre is the single point `n₀`.
    refine ⟨n₀, 1, fun n => ?_⟩
    rw [hiff n]
    constructor
    · rintro ⟨j, -, hn⟩
      refine ⟨0, Nat.zero_lt_one, ?_⟩
      rw [hd, mul_zero, add_zero] at hn
      simp only [zero_mul, add_zero]
      omega
    · rintro ⟨j, hj, hn⟩
      refine ⟨0, hlen, ?_⟩
      have hj0 : j = 0 := by omega
      subst hj0
      simp only [Nat.cast_zero, zero_mul, add_zero] at hn ⊢
      omega
  rcases hE with hEd | hEd
  · -- `E = d`
    refine ⟨n₀, len, fun n => ?_⟩
    rw [hiff n]
    constructor
    · rintro ⟨j, hj, hn⟩
      refine ⟨j, hj, ?_⟩
      have h : (n : ℤ) = (n₀ : ℤ) + (j : ℤ) * (E : ℤ) := by rw [hn, hn₀, hEd]
      exact_mod_cast h
    · rintro ⟨j, hj, hn⟩
      refine ⟨j, hj, ?_⟩
      have h : (n : ℤ) = (n₀ : ℤ) + (j : ℤ) * (E : ℤ) := by exact_mod_cast congrArg Nat.cast hn
      rw [h, hn₀, hEd]
  · -- `E = -d`: the progression runs downwards, so read it from its far end.
    obtain ⟨a, ha⟩ := hreal (len - 1) (by omega)
    refine ⟨a, len, fun n => ?_⟩
    rw [hiff n]
    constructor
    · rintro ⟨j, hj, hn⟩
      refine ⟨len - 1 - j, by omega, ?_⟩
      have hc : ((len - 1 - j : ℕ) : ℤ) = ((len - 1 : ℕ) : ℤ) - (j : ℤ) := by omega
      have h : (n : ℤ) = (a : ℤ) + ((len - 1 - j : ℕ) : ℤ) * (E : ℤ) := by
        rw [hn, ha, hEd, hc]; ring
      exact_mod_cast h
    · rintro ⟨i, hi, hn⟩
      refine ⟨len - 1 - i, by omega, ?_⟩
      have hc : ((len - 1 - i : ℕ) : ℤ) = ((len - 1 : ℕ) : ℤ) - (i : ℤ) := by omega
      have h : (n : ℤ) = (a : ℤ) + (i : ℤ) * (E : ℤ) := by exact_mod_cast congrArg Nat.cast hn
      rw [h, ha, hEd, hc]; ring

/-- **Fibres of a one-variable proper linear piece are natural progressions with a fixed
positive step.**  For a proper linear `L ⊆ ℕ^p × ℕ` with finite parameter-fibres of size at
most `C · (‖x‖_∞ + 1)`, one positive step `E` serves every fibre: the fibre over `x` is
`{a + j·E : j < l}` for some `a` and `l` depending on `x`. -/
theorem exists_step_progression {p : ℕ} {L : Set (Fin p ⊕ Fin 1 → ℕ)}
    (hL : IsProperLinearSet L)
    (hfin : ∀ x : Fin p → ℕ, Set.Finite {y : Fin 1 → ℕ | Sum.elim x y ∈ L})
    (C : ℕ)
    (hbd : ∀ x : Fin p → ℕ,
      Nat.card {y : Fin 1 → ℕ | Sum.elim x y ∈ L} ≤ C * (Finset.univ.sup x + 1)) :
    ∃ E : ℕ, 0 < E ∧ ∀ x : Fin p → ℕ, ∃ a l : ℕ,
      ∀ n : ℕ, n ∈ fib L x ↔ ∃ j : ℕ, j < l ∧ n = a + j * E := by
  classical
  obtain ⟨δ, hprog⟩ := KernelDichotomy.properLinear_fibre_progression hL hfin (C := C) hbd
  obtain ⟨E, hEpos, hEcase⟩ :
      ∃ E : ℕ, 0 < E ∧ (δ 0 = 0 ∨ (E : ℤ) = δ 0 ∨ (E : ℤ) = -δ 0) := by
    by_cases h : δ 0 = 0
    · exact ⟨1, Nat.one_pos, Or.inl h⟩
    · exact ⟨(δ 0).natAbs, by omega, Or.inr (by omega)⟩
  refine ⟨E, hEpos, fun x => ?_⟩
  obtain ⟨y₀, len, hiff, hreal, -⟩ := hprog x
  refine exists_natProg (b := ((y₀ 0 : ℕ) : ℤ)) (d := δ 0) (len := len) hEcase ?_ ?_
  · intro n
    rw [mem_fib, hiff (fun _ => n)]
    simp [Fin.forall_fin_one]
  · intro j hj
    obtain ⟨y, hy⟩ := hreal j hj
    exact ⟨y 0, by simpa using hy 0⟩

/-! ## Progressions of a fixed step -/

/-- `F ⊆ ℕ` is a `D`-progression: between two of its elements, membership is exactly
divisibility of the offset by `D`. -/
def IsDProg (D : ℕ) (F : Set ℕ) : Prop :=
  ∀ n m k : ℕ, n ∈ F → m ∈ F → n ≤ k → k ≤ m → ((∃ t : ℕ, k = n + D * t) ↔ k ∈ F)

theorem IsDProg.inter {D : ℕ} {F G : Set ℕ} (hF : IsDProg D F) (hG : IsDProg D G) :
    IsDProg D (F ∩ G) := fun n m k hn hm h1 h2 =>
  ⟨fun ht => ⟨(hF n m k hn.1 hm.1 h1 h2).1 ht, (hG n m k hn.2 hm.2 h1 h2).1 ht⟩,
    fun hk => (hF n m k hn.1 hm.1 h1 h2).2 hk.1⟩

private theorem isDProg_inter_biInter {D : ℕ} {ι : Type} [DecidableEq ι] {F : ι → Set ℕ}
    (T : Finset ι) :
    (∀ i ∈ T, IsDProg D (F i)) → ∀ G : Set ℕ, IsDProg D G → IsDProg D (G ∩ ⋂ i ∈ T, F i) := by
  classical
  induction T using Finset.induction with
  | empty => intro _ G hG; simpa using hG
  | @insert a T' ha ih =>
    intro hF G hG
    have hstep := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)) (G ∩ F a)
      (hG.inter (hF a (Finset.mem_insert_self a T')))
    have hset : G ∩ ⋂ i ∈ insert a T', F i = (G ∩ F a) ∩ ⋂ i ∈ T', F i := by
      ext n
      simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_insert]
      constructor
      · rintro ⟨hg, hi⟩
        exact ⟨⟨hg, hi a (Or.inl rfl)⟩, fun i hiT => hi i (Or.inr hiT)⟩
      · rintro ⟨⟨hg, hga⟩, hi⟩
        refine ⟨hg, fun i hiT => ?_⟩
        rcases hiT with rfl | hiT
        · exact hga
        · exact hi i hiT
    rw [hset]
    exact hstep

/-- A nonempty finite intersection of `D`-progressions is a `D`-progression. -/
theorem isDProg_biInter {D : ℕ} {ι : Type} [DecidableEq ι] {F : ι → Set ℕ} (T : Finset ι)
    (hT : T.Nonempty) (hF : ∀ i ∈ T, IsDProg D (F i)) : IsDProg D (⋂ i ∈ T, F i) := by
  obtain ⟨i₀, hi₀⟩ := hT
  have hset : (⋂ i ∈ T, F i) = F i₀ ∩ ⋂ i ∈ T, F i := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨h i₀ hi₀, h⟩, fun h => h.2⟩
  rw [hset]
  exact isDProg_inter_biInter T hF _ (hF i₀ hi₀)

private theorem exists_isLeast_isGreatest {F : Set ℕ} (hfin : F.Finite) (hne : F.Nonempty) :
    ∃ mn mx : ℕ, IsLeast F mn ∧ IsGreatest F mx := by
  classical
  have hfne : hfin.toFinset.Nonempty := by
    obtain ⟨n, hn⟩ := hne; exact ⟨n, hfin.mem_toFinset.2 hn⟩
  exact ⟨hfin.toFinset.min' hfne, hfin.toFinset.max' hfne,
    ⟨hfin.mem_toFinset.1 (Finset.min'_mem _ _),
      fun b hb => Finset.min'_le _ b (hfin.mem_toFinset.2 hb)⟩,
    ⟨hfin.mem_toFinset.1 (Finset.max'_mem _ _),
      fun b hb => Finset.le_max' _ b (hfin.mem_toFinset.2 hb)⟩⟩

/-- **Counting a progression of step `D`.**  A `D`-progression with least element `mn` and
greatest element `mx` has `(mx - mn)/D + 1` elements. -/
theorem ncard_of_isDProg {D : ℕ} (hD : 0 < D) {F : Set ℕ}
    {mn mx : ℕ} (hmn : IsLeast F mn) (hmx : IsGreatest F mx) (hF : IsDProg D F) :
    D * F.ncard + mn = D + mx := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, mx = mn + D * M :=
    (hF mn mx mx hmn.1 hmx.1 (hmn.2 hmx.1) le_rfl).2 hmx.1
  have hmem : ∀ j : ℕ, j ≤ M → mn + D * j ∈ F := by
    intro j hj
    refine (hF mn mx (mn + D * j) hmn.1 hmx.1 (Nat.le_add_right _ _) ?_).1 ⟨j, rfl⟩
    rw [hM]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left D hj) mn
  have hsurj : ∀ k ∈ F, ∃ j : ℕ, j ≤ M ∧ k = mn + D * j := by
    intro k hk
    obtain ⟨t, ht⟩ := (hF mn mx k hmn.1 hmx.1 (hmn.2 hk) (hmx.2 hk)).2 hk
    refine ⟨t, ?_, ht⟩
    have hle : D * t ≤ D * M := by
      have h := hmx.2 hk
      rw [ht, hM] at h
      exact Nat.le_of_add_le_add_left h
    exact Nat.le_of_mul_le_mul_left hle hD
  have hbij : Function.Bijective
      (fun j : Fin (M + 1) => (⟨mn + D * j.1, hmem j.1 (Nat.lt_succ_iff.1 j.2)⟩ : F)) := by
    constructor
    · intro j₁ j₂ h
      have hv : mn + D * j₁.1 = mn + D * j₂.1 := congrArg Subtype.val h
      exact Fin.ext (Nat.eq_of_mul_eq_mul_left hD (Nat.add_left_cancel hv))
    · rintro ⟨k, hk⟩
      obtain ⟨j, hj, hkj⟩ := hsurj k hk
      exact ⟨⟨j, by omega⟩, Subtype.ext hkj.symm⟩
  have hcard : F.ncard = M + 1 := by
    have h := Nat.card_eq_of_bijective _ hbij
    simpa [Nat.card_coe_set_eq] using h.symm
  rw [hcard, hM]
  ring

/-! ## Presburger atoms -/

private theorem isSemilinearSet_eq3 (D : ℕ) :
    IsSemilinearSet {v : Fin 3 → ℕ | D * v 0 + v 1 = D + v 2} := by
  have h := SemilinearGraphArith.isSemilinearSet_affine_eq (γ := Fin 3) 0 D ![D, 1, 0] ![0, 0, 1]
  convert h using 1
  ext v
  simp [Fin.sum_univ_three]

private theorem definable_eq3 {A : Set ℕ} {γ : Type} [Finite γ] (a b c : γ) (D : ℕ) :
    A.Definable presburger {g : γ → ℕ | D * g a + g b = D + g c} := by
  have h := ((isSemilinearSet_eq3 D).definable (A := A)).preimage_comp (![a, b, c] : Fin 3 → γ)
  convert h using 1
  ext g
  simp

private theorem isSemilinearSet_res2 (D ρ : ℕ) :
    IsSemilinearSet {v : Fin 2 → ℕ | v 0 = ρ + D * v 1} := by
  have h := SemilinearGraphArith.isSemilinearSet_affine_eq (γ := Fin 2) 0 ρ ![1, 0] ![0, D]
  convert h using 1
  ext v
  simp [Fin.sum_univ_two]

/-- Semilinear sets over a finite index type are closed under finite intersections. -/
theorem isSemilinearSet_biInter_finset {γ : Type} [Finite γ] {ι : Type*}
    {t : ι → Set (γ → ℕ)} (s : Finset ι) (ht : ∀ i, IsSemilinearSet (t i)) :
    IsSemilinearSet (⋂ i ∈ s, t i) := by
  rw [← presburger.definable_iff_isSemilinearSet (A := (∅ : Set ℕ))]
  exact Set.definable_biInter_finset (fun i => (ht i).definable) s

/-! ## Residue classes of the fibre coordinate -/

/-- The set of points whose fibre coordinate lies in the residue class `ρ` mod `D`. -/
def resSet (p : ℕ) (D ρ : ℕ) : Set (Fin p ⊕ Fin 1 → ℕ) :=
  {w : Fin p ⊕ Fin 1 → ℕ | w (Sum.inr 0) % D = ρ}

theorem isSemilinearSet_resSet {p : ℕ} {D ρ : ℕ} (hρ : ρ < D) :
    IsSemilinearSet (resSet p D ρ) := by
  classical
  rw [← presburger.definable_iff_isSemilinearSet (A := (∅ : Set ℕ))]
  have hc : ∀ (w : Fin p ⊕ Fin 1 → ℕ) (u : Fin 1 → ℕ),
      (Sum.elim w u) ∘ (![Sum.inl (Sum.inr 0), Sum.inr 0] :
        Fin 2 → (Fin p ⊕ Fin 1) ⊕ Fin 1) = ![w (Sum.inr 0), u 0] := by
    intro w u; funext i; fin_cases i <;> rfl
  have h := (((isSemilinearSet_res2 D ρ).definable (A := (∅ : Set ℕ))).preimage_comp
    (![Sum.inl (Sum.inr 0), Sum.inr 0] :
      Fin 2 → (Fin p ⊕ Fin 1) ⊕ Fin 1)).exists_of_finite (β := Fin 1)
  convert h using 1
  ext w
  simp only [resSet, Set.mem_ofPred_eq, Set.mem_preimage, hc, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  constructor
  · intro hw
    refine ⟨fun _ => w (Sum.inr 0) / D, ?_⟩
    rw [← hw]
    exact (Nat.mod_add_div _ _).symm
  · rintro ⟨u, hu⟩
    rw [hu, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ]

/-- A piece cut along a residue class is a `D`-progression in every fibre, provided the step of
the piece divides `D`. -/
theorem isDProg_of_step {p : ℕ} {L : Set (Fin p ⊕ Fin 1 → ℕ)} {E D : ℕ} (hE : 0 < E)
    (hED : E ∣ D) {x : Fin p → ℕ} {a l : ℕ}
    (hL : ∀ n : ℕ, n ∈ fib L x ↔ ∃ j : ℕ, j < l ∧ n = a + j * E) (ρ : ℕ) :
    IsDProg D (fib (L ∩ resSet p D ρ) x) := by
  obtain ⟨e, he⟩ := hED
  have hfibeq : ∀ n : ℕ, n ∈ fib (L ∩ resSet p D ρ) x ↔ (n ∈ fib L x ∧ n % D = ρ) := by
    intro n; simp [fib, resSet]
  intro n m k hn hm h1 h2
  rw [hfibeq] at hn hm
  rw [hfibeq]
  obtain ⟨j₁, hj₁, hn1⟩ := (hL n).1 hn.1
  obtain ⟨j₂, hj₂, hm1⟩ := (hL m).1 hm.1
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨(hL _).2 ⟨j₁ + e * t, ?_, ?_⟩, ?_⟩
    · have hcalc : a + (j₁ + e * t) * E = n + D * t := by rw [hn1, he]; ring
      have h3 : a + (j₁ + e * t) * E ≤ a + j₂ * E := by rw [hcalc, ← hm1]; exact h2
      exact lt_of_le_of_lt
        (Nat.le_of_mul_le_mul_right (Nat.le_of_add_le_add_left h3) hE) hj₂
    · rw [hn1, he]; ring
    · rw [← hn.2]
      exact Nat.add_mul_mod_self_left n D t
  · intro hk
    have hmod : Nat.ModEq D n k := by
      show n % D = k % D
      rw [hn.2, hk.2]
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' h1).1 hmod
    exact ⟨t, ((Nat.sub_eq_iff_eq_add h1).1 ht).trans (Nat.add_comm _ _)⟩

/-! ## The count graph of a family of `D`-progressions -/

/-- **A family of `D`-progressions has a semilinear count graph.**  If `A ⊆ ℕ^p × ℕ` is
semilinear with finite fibres and every fibre is a `D`-progression for one fixed positive `D`,
then the graph of the fibre count is semilinear: the count is `(max − min)/D + 1`, and the
fibrewise minimum and maximum are Presburger-definable. -/
theorem isSemilinearSet_countGraph_of_isDProg {p : ℕ} {D : ℕ} (hD : 0 < D)
    {A : Set (Fin p ⊕ Fin 1 → ℕ)} (hA : IsSemilinearSet A)
    (hfin : ∀ x : Fin p → ℕ, (fib A x).Finite)
    (hprog : ∀ x : Fin p → ℕ, IsDProg D (fib A x)) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ |
      (fib A (fun i => z i.castSucc)).ncard = z (Fin.last p)} := by
  classical
  rw [← presburger.definable_iff_isSemilinearSet (A := (∅ : Set ℕ))]
  have hMin : IsSemilinearSet {u : Fin p ⊕ Fin 1 → ℕ | u ∈ A ∧
      ∀ w : Fin 1 → ℕ, Sum.elim (u ∘ Sum.inl) w ∈ A → u (Sum.inr 0) ≤ w 0} :=
    SemilinearMinMax.isSemilinearSet_minCoord 0 hA
  have hMax : IsSemilinearSet {u : Fin p ⊕ Fin 1 → ℕ | u ∈ A ∧
      ∀ w : Fin 1 → ℕ, Sum.elim (u ∘ Sum.inl) w ∈ A → w 0 ≤ u (Sum.inr 0)} :=
    SemilinearMinMax.isSemilinearSet_maxCoord 0 hA
  have hMinMem : ∀ (x : Fin p → ℕ) (n : ℕ),
      (Sum.elim x (fun _ : Fin 1 => n) ∈ {u : Fin p ⊕ Fin 1 → ℕ | u ∈ A ∧
        ∀ w : Fin 1 → ℕ, Sum.elim (u ∘ Sum.inl) w ∈ A → u (Sum.inr 0) ≤ w 0})
        ↔ IsLeast (fib A x) n := by
    intro x n
    simp only [Set.mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun m hm => h2 (fun _ => m) hm⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun w hw => ?_⟩
      have he : (fun _ : Fin 1 => w 0) = w := by funext i; fin_cases i; rfl
      exact h2 (show w 0 ∈ fib A x from by rw [mem_fib, he]; exact hw)
  have hMaxMem : ∀ (x : Fin p → ℕ) (n : ℕ),
      (Sum.elim x (fun _ : Fin 1 => n) ∈ {u : Fin p ⊕ Fin 1 → ℕ | u ∈ A ∧
        ∀ w : Fin 1 → ℕ, Sum.elim (u ∘ Sum.inl) w ∈ A → w 0 ≤ u (Sum.inr 0)})
        ↔ IsGreatest (fib A x) n := by
    intro x n
    simp only [Set.mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun m hm => h2 (fun _ => m) hm⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun w hw => ?_⟩
      have he : (fun _ : Fin 1 => w 0) = w := by funext i; fin_cases i; rfl
      exact h2 (show w 0 ∈ fib A x from by rw [mem_fib, he]; exact hw)
  -- the empty branch
  have hEmpty : (∅ : Set ℕ).Definable presburger
      {z : Fin (p + 1) → ℕ | fib A (fun i => z i.castSucc) = ∅ ∧ z (Fin.last p) = 0} := by
    have hc : ∀ (z : Fin (p + 1) → ℕ) (u : Fin 1 → ℕ),
        (Sum.elim z u) ∘ (Sum.elim (fun i : Fin p => Sum.inl i.castSucc)
          (fun _ : Fin 1 => Sum.inr 0) : Fin p ⊕ Fin 1 → Fin (p + 1) ⊕ Fin 1)
          = Sum.elim (fun i : Fin p => z i.castSucc) (fun _ : Fin 1 => u 0) := by
      intro z u; funext v; cases v <;> rfl
    have h1 := ((hA.definable (A := (∅ : Set ℕ))).preimage_comp
      (Sum.elim (fun i : Fin p => Sum.inl i.castSucc)
        (fun _ : Fin 1 => Sum.inr 0) : Fin p ⊕ Fin 1 → Fin (p + 1) ⊕ Fin 1)).exists_of_finite
      (β := Fin 1)
    have h2 : (∅ : Set ℕ).Definable presburger
        {z : Fin (p + 1) → ℕ | z (Fin.last p) = 0} :=
      ProperPieceCount.definable_coord_const _ 0
    convert h1.compl.inter h2 using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage, hc,
      not_exists]
    refine and_congr_left fun _ => ?_
    rw [Set.eq_empty_iff_forall_notMem]
    exact ⟨fun h u => h (u 0), fun h n => h (fun _ => n)⟩
  -- the nonempty branch
  have hNe : (∅ : Set ℕ).Definable presburger
      {z : Fin (p + 1) → ℕ | ∃ mn mx : ℕ,
        IsLeast (fib A (fun i => z i.castSucc)) mn ∧
        IsGreatest (fib A (fun i => z i.castSucc)) mx ∧
        D * z (Fin.last p) + mn = D + mx} := by
    have hc₁ : ∀ (z : Fin (p + 1) → ℕ) (u : Fin 2 → ℕ),
        (Sum.elim z u) ∘ (Sum.elim (fun i : Fin p => Sum.inl i.castSucc)
          (fun _ : Fin 1 => Sum.inr 0) : Fin p ⊕ Fin 1 → Fin (p + 1) ⊕ Fin 2)
          = Sum.elim (fun i : Fin p => z i.castSucc) (fun _ : Fin 1 => u 0) := by
      intro z u; funext v; cases v <;> rfl
    have hc₂ : ∀ (z : Fin (p + 1) → ℕ) (u : Fin 2 → ℕ),
        (Sum.elim z u) ∘ (Sum.elim (fun i : Fin p => Sum.inl i.castSucc)
          (fun _ : Fin 1 => Sum.inr 1) : Fin p ⊕ Fin 1 → Fin (p + 1) ⊕ Fin 2)
          = Sum.elim (fun i : Fin p => z i.castSucc) (fun _ : Fin 1 => u 1) := by
      intro z u; funext v; cases v <;> rfl
    have h1 := (hMin.definable (A := (∅ : Set ℕ))).preimage_comp
      (Sum.elim (fun i : Fin p => Sum.inl i.castSucc)
        (fun _ : Fin 1 => Sum.inr 0) : Fin p ⊕ Fin 1 → Fin (p + 1) ⊕ Fin 2)
    have h2 := (hMax.definable (A := (∅ : Set ℕ))).preimage_comp
      (Sum.elim (fun i : Fin p => Sum.inl i.castSucc)
        (fun _ : Fin 1 => Sum.inr 1) : Fin p ⊕ Fin 1 → Fin (p + 1) ⊕ Fin 2)
    have h3 := definable_eq3 (A := (∅ : Set ℕ))
      (Sum.inl (Fin.last p) : Fin (p + 1) ⊕ Fin 2) (Sum.inr 0) (Sum.inr 1) D
    have h4 := ((h1.inter h2).inter h3).exists_of_finite (β := Fin 2)
    convert h4 using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, hc₁, hc₂,
      Sum.elim_inl, Sum.elim_inr]
    constructor
    · rintro ⟨mn, mx, h5, h6, h7⟩
      exact ⟨![mn, mx], ⟨(hMinMem _ mn).2 h5, (hMaxMem _ mx).2 h6⟩, by simpa using h7⟩
    · rintro ⟨u, ⟨h5, h6⟩, h7⟩
      exact ⟨u 0, u 1, (hMinMem _ (u 0)).1 h5, (hMaxMem _ (u 1)).1 h6, h7⟩
  convert hEmpty.union hNe using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · intro hz
    rcases Set.eq_empty_or_nonempty (fib A (fun i => z i.castSucc)) with he | hne
    · exact Or.inl ⟨he, by rw [← hz, he, Set.ncard_empty]⟩
    · obtain ⟨mn, mx, hmn, hmx⟩ := exists_isLeast_isGreatest (hfin _) hne
      exact Or.inr ⟨mn, mx, hmn, hmx, by rw [← hz]; exact ncard_of_isDProg hD hmn hmx (hprog _)⟩
  · rintro (⟨he, hz⟩ | ⟨mn, mx, hmn, hmx, hz⟩)
    · rw [he, Set.ncard_empty, hz]
    · have hkey := ncard_of_isDProg hD hmn hmx (hprog (fun i => z i.castSucc))
      have h1 : D * (fib A (fun i => z i.castSucc)).ncard + mn = D * z (Fin.last p) + mn := by
        rw [hkey, hz]
      exact Nat.eq_of_mul_eq_mul_left hD (Nat.add_right_cancel h1)

/-! ## Unions of pieces -/

/-- **From intersections to unions.**  If every nonempty finite intersection of the family `A`
has a semilinear count graph, so does every finite union.  The induction rests on the two-set
identity `|B ∪ C| + |B ∩ C| = |B| + |C|` applied to `B = A a` and `C = ⋃_{i ∈ s} A i`; the
correction term `A a ∩ ⋃_{i ∈ s} A i = ⋃_{i ∈ s} (A a ∩ A i)` is a shorter union of the same
kind. -/
theorem isSemilinearSet_countGraph_biUnion {p : ℕ} {ι : Type} [DecidableEq ι] (s : Finset ι) :
    ∀ A : ι → Set (Fin p ⊕ Fin 1 → ℕ),
      (∀ (i : ι) (x : Fin p → ℕ), (fib (A i) x).Finite) →
      (∀ T : Finset ι, T.Nonempty → IsSemilinearSet {z : Fin (p + 1) → ℕ |
        (fib (⋂ i ∈ T, A i) (fun i => z i.castSucc)).ncard = z (Fin.last p)}) →
      IsSemilinearSet {z : Fin (p + 1) → ℕ |
        (fib (⋃ i ∈ s, A i) (fun i => z i.castSucc)).ncard = z (Fin.last p)} := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro A _ _
    convert SemilinearGraphArith.isSemilinearSet_graph_const (p := p) 0 using 1
    ext z
    simp [fib]
  | @insert a s' ha ih =>
    intro A hfin hgraph
    have hA : IsSemilinearSet {z : Fin (p + 1) → ℕ |
        (fib (A a) (fun i => z i.castSucc)).ncard = z (Fin.last p)} := by
      have h := hgraph {a} (Finset.singleton_nonempty a)
      have hset : (⋂ i ∈ ({a} : Finset ι), A i) = A a := by ext w; simp
      rwa [hset] at h
    have hU' := ih A hfin hgraph
    have hInt : IsSemilinearSet {z : Fin (p + 1) → ℕ |
        (fib (⋃ i ∈ s', A a ∩ A i) (fun i => z i.castSucc)).ncard = z (Fin.last p)} := by
      refine ih (fun i => A a ∩ A i) (fun i x => (hfin i x).subset fun n hn => hn.2) ?_
      intro T hT
      have h := hgraph (insert a T) (Finset.insert_nonempty a T)
      have hset : (⋂ i ∈ T, A a ∩ A i) = ⋂ i ∈ insert a T, A i := by
        ext w
        simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_insert]
        constructor
        · intro hw i hi
          rcases hi with rfl | hi
          · obtain ⟨j, hj⟩ := hT
            exact (hw j hj).1
          · exact (hw i hi).2
        · intro hw i hi
          exact ⟨hw a (Or.inl rfl), hw i (Or.inr hi)⟩
      rw [hset]
      exact h
    have hUeq : ∀ x : Fin p → ℕ,
        (fib (⋃ i ∈ insert a s', A i) x).ncard + (fib (⋃ i ∈ s', A a ∩ A i) x).ncard
          = (fib (A a) x).ncard + (fib (⋃ i ∈ s', A i) x).ncard := by
      intro x
      have e1 : fib (⋃ i ∈ insert a s', A i) x = fib (A a) x ∪ fib (⋃ i ∈ s', A i) x := by
        ext n
        simp only [fib, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_union, Finset.mem_insert,
          exists_prop]
        constructor
        · rintro ⟨i, hi | hi, hn⟩
          · exact Or.inl (hi ▸ hn)
          · exact Or.inr ⟨i, hi, hn⟩
        · rintro (hn | ⟨i, hi, hn⟩)
          · exact ⟨a, Or.inl rfl, hn⟩
          · exact ⟨i, Or.inr hi, hn⟩
      have e2 : fib (⋃ i ∈ s', A a ∩ A i) x = fib (A a) x ∩ fib (⋃ i ∈ s', A i) x := by
        ext n
        simp only [fib, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
        constructor
        · rintro ⟨i, hi, hn1, hn2⟩
          exact ⟨hn1, i, hi, hn2⟩
        · rintro ⟨hn1, i, hi, hn2⟩
          exact ⟨i, hi, hn1, hn2⟩
      rw [e1, e2]
      exact Set.ncard_union_add_ncard_inter _ _ (hfin a x) (finite_fib_biUnion s' hfin x)
    exact SemilinearGraphArith.isSemilinearSet_graph_sub
      (f₁ := fun x => (fib (A a) x).ncard + (fib (⋃ i ∈ s', A i) x).ncard)
      (f₂ := fun x => (fib (⋃ i ∈ s', A a ∩ A i) x).ncard)
      (g := fun x => (fib (⋃ i ∈ insert a s', A i) x).ncard)
      (SemilinearGraphArith.isSemilinearSet_graph_add
        (f₁ := fun x => (fib (A a) x).ncard)
        (f₂ := fun x => (fib (⋃ i ∈ s', A i) x).ncard) hA hU')
      hInt hUeq

/-! ## Summing the residue classes -/

private theorem ncard_eq_sum_residues {F : Set ℕ} (hfin : F.Finite) {D : ℕ} (hD : 0 < D) :
    F.ncard = ∑ ρ ∈ Finset.range D, (F ∩ {n : ℕ | n % D = ρ}).ncard := by
  classical
  have h1 : F.ncard = hfin.toFinset.card := Set.ncard_eq_toFinset_card F hfin
  have h2 : ∀ ρ : ℕ, (F ∩ {n : ℕ | n % D = ρ}).ncard
      = (hfin.toFinset.filter (fun n => n % D = ρ)).card := by
    intro ρ
    have hset : F ∩ {n : ℕ | n % D = ρ}
        = ↑(hfin.toFinset.filter (fun n => n % D = ρ)) := by
      ext n; simp [Set.Finite.mem_toFinset]
    rw [hset, Set.ncard_coe_finset]
  rw [h1]
  simp only [h2]
  exact Finset.card_eq_sum_card_fiberwise (fun n _ => Finset.mem_range.2 (Nat.mod_lt n hD))

/-! ## The one-dimensional counting theorem -/

/-- **`lem:presburger-counting` at `q = 1`.**  For a semilinear `S ⊆ ℕ^p × ℕ` whose
parameter-fibres are finite and of size at most `C · (‖x‖_∞ + 1)`, the count graph, packed as
`Fin (p+1) → ℕ` with the parameters on `Fin.castSucc` and the count on `Fin.last p`, is
semilinear. -/
theorem isSemilinearSet_countGraph_dim_one {p : ℕ} {S : Set (Fin p ⊕ Fin 1 → ℕ)}
    (hS : IsSemilinearSet S)
    (hfin : ∀ x : Fin p → ℕ, Set.Finite {y : Fin 1 → ℕ | Sum.elim x y ∈ S})
    (C : ℕ)
    (hbd : ∀ x : Fin p → ℕ,
      Nat.card {y : Fin 1 → ℕ | Sum.elim x y ∈ S} ≤ C * (Finset.univ.sup x + 1)) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ |
      Nat.card {y : Fin 1 → ℕ | Sum.elim (fun i => z i.castSucc) y ∈ S} = z (Fin.last p)} := by
  classical
  have hfinS : ∀ x : Fin p → ℕ, (fib S x).Finite := fun x => finite_fib (hfin x)
  -- decompose into proper linear pieces
  obtain ⟨𝒮, h𝒮, hSeq⟩ := isProperSemilinearSet_iff.1 hS.isProperSemilinearSet
  set ι : Type := {t : Set (Fin p ⊕ Fin 1 → ℕ) // t ∈ 𝒮} with hι
  set L : ι → Set (Fin p ⊕ Fin 1 → ℕ) := fun i => (i : Set (Fin p ⊕ Fin 1 → ℕ)) with hL
  have hSU : S = ⋃ i ∈ (Finset.univ : Finset ι), L i := by
    rw [hSeq]
    ext w
    constructor
    · rintro ⟨t, ht, hwt⟩
      exact Set.mem_iUnion₂.2 ⟨⟨t, Finset.mem_coe.1 ht⟩, Finset.mem_univ _, hwt⟩
    · intro hw
      obtain ⟨i, -, hwi⟩ := Set.mem_iUnion₂.1 hw
      exact ⟨(i : Set (Fin p ⊕ Fin 1 → ℕ)), Finset.mem_coe.2 i.2, hwi⟩
  have hLsub : ∀ i : ι, L i ⊆ S := by
    intro i w hw
    rw [hSU]
    exact Set.mem_biUnion (Finset.mem_univ i) hw
  have hLfin : ∀ (i : ι) (x : Fin p → ℕ), Set.Finite {y : Fin 1 → ℕ | Sum.elim x y ∈ L i} :=
    fun i x => (hfin x).subset (fun y hy => hLsub i hy)
  have hLbd : ∀ (i : ι) (x : Fin p → ℕ),
      Nat.card {y : Fin 1 → ℕ | Sum.elim x y ∈ L i} ≤ C * (Finset.univ.sup x + 1) := by
    intro i x
    calc Nat.card {y : Fin 1 → ℕ | Sum.elim x y ∈ L i}
        = (fib (L i) x).ncard := card_tupleFibre _ _
      _ ≤ (fib S x).ncard := Set.ncard_le_ncard (fib_mono (hLsub i) x) (hfinS x)
      _ = Nat.card {y : Fin 1 → ℕ | Sum.elim x y ∈ S} := (card_tupleFibre _ _).symm
      _ ≤ C * (Finset.univ.sup x + 1) := hbd x
  -- one positive step for each piece
  have hstep : ∀ i : ι, ∃ E : ℕ, 0 < E ∧ ∀ x : Fin p → ℕ, ∃ a l : ℕ,
      ∀ n : ℕ, n ∈ fib (L i) x ↔ ∃ j : ℕ, j < l ∧ n = a + j * E :=
    fun i => exists_step_progression (h𝒮 (L i) i.2) (hLfin i) C (hLbd i)
  choose E hEpos hEprog using hstep
  -- a common multiple of the steps
  set D : ℕ := ∏ i : ι, E i with hDdef
  have hD : 0 < D := Finset.prod_pos (fun i _ => hEpos i)
  have hED : ∀ i : ι, E i ∣ D := fun i => Finset.dvd_prod_of_mem E (Finset.mem_univ i)
  -- the pieces cut along one residue class
  have hLsl : ∀ i : ι, IsSemilinearSet (L i) := fun i => (h𝒮 (L i) i.2).isLinearSet.isSemilinearSet
  have hpiece : ∀ ρ : ℕ, ρ < D → IsSemilinearSet {z : Fin (p + 1) → ℕ |
      (fib (⋃ i ∈ (Finset.univ : Finset ι), L i ∩ resSet p D ρ)
        (fun i => z i.castSucc)).ncard = z (Fin.last p)} := by
    intro ρ hρ
    have hres : IsSemilinearSet (resSet p D ρ) := isSemilinearSet_resSet hρ
    refine isSemilinearSet_countGraph_biUnion Finset.univ (fun i => L i ∩ resSet p D ρ)
      (fun i x => ((hfinS x).subset (fun n hn => hLsub i hn.1))) ?_
    intro T hT
    obtain ⟨i₀, hi₀⟩ := hT
    refine isSemilinearSet_countGraph_of_isDProg hD
      (isSemilinearSet_biInter_finset T (fun i => (hLsl i).inter hres)) ?_ ?_
    · intro x
      refine (hfinS x).subset (fun n hn => ?_)
      have := Set.mem_iInter₂.1 hn i₀ hi₀
      exact hLsub i₀ this.1
    · intro x
      have hfe : fib (⋂ i ∈ T, L i ∩ resSet p D ρ) x
          = ⋂ i ∈ T, fib (L i ∩ resSet p D ρ) x := by
        ext n; simp [fib]
      rw [hfe]
      refine isDProg_biInter T ⟨i₀, hi₀⟩ (fun i _ => ?_)
      obtain ⟨a, l, hal⟩ := hEprog i x
      exact isDProg_of_step (hEpos i) (hED i) hal ρ
  -- assemble the residue classes
  have hUeq : ∀ (ρ : ℕ) (x : Fin p → ℕ),
      fib (⋃ i ∈ (Finset.univ : Finset ι), L i ∩ resSet p D ρ) x
        = fib S x ∩ {n : ℕ | n % D = ρ} := by
    intro ρ x
    ext n
    simp only [fib, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_univ,
      exists_true_left, resSet, Sum.elim_inr]
    constructor
    · rintro ⟨i, hn1, hn2⟩
      exact ⟨hLsub i hn1, hn2⟩
    · rintro ⟨hn1, hn2⟩
      rw [hSU] at hn1
      obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.1 hn1
      exact ⟨i, hi, hn2⟩
  have hsum : ∀ x : Fin p → ℕ, (fib S x).ncard
      = ∑ ρ : Fin D, (fib (⋃ i ∈ (Finset.univ : Finset ι), L i ∩ resSet p D ρ.1) x).ncard := by
    intro x
    rw [Fin.sum_univ_eq_sum_range (fun ρ =>
      (fib (⋃ i ∈ (Finset.univ : Finset ι), L i ∩ resSet p D ρ) x).ncard) D]
    rw [ncard_eq_sum_residues (hfinS x) hD]
    exact Finset.sum_congr rfl (fun ρ _ => by rw [hUeq ρ x])
  have hgraph : IsSemilinearSet {z : Fin (p + 1) → ℕ |
      (fib S (fun i => z i.castSucc)).ncard = z (Fin.last p)} := by
    refine SemilinearGraphArith.isSemilinearSet_graph_sum'
      (f := fun (ρ : Fin D) (x : Fin p → ℕ) =>
        (fib (⋃ i ∈ (Finset.univ : Finset ι), L i ∩ resSet p D ρ.1) x).ncard)
      (fun ρ => hpiece ρ.1 ρ.2) Finset.univ
      (fun x => (fib S x).ncard) hsum
  have hconv : {z : Fin (p + 1) → ℕ |
      Nat.card {y : Fin 1 → ℕ | Sum.elim (fun i => z i.castSucc) y ∈ S} = z (Fin.last p)}
      = {z : Fin (p + 1) → ℕ | (fib S (fun i => z i.castSucc)).ncard = z (Fin.last p)} := by
    ext z
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, card_tupleFibre]
  rw [hconv]
  exact hgraph

/-- **The natural-number packaging.**  The same statement with the fibre read as a set of
naturals rather than of `Fin 1`-tuples, which is the shape produced by
`ProperPieceCount.exists_indexSet_inter`. -/
theorem isSemilinearSet_countGraph_nat {p : ℕ} {S : Set (Fin p ⊕ Fin 1 → ℕ)}
    (hS : IsSemilinearSet S)
    (hfin : ∀ x : Fin p → ℕ, Set.Finite {n : ℕ | Sum.elim x (fun _ => n) ∈ S})
    (C : ℕ)
    (hbd : ∀ x : Fin p → ℕ,
      Nat.card {n : ℕ | Sum.elim x (fun _ => n) ∈ S} ≤ C * (Finset.univ.sup x + 1)) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ |
      Nat.card {n : ℕ | Sum.elim (fun i => z i.castSucc) (fun _ => n) ∈ S}
        = z (Fin.last p)} := by
  have heq : ∀ x : Fin p → ℕ,
      Nat.card {y : Fin 1 → ℕ | Sum.elim x y ∈ S}
        = Nat.card {n : ℕ | Sum.elim x (fun _ => n) ∈ S} := fun x => card_tupleFibre S x
  have h := isSemilinearSet_countGraph_dim_one hS
    (fun x => finite_tupleFibre (hfin x)) C (fun x => by rw [heq x]; exact hbd x)
  have hset : {z : Fin (p + 1) → ℕ |
      Nat.card {n : ℕ | Sum.elim (fun i => z i.castSucc) (fun _ => n) ∈ S} = z (Fin.last p)}
      = {z : Fin (p + 1) → ℕ |
        Nat.card {y : Fin 1 → ℕ | Sum.elim (fun i => z i.castSucc) y ∈ S} = z (Fin.last p)} := by
    ext z
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, heq]
  rw [hset]
  exact h

/-- **The axiom-shaped packaging at `q = 1`.**  For a relation `R ⊆ ℕ^p × ℕ` with semilinear
graph, finite fibres and a linear fibre bound, the count graph is semilinear. -/
theorem count_graph_dim_one {p : ℕ} (R : (Fin p → ℕ) → (Fin 1 → ℕ) → Prop)
    (hR : IsSemilinearSet {w : Fin p ⊕ Fin 1 → ℕ | R (w ∘ Sum.inl) (w ∘ Sum.inr)})
    (hfin : ∀ x : Fin p → ℕ, Set.Finite {y : Fin 1 → ℕ | R x y})
    (C : ℕ)
    (hbd : ∀ x : Fin p → ℕ,
      Nat.card {y : Fin 1 → ℕ | R x y} ≤ C * (Finset.univ.sup x + 1)) :
    IsSemilinearSet {z : Fin (p + 1) → ℕ |
      Nat.card {y : Fin 1 → ℕ | R (fun i => z i.castSucc) y} = z (Fin.last p)} := by
  have heq : ∀ x : Fin p → ℕ,
      {y : Fin 1 → ℕ | Sum.elim x y ∈ {w : Fin p ⊕ Fin 1 → ℕ | R (w ∘ Sum.inl) (w ∘ Sum.inr)}}
        = {y : Fin 1 → ℕ | R x y} := by
    intro x
    ext y
    have h1 : (Sum.elim x y) ∘ Sum.inl = x := funext fun _ => rfl
    have h2 : (Sum.elim x y) ∘ Sum.inr = y := funext fun _ => rfl
    simp only [Set.mem_ofPred_eq, h1, h2]
  have h := isSemilinearSet_countGraph_dim_one hR
    (fun x => by rw [heq x]; exact hfin x) C (fun x => by rw [heq x]; exact hbd x)
  have hgraph : {z : Fin (p + 1) → ℕ |
      Nat.card {y : Fin 1 → ℕ | R (fun i => z i.castSucc) y} = z (Fin.last p)}
      = {z : Fin (p + 1) → ℕ | Nat.card {y : Fin 1 → ℕ |
        Sum.elim (fun i => z i.castSucc) y ∈
          {w : Fin p ⊕ Fin 1 → ℕ | R (w ∘ Sum.inl) (w ∘ Sum.inr)}} = z (Fin.last p)} := by
    ext z
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, heq]
  rw [hgraph]
  exact h

end CountBaseCase
