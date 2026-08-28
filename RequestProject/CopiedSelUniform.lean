/-
# Per-class uniformity at the slice (§9 d4a-2 — the math core of `hsufUniform`/`hpreUniform`)

The heart of the (4a) per-class uniformity that feeds `CopiedSufRunGate.gate_semantic_split`: on a
homogeneous boundary run of `copiedSlice mS n` whose cell rank is affine-in-depth (from
`CopiedDstarCMS.coordCands_cycle_lengths`) and on which "selected ∧ label = D" is constant on each
`pc`-class (from `CopiedSelConst.selRun_suf_const`/`selRun_pre_const`), a SINGLE deep-interior achiever
forces the WHOLE residue class to equal `d*`.

Mechanism: the selBvec lex-min ENDPOINT of the class is selected-D by the constancy, so
`CopiedDstarC.dstarRankGA'_lex_min` lower-bounds it (`hglob`); with the achiever interior to both run
ends the slope is forced to `0` (`affine_class_uniform`) and `class_uniform_of_dom` collapses the
class.  The position map `posOf` is `fun l => mS+2n+1+l` for the final `D`-run, `id` for the initial
`U`-run, so one lemma serves both directions.
-/
import RequestProject.CopiedSelConst
import RequestProject.CopiedDstarC

namespace CopiedSelUniform

open WRP Step SliceMSO MSOMarkN SliceMarkN CopiedDstar CopiedDstarCMS SliceBoundaryMinCore CopiedSelConst

/-- **Affine-on-residues at a MULTIPLE period.**  `RankAffineAtFrom M Q F → RankAffineAtFrom M (Q*K) F`
(the slope scales by `K`).  A combined period `pc_s * pc_p` then carries BOTH the suffix and prefix
rank-affine recurrences, so one `cls` (mod the combined period) serves `gate_semantic_split`. -/
theorem RankAffineAtFrom_mul {d : ℕ} {M Q : ℕ} {F : ℕ → Fin d → ℤ}
    (h : RankAffineAtFrom M Q F) (K : ℕ) : RankAffineAtFrom M (Q * K) F := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun i => (K : ℤ) * P i, fun l hl => ?_⟩
  induction K with
  | zero => funext i; simp
  | succ K ih =>
    funext i
    have hstep : F (l + Q * (K + 1)) i = F (l + Q * K) i + P i := by
      have := congrFun (hP (l + Q * K) (by omega)) i
      rw [Pi.add_apply] at this
      rw [show l + Q * (K + 1) = (l + Q * K) + Q from by ring]
      exact this
    rw [hstep, congrFun ih i, Pi.add_apply, Pi.add_apply]
    push_cast
    ring

/-- **Two-representative class collapse.**  On a `RankAffineAtFrom T pc F` residue class, if the
two adjacent representatives `T + r` and `T + r + pc` both equal the target vector, the whole class
equals the target.  This is the rank-only slope-zero fact needed by the banded run activation sets:
membership records two equal-rank reps, and the gate then ranges over every selected atom in that
residue band. -/
theorem RankAffineAtFrom.class_eq_of_two_reps {d : ℕ} {T pc : ℕ} {F : ℕ → Fin d → ℤ}
    {target : Fin d → ℤ} (hpc : 1 ≤ pc) (hF : RankAffineAtFrom T pc F)
    {r : ℕ} (hr : r < pc)
    (h0 : F (T + r) = target) (h1 : F (T + r + pc) = target) :
    ∀ l, T ≤ l → (l - T) % pc = r → F l = target := by
  classical
  obtain ⟨P, hP⟩ := hF
  set G : ℕ → Fin d → ℤ := fun k => F (T + r + pc * k) with hGdef
  have hrecG : ∀ k (i : Fin d), G k i = G 0 i + (k : ℤ) * P i := by
    intro k i
    have h := congrFun (SliceRankAtom.RankAffine.iterate hP (T + r) k (by omega)) i
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at h
    exact h
  have h01 : G 0 = G 1 := by
    rw [hGdef]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    rw [h0, h1]
  have hconst := CopiedSufRunGate.affine_class_uniform G P hrecG (by omega : (0 : ℕ) ≠ 1) h01
  intro l hTl hres
  have hdecomp : T + r + pc * ((l - T) / pc) = l := by
    have hpcpos : 0 < pc := Nat.lt_of_lt_of_le Nat.zero_lt_one hpc
    have hrlt : r < pc := hr
    have hdiv := Nat.mod_add_div (l - T) pc
    omega
  rw [← hdecomp]
  change G ((l - T) / pc) = target
  rw [hconst ((l - T) / pc)]
  rw [hGdef]
  simp only [Nat.mul_zero, Nat.add_zero]
  exact h0

/-- **Absolute-to-local run residue.**  If a run position `shift + l` has absolute residue `ρ`
modulo a gate period `Q`, and `pc ∣ Q`, then the activation-set local residue
`ρ - (shift + T)` (computed as `ρ + Q - ((shift + T) % Q)`) is exactly `(l - T) % pc`.
The suffix run uses `shift = mS + 2*n + 1`; the prefix run uses `shift = 0`. -/
theorem runLocalResidue_of_abs_mod {Q pc shift T l ρ : ℕ}
    (hQ : 0 < Q) (hpcQ : pc ∣ Q) (hρ : ρ < Q)
    (habs : (shift + l) % Q = ρ) (hTl : T ≤ l) :
    ((ρ + Q - ((shift + T) % Q)) % pc) = (l - T) % pc := by
  have habsQ : ρ ≡ shift + l [MOD Q] := by
    rw [Nat.ModEq, Nat.mod_eq_of_lt hρ, habs]
  have habsPc : ρ ≡ shift + l [MOD pc] :=
    Nat.ModEq.of_dvd hpcQ habsQ
  have hQzero : Q ≡ 0 [MOD pc] := hpcQ.modEq_zero_nat
  have hleft : ρ + Q ≡ shift + l [MOD pc] := by
    simpa using Nat.ModEq.add habsPc hQzero
  have horiginQ : (shift + T) % Q ≡ shift + T [MOD Q] := Nat.mod_modEq (shift + T) Q
  have horiginPc : (shift + T) % Q ≡ shift + T [MOD pc] :=
    Nat.ModEq.of_dvd hpcQ horiginQ
  have hleLeft : (shift + T) % Q ≤ ρ + Q := by
    have hlt : (shift + T) % Q < Q := Nat.mod_lt _ hQ
    omega
  have hleRight : shift + T ≤ shift + l := by omega
  have hsub := Nat.ModEq.sub hleLeft hleRight hleft horiginPc
  rw [show shift + l - (shift + T) = l - T by omega] at hsub
  exact hsub

/-- Suffix-run update-tuple form of `RankAffineAtFrom.class_eq_of_two_reps`: if the two adjacent
affine representatives in a suffix residue class have rank `d*`, every depth in that class has rank
`d*` for the tuple obtained by updating the distinguished coordinate. -/
theorem suffix_rank_eq_dstar_of_two_reps_update_slice
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) (ī0 : Fin (P.toPoly.arity c) → ℕ)
    (mS n pc T : ℕ) (F : ℕ → Fin P.d → ℤ) (hpc : 1 ≤ pc)
    (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l)
    {r l : ℕ} (hr : r < pc)
    (h0 : F (T + r) = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1 : F (T + r + pc) = CopiedDstar.dstarRankGA_m P hV mS n)
    (hTl : T ≤ l) (hlm : l < mS - 1) (hres : (l - T) % pc = r) :
    P.rank c (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l))
      = CopiedDstar.dstarRankGA_m P hV mS n := by
  have hFF := RankAffineAtFrom.class_eq_of_two_reps hpc hF hr h0 h1 l hTl hres
  rw [hag l hlm, hFF]

/-- Suffix-run absolute-residue form, still on the distinguished-coordinate update tuple. -/
theorem suffix_rank_eq_dstar_of_two_reps_abs_mod_update_slice
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) (ī0 : Fin (P.toPoly.arity c) → ℕ)
    (mS n pc T Q : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hpc : 1 ≤ pc) (hQ : 0 < Q) (hpcQ : pc ∣ Q)
    (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l)) = F l)
    {ρ l : ℕ} (hρ : ρ < Q)
    (h0 : F (T + ((ρ + Q - ((mS + 2 * n + 1 + T) % Q)) % pc))
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1 : F (T + ((ρ + Q - ((mS + 2 * n + 1 + T) % Q)) % pc) + pc)
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (habs : (mS + 2 * n + 1 + l) % Q = ρ)
    (hTl : T ≤ l) (hlm : l < mS - 1) :
    P.rank c (copiedSlice mS n) (Function.update ī0 j0 (mS + 2 * n + 1 + l))
      = CopiedDstar.dstarRankGA_m P hV mS n := by
  set rloc := (ρ + Q - ((mS + 2 * n + 1 + T) % Q)) % pc with hrloc_def
  have hrloc_lt : rloc < pc := by
    rw [hrloc_def]
    exact Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hpc)
  have hres0 := runLocalResidue_of_abs_mod (Q := Q) (pc := pc)
    (shift := mS + 2 * n + 1) (T := T) (l := l) (ρ := ρ)
    hQ hpcQ hρ habs hTl
  have hres : (l - T) % pc = rloc := by rw [hrloc_def]; exact hres0.symm
  exact suffix_rank_eq_dstar_of_two_reps_update_slice P hV c j0 ī0 mS n pc T F
    hpc hF hag (r := rloc) (l := l) hrloc_lt h0 h1 hTl hlm hres

/-- Prefix-run update-tuple form of `RankAffineAtFrom.class_eq_of_two_reps`. -/
theorem prefix_rank_eq_dstar_of_two_reps_update_slice
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) (ī0 : Fin (P.toPoly.arity c) → ℕ)
    (mS n pc T : ℕ) (F : ℕ → Fin P.d → ℤ) (hpc : 1 ≤ pc)
    (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 l) = F l)
    {r l : ℕ} (hr : r < pc)
    (h0 : F (T + r) = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1 : F (T + r + pc) = CopiedDstar.dstarRankGA_m P hV mS n)
    (hTl : T ≤ l) (hlm : l < mS - 1) (hres : (l - T) % pc = r) :
    P.rank c (copiedSlice mS n) (Function.update ī0 j0 l)
      = CopiedDstar.dstarRankGA_m P hV mS n := by
  have hFF := RankAffineAtFrom.class_eq_of_two_reps hpc hF hr h0 h1 l hTl hres
  rw [hag l hlm, hFF]

/-- Prefix-run absolute-residue form of the two-representative collapse, still on the update tuple. -/
theorem prefix_rank_eq_dstar_of_two_reps_abs_mod_update_slice
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) (ī0 : Fin (P.toPoly.arity c) → ℕ)
    (mS n pc T Q : ℕ) (F : ℕ → Fin P.d → ℤ)
    (hpc : 1 ≤ pc) (hQ : 0 < Q) (hpcQ : pc ∣ Q)
    (hF : RankAffineAtFrom T pc F)
    (hag : ∀ l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 l) = F l)
    {ρ l : ℕ} (hρ : ρ < Q)
    (h0 : F (T + ((ρ + Q - (T % Q)) % pc))
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (h1 : F (T + ((ρ + Q - (T % Q)) % pc) + pc)
        = CopiedDstar.dstarRankGA_m P hV mS n)
    (habs : l % Q = ρ)
    (hTl : T ≤ l) (hlm : l < mS - 1) :
    P.rank c (copiedSlice mS n) (Function.update ī0 j0 l)
      = CopiedDstar.dstarRankGA_m P hV mS n := by
  set rloc := (ρ + Q - (T % Q)) % pc with hrloc_def
  have hrloc_lt : rloc < pc := by
    rw [hrloc_def]
    exact Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hpc)
  have hres0 := runLocalResidue_of_abs_mod (Q := Q) (pc := pc)
    (shift := 0) (T := T) (l := l) (ρ := ρ)
    hQ hpcQ hρ (by simpa using habs) hTl
  have hres : (l - T) % pc = rloc := by
    rw [hrloc_def]
    simpa using hres0.symm
  exact prefix_rank_eq_dstar_of_two_reps_update_slice P hV c j0 ī0 mS n pc T F
    hpc hF hag (r := rloc) (l := l) hrloc_lt h0 h1 hTl hlm hres

/-- Arity-free update-tuple per-class uniformity core with direct validity for
the updated tuples.  This is the same slope-zero argument as
`run_class_uniform_core`, but the selected-D constancy and the selected witness
are stated for `Function.update ī0 j0 (posOf l)`.  Thus the proof does not
scalarize tuple fibres to constant tuples. -/
theorem run_class_uniform_update_core_of_valid
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) (ī0 : Fin (P.toPoly.arity c) → ℕ)
    (mS n : ℕ)
    (pc M Nc : ℕ) (F : ℕ → Fin P.d → ℤ) (hpc : 1 ≤ pc)
    (hF : RankAffineAtFrom M pc F)
    (posOf : ℕ → ℕ)
    (hupdval : ∀ l', l' < mS - 1 →
      ∀ i, Function.update ī0 j0 (posOf l') i < (copiedSlice mS n).length)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 (posOf l')) = F l')
    (hselconst : ∀ l₁ l₂, M ≤ l₁ → l₁ < Nc → M ≤ l₂ → l₂ < Nc →
        (l₁ - M) % pc = (l₂ - M) % pc →
        ((P.toPoly.sel c (copiedSlice mS n) (Function.update ī0 j0 (posOf l₁))
            ∧ P.toPoly.label c (copiedSlice mS n) (Function.update ī0 j0 (posOf l₁)) = D)
          ↔ (P.toPoly.sel c (copiedSlice mS n) (Function.update ī0 j0 (posOf l₂))
            ∧ P.toPoly.label c (copiedSlice mS n) (Function.update ī0 j0 (posOf l₂)) = D)))
    (hNcmS : Nc ≤ mS - 1)
    (l_b : ℕ) (hl_b_lo : M + pc ≤ l_b) (hl_bNc : l_b + pc < Nc)
    (hselb : P.toPoly.sel c (copiedSlice mS n) (Function.update ī0 j0 (posOf l_b))
        ∧ P.toPoly.label c (copiedSlice mS n) (Function.update ī0 j0 (posOf l_b)) = D)
    (hach : F l_b = CopiedDstar.dstarRankGA_m P hV mS n) :
    ∀ l', M ≤ l' → l' < mS - 1 → (l' - M) % pc = (l_b - M) % pc →
      F l' = CopiedDstar.dstarRankGA_m P hV mS n := by
  classical
  obtain ⟨PR, hPR⟩ := hF
  have hrec : ∀ (i : Fin P.d) (r' k : ℕ), F (M + r' + pc * k) i = F (M + r') i + k * PR i := by
    intro i r' k
    have hit := congrFun (SliceRankAtom.RankAffine.iterate hPR (M + r') k (by omega)) i
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at hit
    exact hit
  set dstar := CopiedDstar.dstarRankGA_m P hV mS n with hdstar
  set r := (l_b - M) % pc with hrdef
  set kd_b := (l_b - M) / pc with hkdbdef
  have hrlt : r < pc := by rw [hrdef]; exact Nat.mod_lt _ hpc
  have hjeq_b : M + r + pc * kd_b = l_b := by
    rw [hrdef, hkdbdef]; have := Nat.mod_add_div (l_b - M) pc; omega
  set Fc := fun κ => F (M + r + pc * κ) with hFcdef
  have hrecFc : ∀ κ (i : Fin P.d), Fc κ i = Fc 0 i + (κ : ℤ) * PR i := by
    intro κ i
    show F (M + r + pc * κ) i = F (M + r + pc * 0) i + (κ : ℤ) * PR i
    rw [Nat.mul_zero, Nat.add_zero, hrec i r κ]
  have hD : ∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a
      ∧ P.toPoly.labelOf (copiedSlice mS n) a = D :=
    ⟨⟨c, Function.update ī0 j0 (posOf l_b)⟩,
      ⟨hupdval l_b (by omega), hselb.1⟩, hselb.2⟩
  have finish : ∀ (ke : ℕ), ke ≠ kd_b → M + r + pc * ke < Nc →
      ¬ WRP.lexLt (Fc kd_b) (Fc ke) →
      ∀ l', M ≤ l' → l' < mS - 1 → (l' - M) % pc = (l_b - M) % pc → F l' = dstar := by
    intro ke hne hkeNc hdom l' hMl' hl'mS hl'r
    have hkemS : M + r + pc * ke < mS - 1 := by omega
    have hclass_le : (l_b - M) % pc = ((M + r + pc * ke) - M) % pc := by
      rw [show (M + r + pc * ke) - M = r + pc * ke from by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hrlt, hrdef]
    have hsel_le := (hselconst l_b (M + r + pc * ke) (by omega) (by omega) (by omega) hkeNc
      hclass_le).mp hselb
    have hrank_le :
        P.rankOf (copiedSlice mS n) ⟨c, Function.update ī0 j0 (posOf (M + r + pc * ke))⟩ =
          Fc ke := by
      show P.rank c (copiedSlice mS n) (Function.update ī0 j0 (posOf (M + r + pc * ke)))
        = Fc ke
      rw [hag (M + r + pc * ke) hkemS]
    have hglob : ¬ WRP.lexLt (Fc ke) dstar := by
      have hlm := CopiedDstarC.dstarRankGA'_lex_min P hV (copiedSlice mS n) hD
        ⟨c, Function.update ī0 j0 (posOf (M + r + pc * ke))⟩
        ⟨hupdval _ hkemS, hsel_le.1⟩ hsel_le.2
      rw [hrank_le] at hlm
      exact hlm
    have hb : Fc kd_b = dstar := by show F (M + r + pc * kd_b) = dstar; rw [hjeq_b]; exact hach
    have hconst := CopiedSufRunGate.class_uniform_of_dom Fc PR dstar hrecFc hne hdom hglob hb
    have hl'eq : M + r + pc * ((l' - M) / pc) = l' := by
      have h1 : (l' - M) % pc = r := by rw [hl'r, hrdef]
      have := Nat.mod_add_div (l' - M) pc
      omega
    have := hconst ((l' - M) / pc)
    show F l' = dstar
    rw [← hl'eq]; exact this
  have hkd_b : kd_b < numReps M pc r Nc :=
    (mem_iff_lt_numReps M pc r Nc kd_b hpc).mp (by rw [hjeq_b]; omega)
  have hnr1 : 1 ≤ numReps M pc r Nc := Nat.lt_of_le_of_lt (Nat.zero_le kd_b) hkd_b
  by_cases hslope : WRP.lexLt PR (fun _ => 0)
  · have hkd1 : kd_b + 1 < numReps M pc r Nc := by
      have hpos : M + r + pc * (kd_b + 1) < Nc := by
        have he : M + r + pc * (kd_b + 1) = l_b + pc := by rw [Nat.mul_succ]; omega
        rw [he]; omega
      exact (mem_iff_lt_numReps M pc r Nc (kd_b + 1) hpc).mp hpos
    set ke := numReps M pc r Nc - 1 with hkedef
    have hke_lt : ke < numReps M pc r Nc := by rw [hkedef]; omega
    have hke_memNc : M + r + pc * ke < Nc := (mem_iff_lt_numReps M pc r Nc ke hpc).mpr hke_lt
    have hkne : ke ≠ kd_b := by rw [hkedef]; omega
    have hbnd : SliceDstar.selBvecVal F M r PR true 0 ke = F (M + r + pc * ke) := by
      funext i; rw [hrec i r ke]; simp only [SliceDstar.selBvecVal, if_true]
    have hdom := SliceDstarBridge.selBvec_le_member F PR true hrec (iff_of_true rfl hslope)
      r Nc kd_b hkd_b
    rw [hbnd] at hdom
    exact finish ke hkne hke_memNc hdom
  · have hkne : (0 : ℕ) ≠ kd_b := by
      intro h; rw [← h, Nat.mul_zero, Nat.add_zero] at hjeq_b; omega
    have hbnd : SliceDstar.selBvecVal F M r PR false 0 (numReps M pc r Nc - 1)
        = F (M + r + pc * 0) := by
      funext i
      simp only [SliceDstar.selBvecVal, Bool.false_eq_true, if_false, Nat.cast_zero, zero_mul,
        add_zero, Nat.mul_zero]
    have hdom := SliceDstarBridge.selBvec_le_member F PR false hrec
      (iff_of_false Bool.false_ne_true hslope) r Nc kd_b hkd_b
    rw [hbnd] at hdom
    exact finish 0 hkne (by rw [Nat.mul_zero, Nat.add_zero]; omega) hdom

/-- **Per-class uniformity math core (generic position `posOf`).**  Affine-in-depth rank (`hF`/`hag`) +
selection-constancy on each `pc`-class (`hselconst`) + a deep-interior achiever (`M+pc ≤ l_b`,
`l_b+pc < Nc`, `F l_b = d*`) ⟹ the whole residue class of `l_b` (over `[M, mS-1)`) equals `d*`.  The
class endpoint (selBvec lex-min over band `Nc`) is selected-D via `hselconst`, bounded below by `d*` via
`dstarRankGA'_lex_min`; being interior, `l_b ≠` endpoint, so `class_uniform_of_dom` collapses the class
(slope 0).  `posOf = fun l => mS+2n+1+l` (suffix `D`-run) or `id` (prefix `U`-run). -/
theorem run_class_uniform_core
    (P : WRP.Presentation Step Step) (hV : P.Valid) (harity1 : ∀ c, P.toPoly.arity c = 1)
    (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c)) (ī0 : Fin (P.toPoly.arity c) → ℕ)
    (mS n : ℕ)
    (pc M Nc : ℕ) (F : ℕ → Fin P.d → ℤ) (hpc : 1 ≤ pc)
    (hF : RankAffineAtFrom M pc F)
    (posOf : ℕ → ℕ)
    (hposval : ∀ l', l' < mS - 1 → posOf l' < (copiedSlice mS n).length)
    (hag : ∀ l', l' < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update ī0 j0 (posOf l')) = F l')
    (hselconst : ∀ l₁ l₂, M ≤ l₁ → l₁ < Nc → M ≤ l₂ → l₂ < Nc →
        (l₁ - M) % pc = (l₂ - M) % pc →
        ((P.toPoly.sel c (copiedSlice mS n) (fun _ => posOf l₁)
            ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => posOf l₁) = D)
          ↔ (P.toPoly.sel c (copiedSlice mS n) (fun _ => posOf l₂)
            ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => posOf l₂) = D)))
    (hNcmS : Nc ≤ mS - 1)
    (l_b : ℕ) (hl_b_lo : M + pc ≤ l_b) (hl_bNc : l_b + pc < Nc)
    (hselb : P.toPoly.sel c (copiedSlice mS n) (fun _ => posOf l_b)
        ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => posOf l_b) = D)
    (hach : F l_b = CopiedDstar.dstarRankGA_m P hV mS n) :
    ∀ l', M ≤ l' → l' < mS - 1 → (l' - M) % pc = (l_b - M) % pc →
      F l' = CopiedDstar.dstarRankGA_m P hV mS n := by
  classical
  have hsub : Subsingleton (Fin (P.toPoly.arity c)) := by rw [harity1 c]; infer_instance
  have hupd : ∀ v : ℕ, Function.update ī0 j0 v = (fun _ => v) := by
    intro v; funext i; rw [Subsingleton.elim i j0]; simp
  obtain ⟨PR, hPR⟩ := hF
  have hrec : ∀ (i : Fin P.d) (r' k : ℕ), F (M + r' + pc * k) i = F (M + r') i + k * PR i := by
    intro i r' k
    have hit := congrFun (SliceRankAtom.RankAffine.iterate hPR (M + r') k (by omega)) i
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at hit
    exact hit
  set dstar := CopiedDstar.dstarRankGA_m P hV mS n with hdstar
  set r := (l_b - M) % pc with hrdef
  set kd_b := (l_b - M) / pc with hkdbdef
  have hrlt : r < pc := by rw [hrdef]; exact Nat.mod_lt _ hpc
  have hjeq_b : M + r + pc * kd_b = l_b := by
    rw [hrdef, hkdbdef]; have := Nat.mod_add_div (l_b - M) pc; omega
  set Fc := fun κ => F (M + r + pc * κ) with hFcdef
  have hrecFc : ∀ κ (i : Fin P.d), Fc κ i = Fc 0 i + (κ : ℤ) * PR i := by
    intro κ i
    show F (M + r + pc * κ) i = F (M + r + pc * 0) i + (κ : ℤ) * PR i
    rw [Nat.mul_zero, Nat.add_zero, hrec i r κ]
  have hD : ∃ a, P.toPoly.selectedAtom (copiedSlice mS n) a
      ∧ P.toPoly.labelOf (copiedSlice mS n) a = D :=
    ⟨⟨c, fun _ => posOf l_b⟩, ⟨fun _ => hposval l_b (by omega), hselb.1⟩, hselb.2⟩
  -- the common finisher: given an endpoint index `ke` distinct from `kd_b`, dominating the class,
  -- conclude the whole class equals d*
  have finish : ∀ (ke : ℕ), ke ≠ kd_b → M + r + pc * ke < Nc →
      ¬ WRP.lexLt (Fc kd_b) (Fc ke) →
      ∀ l', M ≤ l' → l' < mS - 1 → (l' - M) % pc = (l_b - M) % pc → F l' = dstar := by
    intro ke hne hkeNc hdom l' hMl' hl'mS hl'r
    have hkemS : M + r + pc * ke < mS - 1 := by omega
    have hclass_le : (l_b - M) % pc = ((M + r + pc * ke) - M) % pc := by
      rw [show (M + r + pc * ke) - M = r + pc * ke from by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hrlt, hrdef]
    have hsel_le := (hselconst l_b (M + r + pc * ke) (by omega) (by omega) (by omega) hkeNc
      hclass_le).mp hselb
    have hrank_le : P.rankOf (copiedSlice mS n) ⟨c, fun _ => posOf (M + r + pc * ke)⟩ = Fc ke := by
      show P.rank c (copiedSlice mS n) (fun _ => posOf (M + r + pc * ke)) = Fc ke
      rw [← hupd (posOf (M + r + pc * ke)), hag (M + r + pc * ke) hkemS]
    have hglob : ¬ WRP.lexLt (Fc ke) dstar := by
      have hlm := CopiedDstarC.dstarRankGA'_lex_min P hV (copiedSlice mS n) hD
        ⟨c, fun _ => posOf (M + r + pc * ke)⟩ ⟨fun _ => hposval _ hkemS, hsel_le.1⟩ hsel_le.2
      rw [hrank_le] at hlm
      exact hlm
    have hb : Fc kd_b = dstar := by show F (M + r + pc * kd_b) = dstar; rw [hjeq_b]; exact hach
    have hconst := CopiedSufRunGate.class_uniform_of_dom Fc PR dstar hrecFc hne hdom hglob hb
    have hl'eq : M + r + pc * ((l' - M) / pc) = l' := by
      have h1 : (l' - M) % pc = r := by rw [hl'r, hrdef]
      have := Nat.mod_add_div (l' - M) pc
      omega
    have := hconst ((l' - M) / pc)
    show F l' = dstar
    rw [← hl'eq]; exact this
  have hkd_b : kd_b < numReps M pc r Nc :=
    (mem_iff_lt_numReps M pc r Nc kd_b hpc).mp (by rw [hjeq_b]; omega)
  have hnr1 : 1 ≤ numReps M pc r Nc := Nat.lt_of_le_of_lt (Nat.zero_le kd_b) hkd_b
  by_cases hslope : WRP.lexLt PR (fun _ => 0)
  · -- DEEP: F decreasing; endpoint is the deepest class member (index numReps-1)
    have hkd1 : kd_b + 1 < numReps M pc r Nc := by
      have hpos : M + r + pc * (kd_b + 1) < Nc := by
        have he : M + r + pc * (kd_b + 1) = l_b + pc := by rw [Nat.mul_succ]; omega
        rw [he]; omega
      exact (mem_iff_lt_numReps M pc r Nc (kd_b + 1) hpc).mp hpos
    set ke := numReps M pc r Nc - 1 with hkedef
    have hke_lt : ke < numReps M pc r Nc := by rw [hkedef]; omega
    have hke_memNc : M + r + pc * ke < Nc := (mem_iff_lt_numReps M pc r Nc ke hpc).mpr hke_lt
    have hkne : ke ≠ kd_b := by rw [hkedef]; omega
    have hbnd : SliceDstar.selBvecVal F M r PR true 0 ke = F (M + r + pc * ke) := by
      funext i; rw [hrec i r ke]; simp only [SliceDstar.selBvecVal, if_true]
    have hdom := SliceDstarBridge.selBvec_le_member F PR true hrec (iff_of_true rfl hslope)
      r Nc kd_b hkd_b
    rw [hbnd] at hdom
    exact finish ke hkne hke_memNc hdom
  · -- SHALLOW: F nondecreasing; endpoint is the shallowest class member (index 0)
    have hkne : (0 : ℕ) ≠ kd_b := by
      intro h; rw [← h, Nat.mul_zero, Nat.add_zero] at hjeq_b; omega
    have hbnd : SliceDstar.selBvecVal F M r PR false 0 (numReps M pc r Nc - 1)
        = F (M + r + pc * 0) := by
      funext i
      simp only [SliceDstar.selBvecVal, Bool.false_eq_true, if_false, Nat.cast_zero, zero_mul,
        add_zero, Nat.mul_zero]
    have hdom := SliceDstarBridge.selBvec_le_member F PR false hrec
      (iff_of_false Bool.false_ne_true hslope) r Nc kd_b hkd_b
    rw [hbnd] at hdom
    exact finish 0 hkne (by rw [Nat.mul_zero, Nat.add_zero]; omega) hdom
    -- (finish's endpoint bound is now `< Nc`; `M+r < Nc` from `M+r ≤ l_b < Nc`)

/-- Abstract affine-table run-class collapse.  This is the arity-free interface for the
middle-band slope-zero conclusion itself: an interior affine-table achiever forces every depth in
the same class to have the same affine value.  The separate `RunClassUniformCoverage` below is the
bridge-facing constant-tuple-rank form. -/
def RunClassAffineUniformCoverage (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
      (ī0 : Fin (P.toPoly.arity c) → ℕ)
      (mS n pc M Nc : ℕ) (F : ℕ → Fin P.d → ℤ) (_hpc : 1 ≤ pc)
      (_hF : RankAffineAtFrom M pc F)
      (posOf : ℕ → ℕ)
      (_hposval : ∀ l', l' < mS - 1 → posOf l' < (copiedSlice mS n).length)
      (_hag : ∀ l', l' < mS - 1 →
        P.rank c (copiedSlice mS n) (Function.update ī0 j0 (posOf l')) = F l')
      (_hselconst : ∀ l₁ l₂, M ≤ l₁ → l₁ < Nc → M ≤ l₂ → l₂ < Nc →
          (l₁ - M) % pc = (l₂ - M) % pc →
          ((P.toPoly.sel c (copiedSlice mS n) (fun _ => posOf l₁)
              ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => posOf l₁) = D)
            ↔ (P.toPoly.sel c (copiedSlice mS n) (fun _ => posOf l₂)
              ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => posOf l₂) = D)))
      (_hNcmS : Nc ≤ mS - 1)
      (l_b : ℕ) (_hl_b_lo : M + pc ≤ l_b) (_hl_bNc : l_b + pc < Nc)
      (_hselb : P.toPoly.sel c (copiedSlice mS n) (fun _ => posOf l_b)
          ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => posOf l_b) = D)
      (_hach : F l_b = CopiedDstar.dstarRankGA_m P hV mS n),
      ∀ l', M ≤ l' → l' < mS - 1 → (l' - M) % pc = (l_b - M) % pc →
        F l' = CopiedDstar.dstarRankGA_m P hV mS n

/-- Descriptor-facing run-class collapse for update tuples.  This is the
bridge-facing arity-free form: selected-D constancy, the selected witness, and
tuple validity are all stated for `Function.update ī0 j0 (posOf l)`. -/
def RunClassUpdateUniformCoverage (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
      (ī0 : Fin (P.toPoly.arity c) → ℕ)
      (mS n pc M Nc : ℕ) (F : ℕ → Fin P.d → ℤ) (_hpc : 1 ≤ pc)
      (_hF : RankAffineAtFrom M pc F)
      (posOf : ℕ → ℕ)
      (_hupdval : ∀ l', l' < mS - 1 →
        ∀ i, Function.update ī0 j0 (posOf l') i < (copiedSlice mS n).length)
      (_hag : ∀ l', l' < mS - 1 →
        P.rank c (copiedSlice mS n) (Function.update ī0 j0 (posOf l')) = F l')
      (_hselconst : ∀ l₁ l₂, M ≤ l₁ → l₁ < Nc → M ≤ l₂ → l₂ < Nc →
          (l₁ - M) % pc = (l₂ - M) % pc →
          ((P.toPoly.sel c (copiedSlice mS n) (Function.update ī0 j0 (posOf l₁))
              ∧ P.toPoly.label c (copiedSlice mS n)
                (Function.update ī0 j0 (posOf l₁)) = D)
            ↔ (P.toPoly.sel c (copiedSlice mS n) (Function.update ī0 j0 (posOf l₂))
              ∧ P.toPoly.label c (copiedSlice mS n)
                (Function.update ī0 j0 (posOf l₂)) = D)))
      (_hNcmS : Nc ≤ mS - 1)
      (l_b : ℕ) (_hl_b_lo : M + pc ≤ l_b) (_hl_bNc : l_b + pc < Nc)
      (_hselb : P.toPoly.sel c (copiedSlice mS n) (Function.update ī0 j0 (posOf l_b))
          ∧ P.toPoly.label c (copiedSlice mS n)
            (Function.update ī0 j0 (posOf l_b)) = D)
      (_hach : F l_b = CopiedDstar.dstarRankGA_m P hV mS n),
      ∀ l', M ≤ l' → l' < mS - 1 → (l' - M) % pc = (l_b - M) % pc →
        F l' = CopiedDstar.dstarRankGA_m P hV mS n

/-- Public arity-free supplier for update-tuple run-class collapse. -/
theorem runClassUpdateUniformCoverage
    (P : WRP.Presentation Step Step) (hV : P.Valid) :
    RunClassUpdateUniformCoverage P hV := by
  intro c j0 ī0 mS n pc M Nc F hpc hF posOf hupdval hag hselconst hNcmS
    l_b hl_b_lo hl_bNc hselb hach l' hMl' hl'mS hres
  exact run_class_uniform_update_core_of_valid P hV c j0 ī0 mS n pc M Nc F hpc hF
    posOf hupdval hag hselconst hNcmS l_b hl_b_lo hl_bNc hselb hach l' hMl'
    hl'mS hres

/-- Abstract run-class collapse used by the suffix/prefix semantic split.  The
arity-1 proof below supplies it by scalarizing one coordinate; the
arbitrary-arity route should replace that scalarization with descriptor-level
middle-band coverage. -/
def RunClassUniformCoverage (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    ∀ (c : Fin P.toPoly.K) (j0 : Fin (P.toPoly.arity c))
      (ī0 : Fin (P.toPoly.arity c) → ℕ)
      (mS n pc M Nc : ℕ) (F : ℕ → Fin P.d → ℤ) (_hpc : 1 ≤ pc)
      (_hF : RankAffineAtFrom M pc F)
      (posOf : ℕ → ℕ)
      (_hposval : ∀ l', l' < mS - 1 → posOf l' < (copiedSlice mS n).length)
      (_hag : ∀ l', l' < mS - 1 →
        P.rank c (copiedSlice mS n) (Function.update ī0 j0 (posOf l')) = F l')
      (_hselconst : ∀ l₁ l₂, M ≤ l₁ → l₁ < Nc → M ≤ l₂ → l₂ < Nc →
          (l₁ - M) % pc = (l₂ - M) % pc →
          ((P.toPoly.sel c (copiedSlice mS n) (fun _ => posOf l₁)
              ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => posOf l₁) = D)
            ↔ (P.toPoly.sel c (copiedSlice mS n) (fun _ => posOf l₂)
              ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => posOf l₂) = D)))
      (_hNcmS : Nc ≤ mS - 1)
      (l_b : ℕ) (_hl_b_lo : M + pc ≤ l_b) (_hl_bNc : l_b + pc < Nc)
      (_hselb : P.toPoly.sel c (copiedSlice mS n) (fun _ => posOf l_b)
          ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => posOf l_b) = D)
      (_hach : P.rank c (copiedSlice mS n) (fun _ => posOf l_b)
          = CopiedDstar.dstarRankGA_m P hV mS n),
      ∀ l', M ≤ l' → l' < mS - 1 → (l' - M) % pc = (l_b - M) % pc →
        P.rank c (copiedSlice mS n) (fun _ => posOf l')
          = CopiedDstar.dstarRankGA_m P hV mS n

/-! ## (4a-3) atom packaging — `hsufUniform`/`hpreUniform` in the `gate_semantic_split` shape -/

/-- Supply `run_class_uniform_core`'s `hselconst` (suffix `D`-run, band `Nc`) from `selRun_suf_const`:
two same-class (mod `pc`) deep positions differ by `pc·κ`, exactly the shift the G2 wrapper handles; the
deep margin `T + Nc + 1 ≤ mS` is what keeps the shifted mark in the run. -/
theorem selconst_suf
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hM : ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        (M.accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (mS n pc T Nc : ℕ) (hm1 : 1 ≤ mS) (hNcm : T + Nc + 1 ≤ mS)
    (hgate : ∀ κ b, T ≤ b →
      (fun q => M.δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun q => M.δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) :
    ∀ l₁ l₂, T ≤ l₁ → l₁ < Nc → T ≤ l₂ → l₂ < Nc → (l₁ - T) % pc = (l₂ - T) % pc →
      ((P.toPoly.sel c (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₁)
          ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₁) = D)
        ↔ (P.toPoly.sel c (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₂)
          ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + l₂) = D)) := by
  have onedir : ∀ a d, T ≤ a → a ≤ d → d < Nc → (a - T) % pc = (d - T) % pc →
      ((P.toPoly.sel c (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + a)
          ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + a) = D)
        ↔ (P.toPoly.sel c (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + d)
          ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + d) = D)) := by
    intro a d hTa had hdNc hres
    obtain ⟨κ, hκ⟩ : pc ∣ (d - T) - (a - T) := (Nat.modEq_iff_dvd' (by omega)).mp hres
    have hdeq : d = a + pc * κ := by omega
    have := selRun_suf_const P c M hM mS n a pc T κ hm1 (fun b hb => hgate κ b hb) hTa (by omega)
    rw [hdeq]; exact this
  intro l₁ l₂ hT1 h1 hT2 h2 hres
  rcases le_total l₁ l₂ with hle | hle
  · exact onedir l₁ l₂ hT1 hle h2 hres
  · exact (onedir l₂ l₁ hT2 hle h1 hres.symm).symm

/-- Prefix twin of `selconst_suf` (initial `U`-run, positions `fun _ => l`). -/
theorem selconst_pre
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (M : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hM : ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        (M.accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (mS n pc T Nc : ℕ) (hm1 : 1 ≤ mS) (hNcm : T + Nc + 1 ≤ mS)
    (hgate : ∀ κ b, T ≤ b →
      (fun q => M.δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun q => M.δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) :
    ∀ l₁ l₂, T ≤ l₁ → l₁ < Nc → T ≤ l₂ → l₂ < Nc → (l₁ - T) % pc = (l₂ - T) % pc →
      ((P.toPoly.sel c (copiedSlice mS n) (fun _ => l₁)
          ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => l₁) = D)
        ↔ (P.toPoly.sel c (copiedSlice mS n) (fun _ => l₂)
          ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => l₂) = D)) := by
  have onedir : ∀ a d, T ≤ a → a ≤ d → d < Nc → (a - T) % pc = (d - T) % pc →
      ((P.toPoly.sel c (copiedSlice mS n) (fun _ => a)
          ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => a) = D)
        ↔ (P.toPoly.sel c (copiedSlice mS n) (fun _ => d)
          ∧ P.toPoly.label c (copiedSlice mS n) (fun _ => d) = D)) := by
    intro a d hTa had hdNc hres
    obtain ⟨κ, hκ⟩ : pc ∣ (d - T) - (a - T) := (Nat.modEq_iff_dvd' (by omega)).mp hres
    have hdeq : d = a + pc * κ := by omega
    have := selRun_pre_const P c M hM mS n a pc T κ hm1 (fun b hb => hgate κ b hb) hTa (by omega)
    rw [hdeq]; exact this
  intro l₁ l₂ hT1 h1 hT2 h2 hres
  rcases le_total l₁ l₂ with hle | hle
  · exact onedir l₁ l₂ hT1 hle h2 hres
  · exact (onedir l₂ l₁ hT2 hle h1 hres.symm).symm

/-- Windowed suffix selection-constancy for update tuples.  If all non-moving
coordinates stay outside a clear suffix window `[s,e)`, and every depth in the
class band `[Mcls,Nc)` lies far enough from both window boundaries, then
same-`pc` class depths have the same selected-`D` truth value for the
distinguished-coordinate update tuple. -/
theorem selconst_suf_update_window
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Md : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hMd : ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        (Md.accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (mS n pc Mcls Nc s e mper : ℕ) (hm1 : 1 ≤ mS)
    (ī0 : Fin (P.toPoly.arity c) → ℕ) (j0 : Fin (P.toPoly.arity c))
    (hī0val : ∀ i, ī0 i < (copiedSlice mS n).length)
    (hwin : ∀ l, Mcls ≤ l → l < Nc → s ≤ l ∧ l < e)
    (heL : e ≤ mS - 1)
    (hgap : ∀ l, Mcls ≤ l → l < Nc → mper ≤ l - s ∧ mper ≤ e - 1 - l)
    (hclear : ∀ i, i ≠ j0 →
      ī0 i < mS + 2 * n + 1 + s ∨ mS + 2 * n + 1 + e ≤ ī0 i)
    (hgate : ∀ κ b, mper ≤ b →
      (fun q => Md.δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pc * κ]
        = (fun q => Md.δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) :
    ∀ l₁ l₂, Mcls ≤ l₁ → l₁ < Nc → Mcls ≤ l₂ → l₂ < Nc →
      (l₁ - Mcls) % pc = (l₂ - Mcls) % pc →
      ((P.toPoly.sel c (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + l₁))
          ∧ P.toPoly.label c (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + l₁)) = D)
        ↔ (P.toPoly.sel c (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + l₂))
          ∧ P.toPoly.label c (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + l₂)) = D)) := by
  have hvalUpdate : ∀ l, Mcls ≤ l → l < Nc →
      ∀ i, Function.update ī0 j0 (mS + 2 * n + 1 + l) i < (copiedSlice mS n).length := by
    intro l hMl hlNc i
    by_cases hi : i = j0
    · subst i
      simp [Function.update]
      rw [length_copiedSlice]
      have hle : l < mS - 1 := by
        have hw := hwin l hMl hlNc
        omega
      omega
    · simp [Function.update, hi, hī0val i]
  have onedir : ∀ a d, Mcls ≤ a → a ≤ d → d < Nc →
      (a - Mcls) % pc = (d - Mcls) % pc →
      ((P.toPoly.sel c (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + a))
          ∧ P.toPoly.label c (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + a)) = D)
        ↔ (P.toPoly.sel c (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + d))
          ∧ P.toPoly.label c (copiedSlice mS n)
            (Function.update ī0 j0 (mS + 2 * n + 1 + d)) = D)) := by
    intro a d hMa had hdNc hres
    have hMdle : Mcls ≤ d := by omega
    have haNc : a < Nc := by omega
    obtain ⟨hsa, hae⟩ := hwin a hMa haNc
    obtain ⟨hsd, hde⟩ := hwin d hMdle hdNc
    obtain ⟨hgapAa, hgapRa⟩ := hgap a hMa haNc
    obtain ⟨hgapAd, hgapRd⟩ := hgap d hMdle hdNc
    obtain ⟨κ, hκ⟩ : pc ∣ (d - Mcls) - (a - Mcls) :=
      (Nat.modEq_iff_dvd' (by omega)).mp hres
    have hdeq : d = a + pc * κ := by omega
    exact selRun_suf_update_shift P c Md hMd mS n hm1
      (Function.update ī0 j0 (mS + 2 * n + 1 + a))
      (Function.update ī0 j0 (mS + 2 * n + 1 + d)) j0 s e a d κ mper pc hgate
      (hvalUpdate a hMa haNc) (hvalUpdate d hMdle hdNc)
      (by intro i hi; simp [Function.update, hi])
      (by omega) heL hsa hae hsd hde
      (by simp [Function.update])
      (by simp [Function.update])
      (by intro i hi; simpa [Function.update, hi] using hclear i hi)
      hgapAa hgapAd hgapRa hgapRd (Or.inl hdeq)
  intro l₁ l₂ hM1 h1 hM2 h2 hres
  rcases le_total l₁ l₂ with hle | hle
  · exact onedir l₁ l₂ hM1 hle h2 hres
  · exact (onedir l₂ l₁ hM2 hle h1 hres.symm).symm

/-- Prefix twin of `selconst_suf_update_window`. -/
theorem selconst_pre_update_window
    (P : WRP.Presentation Step Step) (c : Fin P.toPoly.K)
    (Md : SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hMd : ∀ (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        (Md.accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (mS n pc Mcls Nc s e mper : ℕ) (hm1 : 1 ≤ mS)
    (ī0 : Fin (P.toPoly.arity c) → ℕ) (j0 : Fin (P.toPoly.arity c))
    (hī0val : ∀ i, ī0 i < (copiedSlice mS n).length)
    (hwin : ∀ l, Mcls ≤ l → l < Nc → s ≤ l ∧ l < e)
    (heL : e ≤ mS - 1)
    (hgap : ∀ l, Mcls ≤ l → l < Nc → mper ≤ l - s ∧ mper ≤ e - 1 - l)
    (hclear : ∀ i, i ≠ j0 → ī0 i < s ∨ e ≤ ī0 i)
    (hgate : ∀ κ b, mper ≤ b →
      (fun q => Md.δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pc * κ]
        = (fun q => Md.δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) :
    ∀ l₁ l₂, Mcls ≤ l₁ → l₁ < Nc → Mcls ≤ l₂ → l₂ < Nc →
      (l₁ - Mcls) % pc = (l₂ - Mcls) % pc →
      ((P.toPoly.sel c (copiedSlice mS n) (Function.update ī0 j0 l₁)
          ∧ P.toPoly.label c (copiedSlice mS n) (Function.update ī0 j0 l₁) = D)
        ↔ (P.toPoly.sel c (copiedSlice mS n) (Function.update ī0 j0 l₂)
          ∧ P.toPoly.label c (copiedSlice mS n) (Function.update ī0 j0 l₂) = D)) := by
  have hvalUpdate : ∀ l, Mcls ≤ l → l < Nc →
      ∀ i, Function.update ī0 j0 l i < (copiedSlice mS n).length := by
    intro l hMl hlNc i
    by_cases hi : i = j0
    · subst i
      simp [Function.update]
      rw [length_copiedSlice]
      have hle : l < mS - 1 := by
        have hw := hwin l hMl hlNc
        omega
      omega
    · simp [Function.update, hi, hī0val i]
  have onedir : ∀ a d, Mcls ≤ a → a ≤ d → d < Nc →
      (a - Mcls) % pc = (d - Mcls) % pc →
      ((P.toPoly.sel c (copiedSlice mS n) (Function.update ī0 j0 a)
          ∧ P.toPoly.label c (copiedSlice mS n) (Function.update ī0 j0 a) = D)
        ↔ (P.toPoly.sel c (copiedSlice mS n) (Function.update ī0 j0 d)
          ∧ P.toPoly.label c (copiedSlice mS n) (Function.update ī0 j0 d) = D)) := by
    intro a d hMa had hdNc hres
    have hMdle : Mcls ≤ d := by omega
    have haNc : a < Nc := by omega
    obtain ⟨hsa, hae⟩ := hwin a hMa haNc
    obtain ⟨hsd, hde⟩ := hwin d hMdle hdNc
    obtain ⟨hgapAa, hgapRa⟩ := hgap a hMa haNc
    obtain ⟨hgapAd, hgapRd⟩ := hgap d hMdle hdNc
    obtain ⟨κ, hκ⟩ : pc ∣ (d - Mcls) - (a - Mcls) :=
      (Nat.modEq_iff_dvd' (by omega)).mp hres
    have hdeq : d = a + pc * κ := by omega
    exact selRun_pre_update_shift P c Md hMd mS n hm1
      (Function.update ī0 j0 a) (Function.update ī0 j0 d) j0 s e a d κ mper pc hgate
      (hvalUpdate a hMa haNc) (hvalUpdate d hMdle hdNc)
      (by intro i hi; simp [Function.update, hi])
      (by omega) heL hsa hae hsd hde
      (by simp [Function.update])
      (by simp [Function.update])
      (by intro i hi; simpa [Function.update, hi] using hclear i hi)
      hgapAa hgapAd hgapRa hgapRd (Or.inl hdeq)
  intro l₁ l₂ hM1 h1 hM2 h2 hres
  rcases le_total l₁ l₂ with hle | hle
  · exact onedir l₁ l₂ hM1 hle h2 hres
  · exact (onedir l₂ l₁ hM2 hle h1 hres.symm).symm

/-- **(4a-3) atom packaging — suffix.**  `hsufUniform` in the EXACT shape consumed by
`CopiedSufRunGate.gate_semantic_split`, for the slice predicates pinned by `tie_count_fibred_of_gate`
(`selD = selectedAtom ∧ labelOf = D`, `ach = rankOf = dstarRankGA_m`).  A deep-interior final-`D`-run
achiever forces every same-class selected competitor to also achieve d*.  `cls` is
`Nat.pair`(copy, depth mod `pc`), so equal `cls` ⟹ same copy and same residue; the per-class collapse is
`run_class_uniform_core` fed by `selconst_suf`.  Takes the marshalled per-copy data (`Mc`/`hMc`,
`pcF`/`TF`/`FF`, the gate cycle `hgate`, the affine rank `hF`/`hag`) — supplied by
`dstar_setup_fibred` + `coordCands_cycle_lengths` at the call site. -/
theorem hsufUniform_slice
    (P : WRP.Presentation Step Step) (hV : P.Valid) (hRunClass : RunClassUniformCoverage P hV)
    (mS n : ℕ) (hm1 : 1 ≤ mS)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hMc : ∀ c (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (pcF TF : Fin P.toPoly.K → ℕ) (hpcF : ∀ c, 1 ≤ pcF c)
    (Nc : ℕ) (hNcmS : Nc ≤ mS - 1) (hNcm : ∀ c, TF c + Nc + 1 ≤ mS)
    (FF : (c : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    (ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ)
    (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c))
    (hF : ∀ c, RankAffineAtFrom (TF c) (pcF c) (FF c))
    (hag : ∀ c l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l)) = FF c l)
    (hgate : ∀ c κ b, TF c ≤ b →
      (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pcF c * κ]
        = (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) :
    ∀ b : P.toPoly.Atom,
      (∃ l, TF b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧ b.2 = fun _ => mS + 2 * n + 1 + l) →
      (P.toPoly.selectedAtom (copiedSlice mS n) b
        ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      ∀ b' : P.toPoly.Atom,
        (∃ l, TF b'.1 + pcF b'.1 ≤ l ∧ l + pcF b'.1 < Nc ∧ b'.2 = fun _ => mS + 2 * n + 1 + l) →
        Nat.pair b'.1.val ((b'.2 (j0F b'.1)) % pcF b'.1)
          = Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) →
        (P.toPoly.selectedAtom (copiedSlice mS n) b'
          ∧ P.toPoly.labelOf (copiedSlice mS n) b' = D) →
        P.rankOf (copiedSlice mS n) b' = CopiedDstar.dstarRankGA_m P hV mS n := by
  classical
  rintro ⟨cb, ib⟩ ⟨lb, hlo, hhi, hib⟩ hselb hachb ⟨cb', ib'⟩ ⟨lb', hlo', hhi', hib'⟩ hcls hselb'
  dsimp only at hlo hhi hib hlo' hhi' hib' hcls
  rw [hib, hib'] at hcls
  dsimp only at hcls
  have hdec : cb'.val = cb.val
      ∧ (mS + 2 * n + 1 + lb') % pcF cb' = (mS + 2 * n + 1 + lb) % pcF cb := by
    have h := congrArg Nat.unpair hcls
    rwa [Nat.unpair_pair, Nat.unpair_pair, Prod.mk.injEq] at h
  obtain ⟨hcopyval, hreseq⟩ := hdec
  have hcopy : cb' = cb := Fin.val_injective hcopyval
  subst cb'
  have hselb_sl : P.toPoly.sel cb (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + lb)
      ∧ P.toPoly.label cb (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + lb) = D := by
    refine ⟨?_, ?_⟩
    · have h := hselb.1; rw [hib] at h; exact h.2
    · have h := hselb.2; rw [hib] at h; exact h
  have hachRun :
      P.rank cb (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + lb)
        = CopiedDstar.dstarRankGA_m P hV mS n := by
    show P.rank cb (copiedSlice mS n) (fun _ => mS + 2 * n + 1 + lb)
      = CopiedDstar.dstarRankGA_m P hV mS n
    rw [hib] at hachb
    exact hachb
  have hcollapse := hRunClass cb (j0F cb) (ī0F cb) mS n
    (pcF cb) (TF cb) Nc (FF cb) (hpcF cb) (hF cb) (fun l => mS + 2 * n + 1 + l)
    (fun l' hl' => by
      show mS + 2 * n + 1 + l' < (copiedSlice mS n).length
      rw [length_copiedSlice]; omega)
    (hag cb)
    (selconst_suf P cb (Mc cb) (hMc cb) mS n (pcF cb) (TF cb) Nc hm1 (hNcm cb) (hgate cb))
    hNcmS lb hlo hhi hselb_sl hachRun
  have hresM : (lb' - TF cb) % pcF cb = (lb - TF cb) % pcF cb := by
    have hmod : (lb' - TF cb) ≡ (lb - TF cb) [MOD pcF cb] := by
      apply Nat.ModEq.add_right_cancel' (TF cb)
      rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
      exact Nat.ModEq.add_left_cancel' (mS + 2 * n + 1) hreseq
    exact hmod
  have hFlb' := hcollapse lb' (by omega) (by omega) hresM
  show P.rank cb (copiedSlice mS n) ib' = CopiedDstar.dstarRankGA_m P hV mS n
  rw [hib']
  exact hFlb'

/-- **(4a-3) atom packaging — prefix.**  Prefix twin of `hsufUniform_slice` for the initial `U`-run
(positions `fun _ => l`, `posOf = id`, the `U`-letter gate cycle and `selconst_pre`). -/
theorem hpreUniform_slice
    (P : WRP.Presentation Step Step) (hV : P.Valid) (hRunClass : RunClassUniformCoverage P hV)
    (mS n : ℕ) (hm1 : 1 ≤ mS)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hMc : ∀ c (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (pcF TF : Fin P.toPoly.K → ℕ) (hpcF : ∀ c, 1 ≤ pcF c)
    (Nc : ℕ) (hNcmS : Nc ≤ mS - 1) (hNcm : ∀ c, TF c + Nc + 1 ≤ mS)
    (FF : (c : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    (ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ)
    (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c))
    (hF : ∀ c, RankAffineAtFrom (TF c) (pcF c) (FF c))
    (hag : ∀ c l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l) = FF c l)
    (hgate : ∀ c κ b, TF c ≤ b →
      (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pcF c * κ]
        = (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) :
    ∀ b : P.toPoly.Atom,
      (∃ l, TF b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧ b.2 = fun _ => l) →
      (P.toPoly.selectedAtom (copiedSlice mS n) b
        ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      ∀ b' : P.toPoly.Atom,
        (∃ l, TF b'.1 + pcF b'.1 ≤ l ∧ l + pcF b'.1 < Nc ∧ b'.2 = fun _ => l) →
        Nat.pair b'.1.val ((b'.2 (j0F b'.1)) % pcF b'.1)
          = Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) →
        (P.toPoly.selectedAtom (copiedSlice mS n) b'
          ∧ P.toPoly.labelOf (copiedSlice mS n) b' = D) →
        P.rankOf (copiedSlice mS n) b' = CopiedDstar.dstarRankGA_m P hV mS n := by
  classical
  rintro ⟨cb, ib⟩ ⟨lb, hlo, hhi, hib⟩ hselb hachb ⟨cb', ib'⟩ ⟨lb', hlo', hhi', hib'⟩ hcls hselb'
  dsimp only at hlo hhi hib hlo' hhi' hib' hcls
  rw [hib, hib'] at hcls
  dsimp only at hcls
  have hdec : cb'.val = cb.val ∧ lb' % pcF cb' = lb % pcF cb := by
    have h := congrArg Nat.unpair hcls
    rwa [Nat.unpair_pair, Nat.unpair_pair, Prod.mk.injEq] at h
  obtain ⟨hcopyval, hreseq⟩ := hdec
  have hcopy : cb' = cb := Fin.val_injective hcopyval
  subst cb'
  have hselb_sl : P.toPoly.sel cb (copiedSlice mS n) (fun _ => lb)
      ∧ P.toPoly.label cb (copiedSlice mS n) (fun _ => lb) = D := by
    refine ⟨?_, ?_⟩
    · have h := hselb.1; rw [hib] at h; exact h.2
    · have h := hselb.2; rw [hib] at h; exact h
  have hachRun :
      P.rank cb (copiedSlice mS n) (fun _ => lb)
        = CopiedDstar.dstarRankGA_m P hV mS n := by
    show P.rank cb (copiedSlice mS n) (fun _ => lb)
      = CopiedDstar.dstarRankGA_m P hV mS n
    rw [hib] at hachb
    exact hachb
  have hcollapse := hRunClass cb (j0F cb) (ī0F cb) mS n
    (pcF cb) (TF cb) Nc (FF cb) (hpcF cb) (hF cb) (fun l => l)
    (fun l' hl' => by
      show l' < (copiedSlice mS n).length
      rw [length_copiedSlice]; omega)
    (hag cb)
    (selconst_pre P cb (Mc cb) (hMc cb) mS n (pcF cb) (TF cb) Nc hm1 (hNcm cb) (hgate cb))
    hNcmS lb hlo hhi hselb_sl hachRun
  have hresM : (lb' - TF cb) % pcF cb = (lb - TF cb) % pcF cb := by
    have hmod : (lb' - TF cb) ≡ (lb - TF cb) [MOD pcF cb] := by
      apply Nat.ModEq.add_right_cancel' (TF cb)
      rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
      exact hreseq
    exact hmod
  have hFlb' := hcollapse lb' (by omega) (by omega) hresM
  show P.rank cb (copiedSlice mS n) ib' = CopiedDstar.dstarRankGA_m P hV mS n
  rw [hib']
  exact hFlb'

/-- Update-tuple suffix atom packaging.  This is the descriptor-facing analogue
of `hsufUniform_slice`: the suffix-run atoms are `Function.update` tuples, and
the selected-D constancy is supplied directly in the same update-tuple shape. -/
theorem hsufUniform_update_slice
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hRunClass : RunClassUpdateUniformCoverage P hV)
    (mS n : ℕ)
    (pcF TF : Fin P.toPoly.K → ℕ) (hpcF : ∀ c, 1 ≤ pcF c)
    (Nc : ℕ) (hNcmS : Nc ≤ mS - 1)
    (FF : (c : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    (ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ)
    (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c))
    (hF : ∀ c, RankAffineAtFrom (TF c) (pcF c) (FF c))
    (hupdval : ∀ c l, l < mS - 1 →
      ∀ i, Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l) i
        < (copiedSlice mS n).length)
    (hag : ∀ c l, l < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l)) = FF c l)
    (hselconst : ∀ c, ∀ l₁ l₂, TF c ≤ l₁ → l₁ < Nc → TF c ≤ l₂ → l₂ < Nc →
        (l₁ - TF c) % pcF c = (l₂ - TF c) % pcF c →
        ((P.toPoly.sel c (copiedSlice mS n)
              (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₁))
            ∧ P.toPoly.label c (copiedSlice mS n)
              (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₁)) = D)
          ↔ (P.toPoly.sel c (copiedSlice mS n)
              (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₂))
            ∧ P.toPoly.label c (copiedSlice mS n)
              (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₂)) = D))) :
    ∀ b : P.toPoly.Atom,
      (∃ l, TF b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (ī0F b.1) (j0F b.1) (mS + 2 * n + 1 + l)) →
      (P.toPoly.selectedAtom (copiedSlice mS n) b
        ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      ∀ b' : P.toPoly.Atom,
        (∃ l, TF b'.1 + pcF b'.1 ≤ l ∧ l + pcF b'.1 < Nc ∧
          b'.2 = Function.update (ī0F b'.1) (j0F b'.1) (mS + 2 * n + 1 + l)) →
        Nat.pair b'.1.val ((b'.2 (j0F b'.1)) % pcF b'.1)
          = Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) →
        (P.toPoly.selectedAtom (copiedSlice mS n) b'
          ∧ P.toPoly.labelOf (copiedSlice mS n) b' = D) →
        P.rankOf (copiedSlice mS n) b' = CopiedDstar.dstarRankGA_m P hV mS n := by
  classical
  rintro ⟨cb, ib⟩ ⟨lb, hlo, hhi, hib⟩ hselb hachb ⟨cb', ib'⟩ ⟨lb', hlo', hhi', hib'⟩ hcls hselb'
  dsimp only at hlo hhi hib hlo' hhi' hib' hcls
  rw [hib, hib'] at hcls
  simp only [Function.update_self] at hcls
  have hdec : cb'.val = cb.val
      ∧ (mS + 2 * n + 1 + lb') % pcF cb' = (mS + 2 * n + 1 + lb) % pcF cb := by
    have h := congrArg Nat.unpair hcls
    rwa [Nat.unpair_pair, Nat.unpair_pair, Prod.mk.injEq] at h
  obtain ⟨hcopyval, hreseq⟩ := hdec
  have hcopy : cb' = cb := Fin.val_injective hcopyval
  subst cb'
  have hlm : lb < mS - 1 := by
    have := hpcF cb
    omega
  have hlm' : lb' < mS - 1 := by
    have := hpcF cb
    omega
  have hselb_sl :
      P.toPoly.sel cb (copiedSlice mS n)
          (Function.update (ī0F cb) (j0F cb) (mS + 2 * n + 1 + lb))
        ∧ P.toPoly.label cb (copiedSlice mS n)
          (Function.update (ī0F cb) (j0F cb) (mS + 2 * n + 1 + lb)) = D := by
    refine ⟨?_, ?_⟩
    · have h := hselb.1
      rw [hib] at h
      exact h.2
    · have h := hselb.2
      rw [hib] at h
      exact h
  have hachRun :
      P.rank cb (copiedSlice mS n)
          (Function.update (ī0F cb) (j0F cb) (mS + 2 * n + 1 + lb))
        = CopiedDstar.dstarRankGA_m P hV mS n := by
    rw [hib] at hachb
    exact hachb
  have hagb := hag cb lb hlm
  rw [hagb] at hachRun
  have hcollapse := hRunClass cb (j0F cb) (ī0F cb) mS n
    (pcF cb) (TF cb) Nc (FF cb) (hpcF cb) (hF cb)
    (fun l => mS + 2 * n + 1 + l) (hupdval cb) (hag cb) (hselconst cb)
    hNcmS lb hlo hhi hselb_sl hachRun
  have hresM : (lb' - TF cb) % pcF cb = (lb - TF cb) % pcF cb := by
    have hmod : (lb' - TF cb) ≡ (lb - TF cb) [MOD pcF cb] := by
      apply Nat.ModEq.add_right_cancel' (TF cb)
      rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
      exact Nat.ModEq.add_left_cancel' (mS + 2 * n + 1) hreseq
    exact hmod
  have hFlb' := hcollapse lb' (by omega) hlm' hresM
  show P.rank cb (copiedSlice mS n) ib' = CopiedDstar.dstarRankGA_m P hV mS n
  rw [hib', hag cb lb' hlm']
  exact hFlb'

/-- Prefix twin of `hsufUniform_update_slice`. -/
theorem hpreUniform_update_slice
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hRunClass : RunClassUpdateUniformCoverage P hV)
    (mS n : ℕ)
    (pcF TF : Fin P.toPoly.K → ℕ) (hpcF : ∀ c, 1 ≤ pcF c)
    (Nc : ℕ) (hNcmS : Nc ≤ mS - 1)
    (FF : (c : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    (ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ)
    (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c))
    (hF : ∀ c, RankAffineAtFrom (TF c) (pcF c) (FF c))
    (hupdval : ∀ c l, l < mS - 1 →
      ∀ i, Function.update (ī0F c) (j0F c) l i < (copiedSlice mS n).length)
    (hag : ∀ c l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l) = FF c l)
    (hselconst : ∀ c, ∀ l₁ l₂, TF c ≤ l₁ → l₁ < Nc → TF c ≤ l₂ → l₂ < Nc →
        (l₁ - TF c) % pcF c = (l₂ - TF c) % pcF c →
        ((P.toPoly.sel c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₁)
            ∧ P.toPoly.label c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₁) = D)
          ↔ (P.toPoly.sel c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₂)
            ∧ P.toPoly.label c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₂) = D))) :
    ∀ b : P.toPoly.Atom,
      (∃ l, TF b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
        b.2 = Function.update (ī0F b.1) (j0F b.1) l) →
      (P.toPoly.selectedAtom (copiedSlice mS n) b
        ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
      P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
      ∀ b' : P.toPoly.Atom,
        (∃ l, TF b'.1 + pcF b'.1 ≤ l ∧ l + pcF b'.1 < Nc ∧
          b'.2 = Function.update (ī0F b'.1) (j0F b'.1) l) →
        Nat.pair b'.1.val ((b'.2 (j0F b'.1)) % pcF b'.1)
          = Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) →
        (P.toPoly.selectedAtom (copiedSlice mS n) b'
          ∧ P.toPoly.labelOf (copiedSlice mS n) b' = D) →
        P.rankOf (copiedSlice mS n) b' = CopiedDstar.dstarRankGA_m P hV mS n := by
  classical
  rintro ⟨cb, ib⟩ ⟨lb, hlo, hhi, hib⟩ hselb hachb ⟨cb', ib'⟩ ⟨lb', hlo', hhi', hib'⟩ hcls hselb'
  dsimp only at hlo hhi hib hlo' hhi' hib' hcls
  rw [hib, hib'] at hcls
  simp only [Function.update_self] at hcls
  have hdec : cb'.val = cb.val ∧ lb' % pcF cb' = lb % pcF cb := by
    have h := congrArg Nat.unpair hcls
    rwa [Nat.unpair_pair, Nat.unpair_pair, Prod.mk.injEq] at h
  obtain ⟨hcopyval, hreseq⟩ := hdec
  have hcopy : cb' = cb := Fin.val_injective hcopyval
  subst cb'
  have hlm : lb < mS - 1 := by
    have := hpcF cb
    omega
  have hlm' : lb' < mS - 1 := by
    have := hpcF cb
    omega
  have hselb_sl :
      P.toPoly.sel cb (copiedSlice mS n) (Function.update (ī0F cb) (j0F cb) lb)
        ∧ P.toPoly.label cb (copiedSlice mS n) (Function.update (ī0F cb) (j0F cb) lb) = D := by
    refine ⟨?_, ?_⟩
    · have h := hselb.1
      rw [hib] at h
      exact h.2
    · have h := hselb.2
      rw [hib] at h
      exact h
  have hachRun :
      P.rank cb (copiedSlice mS n) (Function.update (ī0F cb) (j0F cb) lb)
        = CopiedDstar.dstarRankGA_m P hV mS n := by
    rw [hib] at hachb
    exact hachb
  have hagb := hag cb lb hlm
  rw [hagb] at hachRun
  have hcollapse := hRunClass cb (j0F cb) (ī0F cb) mS n
    (pcF cb) (TF cb) Nc (FF cb) (hpcF cb) (hF cb)
    (fun l => l) (hupdval cb) (hag cb) (hselconst cb)
    hNcmS lb hlo hhi hselb_sl hachRun
  have hresM : (lb' - TF cb) % pcF cb = (lb - TF cb) % pcF cb := by
    have hmod : (lb' - TF cb) ≡ (lb - TF cb) [MOD pcF cb] := by
      apply Nat.ModEq.add_right_cancel' (TF cb)
      rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
      exact hreseq
    exact hmod
  have hFlb' := hcollapse lb' (by omega) hlm' hresM
  show P.rank cb (copiedSlice mS n) ib' = CopiedDstar.dstarRankGA_m P hV mS n
  rw [hib', hag cb lb' hlm']
  exact hFlb'

/-! ## (4c) the semantic split at the slice — `gate_semantic_split` instantiated with (4a) -/

/-- The slice-level semantic split proposition for the tie competitor quantifier, using the shared
combined period data (`pcF`, `Ts`, `Tp`, `Nc`, `j0F`).  This packages the long conclusion of
`tie_semantic_split_slice` so downstream bridge/counting lemmas can name the split without
repeating all three core/suffix/prefix obligations. -/
def tieSemanticSplitAt
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (mS n : ℕ)
    (c0 : Fin P.toPoly.K) (ī0m : Fin (P.toPoly.arity c0) → ℕ)
    (pcF Ts Tp : Fin P.toPoly.K → ℕ) (Nc : ℕ)
    (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c)) : Prop :=
    (∀ b : P.toPoly.Atom,
        (P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b) ↔
      ((∀ b : P.toPoly.Atom,
          ¬ (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧ b.2 = fun _ => mS + 2 * n + 1 + l) →
          ¬ (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧ b.2 = fun _ => l) →
          (P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
          P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
          P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b)
        ∧ (∀ r : ℕ,
            (∀ b : P.toPoly.Atom,
              (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧ b.2 = fun _ => mS + 2 * n + 1 + l) →
              Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
              (P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
              P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n) →
            (∀ b : P.toPoly.Atom,
              (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧ b.2 = fun _ => mS + 2 * n + 1 + l) →
              Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
              (P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
              P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b))
        ∧ (∀ r : ℕ,
            (∀ b : P.toPoly.Atom,
              (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧ b.2 = fun _ => l) →
              Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
              (P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
              P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n) →
            (∀ b : P.toPoly.Atom,
              (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧ b.2 = fun _ => l) →
              Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
              (P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
              P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b)))

/-- **(4c) semantic split at the slice.**  Instantiates `CopiedSufRunGate.gate_semantic_split` with the
slice predicates pinned by `tie_count_fibred_of_gate` (`selD = selectedAtom ∧ labelOf = D`,
`ach = rankOf = dstarRankGA_m`, `atOrd = atomOrd ⟨c0,ī0m⟩ ·`), fed by `hsufUniform_slice`/
`hpreUniform_slice`.  Both halves use the COMBINED period `pcF = pc_s*pc_p` (lift the per-direction
`coordCands` rank-affines/gate-cycles via `RankAffineAtFrom_mul` / κ-scaling), so the single shared
`cls = Nat.pair b.1.val (b.2 (j0F b.1) % pcF b.1)` serves both directions.  The conclusion is the
tie-membership competitor quantifier `(∀ b sel-D achieving, atomOrd ⟨c0,ī0m⟩ b)` ⟺ CORE (bounded
competitors) ∧ ⋀_r suffix-class-r ∧ ⋀_r prefix-class-r — exactly what the assembled gate must realise. -/
theorem tie_semantic_split_slice
    (P : WRP.Presentation Step Step) (hV : P.Valid) (hRunClass : RunClassUniformCoverage P hV)
    (mS n : ℕ) (hm1 : 1 ≤ mS)
    (c0 : Fin P.toPoly.K) (ī0m : Fin (P.toPoly.arity c0) → ℕ)
    (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
    (hMc : ∀ c (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D)))
    (pcF Ts Tp : Fin P.toPoly.K → ℕ) (hpcF : ∀ c, 1 ≤ pcF c)
    (Nc : ℕ) (hNcmS : Nc ≤ mS - 1)
    (hNcs : ∀ c, Ts c + Nc + 1 ≤ mS) (hNcp : ∀ c, Tp c + Nc + 1 ≤ mS)
    (FFs FFp : (c : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    (ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ)
    (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c))
    (hFs : ∀ c, RankAffineAtFrom (Ts c) (pcF c) (FFs c))
    (hFp : ∀ c, RankAffineAtFrom (Tp c) (pcF c) (FFp c))
    (hags : ∀ c l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l)) = FFs c l)
    (hagp : ∀ c l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l) = FFp c l)
    (hgates : ∀ c κ b, Ts c ≤ b →
      (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pcF c * κ]
        = (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b])
    (hgatep : ∀ c κ b, Tp c ≤ b →
      (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pcF c * κ]
        = (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) :
    tieSemanticSplitAt P hV mS n c0 ī0m pcF Ts Tp Nc j0F :=
  CopiedSufRunGate.gate_semantic_split
    (fun b => P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D)
    (fun b => P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n)
    (fun b => P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b)
    (fun b => ∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧ b.2 = fun _ => mS + 2 * n + 1 + l)
    (fun b => ∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧ b.2 = fun _ => l)
    (fun b => Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1))
    (hsufUniform_slice P hV hRunClass mS n hm1 Mc hMc pcF Ts hpcF Nc hNcmS hNcs FFs
      ī0F j0F hFs hags hgates)
    (hpreUniform_slice P hV hRunClass mS n hm1 Mc hMc pcF Tp hpcF Nc hNcmS hNcp FFp
      ī0F j0F hFp hagp hgatep)

/-- Update-shaped semantic split proposition for descriptor-facing bridge
branches.  The suffix/prefix run classes are represented by the shared base
tuple `ī0F c` with the distinguished coordinate `j0F c` updated to the run
depth. -/
def tieSemanticUpdateSplitAt
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (mS n : ℕ)
    (c0 : Fin P.toPoly.K) (ī0m : Fin (P.toPoly.arity c0) → ℕ)
    (pcF Ts Tp : Fin P.toPoly.K → ℕ) (Nc : ℕ)
    (ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ)
    (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c)) : Prop :=
    (∀ b : P.toPoly.Atom,
        (P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
        P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
        P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b) ↔
      ((∀ b : P.toPoly.Atom,
          ¬ (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
            b.2 = Function.update (ī0F b.1) (j0F b.1) (mS + 2 * n + 1 + l)) →
          ¬ (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
            b.2 = Function.update (ī0F b.1) (j0F b.1) l) →
          (P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
          P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n →
          P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b)
        ∧ (∀ r : ℕ,
            (∀ b : P.toPoly.Atom,
              (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
                b.2 = Function.update (ī0F b.1) (j0F b.1) (mS + 2 * n + 1 + l)) →
              Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
              (P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
              P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n) →
            (∀ b : P.toPoly.Atom,
              (∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
                b.2 = Function.update (ī0F b.1) (j0F b.1) (mS + 2 * n + 1 + l)) →
              Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
              (P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
              P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b))
        ∧ (∀ r : ℕ,
            (∀ b : P.toPoly.Atom,
              (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
                b.2 = Function.update (ī0F b.1) (j0F b.1) l) →
              Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
              (P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
              P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n) →
            (∀ b : P.toPoly.Atom,
              (∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
                b.2 = Function.update (ī0F b.1) (j0F b.1) l) →
              Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1) = r →
              (P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D) →
              P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b)))

/-- Semantic split for the update-shaped suffix/prefix run classes.  The caller
supplies the update-tuple selected-D constancy; `selconst_suf_update_window` and
`selconst_pre_update_window` are the current clear-window suppliers for those
hypotheses. -/
theorem tie_semantic_update_split_slice
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hRunClass : RunClassUpdateUniformCoverage P hV)
    (mS n : ℕ)
    (c0 : Fin P.toPoly.K) (ī0m : Fin (P.toPoly.arity c0) → ℕ)
    (pcF Ts Tp : Fin P.toPoly.K → ℕ) (hpcF : ∀ c, 1 ≤ pcF c)
    (Nc : ℕ) (hNcmS : Nc ≤ mS - 1)
    (FFs FFp : (c : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ)
    (ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ)
    (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c))
    (hFs : ∀ c, RankAffineAtFrom (Ts c) (pcF c) (FFs c))
    (hFp : ∀ c, RankAffineAtFrom (Tp c) (pcF c) (FFp c))
    (hupdvals : ∀ c l, l < mS - 1 →
      ∀ i, Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l) i
        < (copiedSlice mS n).length)
    (hupdvalp : ∀ c l, l < mS - 1 →
      ∀ i, Function.update (ī0F c) (j0F c) l i < (copiedSlice mS n).length)
    (hags : ∀ c l, l < mS - 1 →
      P.rank c (copiedSlice mS n)
        (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l)) = FFs c l)
    (hagp : ∀ c l, l < mS - 1 →
      P.rank c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l) = FFp c l)
    (hselconsts : ∀ c, ∀ l₁ l₂, Ts c ≤ l₁ → l₁ < Nc → Ts c ≤ l₂ → l₂ < Nc →
        (l₁ - Ts c) % pcF c = (l₂ - Ts c) % pcF c →
        ((P.toPoly.sel c (copiedSlice mS n)
              (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₁))
            ∧ P.toPoly.label c (copiedSlice mS n)
              (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₁)) = D)
          ↔ (P.toPoly.sel c (copiedSlice mS n)
              (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₂))
            ∧ P.toPoly.label c (copiedSlice mS n)
              (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₂)) = D)))
    (hselconstp : ∀ c, ∀ l₁ l₂, Tp c ≤ l₁ → l₁ < Nc → Tp c ≤ l₂ → l₂ < Nc →
        (l₁ - Tp c) % pcF c = (l₂ - Tp c) % pcF c →
        ((P.toPoly.sel c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₁)
            ∧ P.toPoly.label c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₁) = D)
          ↔ (P.toPoly.sel c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₂)
            ∧ P.toPoly.label c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₂) = D))) :
    tieSemanticUpdateSplitAt P hV mS n c0 ī0m pcF Ts Tp Nc ī0F j0F :=
  CopiedSufRunGate.gate_semantic_split
    (fun b => P.toPoly.selectedAtom (copiedSlice mS n) b ∧ P.toPoly.labelOf (copiedSlice mS n) b = D)
    (fun b => P.rankOf (copiedSlice mS n) b = CopiedDstar.dstarRankGA_m P hV mS n)
    (fun b => P.toPoly.atomOrd (copiedSlice mS n) ⟨c0, ī0m⟩ b)
    (fun b => ∃ l, Ts b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
      b.2 = Function.update (ī0F b.1) (j0F b.1) (mS + 2 * n + 1 + l))
    (fun b => ∃ l, Tp b.1 + pcF b.1 ≤ l ∧ l + pcF b.1 < Nc ∧
      b.2 = Function.update (ī0F b.1) (j0F b.1) l)
    (fun b => Nat.pair b.1.val ((b.2 (j0F b.1)) % pcF b.1))
    (hsufUniform_update_slice P hV hRunClass mS n pcF Ts hpcF Nc hNcmS FFs
      ī0F j0F hFs hupdvals hags hselconsts)
    (hpreUniform_update_slice P hV hRunClass mS n pcF Tp hpcF Nc hNcmS FFp
      ī0F j0F hFp hupdvalp hagp hselconstp)

/-- Update-shaped semantic split data consumed by the arbitrary-arity bridge
route.  It extends the shared coordinate/rank-affine data with validity for the
updated tuples and the update-shaped semantic split itself.  The clear-window
construction of the selected-D constancy can be hidden behind this package. -/
def TieSemanticUpdateSplitData (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    ∃ (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
      (pcF Ts Tp : Fin P.toPoly.K → ℕ)
      (ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ)
      (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c)) (Mbr : ℕ),
      1 ≤ Mbr ∧ (∀ c, 1 ≤ pcF c) ∧ (∀ c, Ts c ≤ Mbr) ∧ (∀ c, Tp c ≤ Mbr) ∧
      (∀ c (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D))) ∧
      (∀ c κ b, Ts c ≤ b →
        (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pcF c * κ]
          = (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ c κ b, Tp c ≤ b →
        (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pcF c * κ]
          = (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      ∀ mS, Mbr ≤ mS → ∀ n,
        ∃ (FFs FFp : (c : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ) (Nc : ℕ),
          Nc ≤ mS - 1 ∧ mS ≤ Nc + Mbr ∧
          (∀ c, Ts c + Nc + 1 ≤ mS) ∧ (∀ c, Tp c + Nc + 1 ≤ mS) ∧
          (∀ c, RankAffineAtFrom (Ts c) (pcF c) (FFs c)) ∧
          (∀ c, RankAffineAtFrom (Tp c) (pcF c) (FFp c)) ∧
          (∀ c l, l < mS - 1 →
            P.rank c (copiedSlice mS n)
              (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l)) = FFs c l) ∧
          (∀ c l, l < mS - 1 →
            P.rank c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l) = FFp c l) ∧
          (∀ c l, l < mS - 1 →
            ∀ i, Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l) i
              < (copiedSlice mS n).length) ∧
          (∀ c l, l < mS - 1 →
            ∀ i, Function.update (ī0F c) (j0F c) l i < (copiedSlice mS n).length) ∧
          (∀ c, ∀ l₁ l₂, Ts c ≤ l₁ → l₁ < Nc → Ts c ≤ l₂ → l₂ < Nc →
            (l₁ - Ts c) % pcF c = (l₂ - Ts c) % pcF c →
            ((P.toPoly.sel c (copiedSlice mS n)
                  (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₁))
                ∧ P.toPoly.label c (copiedSlice mS n)
                  (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₁)) = D)
              ↔ (P.toPoly.sel c (copiedSlice mS n)
                  (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₂))
                ∧ P.toPoly.label c (copiedSlice mS n)
                  (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₂)) = D))) ∧
          (∀ c, ∀ l₁ l₂, Tp c ≤ l₁ → l₁ < Nc → Tp c ≤ l₂ → l₂ < Nc →
            (l₁ - Tp c) % pcF c = (l₂ - Tp c) % pcF c →
            ((P.toPoly.sel c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₁)
                ∧ P.toPoly.label c (copiedSlice mS n)
                  (Function.update (ī0F c) (j0F c) l₁) = D)
              ↔ (P.toPoly.sel c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₂)
                ∧ P.toPoly.label c (copiedSlice mS n)
                  (Function.update (ī0F c) (j0F c) l₂) = D))) ∧
          (∀ c0 ī0m, tieSemanticUpdateSplitAt P hV mS n c0 ī0m pcF Ts Tp Nc ī0F j0F)

/-- Zero-base refinement of `TieSemanticUpdateSplitData`.  The canonical
arbitrary-arity bridge rows are built for the shared base tuple
`fun _ _ => 0`; this package preserves that fact while retaining the same
destructuring shape as the general update split data. -/
def TieSemanticUpdateZeroSplitData (P : WRP.Presentation Step Step) (hV : P.Valid) :
    Prop :=
    ∃ (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
      (pcF Ts Tp : Fin P.toPoly.K → ℕ)
      (ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ)
      (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c)) (Mbr : ℕ),
      ī0F = (fun _ _ => 0) ∧
      1 ≤ Mbr ∧ (∀ c, 1 ≤ pcF c) ∧ (∀ c, Ts c ≤ Mbr) ∧ (∀ c, Tp c ≤ Mbr) ∧
      (∀ c (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D))) ∧
      (∀ c κ b, Ts c ≤ b →
        (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pcF c * κ]
          = (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ c κ b, Tp c ≤ b →
        (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pcF c * κ]
          = (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      ∀ mS, Mbr ≤ mS → ∀ n,
        ∃ (FFs FFp : (c : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ) (Nc : ℕ),
          Nc ≤ mS - 1 ∧ mS ≤ Nc + Mbr ∧
          (∀ c, Ts c + Nc + 1 ≤ mS) ∧ (∀ c, Tp c + Nc + 1 ≤ mS) ∧
          (∀ c, RankAffineAtFrom (Ts c) (pcF c) (FFs c)) ∧
          (∀ c, RankAffineAtFrom (Tp c) (pcF c) (FFp c)) ∧
          (∀ c l, l < mS - 1 →
            P.rank c (copiedSlice mS n)
              (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l)) = FFs c l) ∧
          (∀ c l, l < mS - 1 →
            P.rank c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l) = FFp c l) ∧
          (∀ c l, l < mS - 1 →
            ∀ i, Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l) i
              < (copiedSlice mS n).length) ∧
          (∀ c l, l < mS - 1 →
            ∀ i, Function.update (ī0F c) (j0F c) l i < (copiedSlice mS n).length) ∧
          (∀ c, ∀ l₁ l₂, Ts c ≤ l₁ → l₁ < Nc → Ts c ≤ l₂ → l₂ < Nc →
            (l₁ - Ts c) % pcF c = (l₂ - Ts c) % pcF c →
            ((P.toPoly.sel c (copiedSlice mS n)
                  (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₁))
                ∧ P.toPoly.label c (copiedSlice mS n)
                  (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₁)) = D)
              ↔ (P.toPoly.sel c (copiedSlice mS n)
                  (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₂))
                ∧ P.toPoly.label c (copiedSlice mS n)
                  (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₂)) = D))) ∧
          (∀ c, ∀ l₁ l₂, Tp c ≤ l₁ → l₁ < Nc → Tp c ≤ l₂ → l₂ < Nc →
            (l₁ - Tp c) % pcF c = (l₂ - Tp c) % pcF c →
            ((P.toPoly.sel c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₁)
                ∧ P.toPoly.label c (copiedSlice mS n)
                  (Function.update (ī0F c) (j0F c) l₁) = D)
              ↔ (P.toPoly.sel c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₂)
                ∧ P.toPoly.label c (copiedSlice mS n)
                  (Function.update (ī0F c) (j0F c) l₂) = D))) ∧
          (∀ c0 ī0m, tieSemanticUpdateSplitAt P hV mS n c0 ī0m pcF Ts Tp Nc ī0F j0F)

/-- Forget the zero-base witness from the canonical update split package. -/
theorem tieSemanticUpdateSplitData_of_zeroSplitData
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hZero : TieSemanticUpdateZeroSplitData P hV) :
    TieSemanticUpdateSplitData P hV := by
  obtain ⟨Mc, pcF, Ts, Tp, ī0F, j0F, Mbr, _hzero, hMbr1, hpcF, hTsMbr,
    hTpMbr, hMc, hsufcyc, hprefcyc, hrows⟩ := hZero
  exact ⟨Mc, pcF, Ts, Tp, ī0F, j0F, Mbr, hMbr1, hpcF, hTsMbr, hTpMbr, hMc,
    hsufcyc, hprefcyc, hrows⟩

/-! ## (4c) marshalling — the combined-period data feeding `tie_semantic_split_slice` -/

/-- Coordinate/cycle data feeding the semantic split, before proving the
suffix/prefix class-collapse obligations.  This separates the pure
`coordCands` plumbing from the semantic run-class coverage supplier. -/
def TieSemanticCoordData (P : WRP.Presentation Step Step) : Prop :=
    ∃ (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
      (pcF Ts Tp : Fin P.toPoly.K → ℕ)
      (ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ)
      (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c)) (Mbr : ℕ),
      1 ≤ Mbr ∧ (∀ c, 1 ≤ pcF c) ∧ (∀ c, Ts c ≤ Mbr) ∧ (∀ c, Tp c ≤ Mbr) ∧
      (∀ c (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D))) ∧
      (∀ c κ b, Ts c ≤ b →
        (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pcF c * κ]
          = (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ c κ b, Tp c ≤ b →
        (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pcF c * κ]
          = (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      ∀ mS, Mbr ≤ mS → ∀ n,
        ∃ (FFs FFp : (c : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ) (Nc : ℕ),
          Nc ≤ mS - 1 ∧ mS ≤ Nc + Mbr ∧
          (∀ c, Ts c + Nc + 1 ≤ mS) ∧ (∀ c, Tp c + Nc + 1 ≤ mS) ∧
          (∀ c, RankAffineAtFrom (Ts c) (pcF c) (FFs c)) ∧
          (∀ c, RankAffineAtFrom (Tp c) (pcF c) (FFp c)) ∧
          (∀ c l, l < mS - 1 →
            P.rank c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l)) = FFs c l) ∧
          (∀ c l, l < mS - 1 →
            P.rank c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l) = FFp c l)

/-- Forget the update-shaped semantic split package down to the shared
coordinate/rank-affine data. -/
theorem tieSemanticCoordData_of_updateSplitData
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hUpdate : TieSemanticUpdateSplitData P hV) :
    TieSemanticCoordData P := by
  obtain ⟨Mc, pcF, Ts, Tp, ī0F, j0F, Mbr, hMbr1, hpcF, hTsMbr, hTpMbr, hMc,
    hsufcyc, hprefcyc, hrows⟩ := hUpdate
  refine ⟨Mc, pcF, Ts, Tp, ī0F, j0F, Mbr, hMbr1, hpcF, hTsMbr, hTpMbr, hMc,
    hsufcyc, hprefcyc, ?_⟩
  intro mS hMbr n
  obtain ⟨FFs, FFp, Nc, hNcmS, hNcmMbr, hNcs, hNcp, hFs, hFp, hags, hagp,
    _hupdvals, _hupdvalp, _hselconsts, _hselconstp, _hupdateSplit⟩ :=
    hrows mS hMbr n
  exact ⟨FFs, FFp, Nc, hNcmS, hNcmMbr, hNcs, hNcp, hFs, hFp, hags, hagp⟩

/-- Zero-base update-shaped semantic split data for an arbitrary chosen
distinguished coordinate in every copy.  This is the general-arity replacement
for the tuple-scalarized compatibility path: the shared base tuple is fixed to
zero, so the non-moving coordinates are outside the suffix/prefix windows and
`selconst_*_update_window` supplies the selected-D constancy directly. -/
theorem tieSemanticUpdateZeroSplitData_of_coordChoice
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hRunClass : RunClassUpdateUniformCoverage P hV)
    (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c)) :
    TieSemanticUpdateZeroSplitData P hV := by
  classical
  obtain ⟨B, hB1, _hcov⟩ := CopiedCells.cells_cover_fibred P
  obtain ⟨m, p, Mc, _hp, _hmB, hMc, _hbFN, _hsetup⟩ := CopiedSetup.dstar_setup_fibred P B
  obtain ⟨q_U, q_D, hloU, hloD, hsufC, hprefC⟩ := coordCands_cycle_lengths P Mc (3 * B + m)
  set ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ := fun _ _ => 0 with hī0F
  choose pcs Ts hpcs hTpcs hgs hffs using fun c => hsufC c (j0F c)
  choose pcp Tp hpcp hTpcp hgp hffp using fun c => hprefC c (j0F c)
  let pcF : Fin P.toPoly.K → ℕ := fun c => pcs c * pcp c
  let TpF : Fin P.toPoly.K → ℕ := fun c => Tp c + 1
  let Mbr : ℕ := max q_U q_D
  refine ⟨Mc, pcF, Ts, TpF, ī0F, j0F, Mbr, hī0F, by omega, ?_, ?_, ?_, hMc, ?_,
    ?_, ?_⟩
  · intro c
    dsimp [pcF]
    exact Nat.mul_le_mul (hpcs c) (hpcp c)
  · intro c
    dsimp [Mbr]
    have := hTpcs c
    have := hpcs c
    omega
  · intro c
    dsimp [TpF, Mbr]
    have := hTpcp c
    have := hpcp c
    omega
  · intro c κ b hb
    dsimp [pcF]
    have h := hgs c (pcp c * κ) b hb
    simpa [Nat.mul_assoc] using h
  · intro c κ b hb
    dsimp [pcF, TpF] at hb ⊢
    have h := hgp c (pcs c * κ) b (by omega)
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  · intro mS hmS n
    choose FFs hFs0 hags using fun c => hffs c (ī0F c) mS n
    choose FFp hFp0 hagp using fun c => hffp c (ī0F c) mS n
    let Nc : ℕ := mS - Mbr
    have hMbr1 : 1 ≤ Mbr := by
      dsimp [Mbr]
      omega
    have hm1 : 1 ≤ mS := le_trans hMbr1 hmS
    have hNcmS : Nc ≤ mS - 1 := by
      dsimp [Nc]
      omega
    have hNcmMbr : mS ≤ Nc + Mbr := by
      dsimp [Nc]
      omega
    have hNcs : ∀ c, Ts c + Nc + 1 ≤ mS := by
      intro c
      dsimp [Nc, Mbr]
      have := hTpcs c
      have := hpcs c
      omega
    have hNcp : ∀ c, TpF c + Nc + 1 ≤ mS := by
      intro c
      dsimp [TpF, Nc, Mbr]
      have := hTpcp c
      have := hpcp c
      omega
    have hFs : ∀ c, RankAffineAtFrom (Ts c) (pcF c) (FFs c) := by
      intro c
      dsimp [pcF]
      exact RankAffineAtFrom_mul (hFs0 c) (pcp c)
    have hFp : ∀ c, RankAffineAtFrom (TpF c) (pcF c) (FFp c) := by
      intro c
      dsimp [TpF, pcF]
      show RankAffineAtFrom (Tp c + 1) (pcs c * pcp c) (FFp c)
      rw [Nat.mul_comm (pcs c) (pcp c)]
      exact (RankAffineAtFrom_mul (hFp0 c) (pcs c)).mono (by omega)
    have hbaseval : ∀ c, ∀ i, ī0F c i < (copiedSlice mS n).length := by
      intro c i
      simp [hī0F, length_copiedSlice]
      omega
    have hupdvals :
        ∀ c l, l < mS - 1 →
          ∀ i, Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l) i
            < (copiedSlice mS n).length := by
      intro c l hl i
      by_cases hi : i = j0F c
      · subst i
        simp [Function.update, length_copiedSlice]
        omega
      · simp [Function.update, hi, hī0F, length_copiedSlice]
        omega
    have hupdvalp :
        ∀ c l, l < mS - 1 →
          ∀ i, Function.update (ī0F c) (j0F c) l i < (copiedSlice mS n).length := by
      intro c l hl i
      by_cases hi : i = j0F c
      · subst i
        simp [Function.update, length_copiedSlice]
        omega
      · simp [Function.update, hi, hī0F, length_copiedSlice]
        omega
    have hselconsts :
        ∀ c, ∀ l₁ l₂, Ts c ≤ l₁ → l₁ < Nc → Ts c ≤ l₂ → l₂ < Nc →
          (l₁ - Ts c) % pcF c = (l₂ - Ts c) % pcF c →
          ((P.toPoly.sel c (copiedSlice mS n)
                (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₁))
              ∧ P.toPoly.label c (copiedSlice mS n)
                (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₁)) = D)
            ↔ (P.toPoly.sel c (copiedSlice mS n)
                (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₂))
              ∧ P.toPoly.label c (copiedSlice mS n)
                (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l₂)) = D)) := by
      intro c l₁ l₂ hT₁ hNc₁ hT₂ hNc₂ hmod
      exact selconst_suf_update_window P c (Mc c) (hMc c) mS n (pcF c) (Ts c) Nc
        0 (mS - 1) (Ts c) hm1 (ī0F c) (j0F c)
        (hbaseval c)
        (by
          intro l hTl hlNc
          constructor <;> omega)
        (by omega)
        (by
          intro l hTl hlNc
          constructor
          · have := hNcs c
            omega
          · have := hNcs c
            omega)
        (by
          intro i hi
          left
          simp [hī0F])
        (by
          intro κ b hb
          dsimp [pcF]
          have h := hgs c (pcp c * κ) b hb
          simpa [Nat.mul_assoc] using h)
        l₁ l₂ hT₁ hNc₁ hT₂ hNc₂ hmod
    have hselconstp :
        ∀ c, ∀ l₁ l₂, TpF c ≤ l₁ → l₁ < Nc → TpF c ≤ l₂ → l₂ < Nc →
          (l₁ - TpF c) % pcF c = (l₂ - TpF c) % pcF c →
          ((P.toPoly.sel c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₁)
              ∧ P.toPoly.label c (copiedSlice mS n)
                (Function.update (ī0F c) (j0F c) l₁) = D)
            ↔ (P.toPoly.sel c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l₂)
              ∧ P.toPoly.label c (copiedSlice mS n)
                (Function.update (ī0F c) (j0F c) l₂) = D)) := by
      intro c l₁ l₂ hT₁ hNc₁ hT₂ hNc₂ hmod
      exact selconst_pre_update_window P c (Mc c) (hMc c) mS n (pcF c) (TpF c) Nc
        1 (mS - 1) (Tp c) hm1 (ī0F c) (j0F c)
        (hbaseval c)
        (by
          intro l hTl hlNc
          dsimp [TpF] at hTl
          constructor <;> omega)
        (by omega)
        (by
          intro l hTl hlNc
          dsimp [TpF] at hTl
          constructor
          · have := hNcp c
            dsimp [TpF] at this
            omega
          · have := hNcp c
            dsimp [TpF] at this
            omega)
        (by
          intro i hi
          left
          simp [hī0F])
        (by
          intro κ b hb
          dsimp [pcF]
          have h := hgp c (pcs c * κ) b hb
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h)
        l₁ l₂ hT₁ hNc₁ hT₂ hNc₂ hmod
    refine ⟨FFs, FFp, Nc, hNcmS, hNcmMbr, hNcs, hNcp, hFs, hFp, hags, hagp,
      hupdvals, hupdvalp, hselconsts, hselconstp, ?_⟩
    intro c0 ī0m
    exact tie_semantic_update_split_slice P hV hRunClass mS n c0 ī0m
      pcF Ts TpF (by
        intro c
        dsimp [pcF]
        exact Nat.mul_le_mul (hpcs c) (hpcp c))
      Nc hNcmS FFs FFp ī0F j0F hFs hFp hupdvals hupdvalp hags hagp
      hselconsts hselconstp

/-- Abstract package of the canonical semantic split data consumed by the
row-indexed tie bridge.  The current constructor is arity-1; the general route
can replace it by proving this package directly. -/
def TieSemanticSplitData (P : WRP.Presentation Step Step) (hV : P.Valid) : Prop :=
    ∃ (Mc : (c : Fin P.toPoly.K) → SliceMSO.DetAuto (MarkedN (P.toPoly.arity c)))
      (pcF Ts Tp : Fin P.toPoly.K → ℕ)
      (ī0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c) → ℕ)
      (j0F : (c : Fin P.toPoly.K) → Fin (P.toPoly.arity c)) (Mbr : ℕ),
      1 ≤ Mbr ∧ (∀ c, 1 ≤ pcF c) ∧ (∀ c, Ts c ≤ Mbr) ∧ (∀ c, Tp c ≤ Mbr) ∧
      (∀ c (w : List Step) (ī : Fin (P.toPoly.arity c) → ℕ), (∀ i, ī i < w.length) →
        ((Mc c).accepts (markAtN (P.toPoly.arity c) w ī) ↔
          (P.toPoly.sel c w ī ∧ P.toPoly.label c w ī = D))) ∧
      (∀ c κ b, Ts c ≤ b →
        (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b + pcF c * κ]
          = (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) D (fun _ => false)))^[b]) ∧
      (∀ c κ b, Tp c ≤ b →
        (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b + pcF c * κ]
          = (fun q => (Mc c).δ q (mkLetter (P.toPoly.arity c) U (fun _ => false)))^[b]) ∧
      ∀ mS, Mbr ≤ mS → ∀ n,
        ∃ (FFs FFp : (c : Fin P.toPoly.K) → ℕ → Fin P.d → ℤ) (Nc : ℕ),
          Nc ≤ mS - 1 ∧ mS ≤ Nc + Mbr ∧
          (∀ c, Ts c + Nc + 1 ≤ mS) ∧ (∀ c, Tp c + Nc + 1 ≤ mS) ∧
          (∀ c, RankAffineAtFrom (Ts c) (pcF c) (FFs c)) ∧
          (∀ c, RankAffineAtFrom (Tp c) (pcF c) (FFp c)) ∧
          (∀ c l, l < mS - 1 →
            P.rank c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) (mS + 2 * n + 1 + l)) = FFs c l) ∧
          (∀ c l, l < mS - 1 →
            P.rank c (copiedSlice mS n) (Function.update (ī0F c) (j0F c) l) = FFp c l) ∧
          (∀ c0 ī0m, tieSemanticSplitAt P hV mS n c0 ī0m pcF Ts Tp Nc j0F)

/-- Build the semantic split package from coordinate/cycle data plus the
run-class coverage supplier.  This is the arity-free constructor for the split
layer; arity one is only one source of the supplier and coordinate data. -/
theorem tieSemanticSplitData_of_coordData
    (P : WRP.Presentation Step Step) (hV : P.Valid)
    (hCoord : TieSemanticCoordData P)
    (hRunClass : RunClassUniformCoverage P hV) :
    TieSemanticSplitData P hV := by
  classical
  obtain ⟨Mc, pcF, Ts, Tp, ī0F, j0F, Mbr, hMbr1, hpcF, hTsMbr, hTpMbr, hMc,
    hsufcyc, hprefcyc, hcoord⟩ := hCoord
  refine ⟨Mc, pcF, Ts, Tp, ī0F, j0F, Mbr, hMbr1, hpcF, hTsMbr, hTpMbr, hMc,
    hsufcyc, hprefcyc, ?_⟩
  intro mS hMbr n
  obtain ⟨FFs, FFp, Nc, hNcmS, hNcmMbr, hNcs, hNcp, hFs, hFp, hags, hagp⟩ :=
    hcoord mS hMbr n
  refine ⟨FFs, FFp, Nc, hNcmS, hNcmMbr, hNcs, hNcp, hFs, hFp, hags, hagp, ?_⟩
  intro c0 ī0m
  exact tie_semantic_split_slice P hV hRunClass mS n (by omega) c0 ī0m Mc hMc
    pcF Ts Tp hpcF Nc hNcmS hNcs hNcp FFs FFp ī0F j0F hFs hFp hags hagp
    hsufcyc hprefcyc

end CopiedSelUniform
