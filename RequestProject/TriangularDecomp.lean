/-
# Triangular decomposition and the canonical tight area sequence

Supporting arithmetic for Lemma 7.3.  Every `c : ℕ` is uniquely
`c = C(b+1,2) + d` with `0 ≤ d ≤ b` (`triangularDecomp`), and the canonical tight
area sequence `canonAreaSeq` built from `(a, b, d)` is a valid Dyck area sequence.
-/
import RequestProject.AreaSeq

open Step

/-! ## Triangular decomposition `c = C(b+1,2) + d`, `0 ≤ d ≤ b` -/

/-- `triangularDecomp c = (b, d)` with `c = b*(b+1)/2 + d` and `d ≤ b`. -/
def triangularDecomp : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | c + 1 =>
    let (b, d) := triangularDecomp c
    if d = b then (b + 1, 0) else (b, d + 1)

/-- The triangular index `b` of `c`. -/
def triB (c : ℕ) : ℕ := (triangularDecomp c).1

/-- The triangular remainder `d` of `c`. -/
def triD (c : ℕ) : ℕ := (triangularDecomp c).2

/-- One-step unfolding of the decomposition. -/
theorem triangularDecomp_succ (c : ℕ) :
    triangularDecomp (c + 1) =
      (if triD c = triB c then (triB c + 1, 0) else (triB c, triD c + 1)) := by
  conv_lhs => rw [triangularDecomp]
  rfl

/-- **Defining specification.**  `d ≤ b` and `c = b*(b+1)/2 + d`. -/
theorem tri_spec (c : ℕ) :
    triD c ≤ triB c ∧ triB c * (triB c + 1) / 2 + triD c = c := by
  induction c with
  | zero => exact ⟨le_rfl, rfl⟩
  | succ c ih =>
      obtain ⟨hle, hrec⟩ := ih
      have hB : triB (c + 1) = (triangularDecomp (c + 1)).1 := rfl
      have hD : triD (c + 1) = (triangularDecomp (c + 1)).2 := rfl
      rw [hB, hD, triangularDecomp_succ]
      have htri : (triB c + 1 + 1) * (triB c + 1) / 2
          = triB c * (triB c + 1) / 2 + (triB c + 1) := by
        have := Nat.triangle_succ (triB c + 1)
        simpa [Nat.mul_comm] using this
      by_cases hbd : triD c = triB c
      · rw [if_pos hbd]
        refine ⟨Nat.zero_le _, ?_⟩
        rw [show (triB c + 1) * (triB c + 1 + 1) = (triB c + 1 + 1) * (triB c + 1) by ring,
          htri]
        omega
      · rw [if_neg hbd]
        exact ⟨by dsimp only; omega, by dsimp only; omega⟩

theorem triD_le_triB (c : ℕ) : triD c ≤ triB c := (tri_spec c).1

theorem tri_recompose (c : ℕ) : triB c * (triB c + 1) / 2 + triD c = c := (tri_spec c).2

/-- Lower triangular bound `C(b+1,2) ≤ c`. -/
theorem triB_choose_le (c : ℕ) : triB c * (triB c + 1) / 2 ≤ c := by
  have := tri_recompose c; omega

/-- Upper triangular bound `c < C(b+2,2)`. -/
theorem lt_triB_succ_choose (c : ℕ) :
    c < (triB c + 1) * (triB c + 2) / 2 := by
  have hrec := tri_recompose c
  have hle := triD_le_triB c
  have htri : (triB c + 1 + 1) * (triB c + 1) / 2
      = triB c * (triB c + 1) / 2 + (triB c + 1) := by
    have := Nat.triangle_succ (triB c + 1)
    simpa [Nat.mul_comm] using this
  have : (triB c + 1) * (triB c + 2) / 2 = triB c * (triB c + 1) / 2 + (triB c + 1) := by
    rw [show (triB c + 1) * (triB c + 2) = (triB c + 1 + 1) * (triB c + 1) by ring]
    exact htri
  omega

/-- If `c ≤ C(N,2)` then `b ≤ N-1`, i.e. the first-ascent length `a = N - b ≥ 1`. -/
theorem triB_le_of_le_choose (N c : ℕ) (hN : 1 ≤ N) (hc : c ≤ N * (N - 1) / 2) :
    triB c ≤ N - 1 := by
  by_contra hgt
  push Not at hgt
  -- `triB c ≥ N`, so `C(triB c+1,2) ≥ C(N+1,2) = C(N,2)+N > C(N,2) ≥ c`, contradiction
  have hlow : triB c * (triB c + 1) / 2 ≤ c := triB_choose_le c
  have e1 : triB c * (triB c + 1) / 2 = (triB c + 1).choose 2 := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]
  have e2 : N * (N - 1) / 2 = N.choose 2 := (Nat.choose_two_right N).symm
  rw [e1] at hlow
  rw [e2] at hc
  have hmono : (N + 1).choose 2 ≤ (triB c + 1).choose 2 :=
    Nat.choose_le_choose 2 (by omega)
  have hpascal : (N + 1).choose 2 = N.choose 2 + N := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
  omega

/-- `b ≥ 1` when `c ≥ 1` (the pure staircase `b = 0` only realises `c = 0`). -/
theorem triB_pos_of_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ triB n := by
  rcases Nat.eq_zero_or_pos (triB n) with h | h
  · exfalso
    have hlt := lt_triB_succ_choose n
    rw [h] at hlt; norm_num at hlt; omega
  · exact h

/-! ## `ValidFrom` building blocks -/

/-- The threading height left after consuming `l` starting from `prev`. -/
def lastPrev (prev : ℤ) : List ℤ → ℤ
  | [] => prev
  | x :: rest => lastPrev (x + 1) rest

/-- `ValidFrom` composes over an append, threading the height. -/
theorem validFrom_append (prev : ℤ) (l1 l2 : List ℤ) (h1 : ValidFrom prev l1)
    (h2 : ValidFrom (lastPrev prev l1) l2) : ValidFrom prev (l1 ++ l2) := by
  induction l1 generalizing prev with
  | nil => simpa [lastPrev] using h2
  | cons x rest ih =>
      obtain ⟨hx0, hxp, hrest⟩ := h1
      exact ⟨hx0, hxp, ih (x + 1) hrest (by simpa [lastPrev] using h2)⟩

/-- A constant run is valid from any height at least the value. -/
theorem validFrom_replicate (n : ℕ) (v prev : ℤ) (hv : 0 ≤ v) (hp : v ≤ prev) :
    ValidFrom prev (List.replicate n v) := by
  induction n generalizing prev with
  | zero => exact trivial
  | succ k ih => exact ⟨hv, hp, ih (v + 1) (by linarith)⟩

/-- The threading height after a constant run. -/
theorem lastPrev_replicate (n : ℕ) (v prev : ℤ) :
    lastPrev prev (List.replicate n v) = if n = 0 then prev else v + 1 := by
  induction n generalizing prev with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, lastPrev, ih]
      cases k <;> simp

/-- The composed shift function used by the staircase recursion. -/
theorem stair_comp (s : ℤ) :
    (fun (i : ℕ) => (i : ℤ) + s) ∘ Nat.succ = (fun (i : ℕ) => (i : ℤ) + (s + 1)) := by
  funext i; simp only [Function.comp]; push_cast; ring

/-- The shifted staircase `(s, s+1, …, s+a-1)` is valid from `s`. -/
theorem validFrom_staircase (a : ℕ) (s : ℤ) (hs : 0 ≤ s) :
    ValidFrom s ((List.range a).map (fun (i : ℕ) => (i : ℤ) + s)) := by
  induction a generalizing s with
  | zero => exact trivial
  | succ k ih =>
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, stair_comp]
      simp only [Nat.cast_zero, zero_add]
      exact ⟨hs, le_rfl, ih (s + 1) (by linarith)⟩

/-- The threading height after a length-`a` staircase from `s` is `s + a`. -/
theorem lastPrev_staircase (a : ℕ) (s : ℤ) :
    lastPrev s ((List.range a).map (fun (i : ℕ) => (i : ℤ) + s)) = s + a := by
  induction a generalizing s with
  | zero => simp [lastPrev]
  | succ k ih =>
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, stair_comp, lastPrev,
        show ((0 : ℕ) : ℤ) + s + 1 = s + 1 by push_cast; ring, ih (s + 1)]
      push_cast; ring

/-! ## The canonical tight area sequence -/

/-- The canonical tight area sequence with first-ascent length `a`, then `b - d`
copies of `a-1`, then `d` copies of `a-2`. -/
def canonAreaSeq (a b d : ℕ) : List ℤ :=
  (List.range a).map (fun (i : ℕ) => (i : ℤ)) ++
  List.replicate (b - d) ((a : ℤ) - 1) ++
  List.replicate d ((a : ℤ) - 2)

/-- **The canonical area sequence is valid** (given `a ≥ 1`, `d ≤ b`, and the
edge condition `2 ≤ a ∨ d = 0` so that the `a-2` block is nonnegative). -/
theorem isValidAreaSeq_canon (a b d : ℕ) (ha : 1 ≤ a) (hd : d ≤ b)
    (hedge : 2 ≤ a ∨ d = 0) :
    IsValidAreaSeq (canonAreaSeq a b d) := by
  unfold IsValidAreaSeq canonAreaSeq
  rw [List.append_assoc]
  have hstair : (List.range a).map (fun (i : ℕ) => (i : ℤ))
      = (List.range a).map (fun (i : ℕ) => (i : ℤ) + 0) := by
    apply List.map_congr_left; intro i _; ring
  rw [hstair]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  apply validFrom_append
  · exact validFrom_staircase a 0 le_rfl
  rw [lastPrev_staircase]
  apply validFrom_append
  · -- (b - d) copies of (a - 1), from height `0 + a`
    exact validFrom_replicate _ _ _ (by linarith) (by linarith)
  · -- d copies of (a - 2), from the height after the plateau
    rw [lastPrev_replicate]
    rcases hedge with hge2 | hd0
    · have h2 : (2 : ℤ) ≤ a := by exact_mod_cast hge2
      apply validFrom_replicate
      · linarith
      · split <;> linarith
    · subst hd0; exact trivial
