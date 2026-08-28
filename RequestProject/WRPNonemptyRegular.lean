/-
# Nonempty-output preimages of WRP transductions are regular (paper §4, `lem:wrp-nonempty-regular`)

Formalisation of Lemma `lem:wrp-nonempty-regular` (`lem:wrp-nonempty-regular`, paper-full-new.tex) of
"A Computational Obstruction to Swapping Area and Dinv:
 An Automata-Theoretic View of the q,t-Catalan Symmetry"
by Baek, Hwang, La, and Yang:

> For every `WRP` transduction `T`, the language
> `{w ∈ dom(T) : |T(w)| ≥ 1}` of inputs with nonempty output is regular.

The proof follows the paper.  By `def:wrp` each selected atom contributes exactly
one output letter, so the output is nonempty if and only if at least one atom is
selected.  "At least one atom is selected" is the finite disjunction over the
copies of the *existential closure* of the selection formula `φ_c`
(Definition `def:polyregular`(iii)); the rank order plays no role in the mere
existence of a selected atom.  Conjoining with the MSO domain sentence and
applying Büchi–Elgot–Trakhtenbrot (`SliceMSO.buchi`), the language is
MSO-definable, hence regular.

The only admitted axiom used is the pre-existing `SliceMSO.buchi`.
-/
import RequestProject.WRP
import RequestProject.MSOClose
import RequestProject.SliceMSO
import RequestProject.Transducers

open MSO

namespace WRPNonemptyRegular

open WRP Polyreg

/-! ## Step 1 — an output exists, and is nonempty iff some atom is selected -/

/-- **A nonempty list with a trichotomous, transitive, irreflexive relation on its
members has an `r`-minimal member** (no member is `r`-below it). -/
theorem exists_min_mem {α : Type*} (r : α → α → Prop) :
    ∀ (L : List α), L ≠ [] →
      (∀ a ∈ L, ¬ r a a) →
      (∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, r a b → r b c → r a c) →
      (∀ a ∈ L, ∀ b ∈ L, r a b ∨ a = b ∨ r b a) →
      ∃ m ∈ L, ∀ b ∈ L, ¬ r b m := by
  intro L
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons x xs ihx =>
      intro _ hirr htr htri
      by_cases hxs : xs = []
      · subst hxs
        refine ⟨x, by simp, ?_⟩
        intro b hb hbad
        rcases List.mem_singleton.mp hb with rfl
        exact hirr b (by simp) hbad
      · have hirr' : ∀ a ∈ xs, ¬ r a a := fun a ha => hirr a (by simp [ha])
        have htri' : ∀ a ∈ xs, ∀ b ∈ xs, r a b ∨ a = b ∨ r b a :=
          fun a ha b hb => htri a (by simp [ha]) b (by simp [hb])
        have htr' : ∀ a ∈ xs, ∀ b ∈ xs, ∀ c ∈ xs, r a b → r b c → r a c :=
          fun a ha b hb c hc => htr a (by simp [ha]) b (by simp [hb]) c (by simp [hc])
        obtain ⟨m0, hm0, hmin0⟩ := ihx hxs hirr' htr' htri'
        rcases htri x (by simp) m0 (by simp [hm0]) with hxm | hxm | hxm
        · refine ⟨x, by simp, ?_⟩
          intro b hb hbx
          rcases List.mem_cons.mp hb with rfl | hbxs
          · exact hirr b (by simp) hbx
          · exact hmin0 b hbxs
              (htr b (by simp [hbxs]) x (by simp) m0 (by simp [hm0]) hbx hxm)
        · subst hxm
          refine ⟨x, by simp, ?_⟩
          intro b hb hbx
          rcases List.mem_cons.mp hb with rfl | hbxs
          · exact hirr b (by simp) hbx
          · exact hmin0 b hbxs hbx
        · refine ⟨m0, by simp [hm0], ?_⟩
          intro b hb hbm0
          rcases List.mem_cons.mp hb with rfl | hbxs
          · exact hirr m0 (by simp [hm0])
              (htr m0 (by simp [hm0]) b (by simp) m0 (by simp [hm0]) hxm hbm0)
          · exact hmin0 b hbxs hbm0

/-- **Sorting a finite set under a strict total order.**  Given a list `L` whose
members are pairwise comparable by a relation `r` that is irreflexive,
transitive and trichotomous on the members of `L`, there is a list `l` with the
same members (without repetition) that is `Pairwise r`-sorted.  Proved by
strong induction extracting an `r`-minimum at each step.  This is the generic
"a `Valid` presentation always has a declarative output" ingredient. -/
theorem exists_sorted_of_strictTotal {α : Type*} (r : α → α → Prop)
    (L : List α)
    (hirr : ∀ a ∈ L, ¬ r a a)
    (htr : ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, r a b → r b c → r a c)
    (htri : ∀ a ∈ L, ∀ b ∈ L, r a b ∨ a = b ∨ r b a) :
    ∃ l : List α, l.Nodup ∧ (∀ a, a ∈ l ↔ a ∈ L) ∧ l.Pairwise r := by
  classical
  -- induct on the (deduplicated) length of `L`
  generalize hn : L.dedup.length = n
  induction n generalizing L with
  | zero =>
      refine ⟨[], List.nodup_nil, ?_, List.Pairwise.nil⟩
      intro a
      have hLnil : L.dedup = [] := List.length_eq_zero_iff.mp hn
      have hL : L = [] := (List.dedup_eq_nil L).mp hLnil
      simp [hL]
  | succ n ih =>
      -- `L` is nonempty; pick an `r`-minimum among its members
      have hLne : L ≠ [] := by
        rintro rfl; simp at hn
      -- the minimal element of the finite nonempty member set
      have hmem_ne : L.dedup ≠ [] := by
        intro h; rw [h] at hn; simp at hn
      -- find an r-minimal member m of L
      obtain ⟨m, hmL, hmin⟩ := exists_min_mem r L hLne hirr htr htri
      -- remove m from L and recurse
      set L' := L.filter (fun a => decide (a ≠ m)) with hL'
      have hmemL' : ∀ a, a ∈ L' ↔ a ∈ L ∧ a ≠ m := by
        intro a
        rw [hL', List.mem_filter]
        simp
      have hirr' : ∀ a ∈ L', ¬ r a a := fun a ha => hirr a ((hmemL' a).mp ha).1
      have htr' : ∀ a ∈ L', ∀ b ∈ L', ∀ c ∈ L', r a b → r b c → r a c :=
        fun a ha b hb c hc => htr a ((hmemL' a).mp ha).1 b ((hmemL' b).mp hb).1
          c ((hmemL' c).mp hc).1
      have htri' : ∀ a ∈ L', ∀ b ∈ L', r a b ∨ a = b ∨ r b a :=
        fun a ha b hb => htri a ((hmemL' a).mp ha).1 b ((hmemL' b).mp hb).1
      -- length of L'.dedup is n
      have hcard : L'.dedup.length = n := by
        -- `L'.dedup` and `L.dedup.erase m` are nodup lists with the same members,
        -- hence permutations, hence equal length.
        have hmd : m ∈ L.dedup := List.mem_dedup.mpr hmL
        have hperm : L'.dedup.Perm (L.dedup.erase m) := by
          refine (List.perm_ext_iff_of_nodup (List.nodup_dedup L')
            ((List.nodup_dedup L).erase m)).mpr (fun a => ?_)
          rw [List.mem_dedup, hmemL' a, (List.nodup_dedup L).mem_erase_iff,
            List.mem_dedup]
          tauto
        have hlen : (L.dedup.erase m).length + 1 = L.dedup.length :=
          List.length_erase_add_one hmd
        rw [hperm.length_eq]
        omega
      obtain ⟨l, hnd, hmemiff, hpair⟩ := ih L' hirr' htr' htri' hcard
      refine ⟨m :: l, ?_, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨?_, hnd⟩
        intro hml
        have := ((hmemiff m).mp hml)
        exact ((hmemL' m).mp this).2 rfl
      · intro a
        rw [List.mem_cons, hmemiff a, hmemL' a]
        constructor
        · rintro (rfl | ⟨haL, _⟩)
          · exact hmL
          · exact haL
        · intro haL
          by_cases h : a = m
          · exact Or.inl h
          · exact Or.inr ⟨haL, h⟩
      · refine List.pairwise_cons.mpr ⟨?_, hpair⟩
        intro b hbl
        have hbmem := (hmemiff b).mp hbl
        obtain ⟨hbL, hbm⟩ := (hmemL' b).mp hbmem
        rcases htri m hmL b hbL with h | h | h
        · exact h
        · exact absurd h.symm hbm
        · exact absurd h (hmin b hbL)

/-- **The selected atoms of `w` form a finite, explicitly enumerable list.**
Every coordinate of a selected atom is `< w.length`, so the selected atoms are the
image of `Σ c, Fin (arity c) → Fin w.length` (a finite type) filtered by selection.
This gives a `List` containing exactly the selected atoms, with no duplicates. -/
theorem exists_selectedAtom_list {Alpha Gamma : Type*}
    (P : WRP.Presentation Alpha Gamma) (w : List Alpha) :
    ∃ L : List P.toPoly.Atom, ∀ a, a ∈ L ↔ P.toPoly.selectedAtom w a := by
  classical
  -- the finite candidate type: copy + in-range tuple
  let Cand := Σ c : Fin P.toPoly.K, Fin (P.toPoly.arity c) → Fin w.length
  -- embed a candidate into an atom
  let toAtom : Cand → P.toPoly.Atom := fun s => ⟨s.1, fun t => (s.2 t : ℕ)⟩
  refine ⟨((Finset.univ : Finset Cand).toList.map toAtom).filter
      (fun a => decide (P.toPoly.selectedAtom w a)), fun a => ?_⟩
  rw [List.mem_filter, List.mem_map]
  simp only [Finset.mem_toList, Finset.mem_univ, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨s, rfl⟩, hsel⟩
    exact hsel
  · intro hsel
    refine ⟨⟨⟨a.1, fun t => ⟨a.2 t, hsel.1 t⟩⟩, ?_⟩, hsel⟩
    -- toAtom of this candidate is a
    cases a with
    | mk c f => rfl

/-- **An output exists for any valid presentation.**  Sorting the finite set of
selected atoms by `≺` produces a declarative output. -/
theorem exists_isOutput {Alpha Gamma : Type*}
    (P : WRP.Presentation Alpha Gamma) (hV : P.Valid) (w : List Alpha) :
    ∃ out, P.IsOutput w out := by
  classical
  obtain ⟨L, hL⟩ := exists_selectedAtom_list P w
  -- restrict the order/validity hypotheses to members of `L` (= selected atoms)
  obtain ⟨l, hnd, hmem, hpair⟩ :=
    exists_sorted_of_strictTotal (P.wrpOrd w) L
      (fun a ha => hV.irrefl w a ((hL a).mp ha))
      (fun a ha b hb c hc => hV.trans w a b c ((hL a).mp ha) ((hL b).mp hb) ((hL c).mp hc))
      (fun a ha b hb => hV.trichot w a b ((hL a).mp ha) ((hL b).mp hb))
  refine ⟨l.map (P.toPoly.labelOf w), l, hnd, ?_, hpair, rfl⟩
  intro a
  rw [hmem a, hL a]

/-- **Nonempty output exists iff some atom is selected.**  Each selected atom
contributes exactly one output letter, so a nonempty output exists exactly when
the selected-atom set is nonempty. -/
theorem nonempty_output_iff_selected {Alpha Gamma : Type*}
    (P : WRP.Presentation Alpha Gamma) (hV : P.Valid) (w : List Alpha) :
    (∃ out, P.IsOutput w out ∧ out ≠ []) ↔ ∃ a, P.toPoly.selectedAtom w a := by
  constructor
  · rintro ⟨out, ⟨atoms, _, hmem, _, rfl⟩, hne⟩
    -- a nonempty `out` forces a nonempty `atoms`, giving a selected atom
    have hatomsne : atoms ≠ [] := by
      intro h; rw [h] at hne; simp at hne
    obtain ⟨a, rest, hcons⟩ := List.exists_cons_of_ne_nil hatomsne
    have ha : a ∈ atoms := by rw [hcons]; simp
    exact ⟨a, (hmem a).mp ha⟩
  · rintro ⟨a, ha⟩
    -- exhibit an output; a selected atom lies in any output's atom list, so it is nonempty
    obtain ⟨out, hout⟩ := exists_isOutput P hV w
    refine ⟨out, hout, ?_⟩
    obtain ⟨atoms, _, hmem, _, rfl⟩ := hout
    have ha' : a ∈ atoms := (hmem a).mpr ha
    simp only [ne_eq, List.map_eq_nil_iff]
    exact List.ne_nil_of_mem ha'

/-! ## Step 2 — the nonempty-output preimage is MSO-definable -/

/-- The MSO sentence "at least one atom is selected": the finite disjunction over
the copies of the existential closure of the selection formula.  (The rank order
plays no role in the mere existence of a selected atom.) -/
noncomputable def someSelectedSentence {Alpha Gamma : Type*} [Fintype Alpha]
    (P : WRP.Presentation Alpha Gamma) : MSO.Sentence Alpha :=
  Formula.bigOrFin (fun c : Fin P.toPoly.K =>
    Formula.closeAllFO (Classical.choose (P.toPoly.selDef c)))

theorem sat_someSelectedSentence {Alpha Gamma : Type*} [Fintype Alpha]
    (P : WRP.Presentation Alpha Gamma) (w : List Alpha) :
    (someSelectedSentence P).Sat w Fin.elim0 Fin.elim0 ↔
      ∃ a, P.toPoly.selectedAtom w a := by
  rw [someSelectedSentence, Formula.sat_bigOrFin]
  constructor
  · rintro ⟨c, hc⟩
    rw [Formula.sat_closeAllFO] at hc
    obtain ⟨ρ, hρrange, hρsat⟩ := hc
    have hsel : P.toPoly.sel c w ρ :=
      (Classical.choose_spec (P.toPoly.selDef c) w ρ).mpr hρsat
    exact ⟨⟨c, ρ⟩, hρrange, hsel⟩
  · rintro ⟨⟨c, ī⟩, hvalid, hsel⟩
    refine ⟨c, ?_⟩
    rw [Formula.sat_closeAllFO]
    refine ⟨ī, hvalid, ?_⟩
    exact (Classical.choose_spec (P.toPoly.selDef c) w ī).mp hsel

/-- The MSO sentence defining the nonempty-output preimage: the domain sentence
conjoined with "some atom is selected". -/
noncomputable def nonemptyPreimageSentence {Alpha Gamma : Type*} [Fintype Alpha]
    (P : WRP.Presentation Alpha Gamma) : MSO.Sentence Alpha :=
  Formula.and (Classical.choose P.toPoly.domainDef) (someSelectedSentence P)

theorem sat_nonemptyPreimageSentence {Alpha Gamma : Type*} [Fintype Alpha]
    (P : WRP.Presentation Alpha Gamma) (w : List Alpha) :
    (nonemptyPreimageSentence P).Sat w Fin.elim0 Fin.elim0 ↔
      P.toPoly.domain w ∧ ∃ a, P.toPoly.selectedAtom w a := by
  rw [nonemptyPreimageSentence, Formula.sat_and, sat_someSelectedSentence]
  exact and_congr_left (fun _ => (Classical.choose_spec P.toPoly.domainDef w).symm)

/-! ## Step 3 — bridge `DetAuto` to `DFA'` / `IsRegularLang` -/

/-- A deterministic finite acceptor (`SliceMSO.DetAuto`) gives a `DFA'` recognising
the same language; the only difference is decidability instances, supplied
classically. -/
theorem isRegularLang_of_detAuto {Alpha : Type} (M : SliceMSO.DetAuto Alpha) :
    IsRegularLang {w | M.accepts w} := by
  classical
  have := M.fintypeQ
  let A : DFA' Alpha :=
    { Q := M.Q
      finQ := M.fintypeQ
      decEqQ := Classical.decEq _
      delta := M.δ
      q0 := M.q0
      F := {q | M.accept q}
      decF := Classical.decPred _ }
  refine ⟨A, ?_⟩
  ext w
  simp only [A, DFA'.language, Set.mem_ofPred_eq, DFA'.accepts, SliceMSO.DetAuto.accepts]

/-! ## The lemma -/

/-- **Lemma `lem:wrp-nonempty-regular` (`lem:wrp-nonempty-regular`, paper-full-new.tex).**  For every
`WRP` transduction `T`, the language `{w ∈ dom(T) : |T(w)| ≥ 1}` of inputs with
nonempty output is regular. -/
theorem wrp_nonempty_preimage_regular
    {Alpha Gamma : Type} [Fintype Alpha]
    (T : List Alpha → Option (List Gamma)) (h : WRP.IsWRP T) :
    IsRegularLang {w | ∃ out, T w = some out ∧ out ≠ []} := by
  classical
  obtain ⟨P, hV, hreal⟩ := h
  -- STEP 1: reduce the preimage to "domain ∧ some atom selected"
  have hset : {w | ∃ out, T w = some out ∧ out ≠ []} =
      {w | P.toPoly.domain w ∧ ∃ a, P.toPoly.selectedAtom w a} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨out, hT, hne⟩
      obtain ⟨hdom, hout⟩ := (hreal w out).mp hT
      exact ⟨hdom, (nonempty_output_iff_selected P hV w).mp ⟨out, hout, hne⟩⟩
    · rintro ⟨hdom, hsel⟩
      obtain ⟨out, hout, hne⟩ := (nonempty_output_iff_selected P hV w).mpr hsel
      exact ⟨out, (hreal w out).mpr ⟨hdom, hout⟩, hne⟩
  -- STEP 2: this set is the language of the MSO sentence
  have hmso : {w | P.toPoly.domain w ∧ ∃ a, P.toPoly.selectedAtom w a} =
      {w | (nonemptyPreimageSentence P).Sat w Fin.elim0 Fin.elim0} := by
    ext w
    simp only [Set.mem_ofPred_eq, sat_nonemptyPreimageSentence]
  -- ... hence recognised by a deterministic acceptor (Büchi), hence regular
  obtain ⟨M, hM⟩ := SliceMSO.buchi (nonemptyPreimageSentence P)
  have hreg : IsRegularLang {w | (nonemptyPreimageSentence P).Sat w Fin.elim0 Fin.elim0} := by
    have : {w | (nonemptyPreimageSentence P).Sat w Fin.elim0 Fin.elim0} =
        {w | M.accepts w} := by
      ext w; simp only [Set.mem_ofPred_eq, hM]
    rw [this]
    exact isRegularLang_of_detAuto M
  rw [hset, hmso]
  exact hreg

end WRPNonemptyRegular
