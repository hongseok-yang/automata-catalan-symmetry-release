/-
# Zeta is not ordinary polyregular (`cor:zeta-not-polyregular`)

Formalises the negative half of §6.2 (`thm:zeta-not-polyregular`, paper-full-new.tex): the Haglund
zeta map is **not** realisable by any ordinary polyregular transduction on the
Dyck domain, over the GENUINE semantic `Polyreg.IsPolyregular` (Def 3.8).

The repository deliberately does **not** transcribe the paper's 2DFT /
composition / regular-preimage / linear-growth-collapse proof (there is no
two-way-transducer model in the repo).  Instead we use a single standard,
project-agnostic closure fact — `polyreg_regular_preimage`, the polyregular
analogue of `SliceMSO.buchi` — applied twice, plus the now-genuine §6.2
combinatorics (`inRegularProbe_zetaMap_twoPyramid`, `inRegularProbe_isRegular`,
`zetaMap_twoPyramid`) and a direct pigeonhole on the resulting `DFA'`.

Route (avoids both composition closure and a separate pumping lemma):

* `R` = the regular probe language (`inRegularProbe`, regular via `probeDFA`).
* If a polyregular `T` realises `ζ` on Dyck paths, then `T⁻¹(R)` is regular
  (`polyreg_regular_preimage` once).
* `E : aᵐ#bⁿ ↦ U^m D^m U^n D^n` is a genuinely polyregular block-counting
  encoder (`encE`, `encE_isPolyregular`); `E⁻¹(T⁻¹(R))` is regular
  (`polyreg_regular_preimage` again).
* On the index family `aᵐ#bⁿ` that set is exactly `{m ≤ n}` (by the probe
  characterisation), which a `DFA'` reading the `a`-prefix cannot recognise
  (pigeonhole).  Contradiction.

The only admitted fact is `polyreg_regular_preimage` (one standard,
project-agnostic axiom).  Everything else — the encoder's polyregularity, the
probe combinatorics, and the pigeonhole — is proved.
-/
import RequestProject.ZetaClassification
import RequestProject.Polyregular

open Step

namespace ZetaNotPolyreg

/-! ## The admitted closure fact -/

/-- **Standard fact, admitted (project-agnostic): regular-preimage closure of
ordinary polyregular functions.**  The preimage of a regular language under a
polyregular function is regular.  This is the polyregular analogue of the
Büchi–Elgot–Trakhtenbrot axiom `SliceMSO.buchi`: a textbook closure property of
polyregular transductions (Bojańczyk), stated entirely over the generic
`Polyreg.IsPolyregular` / `IsRegularLang`, with no project-specific tokens. -/
axiom polyreg_regular_preimage {α β : Type} (f : List α → Option (List β))
    (R : Set (List β)) :
    Polyreg.IsPolyregular f → IsRegularLang R →
    IsRegularLang {w | ∃ out, f w = some out ∧ out ∈ R}

/-! ## The index alphabet and the block-counting encoder -/

/-- The 3-letter input alphabet of the encoder: `a`, `#`, `b`. -/
inductive Sym3 | sa | shash | sb
  deriving DecidableEq

instance : Fintype Sym3 :=
  ⟨⟨{.sa, .shash, .sb}, by decide⟩, fun x => by cases x <;> decide⟩

open Sym3

/-- The regular index word `aᵐ # bⁿ`. -/
def encWord (m n : ℕ) : List Sym3 :=
  List.replicate m sa ++ [shash] ++ List.replicate n sb

/-- The block-counting encoder `E`: `w ↦ U^{#a} D^{#a} U^{#b} D^{#b}`, where
`#a`, `#b` are the numbers of `a`s and `b`s in `w`.  On the index word
`aᵐ # bⁿ` it returns `twoPyramid m n`. -/
def encE (w : List Sym3) : Option (List Step) :=
  some (List.replicate (w.count sa) U ++ List.replicate (w.count sa) D ++
        List.replicate (w.count sb) U ++ List.replicate (w.count sb) D)

/-- `E(aᵐ # bⁿ) = twoPyramid m n`. -/
theorem encE_encWord (m n : ℕ) : encE (encWord m n) = some (twoPyramid m n) := by
  have ha : (encWord m n).count sa = m := by
    simp [encWord, List.count_append, List.count_replicate]
  have hb : (encWord m n).count sb = n := by
    simp [encWord, List.count_append, List.count_replicate]
  rw [encE, ha, hb, twoPyramid]

section EncoderPolyregular

open MSO List

/-! ### The four-copy presentation

The encoder `E` is realised by an explicit `Polyreg.Presentation` with four
arity-1 copies `0,1,2,3 = aU, aD, bU, bD`.  Copies `0,1` select the positions
labelled `a` (`sa`), copies `2,3` the positions labelled `b` (`sb`); copies
`0,2` emit `U`, copies `1,3` emit `D`.  The tie order `χ` is **copy-block
primary** (`0 < 1 < 2 < 3`), position secondary, so the sorted output is the
concatenation `U^{#a} D^{#a} U^{#b} D^{#b}` = `E w`. -/

/-- Selected symbol for copy `c`: copies `0,1` select `sa`; copies `2,3` select `sb`. -/
def selSym (c : Fin 4) : Sym3 := if c.val < 2 then sa else sb

/-- Emitted label for copy `c`: copies `0,2` emit `U`; copies `1,3` emit `D`. -/
def labStep (c : Fin 4) : Step := if c.val % 2 = 0 then U else D

/-- The four-copy block-counting presentation realising `encE`. -/
def encPoly : Polyreg.Presentation Sym3 Step where
  K := 4
  arity := fun _ => 1
  domain := fun _ => True
  domainDef := ⟨Formula.tru, fun _ => Iff.rfl⟩
  sel := fun c w ī => w[ī 0]? = some (selSym c)
  selDef := fun c => ⟨.labelEq 0 (selSym c), fun _ _ => Iff.rfl⟩
  label := fun c _ _ => labStep c
  labelDef := fun c g => by
    by_cases h : labStep c = g
    · exact ⟨.tru, fun w ρ => iff_of_true h trivial⟩
    · exact ⟨.neg .tru, fun w ρ => iff_of_false h (by simp)⟩
  ord := fun c c' _ ī ī' => c.val < c'.val ∨ (c.val = c'.val ∧ ī 0 < ī' 0)
  ordDef := fun c c' => by
    rcases lt_trichotomy c.val c'.val with h | h | h
    · -- `c < c'`: the relation always holds
      refine ⟨.tru, fun w ij => ?_⟩
      simp only [Formula.sat_tru, iff_true]
      exact Or.inl h
    · -- `c = c'`: defer to the position comparison
      refine ⟨.lt (Fin.castAdd 1 0) (Fin.natAdd 1 0), fun w ij => ?_⟩
      simp only [Formula.sat_lt]
      constructor
      · rintro (hc | ⟨_, hp⟩)
        · omega
        · exact hp
      · intro hp; exact Or.inr ⟨h, hp⟩
    · -- `c > c'`: the relation never holds
      refine ⟨.neg .tru, fun w ij => ?_⟩
      simp only [Formula.sat_neg, Formula.sat_tru, not_true, iff_false]
      rintro (hc | ⟨he, _⟩) <;> omega

/-! ### Atom toolkit (mirrors `hsAtom`/`hsPos`, keeping the copy index) -/

/-- The atom of copy `c` at input position `p`. -/
def encAtom (c : Fin 4) (p : ℕ) : encPoly.Atom := ⟨c, fun _ => p⟩

/-- The position coordinate of an atom. -/
def encPos (a : encPoly.Atom) : ℕ := a.2 ⟨0, Nat.one_pos⟩

@[simp] theorem encPos_encAtom (c : Fin 4) (p : ℕ) : encPos (encAtom c p) = p := rfl
@[simp] theorem copy_encAtom (c : Fin 4) (p : ℕ) : (encAtom c p).1 = c := rfl

theorem encAtom_ext {a b : encPoly.Atom} (hc : a.1 = b.1) (hp : encPos a = encPos b) :
    a = b := by
  obtain ⟨c, f⟩ := a
  obtain ⟨c', g⟩ := b
  cases (show c = c' from hc)
  have hfg : f = g := by
    funext t
    have ht : t = ⟨0, Nat.one_pos⟩ := by
      apply Fin.ext
      have h1 := t.isLt
      have h2 : encPoly.arity c = 1 := rfl
      omega
    rw [ht]; exact hp
  rw [hfg]

theorem encAtom_eta (a : encPoly.Atom) : a = encAtom a.1 (encPos a) :=
  (encAtom_ext (a := encAtom a.1 (encPos a)) (b := a) rfl rfl).symm

theorem encAtom_injective (c : Fin 4) : Function.Injective (encAtom c) := fun p q h => by
  have := congrArg encPos h; simpa using this

/-- Selectedness of an atom is exactly: in range, and labelled by its copy's symbol. -/
theorem enc_selectedAtom_iff (w : List Sym3) (a : encPoly.Atom) :
    encPoly.selectedAtom w a ↔ (encPos a < w.length ∧ w[encPos a]? = some (selSym a.1)) := by
  constructor
  · rintro ⟨hval, hsel⟩
    exact ⟨hval ⟨0, Nat.one_pos⟩, hsel⟩
  · rintro ⟨hlt, hsel⟩
    refine ⟨fun t => ?_, hsel⟩
    have ht : t = ⟨0, Nat.one_pos⟩ := by
      apply Fin.ext
      have h1 := t.isLt
      have h2 : encPoly.arity a.1 = 1 := rfl
      omega
    rw [ht]; exact hlt

/-- The tie order in omega-ready normal form: copy-block primary, position secondary. -/
theorem enc_atomOrd_iff (w : List Sym3) (a b : encPoly.Atom) :
    encPoly.atomOrd w a b ↔ (a.1.val < b.1.val ∨ (a.1.val = b.1.val ∧ encPos a < encPos b)) :=
  Iff.rfl

/-! ### Validity: `χ` is a strict total order on selected atoms -/

theorem encPoly_valid : encPoly.Valid where
  irrefl := fun w a _ => by rw [enc_atomOrd_iff]; omega
  trans := fun w a b c _ _ _ hab hbc => by rw [enc_atomOrd_iff] at *; omega
  trichot := fun w a b _ _ => by
    rw [enc_atomOrd_iff, enc_atomOrd_iff]
    rcases lt_trichotomy a.1.val b.1.val with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_trichotomy (encPos a) (encPos b) with hp | hp | hp
      · exact Or.inl (Or.inr ⟨h, hp⟩)
      · exact Or.inr (Or.inl (encAtom_ext (Fin.ext h) hp))
      · exact Or.inr (Or.inr (Or.inr ⟨h.symm, hp⟩))
    · exact Or.inr (Or.inr (Or.inl h))

/-! ### The ascending list of positions of a symbol, and the count bridge -/

/-- The positions of the symbol `s` in `w`, in ascending order. -/
def symPos (w : List Sym3) (s : Sym3) : List ℕ :=
  (w.zipIdx.filter (fun p => p.1 == s)).map Prod.snd

/-- **The count–length bridge**: the number of `s`-positions is `w.count s`. -/
theorem symPos_length (w : List Sym3) (s : Sym3) : (symPos w s).length = w.count s := by
  rw [symPos, List.length_map, ← List.countP_eq_length_filter]
  rw [show (fun p : Sym3 × ℕ => p.1 == s) = (fun x => x == s) ∘ Prod.fst from rfl]
  rw [← List.countP_map, List.zipIdx_map_fst, List.count_eq_countP]

/-- Membership in `symPos`: in range and labelled `s`. -/
theorem mem_symPos (w : List Sym3) (s : Sym3) (i : ℕ) :
    i ∈ symPos w s ↔ (i < w.length ∧ w[i]? = some s) := by
  rw [symPos, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [List.mem_filter] at hp
    obtain ⟨hmem, hfst⟩ := hp
    obtain ⟨hlt, heq⟩ := List.mem_zipIdx' hmem
    simp only [beq_iff_eq] at hfst
    refine ⟨hlt, ?_⟩
    rw [List.getElem?_eq_getElem hlt, ← heq, hfst]
  · rintro ⟨hlt, heq⟩
    refine ⟨(w[i], i), ?_, rfl⟩
    rw [List.mem_filter]
    rw [List.getElem?_eq_getElem hlt] at heq
    refine ⟨?_, by simp [Option.some.inj heq]⟩
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getElem?_eq_getElem hlt]

/-- `symPos` is strictly ascending. -/
theorem symPos_sorted (w : List Sym3) (s : Sym3) : (symPos w s).Pairwise (· < ·) := by
  rw [symPos, List.pairwise_map]
  have hsorted : w.zipIdx.Pairwise (fun p q => p.2 < q.2) := by
    rw [← List.pairwise_map (f := Prod.snd), List.zipIdx_map_snd]
    exact List.pairwise_lt_range'
  exact hsorted.filter _

theorem symPos_nodup (w : List Sym3) (s : Sym3) : (symPos w s).Nodup :=
  (symPos_sorted w s).imp (fun {_a _b} hab => Nat.ne_of_lt hab)

/-! ### The witness atom list and the four `IsOutput` obligations -/

/-- The witness list: the four copy blocks, each the symbol's positions mapped to atoms. -/
def encAtoms (w : List Sym3) : List encPoly.Atom :=
  (symPos w sa).map (encAtom 0) ++ (symPos w sa).map (encAtom 1) ++
  (symPos w sb).map (encAtom 2) ++ (symPos w sb).map (encAtom 3)

/-- A copy's own block contains exactly its selected atoms. -/
theorem mem_encAtoms_block (w : List Sym3) (c : Fin 4) (s : Sym3) (hs : selSym c = s) (i : ℕ) :
    encAtom c i ∈ (symPos w s).map (encAtom c) ↔ encPoly.selectedAtom w (encAtom c i) := by
  rw [enc_selectedAtom_iff, encPos_encAtom, copy_encAtom, hs]
  rw [List.mem_map]
  constructor
  · rintro ⟨j, hj, heq⟩
    have hji : j = i := encAtom_injective c heq
    rw [← hji]; exact (mem_symPos w s j).mp hj
  · intro h; exact ⟨i, (mem_symPos w s i).mpr h, rfl⟩

/-- An atom of copy `c` never lies in a foreign copy's block. -/
theorem not_mem_foreign_block (w : List Sym3) (c c' : Fin 4) (s : Sym3) (i : ℕ)
    (hcc : c ≠ c') : encAtom c i ∉ (symPos w s).map (encAtom c') := by
  rw [List.mem_map]
  rintro ⟨j, _, hj⟩
  exact hcc (congrArg Polyreg.Presentation.Atom.copy hj.symm)

/-- **Membership** for atoms presented as `encAtom c i`. -/
theorem mem_encAtoms_encAtom (w : List Sym3) (c : Fin 4) (i : ℕ) :
    encAtom c i ∈ encAtoms w ↔ encPoly.selectedAtom w (encAtom c i) := by
  rw [encAtoms]
  simp only [List.mem_append]
  fin_cases c
  · constructor
    · rintro (((h | h) | h) | h)
      · exact (mem_encAtoms_block w 0 sa (by decide) i).mp h
      · exact absurd h (not_mem_foreign_block w 0 1 sa i (by decide))
      · exact absurd h (not_mem_foreign_block w 0 2 sb i (by decide))
      · exact absurd h (not_mem_foreign_block w 0 3 sb i (by decide))
    · intro h
      exact Or.inl (Or.inl (Or.inl ((mem_encAtoms_block w 0 sa (by decide) i).mpr h)))
  · constructor
    · rintro (((h | h) | h) | h)
      · exact absurd h (not_mem_foreign_block w 1 0 sa i (by decide))
      · exact (mem_encAtoms_block w 1 sa (by decide) i).mp h
      · exact absurd h (not_mem_foreign_block w 1 2 sb i (by decide))
      · exact absurd h (not_mem_foreign_block w 1 3 sb i (by decide))
    · intro h
      exact Or.inl (Or.inl (Or.inr ((mem_encAtoms_block w 1 sa (by decide) i).mpr h)))
  · constructor
    · rintro (((h | h) | h) | h)
      · exact absurd h (not_mem_foreign_block w 2 0 sa i (by decide))
      · exact absurd h (not_mem_foreign_block w 2 1 sa i (by decide))
      · exact (mem_encAtoms_block w 2 sb (by decide) i).mp h
      · exact absurd h (not_mem_foreign_block w 2 3 sb i (by decide))
    · intro h
      exact Or.inl (Or.inr ((mem_encAtoms_block w 2 sb (by decide) i).mpr h))
  · constructor
    · rintro (((h | h) | h) | h)
      · exact absurd h (not_mem_foreign_block w 3 0 sa i (by decide))
      · exact absurd h (not_mem_foreign_block w 3 1 sa i (by decide))
      · exact absurd h (not_mem_foreign_block w 3 2 sb i (by decide))
      · exact (mem_encAtoms_block w 3 sb (by decide) i).mp h
    · intro h
      exact Or.inr ((mem_encAtoms_block w 3 sb (by decide) i).mpr h)

/-- **Membership** (`IsOutput` obligation 1): the witness list is exactly the selected atoms. -/
theorem mem_encAtoms_iff (w : List Sym3) (a : encPoly.Atom) :
    a ∈ encAtoms w ↔ encPoly.selectedAtom w a := by
  rw [encAtom_eta a]
  exact mem_encAtoms_encAtom w a.1 (encPos a)

/-- Each block is internally `Nodup` (positions distinct, `encAtom c` injective). -/
theorem block_nodup (w : List Sym3) (c : Fin 4) (s : Sym3) :
    ((symPos w s).map (encAtom c)).Nodup :=
  (symPos_nodup w s).map (encAtom_injective c)

/-- Distinct copies give disjoint blocks. -/
theorem blocks_disjoint (w : List Sym3) (c c' : Fin 4) (s s' : Sym3) (hcc : c ≠ c') :
    Disjoint ((symPos w s).map (encAtom c)) ((symPos w s').map (encAtom c')) := by
  rw [List.disjoint_left]
  intro x hx hx'
  rw [List.mem_map] at hx hx'
  obtain ⟨j, _, rfl⟩ := hx
  obtain ⟨k, _, hk⟩ := hx'
  exact hcc (congrArg Polyreg.Presentation.Atom.copy hk.symm)

/-- **No duplicates** (`IsOutput` obligation 2). -/
theorem encAtoms_nodup (w : List Sym3) : (encAtoms w).Nodup := by
  rw [encAtoms]
  refine List.Nodup.append ?_ (block_nodup w 3 sb) ?_
  · refine List.Nodup.append ?_ (block_nodup w 2 sb) ?_
    · refine List.Nodup.append (block_nodup w 0 sa) (block_nodup w 1 sa) ?_
      exact blocks_disjoint w 0 1 sa sa (by decide)
    · rw [List.disjoint_append_left]
      exact ⟨blocks_disjoint w 0 2 sa sb (by decide), blocks_disjoint w 1 2 sa sb (by decide)⟩
  · rw [List.disjoint_append_left, List.disjoint_append_left]
    exact ⟨⟨blocks_disjoint w 0 3 sa sb (by decide), blocks_disjoint w 1 3 sa sb (by decide)⟩,
           blocks_disjoint w 2 3 sb sb (by decide)⟩

/-- Within a block (same copy) the order is position-ascending. -/
theorem block_pairwise (w : List Sym3) (c : Fin 4) (s : Sym3) :
    ((symPos w s).map (encAtom c)).Pairwise (encPoly.atomOrd w) := by
  rw [List.pairwise_map]
  refine (symPos_sorted w s).imp (fun {x y} hxy => ?_)
  rw [enc_atomOrd_iff, copy_encAtom, copy_encAtom, encPos_encAtom, encPos_encAtom]
  exact Or.inr ⟨rfl, hxy⟩

/-- Across blocks with `c.val < c'.val`, every cross pair is ordered. -/
theorem cross_block (w : List Sym3) (c c' : Fin 4) (s s' : Sym3) (hlt : c.val < c'.val)
    (a b : encPoly.Atom) (ha : a ∈ (symPos w s).map (encAtom c))
    (hb : b ∈ (symPos w s').map (encAtom c')) : encPoly.atomOrd w a b := by
  rw [List.mem_map] at ha hb
  obtain ⟨j, _, rfl⟩ := ha
  obtain ⟨k, _, rfl⟩ := hb
  rw [enc_atomOrd_iff, copy_encAtom, copy_encAtom]
  exact Or.inl hlt

/-- **Pairwise** (`IsOutput` obligation 3): the witness list is `χ`-sorted. -/
theorem encAtoms_pairwise (w : List Sym3) : (encAtoms w).Pairwise (encPoly.atomOrd w) := by
  rw [encAtoms, List.pairwise_append, List.pairwise_append, List.pairwise_append]
  refine ⟨⟨⟨block_pairwise w 0 sa, block_pairwise w 1 sa, ?_⟩, block_pairwise w 2 sb, ?_⟩,
          block_pairwise w 3 sb, ?_⟩
  · exact fun a ha b hb => cross_block w 0 1 sa sa (by decide) a b ha hb
  · intro a ha b hb
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · exact cross_block w 0 2 sa sb (by decide) a b ha hb
    · exact cross_block w 1 2 sa sb (by decide) a b ha hb
  · intro a ha b hb
    rw [List.mem_append, List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · exact cross_block w 0 3 sa sb (by decide) a b ha hb
    · exact cross_block w 1 3 sa sb (by decide) a b ha hb
    · exact cross_block w 2 3 sb sb (by decide) a b ha hb

/-- A block's labels are the constant `labStep c`, repeated `w.count s` times. -/
theorem block_labels (w : List Sym3) (c : Fin 4) (s : Sym3) :
    ((symPos w s).map (encAtom c)).map (encPoly.labelOf w)
      = List.replicate (w.count s) (labStep c) := by
  rw [List.map_map]
  rw [show (encPoly.labelOf w ∘ encAtom c) = (fun _ => labStep c) from by funext i; rfl]
  rw [List.map_const', symPos_length]

/-- **The label map** (`IsOutput` obligation 4): the witness labels are `E`'s payload. -/
theorem map_labelOf_encAtoms (w : List Sym3) :
    (encAtoms w).map (encPoly.labelOf w)
      = List.replicate (w.count sa) U ++ List.replicate (w.count sa) D ++
        List.replicate (w.count sb) U ++ List.replicate (w.count sb) D := by
  rw [encAtoms, List.map_append, List.map_append, List.map_append]
  rw [block_labels w 0 sa, block_labels w 1 sa, block_labels w 2 sb, block_labels w 3 sb]
  rw [show labStep 0 = U from by decide, show labStep 1 = D from by decide,
      show labStep 2 = U from by decide, show labStep 3 = D from by decide]

/-- The declarative output of `encPoly` on `w` is exactly `E`'s payload. -/
theorem encE_isOutput (w : List Sym3) :
    encPoly.IsOutput w (List.replicate (w.count sa) U ++ List.replicate (w.count sa) D ++
        List.replicate (w.count sb) U ++ List.replicate (w.count sb) D) :=
  ⟨encAtoms w, encAtoms_nodup w, mem_encAtoms_iff w, encAtoms_pairwise w,
   (map_labelOf_encAtoms w).symm⟩

end EncoderPolyregular

/-- **The encoder is genuinely polyregular.**  (Constructed presentation `encPoly`:
four arity-1 copies `aU, aD, bU, bD` selecting the `a`/`b` positions, labelled
`U`/`D`, ordered by copy-block then position; the sorted output is
`U^{#a} D^{#a} U^{#b} D^{#b}`.) -/
theorem encE_isPolyregular : Polyreg.IsPolyregular encE := by
  refine ⟨encPoly, encPoly_valid, fun w out => ?_⟩
  rw [encE]
  constructor
  · intro h
    exact ⟨trivial, (Option.some.inj h) ▸ encE_isOutput w⟩
  · rintro ⟨_, hout⟩
    exact congrArg some (encPoly.isOutput_unique encPoly_valid (encE_isOutput w) hout)

/-! ## The pigeonhole non-regularity -/

/-- No `DFA'` recognises a language `Bad ⊆ (Sym3)*` that, on the index family,
agrees with `{aᵐ#bⁿ : m ≤ n}`.  Reading the `a`-prefix, two distinct lengths
`i < j` (both `≥ 1`) reach the same state (pigeonhole); then `aⁱ#bⁱ` and
`aʲ#bⁱ` are accepted together, yet `i ≤ i` holds while `j ≤ i` fails. -/
theorem not_regular_le_family
    (Bad : Set (List Sym3)) (hReg : IsRegularLang Bad)
    (hchar : ∀ m n, 1 ≤ m → 1 ≤ n → (encWord m n ∈ Bad ↔ m ≤ n)) : False := by
  obtain ⟨A, hA⟩ := hReg
  have := A.finQ
  have := A.decEqQ
  -- the state reached after reading `a^{k+1}`
  let runA : ℕ → A.Q := fun k => (List.replicate (k + 1) sa).foldl A.delta A.q0
  -- pigeonhole: among the `N+1` prefixes `a^1 … a^{N+1}` (`N = card Q`), two collide
  obtain ⟨i, _, j, _, hij, hcol⟩ :
      ∃ i ∈ Finset.range (Fintype.card A.Q + 1), ∃ j ∈ Finset.range (Fintype.card A.Q + 1),
        i ≠ j ∧ runA i = runA j := by
    have hcard : (Finset.univ : Finset A.Q).card < (Finset.range (Fintype.card A.Q + 1)).card := by
      simp
    obtain ⟨i, hi, j, hj, hij, he⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
        (fun a _ => Finset.mem_univ (runA a))
    exact ⟨i, hi, j, hj, hij, he⟩
  -- order them: `p < q` with the same run state
  obtain ⟨p, q, hpq, hcolpq⟩ : ∃ p q, p < q ∧ runA p = runA q := by
    rcases Nat.lt_or_ge i j with h | h
    · exact ⟨i, j, h, hcol⟩
    · exact ⟨j, i, lt_of_le_of_ne h hij.symm, hcol.symm⟩
  -- the two index words share the suffix `# b^{p+1}`
  have hsplit : ∀ k, encWord (k + 1) (p + 1)
      = List.replicate (k + 1) sa ++ ([shash] ++ List.replicate (p + 1) sb) := by
    intro k; rw [encWord, List.append_assoc]
  -- the run of `encWord (k+1) (p+1)` is the suffix-run started from `runA k`
  have hfold : ∀ k, (encWord (k + 1) (p + 1)).foldl A.delta A.q0
      = ([shash] ++ List.replicate (p + 1) sb).foldl A.delta (runA k) := by
    intro k; rw [hsplit k, List.foldl_append]
  -- runs agree, because the `a`-prefixes reach the same state
  have hrun_eq : (encWord (p + 1) (p + 1)).foldl A.delta A.q0
      = (encWord (q + 1) (p + 1)).foldl A.delta A.q0 := by
    rw [hfold, hfold, hcolpq]
  -- hence accepted together
  have hacc_iff : encWord (p + 1) (p + 1) ∈ Bad ↔ encWord (q + 1) (p + 1) ∈ Bad := by
    rw [← hA]
    show A.accepts _ ↔ A.accepts _
    unfold DFA'.accepts
    rw [hrun_eq]
  -- but the characterisation forces a contradiction
  rw [hchar (p + 1) (p + 1) (by omega) (by omega),
      hchar (q + 1) (p + 1) (by omega) (by omega)] at hacc_iff
  have : q + 1 ≤ p + 1 := hacc_iff.mp (le_refl _)
  omega

/-! ## The separation -/

/-- **Corollary `cor:zeta-not-polyregular` (`thm:zeta-not-polyregular`, paper-full-new.tex), genuine.**
No ordinary polyregular transduction realises the zeta map on the Dyck domain,
over the real `Polyreg.IsPolyregular`.  Admits only `polyreg_regular_preimage`. -/
theorem zetaMap_not_polyregular :
    ¬ ∃ T : List Step → Option (List Step),
      Polyreg.IsPolyregular T ∧ Realises T {P | IsDyckPath P} zetaMap := by
  rintro ⟨T, hTpoly, hTreal⟩
  -- T⁻¹(R) is regular
  have hRpre : IsRegularLang
      {w : List Step | ∃ out, T w = some out ∧ out ∈ {w : List Step | inRegularProbe w}} :=
    polyreg_regular_preimage T {w | inRegularProbe w} hTpoly inRegularProbe_isRegular
  -- E⁻¹(T⁻¹(R)) is regular: call it `Bad`
  have hBad : IsRegularLang
      {w : List Sym3 | ∃ out, encE w = some out ∧
        out ∈ {w : List Step | ∃ o, T w = some o ∧ inRegularProbe o}} :=
    polyreg_regular_preimage encE _ encE_isPolyregular hRpre
  -- on the index family, `Bad` is exactly `{m ≤ n}`
  refine not_regular_le_family _ hBad (fun m n hm hn => ?_)
  have hdyck : IsDyckPath (twoPyramid m n) := isDyckPath_twoPyramid m n hm hn
  have hT2 : T (twoPyramid m n) = some (zetaMap (twoPyramid m n)) := hTreal _ hdyck
  constructor
  · rintro ⟨out, hout, o, hTo, hprobe⟩
    rw [encE_encWord] at hout
    obtain rfl : out = twoPyramid m n := (Option.some.inj hout).symm
    rw [hT2] at hTo
    obtain rfl : o = zetaMap (twoPyramid m n) := (Option.some.inj hTo).symm
    exact (inRegularProbe_zetaMap_twoPyramid m n hm hn).mp hprobe
  · intro hmn
    exact ⟨twoPyramid m n, encE_encWord m n, zetaMap (twoPyramid m n), hT2,
      (inRegularProbe_zetaMap_twoPyramid m n hm hn).mpr hmn⟩

/-- **Theorem `thm:zeta-not-regular` (`cor:zeta-not-regular`, paper-full-new.tex), genuine.**  The
Haglund zeta map is not realisable, on the Dyck domain, by any deterministic MSO
string transduction — equivalently (Engelfriet–Hoogeboom, the equivalence the
paper invokes) by any deterministic two-way finite-state transducer.  This is the
strictly weaker sibling of `zetaMap_not_polyregular`: every regular string
transduction is polyregular (`Polyreg.IsRegular.isPolyregular`), so the corollary
applies directly.  Same trust base (`+ polyreg_regular_preimage`). -/
theorem zetaMap_not_regular :
    ¬ ∃ T : List Step → Option (List Step),
      Polyreg.IsRegular T ∧ Realises T {P | IsDyckPath P} zetaMap := by
  rintro ⟨T, hreg, hreal⟩
  exact zetaMap_not_polyregular ⟨T, hreg.isPolyregular, hreal⟩

end ZetaNotPolyreg
