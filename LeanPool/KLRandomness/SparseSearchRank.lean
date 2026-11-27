/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineCodeCoverage
public import LeanPool.KLRandomness.RandomMatrixAlgebra

/-!
# A computable full-row-rank test without certificates

The checker exhaustively enumerates finite Boolean vectors and checks
surjectivity of the coded matrix. Both the enumeration and the finite loops
have proofs of computability. The correctness theorem identifies acceptance
with actual linear-map surjectivity, independently of the certificate field
of the affine code.
-/

@[expose] public section

namespace Klr.SparseSearch

open AffineCode FiniteMeasure

/-- Explicit enumeration of all Boolean words of the requested length. -/
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (words n).map (false :: ·) ++ (words n).map (true :: ·)

theorem mem_words_iff (n : ℕ) (w : List Bool) : w ∈ words n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons b w => cases b <;> simp [words, List.mem_map, ih]

theorem computable_words : Computable words := by
  have hf : Computable (fun l : List (List Bool) => l.map (false :: ·)) :=
    (Primrec.list_map Primrec.id
      (Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂).to_comp
  have ht : Computable (fun l : List (List Bool) => l.map (true :: ·)) :=
    (Primrec.list_map Primrec.id
      (Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂).to_comp
  have hs : Computable₂ (fun (_ : ℕ) (p : ℕ × List (List Bool)) =>
      p.2.map (false :: ·) ++ p.2.map (true :: ·)) :=
    (Computable.list_append.comp (hf.comp (Computable.snd.comp Computable.snd))
      (ht.comp (Computable.snd.comp Computable.snd))).to₂
  apply (Computable.nat_rec Computable.id (Computable.const [[]]) hs).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [id_eq, words, Nat.rec_add_one] using
      congrArg (fun l => l.map (false :: ·) ++ l.map (true :: ·)) ih

/-- Finite Boolean conjunction of a computable predicate, with a computable
list of arguments. -/
theorem computable_list_all {α β : Type*} [Primcodable α] [Primcodable β]
    [Inhabited β] {f : α → List β} {p : α → β → Bool}
    (hf : Computable f) (hp : Computable₂ p) :
    Computable (fun a => (f a).all (p a)) := by
  have hg : Computable (fun a : α × ℕ => (f a.1).getD a.2 default) :=
    (Primrec.list_getD default).to_comp.comp (hf.comp Computable.fst) Computable.snd
  have hc := (EffectiveScan.computable_boundedAll
    (p := fun a i => p a ((f a).getD i default)) (hp.comp Computable.fst hg)).comp
      (Computable.id.pair (Computable.list_length.comp hf))
  apply hc.of_eq
  intro a
  rw [Bool.eq_iff_iff, EffectiveScan.boundedAll_eq_true, List.all_eq_true,
    List.forall_mem_iff_getElem]
  constructor
  · intro h i hi
    simpa [List.getD_eq_getElem?_getD, hi] using h i hi
  · intro h i hi
    simpa [List.getD_eq_getElem?_getD, hi] using h i hi

/-- Finite Boolean disjunction has the corresponding computability closure. -/
theorem computable_list_any {α β : Type*} [Primcodable α] [Primcodable β]
    [Inhabited β] {f : α → List β} {p : α → β → Bool}
    (hf : Computable f) (hp : Computable₂ p) :
    Computable (fun a => (f a).any (p a)) := by
  have hc := Primrec.not.to_comp.comp
    (computable_list_all hf (Primrec.not.to_comp.comp hp).to₂)
  exact hc.of_eq fun _ => List.any_eq_not_all_not.symm

/-- A word denotes a binary vector by zero-filling missing entries. -/
def wordVector (n : ℕ) (w : List Bool) : Fin n → ZMod 2 :=
  fun i => boolEquivF2 (w.getD i.val false)

@[simp] theorem wordVector_ofFn {n : ℕ} (v : Fin n → ZMod 2) :
    wordVector n (List.ofFn (fun i => boolEquivF2.symm (v i))) = v := by
  funext i
  simp [wordVector]

/-- Dot product over the two-element field of an encoded row and a bit list. -/
def rowValue (c : Data) (x : List Bool) (i : ℕ) : Bool :=
  parity (fun j => entry (rows c) i j && x.getD j false) (width c)

theorem value_rowValue (c : Data) (x : List Bool) (i : Fin (rank c)) :
    boolEquivF2 (rowValue c x i.val) =
      (matrix c).mulVecLin (wordVector (width c) x) i := by
  simp [rowValue, value_parity, value_and, matrix, wordVector,
    Matrix.mulVec, dotProduct]

theorem computable_rowValue :
    Computable (fun p : (Data × List Bool) × ℕ => rowValue p.1.1 p.1.2 p.2) := by
  have hd : Computable (fun p : ((Data × List Bool) × ℕ) × ℕ => p.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hx : Computable (fun p : ((Data × List Bool) × ℕ) × ℕ => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hi : Computable (fun p : ((Data × List Bool) × ℕ) × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hj : Computable (fun p : ((Data × List Bool) × ℕ) × ℕ => p.2) := Computable.snd
  have he := computable_entry.comp ((computable_rows.comp hd).pair (hi.pair hj))
  have hb := (Primrec.list_getD false).to_comp.comp hx hj
  have hc := (computable_parity
    (p := fun p : (Data × List Bool) × ℕ => fun j =>
      entry (rows p.1.1) p.2 j && p.1.2.getD j false)
    (Primrec.and.to_comp.comp he hb)).comp
      (Computable.id.pair (computable_width.comp (Computable.fst.comp Computable.fst)))
  exact hc.of_eq fun _ => rfl

/-- Check the entire coded equation `A x = y` by a bounded row loop. -/
def mapsTo (c : Data) (x y : List Bool) : Bool :=
  EffectiveScan.boundedAll (fun i => decide (rowValue c x i = y.getD i false)) (rank c)

theorem mapsTo_eq_true (c : Data) (x y : List Bool) : mapsTo c x y = true ↔
    (matrix c).mulVecLin (wordVector (width c) x) = wordVector (rank c) y := by
  rw [mapsTo, EffectiveScan.boundedAll_eq_true]
  constructor
  · intro h
    funext i
    rw [← value_rowValue, (of_decide_eq_true (h i.val i.isLt))]
    rfl
  · intro h i hi
    apply decide_eq_true
    apply boolEquivF2.injective
    exact (value_rowValue c x ⟨i, hi⟩).trans (congrFun h ⟨i, hi⟩)

theorem computable_mapsTo :
    Computable (fun p : Data × (List Bool × List Bool) => mapsTo p.1 p.2.1 p.2.2) := by
  have hd : Computable (fun p : (Data × (List Bool × List Bool)) × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hx : Computable (fun p : (Data × (List Bool × List Bool)) × ℕ => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hy : Computable (fun p : (Data × (List Bool × List Bool)) × ℕ => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hi : Computable (fun p : (Data × (List Bool × List Bool)) × ℕ => p.2) := Computable.snd
  have hl := computable_rowValue.comp ((hd.pair hx).pair hi)
  have hr := (Primrec.list_getD false).to_comp.comp hy hi
  have hp := Primrec.eq.decide.to_comp.comp hl hr
  have hc := (EffectiveScan.computable_boundedAll
    (p := fun p : Data × (List Bool × List Bool) => fun i =>
      decide (rowValue p.1 p.2.1 i = p.2.2.getD i false)) hp).comp
      (Computable.id.pair (computable_rank.comp Computable.fst))
  exact hc.of_eq fun _ => rfl

/-- A finite, certificate-free exhaustive surjectivity checker. -/
def fullRank (c : Data) : Bool :=
  (words (rank c)).all (fun y => (words (width c)).any (fun x => mapsTo c x y))

theorem computable_fullRank : Computable fullRank := by
  have hf : Computable (fun p : Data × List Bool => words (width p.1)) :=
    computable_words.comp (computable_width.comp Computable.fst)
  have hp : Computable₂ (fun p : Data × List Bool => fun x => mapsTo p.1 x p.2) :=
    (computable_mapsTo.comp ((Computable.fst.comp Computable.fst).pair
      (Computable.snd.pair (Computable.snd.comp Computable.fst)))).to₂
  have hi := computable_list_any hf hp
  exact computable_list_all (computable_words.comp computable_rank) hi.to₂

/-- The executable checker decides actual full row rank of the coded matrix. -/
theorem fullRank_eq_true (c : Data) :
    fullRank c = true ↔ Function.Surjective (matrix c).mulVecLin := by
  simp only [fullRank, List.all_eq_true, List.any_eq_true]
  constructor
  · intro h v
    let y := List.ofFn (fun i => boolEquivF2.symm (v i))
    have hy : y ∈ words (rank c) := (mem_words_iff _ _).mpr List.length_ofFn
    obtain ⟨x, _, hx⟩ := h y hy
    exact ⟨wordVector (width c) x, by simpa [y] using (mapsTo_eq_true c x y).mp hx⟩
  · intro h y _
    obtain ⟨v, hv⟩ := h (wordVector (rank c) y)
    let x := List.ofFn (fun i => boolEquivF2.symm (v i))
    refine ⟨x, (mem_words_iff _ _).mpr List.length_ofFn, ?_⟩
    apply (mapsTo_eq_true c x y).mpr
    simpa [x] using hv

theorem computablePred_fullRowRank :
    ComputablePred (fun c : Data => Function.Surjective (matrix c).mulVecLin) := by
  have hc : ComputablePred (fun c => fullRank c = true) :=
    ComputablePred.computable_iff.mpr ⟨fullRank, computable_fullRank, rfl⟩
  exact hc.of_eq fullRank_eq_true

end Klr.SparseSearch
