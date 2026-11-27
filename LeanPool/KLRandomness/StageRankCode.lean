/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageRankZero
public import LeanPool.KLRandomness.PoolAdviceComputable

/-!
# Executable unread masks and finite rank predicates

All queries used here are made on a finite prescribed answer transcript.
The unread mask is a total finite computation from the concrete pool list,
and the full-rank and zero-rank tests agree with the mathematical affine
block on that list. No limiting query information is used by these tests.
-/

@[expose] public section

namespace Klr.StageRankCode

open SparseSearch SparseListSearch SparseListCode AffineCode EffectiveScan FiniteMeasure

/-- The concrete Boolean unread-pool mask after the supplied finite transcript. -/
def unreadMask (π : ScanRule) (G : List ℕ) (v : List Bool) : List Bool :=
  tabulate (fun j => !PoolAdvice.readsBefore [π] 0 (G.getD j 0) v.length v) G.length

@[simp] theorem length_unreadMask (π : ScanRule) (G : List ℕ) (v : List Bool) :
    (unreadMask π G v).length = G.length := by simp [unreadMask, tabulate]

theorem computable_unreadMask (π : ScanRule) :
    Computable (fun p : List ℕ × List Bool => unreadMask π p.1 p.2) := by
  have hG : Computable (fun p : (List ℕ × List Bool) × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hv : Computable (fun p : (List ℕ × List Bool) × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  have ha := (Primrec.list_getD (0 : ℕ)).to_comp.comp hG Computable.snd
  have hread := PoolAdvice.computable_readsBefore [π] (Computable.const 0) ha
    (Computable.list_length.comp hv) hv
  have hbit := Primrec.not.to_comp.comp hread
  have htab := (computable_tabulate (f := fun p : List ℕ × List Bool => fun j =>
    !PoolAdvice.readsBefore [π] 0 (p.1.getD j 0) p.2.length p.2) hbit.to₂).comp
      (Computable.id.pair (Computable.list_length.comp Computable.fst))
  exact htab

theorem readsBefore_iff_mem_queriedPositions (π : ScanRule) (a : ℕ) (v : List Bool) :
    PoolAdvice.readsBefore [π] 0 a v.length v = true ↔ a ∈ π.queriedPositions v := by
  rw [PoolAdvice.readsBefore_eq_true]
  constructor
  · rintro ⟨t, ht, hq⟩
    exact Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_univ _, hq⟩
  · intro h
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
    exact ⟨t.val, t.isLt, ht⟩

/-- The executable mask equals the exact finite unread-pool mask. -/
theorem unreadMask_eq_mask (π : ScanRule) (G : List ℕ) (v : List Bool) :
    unreadMask π G v = mask (StageRank.unreadPool G.get π v) := by
  apply List.ext_getElem (by simp)
  intro j hj hk
  have hjG : j < G.length := by simpa using hj
  rw [← List.getD_eq_getElem _ false hj, ← List.getD_eq_getElem _ false hk]
  rw [unreadMask, getD_tabulate _ hjG]
  rw [getD_mask _ (⟨j, hjG⟩ : Fin G.length)]
  apply Bool.eq_iff_iff.mpr
  rw [Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff, decide_eq_true_eq,
    StageRank.mem_unreadPool]
  have hget : G.getD j 0 = G.get ⟨j, hjG⟩ := List.getD_eq_getElem _ _ hjG
  rw [hget]
  exact not_congr (readsBefore_iff_mem_queriedPositions π (G.get ⟨j, hjG⟩) v)

/-- A finite Boolean zero test for every entry of the coded rectangle. -/
def zeroMatrix (c : Data) : Bool :=
  boundedAll (fun i => boundedAll (fun j => !entry (rows c) i j) (width c)) (rank c)

theorem computable_zeroMatrix : Computable zeroMatrix := by
  have hc : Computable (fun p : (Data × ℕ) × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hi : Computable (fun p : (Data × ℕ) × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  have he := computable_entry.comp ((computable_rows.comp hc).pair (hi.pair Computable.snd))
  have hb := (computable_boundedAll
    (p := fun p : Data × ℕ => fun j => !entry (rows p.1) p.2 j)
    (Primrec.not.to_comp.comp he).to₂).comp
      (Computable.id.pair (computable_width.comp Computable.fst))
  have hall := (computable_boundedAll
    (p := fun c : Data => fun i => boundedAll (fun j => !entry (rows c) i j) (width c))
    hb.to₂).comp (Computable.id.pair computable_rank)
  exact hall

theorem zeroMatrix_eq_true (c : Data) : zeroMatrix c = true ↔ matrix c = 0 := by
  rw [zeroMatrix, boundedAll_eq_true]
  constructor
  · intro h
    ext i j
    have hz := (boundedAll_eq_true _ _).mp (h i.val i.isLt) j.val j.isLt
    have he : entry (rows c) i.val j.val = false := by simpa using hz
    change boolEquivF2 (entry (rows c) i.val j.val) = (0 : ZMod 2)
    rw [he]
    rfl
  · intro h i hi
    rw [boundedAll_eq_true]
    intro j hj
    have hz := congrFun (congrFun h (⟨i, hi⟩ : Fin (rank c))) (⟨j, hj⟩ : Fin (width c))
    have he : entry (rows c) i j = false := boolEquivF2.injective hz
    simp only [he, Bool.not_false]

/-- Check whether full unread row rank remains. -/
def fullRankTest (π : ScanRule) (G : List ℕ) (c : Data) (v : List Bool) : Bool :=
  maskedFullRank c (unreadMask π G v)

/-- Check whether unread row rank is zero. -/
def zeroRankTest (π : ScanRule) (G : List ℕ) (c : Data) (v : List Bool) : Bool :=
  zeroMatrix (maskCode c (unreadMask π G v))

theorem computable_fullRankTest (π : ScanRule) {α : Type*} [Primcodable α]
    {G : α → List ℕ} {c : α → Data} {v : α → List Bool}
    (hG : Computable G) (hc : Computable c) (hv : Computable v) :
    Computable (fun p => fullRankTest π (G p) (c p) (v p)) :=
  computable_maskedFullRank.comp hc ((computable_unreadMask π).comp (hG.pair hv))

theorem computable_zeroRankTest (π : ScanRule) {α : Type*} [Primcodable α]
    {G : α → List ℕ} {c : α → Data} {v : α → List Bool}
    (hG : Computable G) (hc : Computable c) (hv : Computable v) :
    Computable (fun p => zeroRankTest π (G p) (c p) (v p)) :=
  computable_zeroMatrix.comp
    (computable_maskCode.comp hc ((computable_unreadMask π).comp (hG.pair hv)))

theorem fullRankTest_eq_true (π : ScanRule) (G : List ℕ) (hG : G.Nodup)
    {m r : ℕ} (a : Entry) (ha : GoodEntry G.length m r a)
    (y : Fin r → ZMod 2) (v : List Bool) :
    fullRankTest π G a.2 v = true ↔
      (StageCandidate.block G.get hG.injective_get a ha y).UnreadFullRank π v := by
  rw [fullRankTest, unreadMask_eq_mask]
  exact (StageRank.unreadFullRank_iff_maskedFullRank _ _ _ _ _ _ _).symm

theorem zeroRankTest_eq_true (π : ScanRule) (G : List ℕ) (hG : G.Nodup)
    {m r : ℕ} (a : Entry) (ha : GoodEntry G.length m r a)
    (y : Fin r → ZMod 2) (v : List Bool) :
    zeroRankTest π G a.2 v = true ↔
      (StageCandidate.block G.get hG.injective_get a ha y).remainingRank π v = 0 := by
  rw [zeroRankTest, zeroMatrix_eq_true, unreadMask_eq_mask]
  exact (StageRank.remainingRank_eq_zero_iff_masked_matrix_eq_zero _ _ _ _ _ _ _).symm

/-- A rank drop has already occurred precisely when full unread rank is lost. -/
def dropTest (π : ScanRule) (G : List ℕ) (c : Data) (v : List Bool) : Bool :=
  !fullRankTest π G c v

/-- Strictly partial unread rank is positive and below full rank. -/
def partialTest (π : ScanRule) (G : List ℕ) (c : Data) (v : List Bool) : Bool :=
  !zeroRankTest π G c v && !fullRankTest π G c v

theorem computable_dropTest (π : ScanRule) {α : Type*} [Primcodable α]
    {G : α → List ℕ} {c : α → Data} {v : α → List Bool}
    (hG : Computable G) (hc : Computable c) (hv : Computable v) :
    Computable (fun p => dropTest π (G p) (c p) (v p)) :=
  Primrec.not.to_comp.comp (computable_fullRankTest π hG hc hv)

theorem computable_partialTest (π : ScanRule) {α : Type*} [Primcodable α]
    {G : α → List ℕ} {c : α → Data} {v : α → List Bool}
    (hG : Computable G) (hc : Computable c) (hv : Computable v) :
    Computable (fun p => partialTest π (G p) (c p) (v p)) :=
  Primrec.and.to_comp.comp
    (Primrec.not.to_comp.comp (computable_zeroRankTest π hG hc hv))
    (Primrec.not.to_comp.comp (computable_fullRankTest π hG hc hv))

theorem dropTest_eq_true (π : ScanRule) (G : List ℕ) (hG : G.Nodup)
    {m r : ℕ} (a : Entry) (ha : GoodEntry G.length m r a)
    (y : Fin r → ZMod 2) (v : List Bool) :
    dropTest π G a.2 v = true ↔
      (StageCandidate.block G.get hG.injective_get a ha y).remainingRank π v < r := by
  rw [dropTest, Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff]
  let B := StageCandidate.block G.get hG.injective_get a ha y
  have h := (fullRankTest_eq_true π G hG a ha y v).trans
    (B.unreadFullRank_iff_remainingRank π v)
  apply (not_congr h).trans
  have hle : B.remainingRank π v ≤ r := B.remainingRank_le π v
  change (¬B.remainingRank π v = r) ↔ B.remainingRank π v < r
  omega

theorem partialTest_eq_true (π : ScanRule) (G : List ℕ) (hG : G.Nodup)
    {m r : ℕ} (a : Entry) (ha : GoodEntry G.length m r a)
    (y : Fin r → ZMod 2) (v : List Bool) :
    partialTest π G a.2 v = true ↔
      0 < (StageCandidate.block G.get hG.injective_get a ha y).remainingRank π v ∧
        (StageCandidate.block G.get hG.injective_get a ha y).remainingRank π v < r := by
  change (!zeroRankTest π G a.2 v && dropTest π G a.2 v) = true ↔ _
  rw [Bool.and_eq_true, dropTest_eq_true π G hG a ha y v,
    Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff]
  apply and_congr _ Iff.rfl
  exact (not_congr (zeroRankTest_eq_true π G hG a ha y v)).trans Nat.pos_iff_ne_zero.symm

end Klr.StageRankCode
