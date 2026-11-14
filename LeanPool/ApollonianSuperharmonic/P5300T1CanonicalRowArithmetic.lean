/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5260T1PlacementLedger
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCentroid
public import LeanPool.ApollonianSuperharmonic.DiamondCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import Mathlib.Algebra.Order.Ring.Star

-- [TABLET NODE: P5300T1CanonicalRowArithmetic]

/-!
# P5300T1CanonicalRowArithmetic

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5300T1CanonicalRowArithmetic (K : DiamondParameter)
    (i : Fin 3) (s : Fin 4)
    (hp : 0 < ((DiamondRecursiveQuadruple K) i.succ).1)
    (hj : 0 < ((DiamondRecursiveQuadruple K)
      ((if Even s.val then i - 1 else i + 1).succ)).1) :
    let q := DiamondRecursiveQuadruple K
    let b : Bool := decide (s.val % 2 = 1)
    let j := if Even s.val then i - 1 else i + 1
    let M := P5260T1PlacementLedger K.1 i b
    let C : GaussianInt := ⟨0, 2 * (K.1 : Int)⟩
    let c : Fin 3 → GaussianInt :=
      ![⟨1, 4 * (K.1 : Int) + 1⟩,
        ⟨-2 * (K.1 : Int) - 1, 2 * (K.1 : Int) - 1⟩,
        ⟨2 * (K.1 : Int), 0⟩]
    let P := fun t => P5124T1ParentModel K.1 t true
    (1 < K.1 ∨ (i = 1 ∧ b = false) ∨ (i = 0 ∧ b = true)) ∧
    (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q 0) (q i.succ)
         else BandVectors.1 (q i.succ) (q 0)) =
      (if s.val < 2 then M.2.1.1 else -M.2.1.1) ∧
    (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q i.succ) (q 0)
         else BandVectors.1 (q 0) (q i.succ)) =
      (if s.val < 2 then M.2.1.2 else -M.2.1.2) ∧
    ∃ tW tZ : GaussianInt,
      M.1.1.cells = (TileTranslation (P i) tW).cells ∧
      M.1.2.cells = (TileTranslation (P j) tZ).cells ∧
      TileCentroid (TileTranslation (P i)
          (if s.val < 2 then tW else C - tW - c i)) -
        TileCentroid (DiamondTile K.1) =
          (1 / 2 : Real) • GaussianRealPoint
            ((⟨0, 1⟩ : GaussianInt) ^ s.val *
              (BandVectors.1 (q i.succ) (q 0) +
                BandVectors.1 (q 0) (q i.succ))) ∧
      TileCentroid (TileTranslation (P j)
          (if s.val < 2 then tZ else C - tZ - c j)) -
        TileCentroid (DiamondTile K.1) =
          (1 / 2 : Real) • GaussianRealPoint
            ((⟨0, 1⟩ : GaussianInt) ^ s.val *
              (if Even s.val then
                BandVectors.1 (q 0) (q (i - 1).succ) -
                  BandVectors.1 (q (i - 1).succ) (q 0)
               else BandVectors.1 (q (i + 1).succ) (q 0) -
                  BandVectors.1 (q 0) (q (i + 1).succ))) := by
-- BODY
  classical
  dsimp only
  let b : Bool := decide (s.val % 2 = 1)
  let j : Fin 3 := if Even s.val then i - 1 else i + 1
  let M := P5260T1PlacementLedger K.1 i b
  let C : GaussianInt := ⟨0, 2 * (K.1 : Int)⟩
  let c : Fin 3 → GaussianInt :=
    ![⟨1, 4 * (K.1 : Int) + 1⟩,
      ⟨-2 * (K.1 : Int) - 1, 2 * (K.1 : Int) - 1⟩,
      ⟨2 * (K.1 : Int), 0⟩]
  let P := fun t => P5124T1ParentModel K.1 t true
  let tW : GaussianInt := if b then
    ![⟨-(K.1 : Int) - 1, -(K.1 : Int)⟩,
      ⟨(K.1 : Int) + 1, -(K.1 : Int)⟩, ⟨0, 2 * (K.1 : Int)⟩] i else 0
  let tZ : GaussianInt := if b then 0 else
    ![⟨0, 2 * (K.1 : Int)⟩, ⟨-(K.1 : Int) - 1, -(K.1 : Int)⟩,
      ⟨(K.1 : Int) + 1, -(K.1 : Int)⟩] i
  have hk : 1 ≤ K.1 := K.2
  obtain ⟨_, hproper, hv0, hv1, hv2, _⟩ := DiamondCoordinateConfiguration K
  have flip := (VectorRecursionLaws _ hproper.1).2.2.2.2 hproper
  have hv (t : Fin 3) : BandVectors.1 ((DiamondRecursiveQuadruple K) t.succ)
      ((DiamondRecursiveQuadruple K) 0) =
      ![⟨(K.1 : Int) + 1, (K.1 : Int)⟩,
        ⟨-(K.1 : Int) - 1, (K.1 : Int)⟩,
        ⟨0, -2 * (K.1 : Int)⟩] t := by
    fin_cases t
    · exact hv0
    · exact hv1
    · exact hv2
  have hv' (t : Fin 3) : BandVectors.1 ((DiamondRecursiveQuadruple K) 0)
      ((DiamondRecursiveQuadruple K) t.succ) =
      ![⟨-(K.1 : Int), (K.1 : Int) + 1⟩,
        ⟨-(K.1 : Int), -(K.1 : Int) - 1⟩,
        ⟨2 * (K.1 : Int), 0⟩] t := by
    rw [(flip t).1, hv]
    fin_cases t <;> ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
  have centroid (n : Nat) : TileCentroid (DiamondTile n) = (0, (n : Real)) := by
    by_cases hn : 0 < n
    · exact P4194T1DiamondCentroid n hn
    · have : n = 0 := by omega
      subst n
      simp [DiamondTile, DiamondCellDomain, TileCentroid]
  have singleton (z : GaussianInt) : TileCentroid (⟨{z}, z⟩ : ProtoTile) =
      ((z.re : Real) + 1 / 2, (z.im : Real) + 1 / 2) := by
    simp [TileCentroid]
  have ht (T : ProtoTile) (v : GaussianInt) :=
    (TileTranslationFormulas T v).2.2.2.2.1
  have hpc (t : Fin 3) : TileCentroid (P t) =
      ![((1 / 2 : Real), 2 * (K.1 : Real) + 1 / 2),
        (-(K.1 : Real) - 1 / 2, (K.1 : Real) - 1 / 2),
        ((K.1 : Real), 0)] t := by
    fin_cases t <;>
      simp only [P5124T1ParentModel, ↓reduceIte, Nat.succ_eq_add_one, Nat.reduceAdd,
          Int.reduceNeg, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
          singleton, Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one, one_div,
          Prod.mk.injEq, P, Fin.reduceFinMk, Matrix.cons_val, ht, centroid, Nat.cast_sub hk,
          Nat.cast_one, zero_add, sub_add_sub_cancel, sub_self, Fin.zero_eta, Int.cast_zero,
          Int.cast_mul, Int.cast_ofNat];
      first | (constructor <;> ring)
  have image_add (A : Finset GaussianInt) (u v : GaussianInt) :
      (A.image (GaussianTranslation u)).image (GaussianTranslation v) =
        A.image (GaussianTranslation (u + v)) := by
    rw [Finset.image_image]
    congr 1
    funext x
    simp [GaussianTranslation, add_assoc]
  have hI2 : (⟨0, 1⟩ : GaussianInt) ^ 2 = -1 := by
    norm_num [pow_two, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul]
  have hI3 : (⟨0, 1⟩ : GaussianInt) ^ 3 = -⟨0, 1⟩ := by
    rw [pow_succ, hI2]
    simp
  have hp0 : (0 : Fin 3) - 1 = 2 := by decide
  have hp1 : (1 : Fin 3) - 1 = 0 := by decide
  have hp2 : (2 : Fin 3) - 1 = 1 := by decide
  have hn0 : (0 : Fin 3) + 1 = 1 := by decide
  have hn1 : (1 : Fin 3) + 1 = 2 := by decide
  have hn2 : (2 : Fin 3) + 1 = 0 := by decide
  refine ⟨?_, ?_, ?_, tW, tZ, ?_, ?_, ?_, ?_⟩
  · by_cases h : 1 < K.1
    · exact Or.inl h
    · have heq : K.1 = 1 := by omega
      fin_cases i <;> fin_cases s <;>
        simp_all [DiamondRecursiveQuadruple, Nat.even_iff,
          ]
  · simp only [hv, hv']
    fin_cases i <;> fin_cases s <;>
      norm_num [P5260T1PlacementLedger, Nat.even_iff, Zsqrtd.ext_iff,
        hI2, hI3, Zsqrtd.re_mul, Zsqrtd.im_mul]
  · simp only [hv, hv']
    fin_cases i <;> fin_cases s <;>
      norm_num [P5260T1PlacementLedger, Nat.even_iff, Zsqrtd.ext_iff,
        hI2, hI3, Zsqrtd.re_mul, Zsqrtd.im_mul] <;>
      first | ring1
  · change M.1.1.cells = (TileTranslation (P i) tW).cells
    fin_cases i <;> fin_cases s <;>
      simp only [P5260T1PlacementLedger, Nat.mod_self, zero_ne_one, decide_false,
          Bool.false_eq_true, ↓reduceIte, Nat.succ_eq_add_one, Nat.reduceAdd,
          P5124T1ParentModel, Int.reduceNeg, TileTranslation, GaussianTranslation,
          Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, neg_mul,
          Fin.mk_one, Finset.image_singleton, add_zero, M, b, tW, P, Fin.reduceFinMk,
          image_add, Fin.zero_eta, Nat.mod_succ, decide_true, Zsqrtd.add_def,
          sub_add_add_cancel, neg_add_cancel, Finset.singleton_inj, Zsqrtd.ext_iff, true_and,
          zero_add, Nat.reduceMod, Nat.zero_mod] <;>
      ring
  · change M.1.2.cells = (TileTranslation (P j) tZ).cells
    fin_cases i <;> fin_cases s <;>
      simp only [P5260T1PlacementLedger, Nat.mod_self, zero_ne_one, decide_false,
          Bool.false_eq_true, ↓reduceIte, Nat.succ_eq_add_one, Nat.reduceAdd,
          P5124T1ParentModel, Int.reduceNeg, TileTranslation, GaussianTranslation,
          Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, neg_mul,
          Fin.mk_one, even_two, sub_self, Finset.image_singleton, Zsqrtd.add_def, zero_add,
          Finset.singleton_inj, Zsqrtd.ext_iff, true_and, M, b, tZ, P, j, Fin.reduceFinMk,
          hp2, sub_add_add_cancel, neg_add_cancel, Fin.zero_eta, hp0, image_add, add_zero,
          Nat.mod_succ, decide_true, Nat.even_iff, one_ne_zero, hn1, hn2, hn0, Nat.reduceMod,
          Nat.zero_mod, Even.zero] <;>
      ring
  · change TileCentroid (TileTranslation (P i)
        (if s.val < 2 then tW else C - tW - c i)) -
      TileCentroid (DiamondTile K.1) = _
    rw [ht, hpc, centroid]
    simp only [hv, hv']
    fin_cases i <;> fin_cases s <;>
      norm_num [tW, b, C, c, GaussianRealPoint, Prod.ext_iff, hI2, hI3,
        GaussianInt.toComplex_def, Zsqrtd.re_mul, Zsqrtd.im_mul] <;>
      first | ring1 | (constructor <;> ring1)
  · change TileCentroid (TileTranslation (P j)
        (if s.val < 2 then tZ else C - tZ - c j)) -
      TileCentroid (DiamondTile K.1) = _
    rw [ht, hpc, centroid]
    simp only [hv, hv']
    fin_cases i <;> fin_cases s <;>
      norm_num [j, Nat.even_iff, hp0, hp1, hp2, hn0, hn1, hn2,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    all_goals
      norm_num [tZ, b, C, c, GaussianRealPoint, Prod.ext_iff, hI2, hI3,
        GaussianInt.toComplex_def, Zsqrtd.re_mul, Zsqrtd.im_mul,
        -GaussianInt.intCast_re, -GaussianInt.intCast_im,
        hp0, hp1, hp2, hn0, hn1, hn2, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail, Fin.add_def, Fin.sub_def];
      first | ring1 | (constructor <;> ring1)

end ApollonianSuperharmonic

end
