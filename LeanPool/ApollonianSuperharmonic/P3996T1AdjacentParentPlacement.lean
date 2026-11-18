/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPrototileReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import Mathlib.Algebra.Order.Ring.Star

-- [TABLET NODE: P3996T1AdjacentParentPlacement]

/-!
# P3996T1AdjacentParentPlacement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3996T1AdjacentParentPlacement
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (i : Fin 3) (s : Fin 4) (U : ProtoTile) (hU : BandPrototile (q 0) U) :
    ∃ Z : ProtoTile,
      BandPrototile (q ((if Even s.val then i - 1 else i + 1).succ)) Z ∧
      TileCentroid Z - TileCentroid U = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then
              BandVectors.1 (q 0) (q ((i - 1).succ)) -
                BandVectors.1 (q ((i - 1).succ)) (q 0)
             else
              BandVectors.1 (q ((i + 1).succ)) (q 0) -
                BandVectors.1 (q 0) (q ((i + 1).succ)))) := by
-- BODY
  have incoming (j : Fin 3) :
      BandVectors.1 (q j.succ) (q 0) =
        BandVectors.1 (q j.succ) (q ((j + 2).succ)) -
          (⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 (q ((j + 1).succ)) (q j.succ) := by
    fin_cases j
    · exact (VectorRecursionLaws q hq.1).2.2.1
    · exact (VectorRecursionLaws ![q 0, q 2, q 3, q 1]
        (SemiProperQuadruple.rotate hq.1)).2.2.1
    · exact (VectorRecursionLaws ![q 0, q 3, q 1, q 2]
        (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1))).2.2.1
  have superbasis (j : Fin 3) :
      BandVectors.1 (q ((j + 2).succ)) (q ((j + 1).succ)) +
        BandVectors.1 (q j.succ) (q ((j + 2).succ)) +
        BandVectors.1 (q ((j + 1).succ)) (q j.succ) = 0 := by
    have law := (VectorRecursionLaws q hq.1).1
    fin_cases j
    · exact law
    · change BandVectors.1 (q 1) (q 3) + BandVectors.1 (q 2) (q 1) +
        BandVectors.1 (q 3) (q 2) = 0
      simpa only [add_assoc, add_left_comm, add_comm] using law
    · change BandVectors.1 (q 2) (q 1) + BandVectors.1 (q 3) (q 2) +
        BandVectors.1 (q 1) (q 3) = 0
      simpa only [add_assoc, add_left_comm, add_comm] using law
  let j : Fin 3 := if Even s.val then i - 1 else i + 1
  let I : GaussianInt := ⟨0, 1⟩
  let e := BandVectors.1 (q ((j + 2).succ)) (q ((j + 1).succ))
  let x := BandVectors.1 (q j.succ) (q ((j + 2).succ))
  let y := BandVectors.1 (q ((j + 1).succ)) (q j.succ)
  let a := BandVectors.1 (q j.succ) (q 0)
  have hs : e + x + y = 0 := superbasis j
  have ha : a = x - I * y := incoming j
  have hf : BandVectors.1 (q 0) (q j.succ) = I * a :=
    ((VectorRecursionLaws q hq.1).2.2.2.2 hq j).1
  let shift : GaussianInt := match s.val with
    | 0 => y
    | 1 => a + y
    | 2 => -y
    | _ => -a - y
  let sign : Bool := decide (s.val < 2)
  have he : e = -x - y := by
    calc e = (e + x + y) - x - y := by ring
         _ = -x - y := by rw [hs]; ring
  have algebra :
      I ^ s.val * (if Even s.val then I * a - a else a - I * a) =
        (if sign then (1 : GaussianInt) else -1) * (e - I * e) + 2 * shift := by
    fin_cases s <;> norm_num [sign, shift, I, show Even (0 : Nat) from by decide,
      show ¬Even (1 : Nat) from by decide,
      show Even (2 : Nat) from by decide,
      show ¬Even (3 : Nat) from by decide] <;>
      simp only [ha, he] <;> apply Zsqrtd.ext <;> simp [I, pow_succ] <;> ring
  obtain ⟨S, hS, _⟩ := BandPrototileReindexedDecomposition q hq U hU
  refine ⟨TileTranslation (S j sign) shift,
    BandPrototileTranslation _ _ shift (hS j sign).1, ?_⟩
  have hc := (hS j sign).2.2
  have target :
      (⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then
            BandVectors.1 (q 0) (q ((i - 1).succ)) -
              BandVectors.1 (q ((i - 1).succ)) (q 0)
           else
            BandVectors.1 (q ((i + 1).succ)) (q 0) -
              BandVectors.1 (q 0) (q ((i + 1).succ))) =
        (if sign then (1 : GaussianInt) else -1) * (e - I * e) + 2 * shift := by
    convert algebra using 1
    dsimp [I]
    congr 1
    split_ifs with h
    · have hj : j = i - 1 := ite_eq_left h
      rw [← hj, hf]
    · have hj : j = i + 1 := ite_eq_right h
      rw [← hj, hf]
  rw [target, (TileTranslationFormulas (S j sign) shift).2.2.2.2.1]
  change TileCentroid (S j sign) - TileCentroid U =
    (if sign = true then (1 : Real) else -1) •
      ((1 / 2 : Real) • (GaussianRealPoint e -
        (-(GaussianRealPoint e).2, (GaussianRealPoint e).1))) at hc
  have hc1 := congrArg Prod.fst hc
  have hc2 := congrArg Prod.snd hc
  cases hs : sign <;>
    simp only [hs, Prod.fst_sub, Bool.false_eq_true, ↓reduceIte, one_div, GaussianRealPoint,
        Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im, Prod.mk_sub_mk,
        sub_neg_eq_add, Prod.smul_mk, smul_eq_mul, neg_smul, one_smul, Prod.neg_mk,
        Prod.snd_sub, neg_mul, one_mul, neg_sub, Zsqrtd.re_add, Zsqrtd.re_sub, Zsqrtd.re_mul,
        zero_mul, mul_one, zero_add, Zsqrtd.re_ofNat, Nat.cast_ofNat, Zsqrtd.im_ofNat,
        mul_zero, add_zero, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_mul,
        Int.cast_ofNat, Zsqrtd.im_add, Zsqrtd.im_sub, Zsqrtd.im_mul, I] at hc1 hc2 ⊢ <;>
    apply Prod.ext <;> simp <;> linarith

end ApollonianSuperharmonic

end
