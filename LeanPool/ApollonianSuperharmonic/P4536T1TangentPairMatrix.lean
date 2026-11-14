/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CircleMatrix
public import LeanPool.ApollonianSuperharmonic.VectorNonvanishing

-- [TABLET NODE: P4536T1TangentPairMatrix]

/-!
# P4536T1TangentPairMatrix

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4536T1TangentPairMatrix (C : BandCircle)
    (q : Fin 4 → CircleCoordinates) (hq : SemiProperQuadruple q)
    (i j : Fin 4) (hij : i ≠ j) (hC : q j = C.1.1) :
    (BandVectors.2 (q i) (q j)).re =
      CircleMatrix C 0 0 * (BandVectors.1 (q i) (q j)).re +
        CircleMatrix C 0 1 * (BandVectors.1 (q i) (q j)).im ∧
    (BandVectors.2 (q i) (q j)).im =
      CircleMatrix C 1 0 * (BandVectors.1 (q i) (q j)).re +
        CircleMatrix C 1 1 * (BandVectors.1 (q i) (q j)).im := by
-- BODY
  have hpos : 0 < (q j).1 := hC ▸ C.2
  have hv := VectorNonvanishing q hq i j hij (Or.inr hpos)
  have hident := VectorSquareProduct q hq i j hij
  have htan := TangencyCoordinateIdentity q hq i j hij
  have hnorm : Zsqrtd.norm (BandVectors.1 (q i) (q j)) = (q i).1 + (q j).1 := by
    have hs : Zsqrtd.norm (BandVectors.1 (q i) (q j)) ^ 2 =
        ((q i).1 + (q j).1) ^ 2 := by
      calc
        _ = Zsqrtd.norm (BandVectors.1 (q i) (q j) ^ 2) := by
          simp [pow_two]
        _ = _ := by rw [hident.1]; exact htan
    have hn := GaussianInt.norm_nonneg (BandVectors.1 (q i) (q j))
    have nn := (SemiProperForestClassification q hq).1
    have hc := add_nonneg (nn i) (nn j)
    nlinarith
  have hgauss : BandVectors.1 (q i) (q j) +
      (q j).2 * star (BandVectors.1 (q i) (q j)) =
      (2 : GaussianInt) * (q j).1 * BandVectors.2 (q i) (q j) := by
    apply mul_left_cancel₀ hv
    calc
      _ = BandVectors.1 (q i) (q j) ^ 2 +
          (q j).2 * (BandVectors.1 (q i) (q j) *
            star (BandVectors.1 (q i) (q j))) := by ring
      _ = (q j).1 * ((q i).2 + (q j).2) := by
        rw [← Zsqrtd.norm_eq_mul_conj, hnorm, hident.1]
        push_cast
        ring
      _ = _ := by
        rw [← hident.2]
        ring
  have hre := congrArg Zsqrtd.re hgauss
  have him := congrArg Zsqrtd.im hgauss
  simp only [Int.reduceNeg, Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.re_star, neg_mul, one_mul,
      Zsqrtd.im_star, mul_neg, neg_neg, Zsqrtd.re_ofNat, Nat.cast_ofNat, Zsqrtd.re_intCast,
      Zsqrtd.im_ofNat, mul_zero, Zsqrtd.im_intCast, add_zero, Zsqrtd.im_mul, zero_mul,
      Zsqrtd.im_add] at hre him
  rw [hC] at hre him
  have hrer : ((BandVectors.1 (q i) C.1.1).re : ℝ) +
      ((C.1.1.2.re : ℝ) * (BandVectors.1 (q i) C.1.1).re +
        (C.1.1.2.im : ℝ) * (BandVectors.1 (q i) C.1.1).im) =
      2 * (C.1.1.1 : ℝ) * (BandVectors.2 (q i) C.1.1).re := by
    exact_mod_cast hre
  have himr : ((BandVectors.1 (q i) C.1.1).im : ℝ) +
      (-((C.1.1.2.re : ℝ) * (BandVectors.1 (q i) C.1.1).im) +
        (C.1.1.2.im : ℝ) * (BandVectors.1 (q i) C.1.1).re) =
      2 * (C.1.1.1 : ℝ) * (BandVectors.2 (q i) C.1.1).im := by
    exact_mod_cast him
  have hcurv : 0 < (C.1.1.1 : ℝ) := by exact_mod_cast C.2
  have hmatrix : CircleMatrix C =
      (2 * (C.1.1.1 : ℝ))⁻¹ •
        ![![1 + (C.1.1.2.re : ℝ), (C.1.1.2.im : ℝ)],
          ![(C.1.1.2.im : ℝ), 1 - (C.1.1.2.re : ℝ)]] := by
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [CircleMatrix, BandCircleEuclideanData]
    all_goals field_simp
  rw [hC, hmatrix]
  constructor
  · change (BandVectors.2 (q i) C.1.1).re =
      (2 * (C.1.1.1 : ℝ))⁻¹ * (1 + (C.1.1.2.re : ℝ)) *
          (BandVectors.1 (q i) C.1.1).re +
        (2 * (C.1.1.1 : ℝ))⁻¹ * (C.1.1.2.im : ℝ) *
          (BandVectors.1 (q i) C.1.1).im
    field_simp [ne_of_gt hcurv]
    nlinarith [hrer]
  · change (BandVectors.2 (q i) C.1.1).im =
      (2 * (C.1.1.1 : ℝ))⁻¹ * (C.1.1.2.im : ℝ) *
          (BandVectors.1 (q i) C.1.1).re +
        (2 * (C.1.1.1 : ℝ))⁻¹ * (1 - (C.1.1.2.re : ℝ)) *
          (BandVectors.1 (q i) C.1.1).im
    field_simp [ne_of_gt hcurv]
    nlinarith [himr]

end ApollonianSuperharmonic

end
