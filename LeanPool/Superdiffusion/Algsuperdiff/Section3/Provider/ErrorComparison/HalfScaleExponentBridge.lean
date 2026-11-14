/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties

/-!
# HalfScaleExponentBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Half-scale finite-exponent comparison

This file compares the finite `q = 1` multiscale ellipticity gauges at scale
parameter `s` with the finite `q = 2` gauges at parameter `s / 2`.

The comparison combines CoarseGraining's Jensen bounds for `q = 1` with the
exact weight identity `geometricWeight (s / 2) 2 = geometricWeight s 1`.

## Main results

* `LambdaSq_finite_one_le_half_two`: `Λ_{s,1} ≤ Λ_{s/2,2}`.
* `lambdaSq_finite_one_inv_le_half_two`: `λ_{s,1}^{-1} ≤ λ_{s/2,2}^{-1}`.
-/

namespace Algsuperdiff.Section3.Provider.ErrorComparison

open HCPolySupport

noncomputable section

private theorem real_rpow_one (x : ℝ) : Real.rpow x 1 = x :=
  Real.rpow_one x

private theorem real_rpow_neg_one (x : ℝ) : Real.rpow x (-1) = x⁻¹ :=
  Real.rpow_neg_one x

private theorem geometricWeight_half_two_eq_one (s : ℝ) (n : ℕ) :
    Book.Ch02.geometricWeight (s / 2) 2 n = Book.Ch02.geometricWeight s 1 n := by
  unfold Book.Ch02.geometricWeight Book.Ch02.geometricDiscount
  rw [show -(s / 2) * 2 = -s * 1 by ring]

private theorem LambdaSqFinite_two_eq_tsum {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (a : Book.Ch02.TriadicCoeffFamily d) :
    Book.Ch02.LambdaSqFinite Q s 2 a =
      ∑' n : ℕ,
        Book.Ch02.geometricWeight s 2 n *
          Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
  unfold Book.Ch02.LambdaSqFinite
  simp only [show (2 : ℝ) / 2 = 1 by norm_num, real_rpow_one]

private theorem lambdaSqFinite_two_inv_eq_tsum {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (a : Book.Ch02.TriadicCoeffFamily d) :
    (Book.Ch02.lambdaSqFinite Q s 2 a)⁻¹ =
      ∑' n : ℕ,
        Book.Ch02.geometricWeight s 2 n *
          Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a := by
  unfold Book.Ch02.lambdaSqFinite
  simp only [show (2 : ℝ) / 2 = 1 by norm_num, real_rpow_neg_one,
    real_rpow_one, inv_inv]

/-- The finite `q = 1` upper multiscale ellipticity at `s` is bounded by the
finite `q = 2` upper multiscale ellipticity at `s / 2`. -/
theorem LambdaSq_finite_one_le_half_two {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Book.Ch02.LambdaSq Q s (.finite 1) a ≤
      Book.Ch02.LambdaSq Q (s / 2) (.finite 2) a := by
  have hrhs :
      Book.Ch02.LambdaSq Q (s / 2) (.finite 2) a =
        ∑' n : ℕ,
          Book.Ch02.geometricWeight s 1 n *
            Book.Ch02.maxDescendantBMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) a := by
    rw [Book.Ch02.LambdaSq_finite, LambdaSqFinite_two_eq_tsum]
    exact tsum_congr fun n => by rw [geometricWeight_half_two_eq_one]
  rw [hrhs]
  exact
    Book.Ch02.LambdaSq_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale
      Q a hs

/-- The inverse finite `q = 1` lower multiscale ellipticity at `s` is bounded
by the inverse finite `q = 2` lower multiscale ellipticity at `s / 2`. -/
theorem lambdaSq_finite_one_inv_le_half_two {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    (Book.Ch02.lambdaSq Q s (.finite 1) a)⁻¹ ≤
      (Book.Ch02.lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
  have hrhs :
      (Book.Ch02.lambdaSq Q (s / 2) (.finite 2) a)⁻¹ =
        ∑' n : ℕ,
          Book.Ch02.geometricWeight s 1 n *
            Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) a := by
    rw [Book.Ch02.lambdaSq_finite, lambdaSqFinite_two_inv_eq_tsum]
    exact tsum_congr fun n => by rw [geometricWeight_half_two_eq_one]
  rw [hrhs]
  exact
    Book.Ch02.lambdaSq_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale
      Q a hs

end

end Algsuperdiff.Section3.Provider.ErrorComparison
