/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianSetInequality

/-! # Ehrhard’s inequality for convex sets

Ehrhard’s inequality for convex sets, stated as Theorem 2.1 of FMP25, follows from restricted
Gaussian interpolation, compact approximation and affine realization of Gaussian laws, including
singular covariance.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Pointwise

namespace EhrhardGaussian.Provider
/-- Gaussian measures satisfy Ehrhard’s inequality for convex sets, including singular Gaussian
measures (Theorem 2.1 of FMP25). -/
theorem ehrhard_inequality {n : ℕ} (γ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian γ]
    (A B : Set (EuclideanSpace ℝ (Fin n))) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (a b : ℝ)
    (ha : cdf (gaussianReal 0 1) a ≤ (γ A).toReal) (hb : cdf (gaussianReal 0 1) b ≤ (γ B).toReal) :
    cdf (gaussianReal 0 1) ((1 - t) * a + t * b) ≤ (γ ((1 - t) • A + t • B)).toReal :=
  EhrhardGaussian.Ehrhard.gaussian_set_ehrhard γ hA hB t ht₀ ht₁ a b ha hb

end EhrhardGaussian.Provider

end
