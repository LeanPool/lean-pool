/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Provider.EhrhardInequality

/-! # Ehrhard inequality for convex Gaussian sets -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal Pointwise

namespace EhrhardGaussian

/-- **Ehrhard's inequality for convex sets** (FMP25 Theorem 2.1): for a Gaussian measure `γ`
on `ℝⁿ`, convex `A, B` and `t ∈ [0, 1]`,
`γ((1−t)A + tB) ≥ Φ((1−t) Φ⁻¹(γ A) + t Φ⁻¹(γ B))`, written with thresholds `a ≤ Φ⁻¹(γ A)`,
`b ≤ Φ⁻¹(γ B)` (which encodes the conventions `Φ⁻¹(0) = −∞`, `Φ⁻¹(1) = +∞`). -/
theorem ehrhard_inequality {n : ℕ} (γ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian γ]
    (A B : Set (EuclideanSpace ℝ (Fin n))) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (a b : ℝ)
    (ha : cdf (gaussianReal 0 1) a ≤ (γ A).toReal) (hb : cdf (gaussianReal 0 1) b ≤ (γ B).toReal) :
    cdf (gaussianReal 0 1) ((1 - t) * a + t * b) ≤ (γ ((1 - t) • A + t • B)).toReal :=
  by exact EhrhardGaussian.Provider.ehrhard_inequality γ A B hA hB t ht₀ ht₁ a b ha hb
end EhrhardGaussian

end

end
