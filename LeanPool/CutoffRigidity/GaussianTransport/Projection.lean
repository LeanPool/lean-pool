/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # The Gaussian coordinate of an isometric splitting -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace CutoffRigidity.Riemann

/-- The abstract output of the splitting theorem used by the transport argument. -/
structure SplitData (M N : Type*) [PseudoEMetricSpace M] [MeasurableSpace M]
    [PseudoEMetricSpace N] [MeasurableSpace N] (k : ℕ) (ρ : ℝ) (μ : Measure M) where
  /-- The map into the Euclidean factor and its complement. -/
  Φ : M → EuclideanSpace ℝ (Fin k) × N
  /-- The marginal on the complementary factor. -/
  μ' : Measure N
  prob' : IsProbabilityMeasure μ'
  aemeasurable : AEMeasurable Φ μ
  dist_sq : ∀ x y, edist x y ^ 2 = edist (Φ x).1 (Φ y).1 ^ 2 + edist (Φ x).2 (Φ y).2 ^ 2
  map_eq : μ.map Φ = (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
    (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).prod μ'

variable {M N : Type*} [PseudoEMetricSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [PseudoEMetricSpace N] [MeasurableSpace N] {k : ℕ} {ρ : ℝ} {μ : Measure M}

namespace SplitData

variable (D : SplitData M N k ρ μ)

/-- The Euclidean coordinate. -/
def proj (x : M) : EuclideanSpace ℝ (Fin k) := (D.Φ x).1

omit [OpensMeasurableSpace M] in
theorem edist_proj_le (x y : M) : edist (D.proj x) (D.proj y) ≤ edist x y := by
  have h := D.dist_sq x y
  have h2 : edist (D.proj x) (D.proj y) ^ 2 ≤ edist x y ^ 2 := by
    rw [h]; exact le_self_add
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h2

omit [OpensMeasurableSpace M] in
theorem lipschitz_proj : LipschitzWith 1 D.proj :=
  LipschitzWith.of_edist_le fun x y => by simpa using D.edist_proj_le x y

theorem measurable_proj : Measurable D.proj := D.lipschitz_proj.continuous.measurable

omit [OpensMeasurableSpace M] in
/-- The projection of `μ` is the Gaussian `N(0, ρ⁻¹ I)`. -/
theorem map_proj_eq :
    μ.map D.proj = multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
      (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
  have := D.prob'
  have h : D.proj = Prod.fst ∘ D.Φ := rfl
  rw [h, ← AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable D.aemeasurable,
    D.map_eq]
  simp

end SplitData

end CutoffRigidity.Riemann
