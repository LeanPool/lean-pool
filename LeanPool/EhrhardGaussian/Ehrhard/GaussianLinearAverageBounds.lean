/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianLinearAverage

/-! # Uniform bounds for averages of bounded smooth Gaussian observables -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open EhrhardGaussian.Gaussian (standardGaussianMeasure)

namespace EhrhardGaussian.Ehrhard


/-- A uniform absolute bound is preserved by Gaussian linear averaging. -/
theorem abs_gaussianLinearAverage_le {E : Type*} {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (J : (Fin n → ℝ) → E → (Fin n → ℝ)) {C : ℝ} (hbound : ∀ y, |F y| ≤ C) (p : E) :
    |∫ z, F (J z p) ∂standardGaussianMeasure n| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (f := fun z => F (J z p)) (C := C)
    (ae_of_all (standardGaussianMeasure n) fun z => by
      simpa only [Real.norm_eq_abs] using hbound (J z p))
  simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



end EhrhardGaussian.Ehrhard

end
