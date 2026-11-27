/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ComplexifiedOperator
public import LeanPool.VacuumBellSeparation.FreeField.RealCommutation

/-!
# Literal statement construction extracted from Gaussian/SourceGram

The moved declarations retain their original text. Later target proofs remain separate.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap HilbertComplexification
open scoped ComplexConjugate

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Source map linear. -/
noncomputable def sourceMapLinear (K : E →ₗᵢ[ℝ] H) : HilbertComplexification E →ₗ[ℂ] H where
  toFun z := K z.re + Complex.I • K z.im
  map_add' z w := by simp [smul_add]; abel
  map_smul' c z := by
    have hre : (c.re : ℂ) + Complex.I * (c.im : ℂ) = c := by
      apply Complex.ext <;> simp
    have him : -(c.im : ℂ) + Complex.I * (c.re : ℂ) = c * Complex.I := by
      apply Complex.ext <;> simp
    simp only [re_smul, im_smul, map_sub, map_add, map_smul,
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_add, smul_smul]
    calc
      ((c.re : ℂ) • K z.re - (c.im : ℂ) • K z.im) +
          ((Complex.I * (c.im : ℂ)) • K z.re +
            (Complex.I * (c.re : ℂ)) • K z.im) =
          ((c.re : ℂ) + Complex.I * (c.im : ℂ)) • K z.re +
            (-(c.im : ℂ) + Complex.I * (c.re : ℂ)) • K z.im := by module
      _ = c • K z.re + (c * Complex.I) • K z.im := by rw [hre, him]

omit [CompleteSpace E] [CompleteSpace H] in
theorem norm_sourceMapLinear_le (K : E →ₗᵢ[ℝ] H) (z : HilbertComplexification E) :
    ‖sourceMapLinear K z‖ ≤ Real.sqrt 2 * ‖z‖ := by
  have hsum : ‖z.re‖ + ‖z.im‖ ≤ Real.sqrt 2 * ‖z‖ := by
    apply nonneg_le_nonneg_of_sq_le_sq
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    simp only [← pow_two]
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), HilbertComplexification.norm_sq]
    nlinarith [sq_nonneg (‖z.re‖ - ‖z.im‖)]
  calc
    ‖sourceMapLinear K z‖ ≤ ‖K z.re‖ + ‖Complex.I • K z.im‖ := norm_add_le _ _
    _ = ‖z.re‖ + ‖z.im‖ := by simp [norm_smul]
    _ ≤ Real.sqrt 2 * ‖z‖ := hsum

/-- The bounded complex source map induced by the real physical embedding. -/
noncomputable def sourceMap (K : E →ₗᵢ[ℝ] H) : HilbertComplexification E →L[ℂ] H :=
  (sourceMapLinear K).mkContinuous (Real.sqrt 2) (norm_sourceMapLinear_le K)


/-- The commutation operator on the actual Hilbert complexification. -/
noncomputable def complexCommutation (K : E →ₗᵢ[ℝ] H) :
    HilbertComplexification E →L[ℂ] HilbertComplexification E :=
  complexify (realCommutation K)


end VacuumBellSeparation.Gaussian
