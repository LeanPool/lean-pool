/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GeneratorIntertwining
public import LeanPool.CutoffRigidity.PotentialSplitting
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Potential splitting forced by an affine eigenfunction

The affine eigenfunction equation is interpreted using the actual pointwise
Langevin differential operator. It determines the potential derivative along
the affine gradient; integrating this identity gives the Gaussian quadratic
potential in that direction. Spectral attainment and Hessian rigidity are
separate prerequisites.
-/

public section

namespace CutoffRigidity

open MeasureTheory
open scoped ENNReal

section DirectionalIntegration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Integrating an affine directional drift gives the exact quadratic increment
of the potential along each line. -/
theorem potential_line_increment_of_directional_drift
    (V : E → ℝ) (hV : Differentiable ℝ V) (v : E) (hv : ‖v‖ = 1)
    (ρ c : ℝ)
    (hdir : ∀ x : E, fderiv ℝ V x v = ρ * (inner ℝ v x + c))
    (x : E) (u : ℝ) :
    V (x + u • v) = V x + ρ * ((inner ℝ v x + c) * u + u ^ 2 / 2) := by
  let F : ℝ → ℝ := fun s => V (x + s • v) -
    ρ * ((inner ℝ v x + c) * s + s ^ 2 / 2)
  have hF (s : ℝ) : HasDerivAt F 0 s := by
    have hline : HasDerivAt (fun t : ℝ => x + t • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add x
    have hpot := (hV (x + s • v)).hasFDerivAt.comp_hasDerivAt s hline
    have hpoly := (((hasDerivAt_id s).const_mul (inner ℝ v x + c)).add
      (((hasDerivAt_id s).pow 2).div_const 2)).const_mul ρ
    have hsub := hpot.sub hpoly
    convert hsub using 1
    · ext t
      rfl
    · rw [hdir, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hv]
      simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
  have heq := is_const_of_deriv_eq_zero (fun s => (hF s).differentiableAt)
    (fun s => (hF s).deriv) u 0
  dsimp [F] at heq
  simp only [zero_smul, add_zero, mul_zero] at heq
  linarith

/-- Translating the Gaussian center to zero and subtracting the full quadratic
potential leaves an interaction invariant in the unit direction. -/
theorem centered_residual_invariant_of_directional_drift
    (V : E → ℝ) (hV : Differentiable ℝ V) (v : E) (hv : ‖v‖ = 1)
    (ρ c : ℝ)
    (hdir : ∀ x : E, fderiv ℝ V x v = ρ * (inner ℝ v x + c))
    (y : E) (u : ℝ) :
    V (y + u • v - c • v) - ρ / 2 * ‖y + u • v‖ ^ 2 =
      V (y - c • v) - ρ / 2 * ‖y‖ ^ 2 := by
  have harg : y + u • v - c • v = (y - c • v) + u • v := by abel
  rw [harg, potential_line_increment_of_directional_drift V hV v hv ρ c hdir,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv,
    norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right, real_inner_comm y v, hv]
  ring

end DirectionalIntegration

section AffineEigenfunction

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A nonconstant affine eigenfunction forces the exact directional derivative
of the potential in its normalized gradient direction. -/
theorem affine_eigenfunction_directional_drift
    (V : E → ℝ) (a : E) (b ρ : ℝ)
    (heigen : ∀ x : E,
      langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
        -ρ * (inner ℝ a x + b)) (x : E) :
    fderiv ℝ V x (‖a‖⁻¹ • a) = ρ * (inner ℝ (‖a‖⁻¹ • a) x + b / ‖a‖) := by
  have he := heigen x
  change langevinDifferentialOperator V (fun y => (innerSL ℝ a) y + b) x = _ at he
  rw [langevinDifferentialOperator_affine V (innerSL ℝ a) b x] at he
  change -inner ℝ a (gradient V x) = -ρ * (inner ℝ a x + b) at he
  have hinner : inner ℝ (gradient V x) a = ρ * (inner ℝ a x + b) := by
    rw [real_inner_comm]
    linarith
  rw [← inner_gradient_left, inner_smul_right, hinner, real_inner_smul_left]
  ring

/-- The eigenfunction equation fixes the potential increment on its gradient lines. -/
theorem affine_eigenfunction_potential_increment
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : E) (ha : a ≠ 0) (b ρ : ℝ)
    (heigen : ∀ x : E,
      langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
        -ρ * (inner ℝ a x + b)) (x : E) (u : ℝ) :
    V (x + u • (‖a‖⁻¹ • a)) = V x +
      ρ * ((inner ℝ (‖a‖⁻¹ • a) x + b / ‖a‖) * u + u ^ 2 / 2) := by
  apply potential_line_increment_of_directional_drift V hV (‖a‖⁻¹ • a) _ ρ (b / ‖a‖)
    (affine_eigenfunction_directional_drift V a b ρ heigen) x u
  simp [norm_smul, norm_ne_zero_iff.mpr ha]

/-- The translated residual potential obtained from the affine eigenfunction. -/
theorem affine_eigenfunction_residual_translation_invariant
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : E) (ha : a ≠ 0) (b ρ : ℝ)
    (heigen : ∀ x : E,
      langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
        -ρ * (inner ℝ a x + b)) (y : E) (u : ℝ) :
    V (y + u • (‖a‖⁻¹ • a) - (b / ‖a‖) • (‖a‖⁻¹ • a)) -
        ρ / 2 * ‖y + u • (‖a‖⁻¹ • a)‖ ^ 2 =
      V (y - (b / ‖a‖) • (‖a‖⁻¹ • a)) - ρ / 2 * ‖y‖ ^ 2 := by
  apply centered_residual_invariant_of_directional_drift V hV (‖a‖⁻¹ • a) _ ρ (b / ‖a‖)
    (affine_eigenfunction_directional_drift V a b ρ heigen) y u
  simp [norm_smul, norm_ne_zero_iff.mpr ha]

/-- Translating the actual Gibbs probability law translates its potential by
the inverse shift, because Lebesgue volume is translation invariant. -/
theorem gibbs_map_translation (V : E → ℝ) (hV : Measurable V) (m : E) :
    ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
        (fun x => x + m) =
      (volume : Measure E).withDensity (fun y => ENNReal.ofReal (Real.exp (-V (y - m)))) := by
  have h := map_withDensity_comp (volume : Measure E) (fun x => x + m)
    (fun y => ENNReal.ofReal (Real.exp (-V (y - m)))) (by fun_prop) (by fun_prop)
  rw [(measurePreserving_add_right (volume : Measure E) m).map_eq] at h
  simpa only [add_sub_cancel_right] using h

/-- The pointwise directional drift identity forces a genuine Gaussian factor
of the translated Gibbs law. The probability premise is precisely Gibbs
normalization, not an assumed factorization or projection law. -/
theorem directional_drift_gibbs_factor
    (V : E → ℝ) (hV : Differentiable ℝ V) (v : E) (hv : ‖v‖ = 1)
    (ρ c : ℝ) (hρ : 0 < ρ)
    (hdir : ∀ x : E, fderiv ℝ V x v = ρ * (inner ℝ v x + c))
    (hprob : IsProbabilityMeasure ((volume : Measure E).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-V x))))) :
    ∃ ν : Measure (Submodule.span ℝ {v})ᗮ, IsProbabilityMeasure ν ∧
      ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
          (fun x => (unitDirectionCoordinates v hv (x + c • v)).ofLp) =
        (ProbabilityTheory.gaussianReal 0 (ρ⁻¹).toNNReal).prod ν := by
  let W : E → ℝ := fun y => V (y - c • v) - ρ / 2 * ‖y‖ ^ 2
  have hW : Measurable W := by
    have hVm : Measurable V := hV.continuous.measurable
    fun_prop
  have hWInv : ∀ y : E, ∀ u : ℝ, W (y + u • v) = W y :=
    centered_residual_invariant_of_directional_drift V hV v hv ρ c hdir
  have hpotential : (fun y : E => ρ / 2 * ‖y‖ ^ 2 + W y) = fun y => V (y - c • v) := by
    funext y
    dsimp [W]
    ring
  have hmodel : (volume : Measure E).withDensity
      (fun y => ENNReal.ofReal (Real.exp (-(ρ / 2 * ‖y‖ ^ 2 + W y)))) =
      ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
        (fun x => x + c • v) := by
    rw [gibbs_map_translation V hV.continuous.measurable]
    congr 1
    funext y
    congr 2
    exact congrArg Neg.neg (congrFun hpotential y)
  have hprobW : IsProbabilityMeasure ((volume : Measure E).withDensity
      (fun y => ENNReal.ofReal (Real.exp (-(ρ / 2 * ‖y‖ ^ 2 + W y))))) := by
    rw [hmodel]
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 hprob
  obtain ⟨ν, hν, hfactor⟩ := normalized_gibbs_unit_direction_factor v hv W hW hWInv hρ hprobW
  refine ⟨ν, hν, ?_⟩
  rw [hmodel, Measure.map_map (by fun_prop) (by fun_prop)] at hfactor
  exact hfactor

/-- The affine eigenfunction itself therefore yields the Gaussian measure
factor in its normalized gradient direction, with center `-b/‖a‖`. -/
theorem affine_eigenfunction_gibbs_factor
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : E) (ha : a ≠ 0) (b ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x : E,
      langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
        -ρ * (inner ℝ a x + b))
    (hprob : IsProbabilityMeasure ((volume : Measure E).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-V x))))) :
    ∃ A : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (Submodule.span ℝ {‖a‖⁻¹ • a})ᗮ),
      A.symm (WithLp.toLp 2 (1, (0 : (Submodule.span ℝ {‖a‖⁻¹ • a})ᗮ))) = ‖a‖⁻¹ • a ∧
      ∃ ν : Measure (Submodule.span ℝ {‖a‖⁻¹ • a})ᗮ, IsProbabilityMeasure ν ∧
        ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
            (fun x => (A (x + (b / ‖a‖) • (‖a‖⁻¹ • a))).ofLp) =
          (ProbabilityTheory.gaussianReal 0 (ρ⁻¹).toNNReal).prod ν := by
  have hv : ‖‖a‖⁻¹ • a‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr ha]
  refine ⟨unitDirectionCoordinates (‖a‖⁻¹ • a) hv,
    unitDirectionCoordinates_symm_one_zero _ hv, ?_⟩
  exact directional_drift_gibbs_factor V hV (‖a‖⁻¹ • a) hv ρ (b / ‖a‖) hρ
    (affine_eigenfunction_directional_drift V a b ρ heigen) hprob

end AffineEigenfunction

end CutoffRigidity
