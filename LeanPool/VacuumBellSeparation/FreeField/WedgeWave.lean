/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeGeometry
public import LeanPool.VacuumBellSeparation.FreeField.Microcausality.Edges

/-!
# The actual complex-rapidity wave of a compact left-wedge source

The integral uses the original spacetime source and the original massive
shell phase. Negative phase rapidity is essential: real ζ gives momentum
boost +ζ, so positive imaginary ζ is the decaying strip for the left wedge.
Integration by parts gives polynomial decay uniform up to both strip edges.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

/-- Wedge wave given by `∫ x : Spacetime, Complex.exp (Complex.I * boostPhase m (-ζ) p x) * (F.1 x
: ℂ)`. -/
noncomputable def wedgeWave (m : ℝ) (F : RealTestFunction) (ζ : ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ∫ x : Spacetime, Complex.exp (Complex.I * boostPhase m (-ζ) p x) * (F.1 x : ℂ)

theorem integrable_wedgeWave_integrand (m : ℝ) (F : RealTestFunction) (ζ : ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Integrable (fun x : Spacetime =>
      Complex.exp (Complex.I * boostPhase m (-ζ) p x) * (F.1 x : ℂ)) := by
  simpa only [sub_zero, boostPhaseCLM_apply] using
    integrable_expPhase_mul (boostPhaseCLM m (-ζ) p) 0 F

theorem wedgeWave_ofReal (m η : ℝ) (F : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    wedgeWave m F (η : ℂ) p = oneParticle m F (shellBoost m η p) := by
  rw [wedgeWave, oneParticle_eq_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have hp : boostPhase m (-(η : ℂ)) p x =
        ((dispersion m (shellBoost m η p) * x.1 - ⟪shellBoost m η p, x.2⟫_ℝ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg, boostPhase_ofReal_eq_zero_shellBoost, neg_neg, boostPhase_zero]
    exact congrArg (fun a : ℂ => Complex.exp (Complex.I * a) * (F.1 x : ℂ)) hp

theorem wedgeWave_zero (m : ℝ) (F : RealTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    wedgeWave m F 0 p = oneParticle m F p := by
  simpa only [Complex.ofReal_zero, shellBoost_zero] using wedgeWave_ofReal m 0 F p

theorem boostPhase_neg_pi_mul_I_eq (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (x : Spacetime) :
    boostPhase m (-((Real.pi : ℂ) * Complex.I)) p x =
      boostPhase m ((Real.pi : ℂ) * Complex.I) p x := by
  unfold boostPhase
  rw [Complex.cosh_neg, Complex.sinh_neg, Complex.cosh_mul_I, Complex.sinh_mul_I,
    Complex.cos_pi, Complex.sin_pi]
  ring

/-- The upper boundary involves transverse reflection, not full momentum
reflection. This is the literal complex conjugate of the original source wave. -/
theorem wedgeWave_pi_mul_I (m : ℝ) (F : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    wedgeWave m F ((Real.pi : ℂ) * Complex.I) p =
      conj (oneParticle m F (axisReflection p)) := by
  rw [wedgeWave, oneParticle_eq_integral, ← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have he : Complex.exp (Complex.I * boostPhase m (-((Real.pi : ℂ) * Complex.I)) p x) =
        conj (Complex.exp (Complex.I *
          ((dispersion m (axisReflection p) * x.1 - ⟪axisReflection p, x.2⟫_ℝ : ℝ) : ℂ))) := by
      rw [boostPhase_neg_pi_mul_I_eq, exp_I_mul_boostPhase_pi_mul_I, boostPhase_zero]
    simpa only [oneParticleIntegrand, map_mul, Complex.conj_ofReal] using
      congrArg (fun a : ℂ => a * (F.1 x : ℂ)) he

theorem wedgeWave_add_ofReal (m η : ℝ) (F : RealTestFunction) (ζ : ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    wedgeWave m F ((η : ℂ) + ζ) p = wedgeWave m F ζ (shellBoost m η p) := by
  unfold wedgeWave
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have hp : boostPhase m (-((η : ℂ) + ζ)) p x =
        boostPhase m (-ζ) (shellBoost m η p) x := by
      rw [neg_add, ← Complex.ofReal_neg, boostPhase_add_ofReal, neg_neg]
    exact congrArg (fun a : ℂ => Complex.exp (Complex.I * a) * (F.1 x : ℂ)) hp

theorem im_boostPhase_neg_mul_I_nonneg_of_leftWedge (m θ : ℝ)
    (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (p : EuclideanSpace ℝ (Fin 3))
    {x : Spacetime} (hx : x ∈ leftWedge 0) :
    0 ≤ (boostPhase m (-((θ : ℂ) * Complex.I)) p x).im := by
  rw [← neg_mul, ← Complex.ofReal_neg, boostPhase_ofReal_mul_I_im, Real.sin_neg]
  have hω : 0 ≤ dispersion m p := Real.sqrt_nonneg _
  have hp : |⟪e₁, p⟫_ℝ| ≤ dispersion m p :=
    (abs_inner_e₁_le p).trans (norm_le_dispersion m p)
  have hprod : |⟪e₁, p⟫_ℝ * x.1| ≤ dispersion m p * |x.1| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)
  change ⟪e₁, x.2⟫_ℝ + |x.1| < 0 at hx
  have harg : dispersion m p * ⟪e₁, x.2⟫_ℝ - ⟪e₁, p⟫_ℝ * x.1 ≤ 0 := by
    have hb := mul_le_mul_of_nonneg_left hx.le hω
    nlinarith [neg_abs_le (⟪e₁, p⟫_ℝ * x.1)]
  exact mul_nonneg_of_nonpos_of_nonpos
    (neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi hθ₀ hθπ))
    harg

/-- Uniform polynomial decay on the entire closed imaginary strip, obtained
from the already proved integration-by-parts identity for the actual source. -/
theorem norm_wedgeWave_mul_I_le {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) (N : ℕ) {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖wedgeWave m F ((θ : ℂ) * Complex.I) p‖ ≤
      (2 / dispersion m p) ^ N * maxCoordDerivNorm F N := by
  let c := boostPhaseCLM m (-((θ : ℂ) * Complex.I)) p
  have hsum : dispersion m p ^ 2 ≤ ∑ j : Fin 4, ‖c (coordDir j)‖ ^ 2 := by
    have he : -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I := by simp
    simp only [c, he, sum_norm_sq_boostPhaseCLM_coordDir]
    exact le_add_of_nonneg_right (sq_nonneg _)
  obtain ⟨j, hj⟩ := exists_le_norm_coordDir hsum
  have hc : ∀ x ∈ tsupport F.1, 0 ≤ (c (x - 0)).im := by
    intro x hx
    simpa only [c, sub_zero, boostPhaseCLM_apply] using
      im_boostPhase_neg_mul_I_nonneg_of_leftWedge m θ hθ₀ hθπ p (hF hx)
  have hb := norm_pow_mul_norm_integral_expPhase_le c 0 (coordDir j) F N hc
  simp only [sub_zero] at hb
  change ‖c (coordDir j)‖ ^ N * ‖wedgeWave m F ((θ : ℂ) * Complex.I) p‖ ≤ _ at hb
  have hω := dispersion_pos hm.ne' p
  have hp : (dispersion m p / 2) ^ N ≤ ‖c (coordDir j)‖ ^ N :=
    pow_le_pow_left₀ (by positivity) hj N
  have hbound : (dispersion m p / 2) ^ N * ‖wedgeWave m F ((θ : ℂ) * Complex.I) p‖ ≤
      maxCoordDerivNorm F N :=
    (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
      (hb.trans (le_maxCoordDerivNorm F N j))
  have hinv : (2 / dispersion m p) ^ N * (dispersion m p / 2) ^ N = 1 := by
    rw [← mul_pow]
    have he : (2 / dispersion m p) * (dispersion m p / 2) = 1 := by field_simp [hω.ne']
    rw [he, one_pow]
  have hh := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ (2 / dispersion m p) ^ N by positivity)
  simpa only [← mul_assoc, hinv, one_mul] using hh

end VacuumBellSeparation
