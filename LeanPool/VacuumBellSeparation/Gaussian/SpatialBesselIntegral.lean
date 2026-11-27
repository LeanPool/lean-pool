/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialShiftedLaplaceBounds
public import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# The actual cosh integral and its shifted-Laplace representation

The modified Bessel quantity here is defined by the manuscript's literal
cosh integral. An actual injective differentiable change of variables
establishes both integral equality and convergence for orders one and two.
Identification with the spatial Fourier covariance kernel, for sources with separated supports,
is proved in other modules (`modifiedBesselIntegral_eq_besselKReal` in
`Gaussian/SpatialBesselCompatibility.lean`, `timeZeroFourierCovariance_eq_bessel_kernel` in
`FreeField/SpatialSeparatedCovarianceKernel.lean`).
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Set

/-- Shifted arcosh given by `Real.arcosh (v + 1)`. -/
noncomputable def shiftedArcosh (v : ℝ) : ℝ := Real.arcosh (v + 1)

theorem shiftedArcosh_hasDerivAt {v : ℝ} (hv : 0 < v) :
    HasDerivAt shiftedArcosh (Real.sqrt (v * (v + 2)))⁻¹ v := by
  have h : HasDerivAt (fun x : ℝ => Real.arcosh (x + 1))
      ((Real.sqrt ((v + 1) ^ 2 - 1))⁻¹ * 1) v :=
    HasDerivAt.comp (h₂ := Real.arcosh) (h := fun x : ℝ => x + 1) v
      (Real.hasDerivAt_arcosh (show v + 1 ∈ Ioi 1 from by
        change 1 < v + 1
        linarith))
      ((hasDerivAt_id v).add_const 1)
  change HasDerivAt (fun x : ℝ => Real.arcosh (x + 1))
    (Real.sqrt (v * (v + 2)))⁻¹ v
  convert h using 1
  rw [mul_one, show (v + 1) ^ 2 - 1 = v * (v + 2) by ring]

theorem shiftedArcosh_injOn : InjOn shiftedArcosh (Ioi 0) := by
  intro v hv w hw h
  change 0 < v at hv
  change 0 < w at hw
  have hc := congrArg Real.cosh h
  simp only [shiftedArcosh, Real.cosh_arcosh (show 1 ≤ v + 1 by linarith),
    Real.cosh_arcosh (show 1 ≤ w + 1 by linarith)] at hc
  linarith

theorem shiftedArcosh_image : shiftedArcosh '' Ioi (0 : ℝ) = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    change 0 < v at hv
    exact Real.arcosh_pos (by linarith)
  · intro hu
    refine ⟨Real.cosh u - 1, ?_, ?_⟩
    · exact sub_pos.mpr (Real.one_lt_cosh.mpr (ne_of_gt hu))
    · simpa only [shiftedArcosh, sub_add_cancel] using Real.arcosh_cosh hu.le

theorem integral_shiftedArcosh {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) :
    (∫ u in Ioi (0 : ℝ), g u) =
      ∫ v in Ioi (0 : ℝ), (Real.sqrt (v * (v + 2)))⁻¹ • g (shiftedArcosh v) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun v hv => (shiftedArcosh_hasDerivAt hv).hasDerivWithinAt) shiftedArcosh_injOn g
  rw [shiftedArcosh_image] at h
  simpa only [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))] using h

theorem integrableOn_shiftedArcosh_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) :
    IntegrableOn g (Ioi (0 : ℝ)) ↔ IntegrableOn
      (fun v => (Real.sqrt (v * (v + 2)))⁻¹ • g (shiftedArcosh v)) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun v hv => (shiftedArcosh_hasDerivAt hv).hasDerivWithinAt) shiftedArcosh_injOn g
  rw [shiftedArcosh_image] at h
  simpa only [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))] using h

/-- Modified Bessel integral given by `∫ u in Ioi (0 : ℝ), Real.exp (-x * Real.cosh u) * Real.cosh
((n : ℝ) * u)`. -/
noncomputable def modifiedBesselIntegral (n : ℕ) (x : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-x * Real.cosh u) * Real.cosh ((n : ℝ) * u)

theorem shiftedArcosh_integrand_one (x : ℝ) {v : ℝ} (hv : 0 < v) :
    (Real.sqrt (v * (v + 2)))⁻¹ *
      (Real.exp (-x * Real.cosh (shiftedArcosh v)) * Real.cosh (shiftedArcosh v)) =
      Real.exp (-x) * (shiftedBesselDensityOne v * Real.exp (-x * v)) := by
  rw [shiftedArcosh, Real.cosh_arcosh (show 1 ≤ v + 1 by linarith),
    show -x * (v + 1) = -x + -x * v by ring, Real.exp_add]
  unfold shiftedBesselDensityOne
  ring

theorem shiftedArcosh_integrand_two (x : ℝ) {v : ℝ} (hv : 0 < v) :
    (Real.sqrt (v * (v + 2)))⁻¹ *
      (Real.exp (-x * Real.cosh (shiftedArcosh v)) * Real.cosh (2 * shiftedArcosh v)) =
      Real.exp (-x) * (shiftedBesselDensityTwo v * Real.exp (-x * v)) := by
  rw [Real.cosh_two_mul, Real.sinh_sq, shiftedArcosh,
    Real.cosh_arcosh (show 1 ≤ v + 1 by linarith),
    show -x * (v + 1) = -x + -x * v by ring, Real.exp_add]
  unfold shiftedBesselDensityTwo
  ring

theorem modifiedBesselIntegral_one_eq (x : ℝ) :
    modifiedBesselIntegral 1 x = shiftedBesselLaplaceOne x := by
  unfold modifiedBesselIntegral shiftedBesselLaplaceOne
  simp only [Nat.cast_one, one_mul]
  rw [integral_shiftedArcosh, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi (fun v hv => shiftedArcosh_integrand_one x hv)

theorem modifiedBesselIntegral_two_eq (x : ℝ) :
    modifiedBesselIntegral 2 x = shiftedBesselLaplaceTwo x := by
  unfold modifiedBesselIntegral shiftedBesselLaplaceTwo
  norm_num only [Nat.cast_ofNat]
  rw [integral_shiftedArcosh, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi (fun v hv => shiftedArcosh_integrand_two x hv)

theorem integrableOn_modifiedBessel_one {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => Real.exp (-x * Real.cosh u) * Real.cosh u) (Ioi 0) := by
  rw [integrableOn_shiftedArcosh_iff]
  refine IntegrableOn.congr_fun
    ((integrableOn_shiftedBessel_density_one hx).const_mul (Real.exp (-x)))
    (fun v hv => (shiftedArcosh_integrand_one x hv).symm) measurableSet_Ioi

theorem integrableOn_modifiedBessel_two {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => Real.exp (-x * Real.cosh u) * Real.cosh (2 * u))
      (Ioi 0) := by
  rw [integrableOn_shiftedArcosh_iff]
  refine IntegrableOn.congr_fun
    ((integrableOn_shiftedBessel_density_two hx).const_mul (Real.exp (-x)))
    (fun v hv => (shiftedArcosh_integrand_two x hv).symm) measurableSet_Ioi

theorem modifiedBesselIntegral_one_le {x : ℝ} (hx : 0 < x) :
    modifiedBesselIntegral 1 x ≤ Real.exp (-x) *
      (x⁻¹ + Real.sqrt (Real.pi / (2 * x))) := by
  rw [modifiedBesselIntegral_one_eq]
  exact shiftedBesselLaplaceOne_le hx

theorem modifiedBesselIntegral_two_le {x : ℝ} (hx : 0 < x) :
    modifiedBesselIntegral 2 x ≤ Real.exp (-x) *
      (2 * (x ^ 2)⁻¹ + 4 * x⁻¹ + Real.sqrt (Real.pi / (2 * x))) := by
  rw [modifiedBesselIntegral_two_eq]
  exact shiftedBesselLaplaceTwo_le hx

end VacuumBellSeparation.Gaussian
