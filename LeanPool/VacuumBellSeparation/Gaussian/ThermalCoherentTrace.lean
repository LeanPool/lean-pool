/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CoherentTraceSeries
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalState

/-!
# Actual coherent integral for the complex thermal expectation

The square root of the thermal density has summable basis norms. This
gives the absolute integral bound needed to exchange the number-basis
series and the coherent integral. Parseval then identifies the pointwise
series with the genuine square-root sandwich. The input operator can be
any bounded complex operator, including a Weyl unitary.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap MeasureTheory
open scoped ComplexConjugate

theorem hasSum_coherentFrame_sandwich
    {S : OscillatorSpace →L[ℂ] OscillatorSpace} (hS : IsSelfAdjoint S)
    (A : OscillatorSpace →L[ℂ] OscillatorSpace) (z : ℂ) :
    HasSum (fun n => inner ℂ (coherentFrameCoordinate (S (numberBasis n)) z)
      (coherentFrameCoordinate (S (A (numberBasis n))) z))
      ((Real.pi : ℂ)⁻¹ * inner ℂ (S (coherentVector z)) (A (S (coherentVector z)))) := by
  let c : ℂ := (Real.sqrt Real.pi : ℂ)⁻¹
  let v := coherentVector z
  have hc : conj c * c = (Real.pi : ℂ)⁻¹ := by
    change conj ((Real.sqrt Real.pi : ℂ)⁻¹) * (Real.sqrt Real.pi : ℂ)⁻¹ =
      (Real.pi : ℂ)⁻¹
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← pow_two,
      ← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hleft (n : ℕ) : coherentFrameCoordinate (S (numberBasis n)) z =
      c * inner ℂ (S v) (numberBasis n) := by
    rw [coherentFrameCoordinate, ← S.adjoint_inner_left, hS.adjoint_eq]
  have hright (n : ℕ) : coherentFrameCoordinate (S (A (numberBasis n))) z =
      c * inner ℂ (A.adjoint (S v)) (numberBasis n) := by
    rw [coherentFrameCoordinate, ← S.adjoint_inner_left, hS.adjoint_eq,
      ← A.adjoint_inner_left]
  have hterm (n : ℕ) : inner ℂ (coherentFrameCoordinate (S (numberBasis n)) z)
      (coherentFrameCoordinate (S (A (numberBasis n))) z) =
      (conj c * c) * (inner ℂ (A.adjoint (S v)) (numberBasis n) *
        inner ℂ (numberBasis n) (S v)) := by
    rw [hleft, hright, RCLike.inner_apply', map_mul, inner_conj_symm]
    ring
  have h := (numberBasis.hasSum_inner_mul_inner (A.adjoint (S v)) (S v)).mul_left
    (conj c * c)
  have hval : (conj c * c) * inner ℂ (A.adjoint (S v)) (S v) =
      (Real.pi : ℂ)⁻¹ * inner ℂ (S v) (A (S v)) := by
    rw [hc, A.adjoint_inner_left]
  simpa only [← hterm, hval] using h

theorem summable_sqrt_thermal_basis_norm {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Summable fun n => ‖CFC.sqrt (thermalDensity q) (numberBasis n)‖ := by
  have hn (n : ℕ) : ‖CFC.sqrt (thermalDensity q) (numberBasis n)‖ =
      Real.sqrt (thermalWeight q n) := by
    calc
      _ = ‖Real.sqrt (thermalWeight q n) • numberBasis n‖ :=
        congrArg norm (sqrt_diagonalOperator_apply_basis numberBasis
          (hasSum_thermalWeight hq₀ hq₁).summable
          (fun k => mul_nonneg (sub_nonneg.mpr hq₁.le) (pow_nonneg hq₀ k)) n)
      _ = _ := by
        rw [norm_smul, numberBasis.orthonormal.norm_eq_one, mul_one, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
  simpa only [hn, Real.sqrt_eq_rpow] using
    (hasSum_thermalWeight_rpow hq₀ hq₁ (by norm_num : (0 : ℝ) < 1 / 2)).summable

theorem thermalState_eq_coherent_integral {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (A : OscillatorSpace →L[ℂ] OscillatorSpace) :
    thermalState hq₀ hq₁ A = ∫ z : ℂ, (Real.pi : ℂ)⁻¹ *
      inner ℂ (CFC.sqrt (thermalDensity q) (coherentVector z))
        (A (CFC.sqrt (thermalDensity q) (coherentVector z))) := by
  let S := CFC.sqrt (thermalDensity q)
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hnorm (n : ℕ) : ‖S (A (numberBasis n))‖ ≤ ‖S‖ * ‖A‖ := by
    calc
      ‖S (A (numberBasis n))‖ ≤ ‖S‖ * ‖A (numberBasis n)‖ := S.le_opNorm _
      _ ≤ ‖S‖ * (‖A‖ * ‖numberBasis n‖) :=
        mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
      _ = ‖S‖ * ‖A‖ := by rw [numberBasis.orthonormal.norm_eq_one, mul_one]
  have hs : Summable fun n => ‖S (numberBasis n)‖ * ‖S (A (numberBasis n))‖ :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (hnorm n) (norm_nonneg _))
      ((summable_sqrt_thermal_basis_norm hq₀ hq₁).mul_right (‖S‖ * ‖A‖))
  have hseries := hasSum_integral_inner_coherentFrameCoordinate hs
  have hcoef (n : ℕ) : inner ℂ (S (numberBasis n)) (S (A (numberBasis n))) =
      (thermalWeight q n : ℂ) * inner ℂ (numberBasis n) (A (numberBasis n)) := by
    rw [← S.adjoint_inner_left, hS.adjoint_eq, ← mul_apply_eq_comp, ← pow_two]
    change inner ℂ ((CFC.sqrt (thermalDensity q) ^ 2) (numberBasis n))
      (A (numberBasis n)) = _
    rw [CFC.sq_sqrt _ (thermalDensity_nonneg hq₀ hq₁),
      thermalDensity_apply_numberBasis hq₀ hq₁,
      inner_smul_left_eq_smul, Algebra.smul_def, Complex.coe_algebraMap]
  have hexpect := (summable_diagonalExpectation_terms numberBasis
    (hasSum_thermalWeight hq₀ hq₁).summable A).hasSum
  simp_rw [hcoef] at hseries
  calc
    thermalState hq₀ hq₁ A = ∫ z : ℂ, ∑' n,
        inner ℂ (coherentFrameCoordinate (S (numberBasis n)) z)
          (coherentFrameCoordinate (S (A (numberBasis n))) z) := hexpect.unique hseries
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      exact (hasSum_coherentFrame_sandwich hS A z).tsum_eq

end VacuumBellSeparation.Gaussian
