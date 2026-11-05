/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.ExponentialWeight

/-!
# WeightedToBall

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# From a weighted mass bound to a local `L²` bound

The exponentially weighted mass estimate controls the square of a solution
against a weight that is bounded below on the region of interest.  Dividing by
that lower bound turns the weighted statement into the plain local `L²`
statement consumed by the pointwise estimate.

## Main results

- `DivergenceFormProcess.Decay.setIntegral_sq_le_exp_mul_weighted`
- `DivergenceFormProcess.Decay.setIntegral_sq_le_exp_mul_localizedWeight`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- A weight bounded below on a subset converts a weighted integral bound into
a plain one on that subset. -/
theorem setIntegral_sq_le_exp_mul_weighted {U B : Set (Vec d)} (hBU : B ⊆ U)
    (hBmeas : MeasurableSet B) {w theta : Vec d → ℝ} {c : ℝ}
    (hthetaNonneg : ∀ y, 0 ≤ theta y)
    (hlower : ∀ y ∈ B, 1 ≤ Real.exp c * theta y)
    (hsq : IntegrableOn (fun y => w y ^ 2) U)
    (hint : IntegrableOn (fun y => w y ^ 2 * theta y) U) :
    (∫ y in B, w y ^ 2 ∂volume) ≤
      Real.exp c * ∫ y in U, w y ^ 2 * theta y ∂volume := by
  have h1 : (∫ y in B, w y ^ 2 ∂volume) ≤
      ∫ y in B, Real.exp c * (w y ^ 2 * theta y) ∂volume := by
    refine setIntegral_mono_on (hsq.mono_set hBU)
      ((hint.mono_set hBU).const_mul _) hBmeas ?_
    intro y hy
    have hwsq : (0 : ℝ) ≤ w y ^ 2 := sq_nonneg _
    calc
      w y ^ 2 = w y ^ 2 * 1 := by ring
      _ ≤ w y ^ 2 * (Real.exp c * theta y) :=
        mul_le_mul_of_nonneg_left (hlower y hy) hwsq
      _ = Real.exp c * (w y ^ 2 * theta y) := by ring
  have h2 : (∫ y in B, Real.exp c * (w y ^ 2 * theta y) ∂volume) ≤
      ∫ y in U, Real.exp c * (w y ^ 2 * theta y) ∂volume := by
    refine setIntegral_mono_set (hint.const_mul _) ?_ (LE.le.eventuallyLE hBU)
    exact Filter.Eventually.of_forall fun y =>
      mul_nonneg (Real.exp_pos c).le
        (mul_nonneg (sq_nonneg _) (hthetaNonneg y))
  simp only [integral_const_mul] at h1 h2
  linarith only [h1, h2]

/-- The localized exponential weight of the Agmon estimate is bounded below on
any region where the localization is at least one and the phase is at least
`t`. -/
theorem setIntegral_sq_le_exp_mul_localizedWeight {U B : Set (Vec d)}
    (hBU : B ⊆ U) (hBmeas : MeasurableSet B) {w eta psi : Vec d → ℝ}
    {kappa t : ℝ} (hkappa : 0 ≤ kappa)
    (hetaOne : ∀ y ∈ B, 1 ≤ eta y ^ 2) (hpsiLow : ∀ y ∈ B, t ≤ psi y)
    (hsq : IntegrableOn (fun y => w y ^ 2) U)
    (hint : IntegrableOn (fun y => w y ^ 2 *
      (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2)) U) :
    (∫ y in B, w y ^ 2 ∂volume) ≤
      Real.exp (-(2 * kappa * t)) *
        ∫ y in U, w y ^ 2 *
          (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume := by
  refine setIntegral_sq_le_exp_mul_weighted hBU hBmeas ?_ ?_ hsq hint
  · intro y
    positivity
  · intro y hy
    have hexpSq : ∀ z : ℝ, Real.exp z ^ 2 = Real.exp (2 * z) := by
      intro z
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hphase : Real.exp (2 * (kappa * t)) ≤ Real.exp (2 * (kappa * psi y)) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left (hpsiLow y hy) hkappa
      linarith only [this]
    have hetaLow := hetaOne y hy
    have hexpPos : (0 : ℝ) < Real.exp (2 * (kappa * t)) := Real.exp_pos _
    have hcancel : Real.exp (-(2 * kappa * t)) * Real.exp (2 * (kappa * t)) = 1 := by
      rw [← Real.exp_add]
      have : -(2 * kappa * t) + 2 * (kappa * t) = 0 := by ring
      rw [this, Real.exp_zero]
    calc
      (1 : ℝ) = Real.exp (-(2 * kappa * t)) * Real.exp (2 * (kappa * t)) :=
        hcancel.symm
      _ ≤ Real.exp (-(2 * kappa * t)) * Real.exp (2 * (kappa * psi y)) :=
        mul_le_mul_of_nonneg_left hphase (Real.exp_pos _).le
      _ = Real.exp (-(2 * kappa * t)) * (1 * Real.exp (kappa * psi y) ^ 2) := by
        rw [hexpSq (kappa * psi y), one_mul]
      _ ≤ Real.exp (-(2 * kappa * t)) *
          (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right hetaLow (sq_nonneg _)

end DivergenceFormProcess.Decay
