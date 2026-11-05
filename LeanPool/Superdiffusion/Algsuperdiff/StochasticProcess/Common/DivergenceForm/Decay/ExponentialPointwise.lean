/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.Pointwise
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.RateOptimization

/-!
# ExponentialPointwise

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Pointwise exponential decay under small contrast

Combining the interior pointwise estimate with the radius balance turns an
exponentially small local `L²` size into an exponentially small pointwise
value, at the reduced rate `kappa * alpha / (alpha + d / 2)`.  The balance is
taken over the radii the interior estimate allows, up to `r / 2`, so the
statement holds at every scale `r` and the constant carries the explicit
powers of `r`.

The small-contrast hypothesis comes from the interior Schauder estimate that
supplies the Hölder modulus.  For a general elliptic field the same conclusion
would need a De Giorgi--Nash--Moser local boundedness estimate, which the
layer does not carry.

## Main results

- `DivergenceFormProcess.Decay.exists_representative_abs_center_le_exp`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal

variable {d : ℕ}

/-- The unit ball carries positive volume. -/
theorem unitBallVolume_pos :
    0 < (volume (smallContrastUnitBall d)).toReal := by
  have hne : (volume (smallContrastUnitBall d)).toReal ≠ 0 := by
    simpa only [smallContrastUnitBall] using
      HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero
        (0 : Vec d) (by norm_num : (0 : ℝ) < 1)
  exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)

/-- Pointwise exponential decay of the continuous representative at the centre
of a ball, from an exponentially small local `L²` size. -/
theorem exists_representative_abs_center_le_exp [NeZero d]
    {a : CoeffField d} {Om : Set (Vec d)} (hOm : IsOpen Om)
    {u : H1Function Om} {g : Vec d → ℝ} {G E delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hameas : Measurable a)
    (ha : CoefficientIdentityDistanceLE Om a delta)
    (hsol : IsScalarForcedWeakSolution a Om g u)
    {x₀ : Vec d} {r : ℝ} (hr : 0 < r) (hball : euclideanBall x₀ r ⊆ Om)
    (hG : 0 ≤ G)
    (hgb : ∀ᵐ x ∂volumeMeasureOn (euclideanBall x₀ r), |g x| ≤ G)
    (hE : vectorLpSizeOn (euclideanBall x₀ r) 2 u.grad ≤ E)
    {kappa s D : ℝ} (hkappa : 0 ≤ kappa) (hs : 0 ≤ s) (hD : 0 ≤ D)
    (hL2 : ∀ rho : ℝ, 0 < rho → rho ≤ r / 2 →
      (∫ y in euclideanBall x₀ rho, u.toFun y ^ 2 ∂volume) ≤
        D ^ 2 * Real.exp (-(2 * (kappa * s)))) :
    ∃ v : Vec d → ℝ,
      ContinuousOn v (euclideanBall x₀ (r / 2)) ∧
      v =ᵐ[volume.restrict (euclideanBall x₀ r)] u.toFun ∧
      |v x₀| ≤
        (D / Real.sqrt ((volume (smallContrastUnitBall d)).toReal) /
            Real.sqrt ((r / 2) ^ d) +
          smallContrastZerothSchauderConstant d *
              (r ^ (1 - alpha - (d : ℝ) / 2) * E + r ^ (2 - alpha) * G) *
            (r / 2) ^ alpha) *
          Real.exp (-(kappa * alpha / (alpha + (d : ℝ) / 2) * s)) := by
  classical
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha.1
  obtain ⟨v, hvcont, hvae, hvbound⟩ :=
    exists_representative_abs_center_le hOm hd halpha hdelta0 hdelta hameas ha
      hsol hr hball hG hgb hE
  refine ⟨v, hvcont, hvae, ?_⟩
  set K : ℝ := smallContrastZerothSchauderConstant d *
    (r ^ (1 - alpha - (d : ℝ) / 2) * E + r ^ (2 - alpha) * G) with hK
  have hcd : 0 < (volume (smallContrastUnitBall d)).toReal := unitBallVolume_pos
  have hsqrtcd : 0 < Real.sqrt ((volume (smallContrastUnitBall d)).toReal) :=
    Real.sqrt_pos.2 hcd
  set A : ℝ := D / Real.sqrt ((volume (smallContrastUnitBall d)).toReal) with hA
  have hstep : ∀ rho : ℝ, 0 < rho → rho ≤ r / 2 →
      |v x₀| ≤ A * Real.exp (-(kappa * s)) / Real.sqrt (rho ^ d) +
        K * rho ^ alpha := by
    intro rho hrho hrhoHalf
    have hbase := hvbound rho hrho hrhoHalf
    have hsqrtRho : 0 < Real.sqrt (rho ^ d) :=
      Real.sqrt_pos.2 (pow_pos hrho d)
    have hL2rho := hL2 rho hrho hrhoHalf
    have hnum : Real.sqrt (∫ y in euclideanBall x₀ rho, u.toFun y ^ 2 ∂volume) ≤
        D * Real.exp (-(kappa * s)) := by
      have hmono := Real.sqrt_le_sqrt hL2rho
      have hval : Real.sqrt (D ^ 2 * Real.exp (-(2 * (kappa * s)))) =
          D * Real.exp (-(kappa * s)) := by
        rw [Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD, sqrt_exp_eq]
        congr 2
        ring
      rwa [hval] at hmono
    have hden : Real.sqrt ((volume (smallContrastUnitBall d)).toReal * rho ^ d) =
        Real.sqrt ((volume (smallContrastUnitBall d)).toReal) *
          Real.sqrt (rho ^ d) := Real.sqrt_mul hcd.le _
    have hfrac : Real.sqrt (∫ y in euclideanBall x₀ rho, u.toFun y ^ 2 ∂volume) /
        Real.sqrt ((volume (smallContrastUnitBall d)).toReal * rho ^ d) ≤
          A * Real.exp (-(kappa * s)) / Real.sqrt (rho ^ d) := by
      rw [hden]
      have hpos : 0 < Real.sqrt ((volume (smallContrastUnitBall d)).toReal) *
          Real.sqrt (rho ^ d) := mul_pos hsqrtcd hsqrtRho
      rw [div_le_iff₀ hpos, hA]
      have hclear : D / Real.sqrt ((volume (smallContrastUnitBall d)).toReal) *
          Real.exp (-(kappa * s)) / Real.sqrt (rho ^ d) *
            (Real.sqrt ((volume (smallContrastUnitBall d)).toReal) *
              Real.sqrt (rho ^ d)) = D * Real.exp (-(kappa * s)) := by
        field_simp
      rw [hclear]
      exact hnum
    linarith only [hbase, hfrac]
  exact le_mul_exp_of_two_term_bound (by linarith only [hr]) halpha0 hkappa hs
    hstep

end DivergenceFormProcess.Decay
