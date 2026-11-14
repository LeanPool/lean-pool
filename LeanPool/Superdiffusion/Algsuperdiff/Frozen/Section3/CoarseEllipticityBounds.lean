/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Exponent
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.LowerFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffMultiscaleEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.Assembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperLeg

/-!
# CoarseEllipticityBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds
    (d : ℕ) :
    ∃ Ccg : ℝ, 0 < Ccg ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Ccg / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ q : CoarseEllipticityExponent,
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              Probability.IsLowerIntegerFamilyOrlicz
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma
                    ((1 - sigma) / 2))
                  (fun L : ℤ =>
                    fun omega =>
                      Observable.cutoffLowerEllipticityInv
                          M m L s
                          (by
                            exact
                              (add_pos
                                (div_pos M.shellPrefix.gamma_pos (by norm_num))
                              (Real.exp_pos
                                (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                    M.gamma⁻¹)))).trans_le hsWindow.1)
                          q omega *
                        (Annealed.sigmaBar M (m - 1) : ℝ))
                  (m - 1)
                  (lowerEllipticityProfile Ccg M.gamma s q)
                  (Real.exp
                    (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) ∧
                Probability.IsDeterministicShiftTwoTermOneSidedOrlicz
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma 1)
                  (HCPolySupport.IndependentSums.gammaSigma
                    ((1 - sigma) / 3))
                  (fun omega =>
                    Observable.cutoffUpperEllipticity
                        M m m s
                        (by
                          exact
                            (add_pos
                              (div_pos M.shellPrefix.gamma_pos (by norm_num))
                            (Real.exp_pos
                              (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                  M.gamma⁻¹)))).trans_le hsWindow.1)
                        q omega *
                      (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹)
                  Ccg
                  (Ccg * (Disorder.cstar M)⁻¹ * s * M.gamma *
                    (2 * s - M.gamma)⁻¹ ^ 3)
                  (Real.exp
                    (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))
-- FROZEN-STATEMENT-END
    := by
  exact
    Algsuperdiff.Section3.Provider.CoarseEllipticity.coarse_ellipticity_bounds_of_legs
      d
      (Algsuperdiff.Section3.Provider.CoarseEllipticity.superposedFlux_coarse_ellipticity_lower_leg
        d)
      (Algsuperdiff.Section3.Provider.CoarseEllipticity.superposedFlux_coarse_ellipticity_upper_leg
        d)
