/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.GoodEvents
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.CgEllipLowerConstant
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.FluxCorrectedTwoScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.BoundsEaLProviderFinal

/-!
# BoundsMathcalEaL

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

/-!
# Moment bounds for the two-scale coarse-graining error — [ABK] `l.bounds.mathcal.E.aL`

Every `p`-th moment of the two-scale flux-corrected error observable between
scales `n <= m` is bounded, in the admissible range of `p`, by the `p`-th
power of `C 3^{s(m-n)/2} sqrt p (s^{-1} + sqrt (m-n)) sqrt gamma`: the error is
sub-Gaussian at size `sqrt gamma`, with a geometric loss in the scale gap.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section4.bounds_mathcal_E_aL
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar →
        M.gamma ≤ (C⁻¹) ^ (10 : ℕ) →
        ∀ m n : ℤ, n ≤ m → (m : ℝ) ≤ (n : ℝ) + M.gamma⁻¹ →
          ∀ s : ℝ, s ∈ Set.Icc (C ^ (2 : ℕ) * Real.sqrt M.gamma) (1 / 4) →
            ∀ hs : 0 < s,
              ∀ p : ℝ, p ∈ Set.Icc (2 * (d : ℝ) * s⁻¹) (C⁻¹ * M.gamma⁻¹ * s) →
                (∫⁻ omega,
                    Algsuperdiff.Section4.Support.fluxCorrectedTwoScaleErrorObservableSup
                        M m n ⟨s, hs⟩ omega ^ p
                      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                  ENNReal.ofReal
                      (C * Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ))) *
                        Real.sqrt p *
                        (s⁻¹ + Real.sqrt ((m : ℝ) - (n : ℝ))) *
                        Real.sqrt M.gamma) ^ p
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.BoundsEaL.bounds_mathcal_E_aL_provider d cstar _hcstar
