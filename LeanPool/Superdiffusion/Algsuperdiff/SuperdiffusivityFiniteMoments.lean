/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.MainTheorems
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.DisplacementIntegrability

/-!
# Superdiffusivity with finite displacement moments

This bridge intersects the thresholds from the quantitative theorem and its
integrability companion. The displayed expectations therefore have integrable
first and second displacement observables in the same small-coupling regime.
The original quantitative theorem remains available with its unchanged statement.
-/

@[expose] public section

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form
open HCPolySupport MarkovProcess MeasureTheory
open scoped ENNReal NNReal

/-- One positive threshold gives both displacement integrability and the full
quantitative superdiffusivity bounds, uniformly at every positive time. -/
theorem Algsuperdiff.superdiffusivity_with_finite_moments
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ t : ℝ, 0 < t →
      (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
        letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
        letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
        Integrable (fun path : ContinuousPath (OnePoint (Vec d)) =>
          onePointRetract (0 : Vec d) (path t.toNNReal))
          ((streamExhaustionTailInput M omega).wholeSpaceProcess
            ((0 : Vec d) : OnePoint (Vec d))) ∧
        Integrable (fun path : ContinuousPath (OnePoint (Vec d)) =>
          vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal)))
          ((streamExhaustionTailInput M omega).wholeSpaceProcess
            ((0 : Vec d) : OnePoint (Vec d)))) ∧
      ∀ p : ℝ, 1 ≤ p →
        p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) →
        (∫⁻ omega : FullSample d M.gamma,
            (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
             letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
             ENNReal.ofReal
                |(∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
                    ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                        ((0 : Vec d) : OnePoint (Vec d)))) -
                  2 * (d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2| ^ p)
            ∂(fullSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
              Real.sqrt M.gamma * |Real.log M.gamma| ^ (4 : ℕ) *
              intrinsicScale M.nu cstar M.gamma t ^ 2) ^ p ∧
        (∫⁻ omega : FullSample d M.gamma,
            (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
             letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
             ENNReal.ofReal
                (vecNormSq (∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
                    ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                        ((0 : Vec d) : OnePoint (Vec d))))) ^ p)
            ∂(fullSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (C * (p + |Real.log M.gamma|) * M.gamma *
              |Real.log M.gamma| ^ (7 : ℕ) *
              intrinsicScale M.nu cstar M.gamma t ^ 2) ^ p := by
  obtain ⟨gammaA, C, hgammaA, hC, hbound⟩ :=
    Algsuperdiff.superdiffusivity d cstar hcstar
  obtain ⟨gammaI, hgammaI, hfinite⟩ :=
    Algsuperdiff.Section5.Provider.exists_ae_integrable_streamProcess_displacement
      d hd cstar hcstar
  refine ⟨min gammaA gammaI, C, lt_min hgammaA hgammaI, hC, ?_⟩
  intro M hcs hgamma t ht
  constructor
  · simpa only [streamProcess] using
      hfinite M hcs (hgamma.trans (min_le_right gammaA gammaI)) t ht
  · exact hbound M hcs (hgamma.trans (min_le_left gammaA gammaI)) t ht
