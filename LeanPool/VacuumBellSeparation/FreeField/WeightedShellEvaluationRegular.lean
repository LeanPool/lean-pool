/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedShellEvaluationCutoff

/-!
# The actual weighted source evaluation on the normalized regular target

The constant depends only on the modular exponent. The geometric
domination, chart bounds, contour probability, cutoff comparison and
physical mass scaling are all discharged. The wave is the literal
complexified compact-source Fourier wave, retaining its cross terms.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

theorem modularAngle_sin_pos {c : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) :
    0 < Real.sin (2 * Real.pi * c) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by nlinarith [Real.pi_pos])

theorem normalizedTarget_weightedSource_evaluation
    {c : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (t E : ℝ) (_ : 0 < E) (hm : 0 < t * E)
        (T : ℝ) (_ : 0 < T) (U : Set (EuclideanSpace ℝ (Fin 3))),
        U ⊆ Metric.ball 0 T → ∀ u v : SourceTestSpace hm U,
          ∀ z : ComplexSpacetime, (t, z) ∈ normalizedTarget →
            E ^ 2 * ‖scaledComplexTestWave E u.1 v.1 z‖ ^ 2 ≤
              C * Real.exp (2 * (2048 / Real.sin (2 * Real.pi * c)) * T * E) *
                ‖sourceModularWeight hm U c
                  (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U) +
                    Complex.I • Gaussian.HilbertComplexification.ofReal
                      (v : SourceHilbert hm U))‖ ^ 2 := by
  have hs := modularAngle_sin_pos hc hc2
  obtain ⟨N, hN, D, hp, C, hC, hCt, hsub⟩ := normalizedTarget_uniform_contour_submean hs
  let _ : IsProbabilityMeasure (contourMixtureProbability D) := hp
  refine ⟨C.toReal, ENNReal.toReal_pos hC.ne' hCt.ne, ?_⟩
  intro t E hE hm T hT U hU u v z hz
  let ℓ : ℝ := 64 / Real.sin (2 * Real.pi * c)
  have hℓ : 0 < ℓ := div_pos (by norm_num) hs
  have hgeo : ∀ᵐ a ∂contourMixtureProbability D,
      Real.sqrt 2 * spacetimeEuclideanOperatorNorm (contourMixtureFamily D a).symm < ℓ := by
    filter_upwards [contourMixtureProbability_ae_norm_bounds D] with a ha
    have hsqrt : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    calc
      _ < Real.sqrt 2 * (32 / Real.sin (2 * Real.pi * c)) :=
        mul_lt_mul_of_pos_left ha.2 (Real.sqrt_pos.mpr (by norm_num))
      _ < 2 * (32 / Real.sin (2 * Real.pi * c)) :=
        mul_lt_mul_of_pos_right hsqrt (div_pos (by norm_num) hs)
      _ = ℓ := by dsimp [ℓ]; ring
  have hsource := averaged_complexTestContour_lintegral_le_sourceWeight_ae
    (contourMixtureProbability D) hm ℓ (contourMixtureFamily D)
    (fun a => (contourMixtureFamily_isProper D a).1)
    (contourMixtureFamily_isOrthochronous D)
    (continuous_contourMixtureFamily_apply D) hgeo hT hU u v hc hc2.le
  have hscale := averaged_scaledComplexTestContour_lintegral t hE
    (contourMixtureProbability D) (contourMixtureFamily D) (ℓ * T)
    (2 * Real.pi * c) u.1 v.1
  have hsub' := hsub t z hz (scaledComplexTestWave E u.1 v.1)
    (differentiable_scaledComplexTestWave E u.1 v.1)
  have hcut := contourMixture_cutoff_lintegral_le_damped hs hE.le
    (mul_pos hℓ hT).le D u.1 v.1 (t := t)
  have hexp : 2 * (ℓ * T) * E * (32 / Real.sin (2 * Real.pi * c)) *
      Real.sin (2 * Real.pi * c) =
        2 * (2048 / Real.sin (2 * Real.pi * c)) * T * E := by
    dsimp [ℓ]
    field_simp [hs.ne']
    ring
  rw [hexp] at hcut
  have hb := hsub'.trans (_root_.mul_le_mul_right hcut C)
  have hb' := _root_.mul_le_mul_right hb (ENNReal.ofReal (E ^ 2))
  have hfinal : ENNReal.ofReal (E ^ 2) *
      ENNReal.ofReal (‖scaledComplexTestWave E u.1 v.1 z‖ ^ 2) ≤
      C * ENNReal.ofReal (Real.exp (2 * (2048 / Real.sin (2 * Real.pi * c)) * T * E)) *
        ENNReal.ofReal (‖sourceModularWeight hm U c
          (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U) +
            Complex.I • Gaussian.HilbertComplexification.ofReal
              (v : SourceHilbert hm U))‖ ^ 2) := by
    calc
      _ ≤ (C * ENNReal.ofReal (Real.exp
          (2 * (2048 / Real.sin (2 * Real.pi * c)) * T * E))) *
          (ENNReal.ofReal (E ^ 2) * ∫⁻ a, ∫⁻ p,
            ENNReal.ofReal (scaledComplexTestContourIntegrand t E (ℓ * T)
              (2 * Real.pi * c) (contourMixtureFamily D a) u.1 v.1 p)
              ∂oneParticleMeasure t ∂contourMixtureProbability D) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hb'
      _ ≤ _ := _root_.mul_le_mul_right (hscale.trans_le hsource) _
  rw [← ENNReal.ofReal_mul (sq_nonneg E)] at hfinal
  have hCof : ENNReal.ofReal C.toReal = C := ENNReal.ofReal_toReal hCt.ne
  rw [← hCof, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul (by positivity)] at hfinal
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfinal

end VacuumBellSeparation
