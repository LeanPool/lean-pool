/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedShellEvaluationHolomorphic
public import LeanPool.VacuumBellSeparation.Shell.LocalHolomorphicVolumeSubmean
public import LeanPool.VacuumBellSeparation.Shell.InducedShellVolumeCompatibility

/-!
# Actual source-wave submean against the induced shell Gram density

The wave is the literal complexified Cauchy-data expression, including
the cross terms between two real tests. Holomorphy and genuine Euclidean
volume yield the estimate; a lower chart-density bound is kept explicit
for the quantitative regular-patch geometry to supply.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Metric Set
open scoped ENNReal

/-- Complex test shell chart wave. -/
noncomputable def complexTestShellChartWave (u v : TimeZeroSource) (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (w : ShellEuclideanDomain) : ℂ :=
  complexSourceWave u (lorentzComplexShellChart m Λ (shellEuclideanCoordinates w)) +
    Complex.I * complexSourceWave v
      (lorentzComplexShellChart m Λ (shellEuclideanCoordinates w))

theorem differentiableAt_complexTestShellChartWave {m : ℝ}
    (u v : TimeZeroSource) (Λ : Spacetime ≃L[ℝ] Spacetime)
    {w : ShellEuclideanDomain} (hw : w ∈ euclideanShellChartDomain m) :
    DifferentiableAt ℂ (complexTestShellChartWave u v m Λ) w :=
  (differentiableAt_complexSourceWave_shellChart u Λ hw).add
    ((differentiableAt_complexSourceWave_shellChart v Λ hw).const_mul Complex.I)

theorem complexTestShellChartWave_volume_submean {m R : ℝ}
    (u v : TimeZeroSource) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (c : ShellEuclideanDomain) (hR : 0 < R)
    (hsub : ball c (2 * R) ⊆ euclideanShellChartDomain m) :
    ENNReal.ofReal (‖complexTestShellChartWave u v m Λ c‖ ^ 2) *
        volume (ball (0 : ℂ) R) ^ 3 ≤
      ∫⁻ w in ball c (2 * R), ENNReal.ofReal (‖complexTestShellChartWave u v m Λ w‖ ^ 2) :=
  local_shellEuclidean_submean_sq (isOpen_euclideanShellChartDomain m)
    (complexTestShellChartWave u v m Λ)
    (fun _ hw => differentiableAt_complexTestShellChartWave u v Λ hw) hR hsub

theorem inducedShellCoordinateVolume_lintegral {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) {s : Set ShellEuclideanDomain}
    (hs : MeasurableSet s) (hsub : s ⊆ euclideanShellChartDomain m)
    (g : ShellEuclideanDomain → ℝ≥0∞) :
    (∫⁻ w in s, g w ∂inducedShellCoordinateVolume m Λ) =
      ∫⁻ w in s, ENNReal.ofReal (inducedShellChartDensity m Λ w) * g w := by
  have hJ : AEMeasurable (fun w => ENNReal.ofReal (inducedShellChartDensity m Λ w))
      (volume.restrict s) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((continuousOn_inducedShellChartDensity m Λ).mono hsub).aemeasurable hs)
  rw [inducedShellCoordinateVolume, Measure.restrict_restrict hs,
    inter_eq_left.mpr hsub]
  exact setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀' volume s hJ g
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)

theorem complexTestShellChartWave_induced_submean {m R d : ℝ}
    (u v : TimeZeroSource) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (c : ShellEuclideanDomain) (hR : 0 < R)
    (hsub : ball c (2 * R) ⊆ euclideanShellChartDomain m)
    (hJ : ∀ w ∈ ball c (2 * R), d ≤ inducedShellChartDensity m Λ w) :
    ENNReal.ofReal d * (ENNReal.ofReal (‖complexTestShellChartWave u v m Λ c‖ ^ 2) *
        volume (ball (0 : ℂ) R) ^ 3) ≤
      ∫⁻ w in ball c (2 * R), ENNReal.ofReal (‖complexTestShellChartWave u v m Λ w‖ ^ 2)
        ∂inducedShellCoordinateVolume m Λ := by
  calc
    _ ≤ ENNReal.ofReal d * (∫⁻ w in ball c (2 * R),
        ENNReal.ofReal (‖complexTestShellChartWave u v m Λ w‖ ^ 2)) :=
      _root_.mul_le_mul_right (complexTestShellChartWave_volume_submean u v Λ c hR hsub) _
    _ = ∫⁻ w in ball c (2 * R), ENNReal.ofReal d *
        ENNReal.ofReal (‖complexTestShellChartWave u v m Λ w‖ ^ 2) :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ w in ball c (2 * R), ENNReal.ofReal (inducedShellChartDensity m Λ w) *
        ENNReal.ofReal (‖complexTestShellChartWave u v m Λ w‖ ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
      exact _root_.mul_le_mul_left (ENNReal.ofReal_le_ofReal (hJ w hw)) _
    _ = _ := (inducedShellCoordinateVolume_lintegral Λ measurableSet_ball hsub _).symm

end VacuumBellSeparation
