/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedCompact
public import LeanPool.EscauriazaSereginSverak.Linear.UCTrace

/-!
# Real quadratic energy from weak `L²` data

The Euclidean vector and spatial-gradient energies used in the short-time
Carleman argument are integrable wherever the corresponding weak fields
belong to `L²`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Square-integrable field and weak gradient data yield integrable real
quadratic energy on the same set. -/
theorem bu_memLp_quadratic_energy_integrable
    (S : Set ParabolicPoint)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (hw : MemLp w 2 (volume.restrict S))
    (hDw : MemLp Dw 2 (volume.restrict S)) :
    IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2) S volume ∧
      IntegrableOn (fun z => spatialGradientSq w Dw z) S volume := by
  have hnormInt : Integrable (fun z : ParabolicPoint => ‖w z‖ ^ 2)
      (volume.restrict S) := by
    simpa using hw.integrable_norm_pow (p := 2) (by norm_num)
  have hEmeas : AEStronglyMeasurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (w z) ^ 2)
      (volume.restrict S) :=
    (continuous_vec3EuclideanNorm.pow 2).comp_aestronglyMeasurable
      hw.aestronglyMeasurable
  have hbound (z : ParabolicPoint) :
      vec3EuclideanNorm (w z) ^ 2 ≤ 3 * ‖w z‖ ^ 2 := by
    have h := vec3EuclideanNorm_le_sqrt_three_mul_norm (w z)
    have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := by norm_num
    have hnn : 0 ≤ vec3EuclideanNorm (w z) := vec3EuclideanNorm_nonneg _
    have hn : 0 ≤ Real.sqrt 3 * ‖w z‖ := by positivity
    nlinarith only [h, hs, hnn, hn, sq_nonneg (‖w z‖)]
  have hwInt : IntegrableOn
      (fun z => vec3EuclideanNorm (w z) ^ 2) S volume := by
    apply Integrable.mono' (hnormInt.const_mul 3) hEmeas
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound z
  have hDwlin : (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hDw.aestronglyMeasurable).1 hDw
    simpa using h
  have hGmeas : AEStronglyMeasurable
      (fun z : ParabolicPoint => spatialGradientSq w Dw z)
      (volume.restrict S) := by
    have hcont : Continuous
        (fun u : Fin 3 → Vec3 =>
          ∑ i : Fin 3, ∑ j : Fin 3, (u i j) ^ (2 : ℕ)) := by
      fun_prop
    simpa only [spatialGradientSq] using
      hcont.comp_aestronglyMeasurable hDw.aestronglyMeasurable
  have hGlin : (∫⁻ z in S,
      ENNReal.ofReal (spatialGradientSq w Dw z)) < ⊤ := by
    calc
      _ ≤ ∫⁻ z in S, 9 * ‖Dw z‖ₑ ^ (2 : ℝ) :=
        lintegral_mono (fun z => CKN.ofReal_spatialGradientSq_le_nine_mul w Dw z)
      _ = 9 * ∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_const_mul' 9 _ (by norm_num)]
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hDwlin
  have hGInt : IntegrableOn (fun z => spatialGradientSq w Dw z)
      S volume :=
    (lintegral_ofReal_ne_top_iff_integrable hGmeas
      (Filter.Eventually.of_forall (fun z => by
        dsimp [spatialGradientSq]
        positivity))).mp hGlin.ne
  exact ⟨hwInt, hGInt⟩

end ESS
