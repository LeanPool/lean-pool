/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCutoffBridge
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanSobolevConsumers

/-!
# Carleman inequality for the translated Gaussian cutoff

The compact cutoff data satisfy the Gaussian Carleman inequality with explicit
constant `exp(4/3) * (9 + 2 * sqrt 6)`.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem buGaussian_memLp_set_l2_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ParabolicPoint → E} {U : Set ParabolicPoint}
    (hf : MemLp f 2 volume) :
    (∫⁻ z in U, ‖f z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hrestrict : MemLp f 2 (volume.restrict U) := hf.restrict U
  have hfinite := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (p := (2 : ℝ≥0∞)) (μ := volume.restrict U) (by norm_num) (by norm_num)
    hrestrict.aestronglyMeasurable).1 hrestrict
  simpa using hfinite

private theorem buGaussian_memLp_data_l2_finite
    {U : Set ParabolicPoint}
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hw : MemLp w 2 volume) (hDw : MemLp Dw 2 volume)
    (hD2w : MemLp D2w 2 volume) (hDtw : MemLp Dtw 2 volume) :
    (∫⁻ z in U, ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
      ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hW := buGaussian_memLp_set_l2_finite (U := U) hw
  have hG := buGaussian_memLp_set_l2_finite (U := U) hDw
  have hH := buGaussian_memLp_set_l2_finite (U := U) hD2w
  have hT := buGaussian_memLp_set_l2_finite (U := U) hDtw
  let μ := volume.restrict U
  let W : ParabolicPoint → ℝ≥0∞ := fun z => ‖w z‖ₑ ^ (2 : ℝ)
  let G : ParabolicPoint → ℝ≥0∞ := fun z => ‖Dw z‖ₑ ^ (2 : ℝ)
  let H : ParabolicPoint → ℝ≥0∞ := fun z => ‖D2w z‖ₑ ^ (2 : ℝ)
  let T : ParabolicPoint → ℝ≥0∞ := fun z => ‖Dtw z‖ₑ ^ (2 : ℝ)
  have hWm : AEMeasurable W μ :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((hw.restrict U).aestronglyMeasurable.enorm)
  have hGm : AEMeasurable G μ :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((hDw.restrict U).aestronglyMeasurable.enorm)
  have hHm : AEMeasurable H μ :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((hD2w.restrict U).aestronglyMeasurable.enorm)
  have hTm : AEMeasurable T μ :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((hDtw.restrict U).aestronglyMeasurable.enorm)
  let F₁ : ParabolicPoint → ℝ≥0∞ := fun z => W z + G z
  have hF₁m : AEMeasurable F₁ μ := hWm.add hGm
  have hsum₁ : (∫⁻ z, F₁ z ∂μ) < ⊤ := by
    rw [lintegral_add_left' hWm]
    exact ENNReal.add_lt_top.mpr ⟨hW, hG⟩
  let F₂ : ParabolicPoint → ℝ≥0∞ := fun z => F₁ z + H z
  have hF₂m : AEMeasurable F₂ μ := hF₁m.add hHm
  have hsum₂ : (∫⁻ z, F₂ z ∂μ) < ⊤ := by
    rw [lintegral_add_left' hF₁m]
    exact ENNReal.add_lt_top.mpr ⟨hsum₁, hH⟩
  let F₃ : ParabolicPoint → ℝ≥0∞ := fun z => F₂ z + T z
  have hsum₃ : (∫⁻ z, F₃ z ∂μ) < ⊤ := by
    rw [lintegral_add_left' hF₂m]
    exact ENNReal.add_lt_top.mpr ⟨hsum₂, hT⟩
  simpa [μ, F₃, F₂, F₁, W, G, H, T] using hsum₃

/-- The translated cutoff of rescaled data is an admissible input for the
Gaussian Carleman estimate, with its explicit constant. -/
theorem buGaussian_shifted_cutoff_carleman
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 (2 - 1 / 6))
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      ‖buGaussianShiftedField (1 / 6) v z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDw (1 / 6) Dv z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedD2w (1 / 6) D2v z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDtw (1 / 6) Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    ∀ a : ℝ, 0 < a →
      ∫ z in spaceTimeSet univ (Ioo 0 2),
        (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          (a / z.2 * vec3EuclideanNorm (buGaussianShiftedCutoffField ρ hρ ε v z) ^ 2 +
            spatialGradientSq (buGaussianShiftedCutoffField ρ hρ ε v)
              (buGaussianShiftedCutoffDw ρ hρ ε v Dv) z) ≤
        (Real.exp (4 / 3) * (9 + 2 * Real.sqrt 6)) *
          ∫ z in spaceTimeSet univ (Ioo 0 2),
            (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
              Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
              vec3EuclideanNorm (fun i =>
                buGaussianShiftedCutoffDtw ρ hρ ε v Dtv z i +
                  ∑ j, buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v z i j j) ^ 2 := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo 0 2)
  obtain ⟨hweakCut, hcompact, hsupport, hfieldMem, hDwMem, hD2Mem, hDtMem⟩ :=
    buGaussian_shifted_cutoff_admissible hρ hε hweak hL2
  have hL2Cut := buGaussian_memLp_data_l2_finite
    (U := U) hfieldMem hDwMem hD2Mem hDtMem
  have hcarleman := bu_carleman_sobolev_gaussian
    (buGaussianShiftedCutoffField ρ hρ ε v)
    (buGaussianShiftedCutoffDw ρ hρ ε v Dv)
    (buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v)
    (buGaussianShiftedCutoffDtw ρ hρ ε v Dtv)
    hweakCut hcompact hsupport hL2Cut
  intro a ha
  have h := hcarleman a ha
  simpa [ucWeakHeatVector] using h

end ESS
