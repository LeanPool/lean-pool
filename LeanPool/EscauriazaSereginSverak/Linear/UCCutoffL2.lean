/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCWeakProduct
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Quadratic data for the Gaussian cutoff

Bounded smooth cutoff factors preserve the finite quadratic data used in
`lem:uc-gaussian`.
-/

public section


open MeasureTheory CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

private theorem uc_memLp_mul_bounded
    {μ : Measure ParabolicPoint}
    {f g : ParabolicPoint → ℝ}
    (hf : MemLp f 2 μ)
    (hg : Continuous g)
    (C : ℝ)
    (hbound : ∀ z, |g z| ≤ C) :
    MemLp (fun z => g z * f z) 2 μ := by
  apply MemLp.of_le_mul (c := C) hf
    (hg.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with z
  change |g z * f z| ≤ C * |f z|
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hbound z) (abs_nonneg _)

/-- The Gaussian cutoff preserves quadratic data for all three weak derivative
fields on the normalized cylinder. -/
theorem ucGaussianCutoff_memLp_data
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    {v : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hv : MemLp v 2 (volume.restrict (ucCylinder ρ)))
    (hDw : MemLp Dw 2 (volume.restrict (ucCylinder ρ)))
    (hD2w : MemLp D2w 2 (volume.restrict (ucCylinder ρ)))
    (hDtw : MemLp Dtw 2 (volume.restrict (ucCylinder ρ))) :
    MemLp
        (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v)
        2 (volume.restrict (ucCylinder ρ)) ∧
    MemLp
        (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dw)
        2 (volume.restrict (ucCylinder ρ)) ∧
    MemLp
        (ucCutoffD2 (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dw D2w)
        2 (volume.restrict (ucCylinder ρ)) ∧
    MemLp
        (ucCutoffDt (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dtw)
        2 (volume.restrict (ucCylinder ρ)) := by
  let U := ucCylinder ρ
  let ζ := ucGaussianCutoff ρ hρ ε
  have hζsmooth := ucGaussianCutoff_smooth ρ hρ ε
  have hζc : Continuous ζ := by
    change Continuous (fun z : ParabolicPoint =>
      ζ (parabolicHomeomorph z))
    exact hζsmooth.continuous.comp parabolicHomeomorph.continuous
  have hζb (z : ParabolicPoint) : |ζ z| ≤ 1 := by
    obtain ⟨h0, h1⟩ := ucGaussianCutoff_bounds hρ ε z
    rwa [abs_of_nonneg h0]
  have hζspc (j : Fin 3) :
      Continuous (fun z : ParabolicPoint => spatialPartial ζ j z) := by
    have hs := spatialPartial_contDiff hζsmooth j
    convert hs.continuous.comp parabolicHomeomorph.continuous using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hζsptc (j k : Fin 3) :
      Continuous (fun z : ParabolicPoint => spatialSecondPartial ζ j k z) := by
    have hs := spatialPartial_contDiff (spatialPartial_contDiff hζsmooth j) k
    convert hs.continuous.comp parabolicHomeomorph.continuous using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hζtc : Continuous (fun z : ParabolicPoint => timePartial ζ z) := by
    have hs := contDiff_timePartial hζsmooth
    convert hs.continuous.comp parabolicHomeomorph.continuous using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hζspb (j : Fin 3) (z : ParabolicPoint) :
      |spatialPartial ζ j z| ≤ cutoffGradientConstant / ρ :=
    ucGaussianCutoff_spatialPartial_bound hρ ε z j
  have hζ2b (j k : Fin 3) (z : ParabolicPoint) :
      |spatialSecondPartial ζ j k z| ≤
        cutoffSecondDerivativeConstant / ρ ^ 2 :=
    ucGaussianCutoff_spatialSecondPartial_bound hρ ε z j k
  have hζtb (z : ParabolicPoint) :
      |timePartial ζ z| ≤ 32 + 8 / ε :=
    ucGaussianCutoff_timePartial_bound hρ hε z
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply MemLp.of_eval
    intro i
    have hmul := uc_memLp_mul_bounded (hv.eval i) hζc 1 hζb
    convert hmul using 1
    ext z
    rfl
  · apply MemLp.of_eval
    intro i
    apply MemLp.of_eval
    intro j
    have hA := uc_memLp_mul_bounded ((hDw.eval i).eval j)
      hζc 1 hζb
    have hB := uc_memLp_mul_bounded (hv.eval i) (hζspc j)
      (cutoffGradientConstant / ρ) (hζspb j)
    convert hA.add hB using 1
    ext z
    dsimp [ucCutoffDw, ζ, ucGaussianCutoff]
    ring
  · apply MemLp.of_eval
    intro i
    apply MemLp.of_eval
    intro j
    apply MemLp.of_eval
    intro k
    have hA := uc_memLp_mul_bounded (((hD2w.eval i).eval j).eval k)
      hζc 1 hζb
    have hB := uc_memLp_mul_bounded ((hDw.eval i).eval j)
      (hζspc k) (cutoffGradientConstant / ρ) (hζspb k)
    have hC := uc_memLp_mul_bounded ((hDw.eval i).eval k)
      (hζspc j) (cutoffGradientConstant / ρ) (hζspb j)
    have hD := uc_memLp_mul_bounded (hv.eval i)
      (hζsptc j k) (cutoffSecondDerivativeConstant / ρ ^ 2) (hζ2b j k)
    convert ((hA.add hB).add hC).add hD using 1
    ext z
    dsimp [ucCutoffD2, ζ, ucGaussianCutoff]
    ring
  · apply MemLp.of_eval
    intro i
    have hA := uc_memLp_mul_bounded (hDtw.eval i) hζc 1 hζb
    have hB := uc_memLp_mul_bounded (hv.eval i) hζtc
      (32 + 8 / ε) hζtb
    convert hA.add hB using 1
    ext z
    dsimp [ucCutoffDt, ζ, ucGaussianCutoff]
    ring

/-- Finite quadratic data on the normalized cylinder give finite quadratic
data after the Gaussian cutoff. -/
theorem ucGaussianCutoff_l2_data
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    {v : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Set.Ioo 0 2)
      v Dw D2w Dtw)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    MemLp
        (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v)
        2 (volume.restrict (ucCylinder ρ)) ∧
    MemLp
        (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dw)
        2 (volume.restrict (ucCylinder ρ)) ∧
    MemLp
        (ucCutoffD2 (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dw D2w)
        2 (volume.restrict (ucCylinder ρ)) ∧
    MemLp
        (ucCutoffDt (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dtw)
        2 (volume.restrict (ucCylinder ρ)) := by
  have hvfin : (∫⁻ z in ucCylinder ρ, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply (lintegral_mono ?_).trans_lt hL2
    intro z
    exact (le_add_right le_rfl).trans
      ((le_add_right le_rfl).trans (le_add_right le_rfl))
  have hDwfin : (∫⁻ z in ucCylinder ρ, ‖Dw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply (lintegral_mono ?_).trans_lt hL2
    intro z
    exact (le_add_left le_rfl).trans
      ((le_add_right le_rfl).trans (le_add_right le_rfl))
  have hD2fin : (∫⁻ z in ucCylinder ρ, ‖D2w z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply (lintegral_mono ?_).trans_lt hL2
    intro z
    exact (le_add_left le_rfl).trans (le_add_right le_rfl)
  have hDtfin : (∫⁻ z in ucCylinder ρ, ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply (lintegral_mono ?_).trans_lt hL2
    intro z
    exact le_add_left le_rfl
  have hvm : MemLp v 2 (volume.restrict (ucCylinder ρ)) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hweak.1.aestronglyMeasurable).2
    simpa [ucCylinder] using hvfin
  have hDwm : MemLp Dw 2 (volume.restrict (ucCylinder ρ)) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hweak.2.1.aestronglyMeasurable).2
    simpa [ucCylinder] using hDwfin
  have hD2m : MemLp D2w 2 (volume.restrict (ucCylinder ρ)) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hweak.2.2.1.aestronglyMeasurable).2
    simpa [ucCylinder] using hD2fin
  have hDtm : MemLp Dtw 2 (volume.restrict (ucCylinder ρ)) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hweak.2.2.2.1.aestronglyMeasurable).2
    simpa [ucCylinder] using hDtfin
  exact ucGaussianCutoff_memLp_data hρ hε hvm hDwm hD2m hDtm

end ESS
