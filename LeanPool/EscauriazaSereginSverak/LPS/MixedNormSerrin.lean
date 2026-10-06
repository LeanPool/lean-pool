/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSpaceTimeMollify
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The finite Serrin exponents satisfy the critical scaling relation in
`thm:lps`. -/
theorem lps_exponent_relation (s : ℝ) (hs : 3 < s) :
    3 / s + 2 / (2 * s / (s - 3)) = 1 := by
  have hs0 : s ≠ 0 := ne_of_gt (lt_trans (by norm_num) hs)
  have hsm3 : s - 3 ≠ 0 := sub_ne_zero.mpr hs.ne'
  field_simp [hs0, hsm3]
  ring

/-- A finite mixed Serrin integral gives a finite spatial slice norm at almost
every time, as used in `thm:lps`. -/
theorem lps_finite_branch_slice_memLp_ae
    {T s : ℝ} {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hs : 3 < s)
    (hmix : (∫⁻ t in Ioo 0 T,
      (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
        ((2 * s / (s - 3)) / s)) < ⊤) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal s) volume := by
  let ν : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  rw [serrin_slab_measure_eq T] at hu
  have hscalar : AEStronglyMeasurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (u z)) ν :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hu
  let F : ParabolicPoint → ℝ≥0∞ := fun z =>
    ‖vec3EuclideanNorm (u z)‖ₑ ^ s
  have hF : AEMeasurable F ν := hscalar.enorm.pow_const _
  have hG : AEMeasurable (fun t : ℝ => ∫⁻ x : Vec3, F (x, t) ∂volume)
      (volume.restrict (Ioo 0 T)) := by
    exact hF.lintegral_prod_left'
  have hp : 0 < (2 * s / (s - 3)) / s := by
    have hs0 : 0 < s := lt_trans (by norm_num) hs
    have hden : 0 < s - 3 := by linarith only [hs]
    positivity
  have hmomentMeas : AEMeasurable
      (fun t : ℝ => (∫⁻ x : Vec3, F (x, t) ∂volume) ^ ((2 * s / (s - 3)) / s))
      (volume.restrict (Ioo 0 T)) := hG.pow_const _
  have hmomentFinite :
      (∫⁻ t, (∫⁻ x : Vec3, F (x, t) ∂volume) ^ ((2 * s / (s - 3)) / s)
        ∂(volume.restrict (Ioo 0 T))) < ⊤ := by
    have hFraw (z : ParabolicPoint) :
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ s = F z := by
      rw [← Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
    have hEq :
        (∫⁻ t in Ioo 0 T,
          (∫⁻ x : Vec3, F (x, t) ∂volume) ^ ((2 * s / (s - 3)) / s)) =
        (∫⁻ t in Ioo 0 T,
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s ∂volume) ^
              ((2 * s / (s - 3)) / s)) := by
      apply lintegral_congr
      intro t
      congr 1
      apply lintegral_congr
      intro x
      exact (hFraw (x, t)).symm
    rw [hEq]
    exact hmix
  have hfiniteAE : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫⁻ x : Vec3, F (x, t) ∂volume) ^ ((2 * s / (s - 3)) / s) < ⊤ :=
    ae_lt_top' hmomentMeas hmomentFinite.ne
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫⁻ x : Vec3, F (x, t) ∂volume) < ⊤ := by
    filter_upwards [hfiniteAE] with t ht
    exact (ENNReal.rpow_lt_top_iff_of_pos hp).mp ht
  have hsliceMeas : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      AEStronglyMeasurable (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) volume := by
    filter_upwards [hu.prodMk_right] with t ht
    exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable ht
  filter_upwards [hslice, hsliceMeas] with t hfin hmeas
  have hp0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr (lt_trans (by norm_num) hs)).ne'
  have hptop : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcongr :
      (fun x : Vec3 => ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s) =ᵐ[volume]
        (fun x => F (x, t)) := by
    filter_upwards [] with x
    change ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s =
      ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s
    rfl
  have hlin : (∫⁻ x : Vec3,
      ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s ∂volume) < ⊤ := by
    exact lt_of_le_of_lt (le_of_eq (lintegral_congr_ae hcongr)) hfin
  rw [memLp_iff,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hmeas]
  rw [show (ENNReal.ofReal s).toReal = s from
    ENNReal.toReal_ofReal (le_of_lt (lt_trans (by norm_num) hs))]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hlin.ne

/-- The finite mixed Serrin integral makes the time power of the slice
`L^s` norm integrable, as used in `thm:lps`. -/
theorem lps_finite_branch_time_moment_integrable
    {T s : ℝ} {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hs : 3 < s)
    (hmix : (∫⁻ t in Ioo 0 T,
      (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
        ((2 * s / (s - 3)) / s)) < ⊤) :
    IntegrableOn (fun t : ℝ =>
      (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal s) volume).toReal ^ (2 * s / (s - 3))) (Ioo 0 T) := by
  let ν : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  rw [serrin_slab_measure_eq T] at hu
  have hscalar : AEStronglyMeasurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (u z)) ν :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hu
  let F : ParabolicPoint → ℝ≥0∞ := fun z =>
    ‖vec3EuclideanNorm (u z)‖ₑ ^ s
  have hF : AEMeasurable F ν := hscalar.enorm.pow_const _
  have hG : AEMeasurable (fun t : ℝ => ∫⁻ x : Vec3, F (x, t) ∂volume)
      (volume.restrict (Ioo 0 T)) := hF.lintegral_prod_left'
  have hexp : 0 < (2 * s / (s - 3)) / s := by
    have hs0 : 0 < s := lt_trans (by norm_num) hs
    have hden : 0 < s - 3 := by linarith only [hs]
    positivity
  have hmomentMeas : AEMeasurable
      (fun t : ℝ => (∫⁻ x : Vec3, F (x, t) ∂volume) ^ ((2 * s / (s - 3)) / s))
      (volume.restrict (Ioo 0 T)) := hG.pow_const _
  have hFraw (z : ParabolicPoint) :
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ s = F z := by
    rw [← Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
  have hEq :
      (∫⁻ t in Ioo 0 T,
        (∫⁻ x : Vec3, F (x, t) ∂volume) ^ ((2 * s / (s - 3)) / s)) =
      (∫⁻ t in Ioo 0 T,
        (∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s ∂volume) ^
            ((2 * s / (s - 3)) / s)) := by
    apply lintegral_congr
    intro t
    congr 1
    apply lintegral_congr
    intro x
    exact (hFraw (x, t)).symm
  have hmomentFinite :
      (∫⁻ t in Ioo 0 T,
        (∫⁻ x : Vec3, F (x, t) ∂volume) ^ ((2 * s / (s - 3)) / s)) < ⊤ := by
    rw [hEq]
    exact hmix
  have hbase := integrable_toReal_of_lintegral_ne_top hmomentMeas hmomentFinite.ne
  have hsliceMeas : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      AEStronglyMeasurable (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) volume := by
    filter_upwards [hu.prodMk_right] with t ht
    exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable ht
  refine hbase.congr ?_
  filter_upwards [hsliceMeas] with t ht
  have hs0 : ENNReal.ofReal s ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (lt_trans (by norm_num) hs)).ne'
  have hstop : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsreal : (ENNReal.ofReal s).toReal = s :=
    ENNReal.toReal_ofReal (le_of_lt (lt_trans (by norm_num) hs))
  symm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hs0 hstop ht, hsreal]
  have hroot : 0 ≤ (∫⁻ x : Vec3,
      ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s ∂volume).toReal := ENNReal.toReal_nonneg
  calc
    ((∫⁻ x : Vec3, ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s ∂volume) ^ (1 / s)).toReal ^
        (2 * s / (s - 3)) =
      (∫⁻ x : Vec3, ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s ∂volume).toReal ^
        ((1 / s) * (2 * s / (s - 3))) := by
      rw [← ENNReal.toReal_rpow, ← Real.rpow_mul hroot]
    _ = (∫⁻ x : Vec3,
        ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s ∂volume).toReal ^
          ((2 * s / (s - 3)) / s) := by
      congr 1
      ring
    _ = ((∫⁻ x : Vec3,
        ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s ∂volume) ^
          ((2 * s / (s - 3)) / s)).toReal := by
      rw [ENNReal.toReal_rpow]

end ESS

end
