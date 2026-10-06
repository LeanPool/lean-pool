/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSpatial
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateTestField

/-!
# Serrin slices on a general time interval

A finite mixed Serrin integral on `(t₀, t₁)` gives a finite spatial norm of
almost every time slice (`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A finite mixed Serrin integral on `(t₀, t₁)` gives a finite spatial slice
norm at almost every time. -/
theorem lps_h1_finite_slice_memLp_ae
    {t₀ t₁ s : ℝ} {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hs : 3 < s)
    (hmix : (∫⁻ t in Ioo t₀ t₁,
      (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
        ((2 * s / (s - 3)) / s)) < ⊤) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)),
      MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal s) volume := by
  let ν : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo t₀ t₁))
  have hslab : (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁)) :
      Measure (Vec3 × ℝ)) = ν := by
    show (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo t₀ t₁) = ν
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have huν : AEStronglyMeasurable u ν := hslab ▸ hu
  have hscalar : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => vec3EuclideanNorm (u z)) ν :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable huν
  let F : Vec3 × ℝ → ℝ≥0∞ := fun z => ‖vec3EuclideanNorm (u z)‖ₑ ^ s
  have hF : AEMeasurable F ν := hscalar.enorm.pow_const _
  have hG : AEMeasurable (fun t : ℝ => ∫⁻ x : Vec3, F (x, t) ∂volume)
      (volume.restrict (Ioo t₀ t₁)) := hF.lintegral_prod_left'
  have hp : 0 < (2 * s / (s - 3)) / s := by
    have hs0 : 0 < s := lt_trans (by norm_num) hs
    have hden : 0 < s - 3 := by linarith only [hs]
    positivity
  have hmomentMeas : AEMeasurable
      (fun t : ℝ => (∫⁻ x : Vec3, F (x, t) ∂volume) ^ ((2 * s / (s - 3)) / s))
      (volume.restrict (Ioo t₀ t₁)) := hG.pow_const _
  have hmomentFinite :
      (∫⁻ t, (∫⁻ x : Vec3, F (x, t) ∂volume) ^ ((2 * s / (s - 3)) / s)
        ∂(volume.restrict (Ioo t₀ t₁))) < ⊤ := by
    have hFraw (z : Vec3 × ℝ) :
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ s = F z := by
      rw [← Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
    have hEq :
        (∫⁻ t in Ioo t₀ t₁, (∫⁻ x : Vec3, F (x, t) ∂volume) ^ ((2 * s / (s - 3)) / s)) =
        (∫⁻ t in Ioo t₀ t₁, (∫⁻ x : Vec3,
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
  have hfiniteAE : ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)),
      (∫⁻ x : Vec3, F (x, t) ∂volume) ^ ((2 * s / (s - 3)) / s) < ⊤ :=
    ae_lt_top' hmomentMeas hmomentFinite.ne
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)), (∫⁻ x : Vec3, F (x, t) ∂volume) < ⊤ := by
    filter_upwards [hfiniteAE] with t ht
    exact (ENNReal.rpow_lt_top_iff_of_pos hp).mp ht
  have hsliceMeas : ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)),
      AEStronglyMeasurable (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) volume := by
    filter_upwards [huν.prodMk_right] with t ht
    exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable ht
  filter_upwards [hslice, hsliceMeas] with t hfin hmeas
  have hp0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr (lt_trans (by norm_num) hs)).ne'
  have hptop : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hmeas]
  rw [show (ENNReal.ofReal s).toReal = s from
    ENNReal.toReal_ofReal (le_of_lt (lt_trans (by norm_num) hs))]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hfin.ne

end ESS

end
