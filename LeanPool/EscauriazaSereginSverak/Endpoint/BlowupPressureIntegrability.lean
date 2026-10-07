/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupVanishing
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Time integration of the local pressure norm

Tonelli converts the time integral of the spatial `L^(3/2)` pressure norm
into its space-time integral (`lem:pressure-split`).
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The time integral of the spatial `L^(3/2)` norm power equals the
space-time `L^(3/2)` mass. -/
theorem blowupScalarTimeThreeHalves_eq
    {Ω : Set Vec3} {J : Set ℝ}
    (p : ParabolicPoint → ℝ)
    (hp : AEStronglyMeasurable (fun z : Vec3 × ℝ => p (z.1, z.2))
      ((volume.restrict Ω).prod (volume.restrict J))) :
    (∫⁻ t in J,
      eLpNorm (fun x : Vec3 => p (x, t)) (3 / 2 : ℝ≥0∞)
        (volume.restrict Ω) ^ (3 / 2 : ℝ)) =
      ∫⁻ z,
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)
        ∂((volume.restrict Ω).prod (volume.restrict J)) := by
  let μx := volume.restrict Ω
  let μt := volume.restrict J
  have hslice := hp.prodMk_right
  have hpow : ∀ᵐ t ∂μt,
      eLpNorm (fun x : Vec3 => p (x, t)) (3 / 2 : ℝ≥0∞)
          μx ^ (3 / 2 : ℝ) =
        ∫⁻ x, ENNReal.ofReal |p (x, t)| ^ (3 / 2 : ℝ) ∂μx := by
    filter_upwards [hslice] with t ht
    have h := eLpNorm_nnreal_pow_eq_lintegral
      (p := (3 / 2 : NNReal)) (f := fun x : Vec3 => p (x, t))
      (by norm_num) ht
    norm_num at h ⊢
    simpa [Real.enorm_eq_ofReal_abs] using h
  have hmeas : AEMeasurable
      (fun z : Vec3 × ℝ => ENNReal.ofReal |p z| ^ (3 / 2 : ℝ))
      (μx.prod μt) := by
    simpa only [μx, μt, Real.enorm_eq_ofReal_abs, Function.comp_def] using
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hp.enorm)
  calc
    (∫⁻ t in J,
      eLpNorm (fun x : Vec3 => p (x, t)) (3 / 2 : ℝ≥0∞)
        (volume.restrict Ω) ^ (3 / 2 : ℝ)) =
      ∫⁻ t, ∫⁻ x,
        ENNReal.ofReal |p (x, t)| ^ (3 / 2 : ℝ) ∂μx ∂μt := by
          exact lintegral_congr_ae hpow
    _ = ∫⁻ z, ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)
        ∂(μx.prod μt) := (lintegral_prod_symm _ hmeas).symm
    _ = _ := rfl

/-- A space-time `L^(3/2)` pressure has `L^(3/2)` spatial slices at almost
every time. -/
theorem pressureSlice_memLp_ae
    {J : Set ℝ} (p : ParabolicPoint → ℝ)
    (hp : MemLp (fun z : Vec3 × ℝ => p (z.1, z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod (volume.restrict J))) :
    ∀ᵐ t ∂(volume.restrict J),
      MemLp (fun x : Vec3 => p (x, t)) (3 / 2 : ℝ≥0∞)
        (volume.restrict (CKN.euclideanBall 0 1)) := by
  let μx : Measure Vec3 := volume.restrict (CKN.euclideanBall 0 1)
  let μt : Measure ℝ := volume.restrict J
  have hsm := hp.aestronglyMeasurable.prodMk_right
  have htime := blowupScalarTimeThreeHalves_eq (Ω := CKN.euclideanBall 0 1)
    (J := J) p hp.aestronglyMeasurable
  have hspace : (∫⁻ z, ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)
        ∂(μx.prod μt)) < ⊤ := by
    have h := eLpNorm_nnreal_pow_eq_lintegral
      (p := (3 / 2 : NNReal)) (f := fun z : Vec3 × ℝ => p (z.1,z.2))
      (by norm_num) hp.aestronglyMeasurable
    have htop : eLpNorm (fun z : Vec3 × ℝ => p (z.1,z.2))
        (3 / 2 : ℝ≥0∞) (μx.prod μt) ^ (3 / 2 : ℝ) < ⊤ := by
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hp.ne
    norm_num at h
    have heq : (∫⁻ z, ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)
        ∂(μx.prod μt)) = eLpNorm (fun z : Vec3 × ℝ => p (z.1,z.2))
        (3 / 2 : ℝ≥0∞) (μx.prod μt) ^ (3 / 2 : ℝ) := by
      simpa only [Real.enorm_eq_ofReal_abs] using h.symm
    rw [heq]
    exact htop
  have htimeTop : (∫⁻ t,
      eLpNorm (fun x : Vec3 => p (x,t)) (3 / 2 : ℝ≥0∞) μx ^ (3 / 2 : ℝ)
      ∂μt) < ⊤ := by simpa only [μx, μt] using htime.trans_lt hspace
  have hpowMeas : AEMeasurable
      (fun z : Vec3 × ℝ => ENNReal.ofReal |p z| ^ (3 / 2 : ℝ))
      (μx.prod μt) := by
    simpa only [μx, μt, Real.enorm_eq_ofReal_abs, Function.comp_def] using
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        hp.aestronglyMeasurable.enorm)
  have hinnerMeas : AEMeasurable
      (fun t : ℝ => ∫⁻ x, ENNReal.ofReal |p (x,t)| ^ (3 / 2 : ℝ) ∂μx)
      μt := hpowMeas.lintegral_prod_left'
  have hinnerTop : (∫⁻ t, ∫⁻ x,
      ENNReal.ofReal |p (x,t)| ^ (3 / 2 : ℝ) ∂μx ∂μt) < ⊤ := by
    rw [← lintegral_prod_symm _ hpowMeas]
    exact hspace
  have hinnerFinite := ae_lt_top' hinnerMeas hinnerTop.ne
  filter_upwards [hsm, hinnerFinite] with t ht hfin
  have h := eLpNorm_nnreal_pow_eq_lintegral
    (p := (3 / 2 : NNReal)) (f := fun x : Vec3 => p (x,t))
    (by norm_num) ht
  have heq : eLpNorm (fun x : Vec3 => p (x,t))
      (3 / 2 : ℝ≥0∞) μx ^ (3 / 2 : ℝ) =
      ∫⁻ x, ENNReal.ofReal |p (x,t)| ^ (3 / 2 : ℝ) ∂μx := by
    norm_num at h ⊢
    simpa only [μx, Real.enorm_eq_ofReal_abs] using h
  have hnormPow : eLpNorm (fun x : Vec3 => p (x,t))
      (3 / 2 : ℝ≥0∞) μx ^ (3 / 2 : ℝ) < ⊤ := heq.trans_lt hfin
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 3 / 2)).mp hnormPow

/-- Integrable harmonic pressure slices have an interior time-integrated
supremum bound. -/
theorem blowupHarmonicPressure_bound
    {J : Set ℝ} (p₂ : ParabolicPoint → ℝ)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod (volume.restrict J)))
    (hharm : ∀ᵐ t ∂(volume.restrict J),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p₂ (x,t))) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      (∫⁻ t in J,
        eLpNorm (fun x : Vec3 => p₂ (x,t)) ⊤
          (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))) ^
            (3 / 2 : ℝ)) ≤
        C * eLpNorm (fun z : Vec3 × ℝ => p₂ (z.1,z.2))
          (3 / 2 : ℝ≥0∞)
          ((volume.restrict (CKN.euclideanBall 0 1)).prod
            (volume.restrict J)) ^ (3 / 2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := blowupHarmonicSlices_time_bound
  refine ⟨C, hC, ?_⟩
  have hslices := pressureSlice_memLp_ae p₂ hp₂
  have hboth : ∀ᵐ t ∂(volume.restrict J),
      MemLp (fun x : Vec3 => p₂ (x,t)) (3 / 2 : ℝ≥0∞)
        (volume.restrict (CKN.euclideanBall 0 1)) ∧
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p₂ (x,t)) := hslices.and hharm
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hcoeff] at hbound
  have hraw := hbound p₂ J hboth
  have htime := blowupScalarTimeThreeHalves_eq
    (Ω := CKN.euclideanBall 0 1) (J := J) p₂ hp₂.aestronglyMeasurable
  have htotal := eLpNorm_nnreal_pow_eq_lintegral
      (p := (3 / 2 : NNReal))
      (f := fun z : Vec3 × ℝ => p₂ (z.1,z.2))
      (by norm_num) hp₂.aestronglyMeasurable
  have heq : (∫⁻ t in J,
      eLpNorm (fun x : Vec3 => p₂ (x,t)) (3 / 2 : ℝ≥0∞)
        (volume.restrict (CKN.euclideanBall 0 1)) ^ (3 / 2 : ℝ)) =
      eLpNorm (fun z : Vec3 × ℝ => p₂ (z.1,z.2))
        (3 / 2 : ℝ≥0∞)
        ((volume.restrict (CKN.euclideanBall 0 1)).prod
          (volume.restrict J)) ^ (3 / 2 : ℝ) := by
    norm_num at htotal ⊢
    rw [htime]
    simpa only [Real.enorm_eq_ofReal_abs] using htotal.symm
  rw [heq] at hraw
  exact hraw

/-- The harmonic interior supremum, extended by zero in time, has finite
`L^(3/2)` mass on the whole time line. -/
theorem blowupHarmonicPressure_global_sup_integrable
    (p₂ : ParabolicPoint → ℝ)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (hharm : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p₂ (x,t))) :
    (∫⁻ t : ℝ,
      ((Ioo (-1 : ℝ) 0).indicator
        (fun s => eLpNorm (fun x : Vec3 => p₂ (x,s)) ⊤
          (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ)))) t) ^
            (3 / 2 : ℝ)) < ⊤ := by
  obtain ⟨C, hC, hbound⟩ := blowupHarmonicPressure_bound
    (J := Ioo (-1 : ℝ) 0) p₂ hp₂ hharm
  have hnorm : eLpNorm (fun z : Vec3 × ℝ => p₂ (z.1,z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))) ^ (3 / 2 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hp₂.ne
  have htime : (∫⁻ t in Ioo (-1 : ℝ) 0,
      eLpNorm (fun x : Vec3 => p₂ (x,t)) ⊤
        (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))) ^
          (3 / 2 : ℝ)) < ⊤ :=
    hbound.trans_lt (ENNReal.mul_lt_top hC hnorm)
  have hind : (∫⁻ t : ℝ,
      ((Ioo (-1 : ℝ) 0).indicator
        (fun s => eLpNorm (fun x : Vec3 => p₂ (x,s)) ⊤
          (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ)))) t) ^
            (3 / 2 : ℝ)) =
      (∫⁻ t in Ioo (-1 : ℝ) 0,
        eLpNorm (fun x : Vec3 => p₂ (x,t)) ⊤
          (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))) ^
            (3 / 2 : ℝ)) := by
    rw [← lintegral_indicator (measurableSet_Ioo)]
    congr 1
    funext t
    by_cases ht : t ∈ Ioo (-1 : ℝ) 0
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  rw [hind]
  exact htime

end ESS
