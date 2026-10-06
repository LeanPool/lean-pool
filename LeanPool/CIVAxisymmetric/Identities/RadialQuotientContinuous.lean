/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.MeridionalSlices
public import LeanPool.CIVAxisymmetric.Statements.RadialQuotient
public import LeanPool.CIVAxisymmetric.Setting.Rotation
public import LeanPool.CIVAxisymmetric.Setting.RotationLemmas
public import LeanPool.CIVAxisymmetric.Setting.AngularMeanSmooth
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! ### Auxiliary lemmas -/

public section

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



private lemma rotZ_neg_pi_meridional_zero (x₃ : ℝ) :
    rotZ (-Real.pi) (meridional 0 x₃) = meridional 0 x₃ := by
  rw [rotZ_meridional]
  unfold meridional
  simp [Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]

private lemma rotField_pi_eq_rotZ_pi_at_axis (u : ParabolicPoint → Vec3) (t : ℝ)
    (x₃ : ℝ) :
    rotField Real.pi u ((meridional 0 x₃, t) : ParabolicPoint) =
      rotZ Real.pi (u ((meridional 0 x₃, t) : ParabolicPoint)) := by
  let z : ParabolicPoint := (meridional 0 x₃, t)
  have h := rotField_apply Real.pi u z
  have hz1 : z.1 = meridional 0 x₃ := rfl
  have hz2 : z.2 = t := rfl
  rw [hz1, hz2] at h
  rw [rotZ_meridional] at h
  have h_simp : (![Real.cos (-Real.pi) * (0 : ℝ), Real.sin (-Real.pi) * (0 : ℝ), x₃] : Vec3) =
    meridional 0 x₃ := by
    unfold meridional
    ext i; fin_cases i <;> simp [Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
  rw [h_simp] at h
  simpa [z] using h

private lemma component_zero_neg_eq_component_zero (v : Vec3) (h : rotZ Real.pi v = v) : v 0 = 0
    := by
  have h0 : rotZ Real.pi v 0 = v 0 := by rw [h]
  rw [rotZ_apply_zero] at h0
  simp [Real.cos_pi, Real.sin_pi] at h0
  linarith only [h0]

/-! ### Main theorems -/

theorem meridional_axis_component_zero (u : ParabolicPoint → Vec3) (t : ℝ)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0)
    (x₃ : ℝ) (hx : |x₃| < 1) :
    u ((meridional 0 x₃, t) : ParabolicPoint) 0 = 0 := by
  have hmem : ((meridional 0 x₃, t) : ParabolicPoint) ∈ unitCylinder :=
    mem_unitCylinder_meridional x₃ hx t ht
  have h_eq : rotField Real.pi u ((meridional 0 x₃, t) : ParabolicPoint) = u ((meridional 0 x₃,
    t) : ParabolicPoint) :=
    haxi.rotField_eq (rotZ_mem_unitCylinder) Real.pi hmem
  rw [rotField_pi_eq_rotZ_pi_at_axis u t x₃] at h_eq
  exact component_zero_neg_eq_component_zero (u ((meridional 0 x₃, t) : ParabolicPoint)) h_eq

/-! ### Smoothness of the axial slice `x ↦ u (x, t) 0` -/

private lemma contDiffOn_axial_slice (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t) 0) (vec3Ball (0 : Vec3) 1) := by
  have hemb : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => ((x, t) : Vec3 × ℝ))
      (vec3Ball (0 : Vec3) 1) := (contDiff_id.prodMk contDiff_const).contDiffOn
  have hmaps : Set.MapsTo (fun x : Vec3 => ((x, t) : Vec3 × ℝ)) (vec3Ball (0 : Vec3) 1)
      unitCylinder := by
    intro x hx
    unfold unitCylinder spaceTimeSet
    exact Set.mk_mem_prod hx ht
  exact contDiffOn_pi.1 (hu.comp hemb hmaps) 0

private lemma differentiableAt_axial_slice (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) {p : Vec3} (hp : p ∈ vec3Ball (0 : Vec3) 1) :
    DifferentiableAt ℝ (fun x : Vec3 => u (x, t) 0) p := by
  have hcd1 : ContDiffOn ℝ (1 : ℕ∞) (fun x : Vec3 => u (x, t) 0) (vec3Ball (0 : Vec3) 1) :=
    (contDiffOn_axial_slice u t hu ht).of_le (by exact_mod_cast le_top)
  exact (hcd1.differentiableOn one_ne_zero).differentiableAt
    ((isOpen_vec3Ball 0 1).mem_nhds hp)

private lemma continuousOn_spatialPartial_axial (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun p : Vec3 => spatialPartial (fun w => u w 0) 0 (p, t))
      (vec3Ball (0 : Vec3) 1) := by
  have hcd1 : ContDiffOn ℝ (1 : ℕ∞) (fun x : Vec3 => u (x, t) 0) (vec3Ball (0 : Vec3) 1) :=
    (contDiffOn_axial_slice u t hu ht).of_le (by exact_mod_cast le_top)
  exact (hcd1.continuousOn_fderiv_of_isOpen (isOpen_vec3Ball 0 1) le_rfl).clm_apply
    continuousOn_const

/-! ### The integral representation of the radial quotient -/

private lemma radialQuotient_eq_integral (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0)
    (x₁ x₃ : ℝ) (hx : x₁ ^ 2 + x₃ ^ 2 < 1) :
    radialQuotient u (meridional x₁ x₃, t) =
      ∫ s in (0:ℝ)..1, spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t) := by
  have hx3 : |x₃| < 1 := (sq_lt_one_iff_abs_lt_one x₃).mp (by nlinarith only [hx, sq_nonneg x₁])
  have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => u (meridional (s * x₁) x₃, t) 0)
        (x₁ * spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t)) s := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith only [hs.1], hs.2⟩
    have hmem : meridional (s * x₁) x₃ ∈ vec3Ball (0 : Vec3) 1 :=
      meridional_scale_mem_vec3Ball hx hs1
    have hdiff := differentiableAt_axial_slice u t hu ht hmem
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_meridional_scale x₁ x₃ s)
    rw [show (fderiv ℝ (fun x : Vec3 => u (x, t) 0) (meridional (s * x₁) x₃))
        (x₁ • basisVec 0) =
        x₁ * spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t) from by
      rw [map_smul, smul_eq_mul]; rfl] at hcomp
    exact hcomp
  have hint : IntervalIntegrable
      (fun s => x₁ * spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t))
      MeasureTheory.volume 0 1 := by
    have hcont := continuousOn_spatialPartial_axial u t hu ht
    have hpath : Continuous (fun s : ℝ => meridional (s * x₁) x₃) := by
      unfold meridional; fun_prop
    have hmaps : Set.MapsTo (fun s : ℝ => meridional (s * x₁) x₃) (Set.uIcc (0:ℝ) 1)
        (vec3Ball (0 : Vec3) 1) := by
      intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      exact meridional_scale_mem_vec3Ball hx (abs_le.mpr ⟨by linarith only [hs.1], hs.2⟩)
    exact (continuous_const.continuousOn.mul
      (hcont.comp' hpath.continuousOn hmaps)).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [one_mul, zero_mul] at hFTC
  rw [meridional_axis_component_zero u t haxi ht x₃ hx3, sub_zero,
    intervalIntegral.integral_const_mul] at hFTC
  simp only [radialQuotient, meridional_apply_zero]
  split_ifs with hx1
  · subst hx1
    simp only [mul_zero]
    rw [intervalIntegral.integral_const]
    simp
  · rw [div_eq_iff hx1, mul_comm]
    exact hFTC.symm

/-! ### Continuity of the parametric integral, jointly on the meridional plane -/

private lemma continuousOn_clamped_integrand (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
        spatialPartial (fun w => u w 0) 0
          (meridional (max 0 (min p.1 1) * p.2.1) p.2.2, t))
      (Set.univ ×ˢ {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1}) := by
  have hspat := continuousOn_spatialPartial_axial u t hu ht
  have hq : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      meridional (max 0 (min p.1 1) * p.2.1) p.2.2) := by
    unfold meridional
    fun_prop
  have hmaps : Set.MapsTo (fun p : ℝ × (ℝ × ℝ) => meridional (max 0 (min p.1 1) * p.2.1) p.2.2)
      (Set.univ ×ˢ {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1}) (vec3Ball (0 : Vec3) 1) := by
    rintro ⟨s, y⟩ ⟨-, hy⟩
    exact meridional_scale_mem_vec3Ball hy (abs_clamp_le_one s)
  exact hspat.comp' hq.continuousOn hmaps

private lemma continuousOn_integral_spatialPartial (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun y : ℝ × ℝ =>
        ∫ s in (0:ℝ)..1, spatialPartial (fun w => u w 0) 0 (meridional (s * y.1) y.2, t))
      {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1} := by
  have hopen : IsOpen {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hGc : ContDiffOn ℝ (0 : ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => spatialPartial (fun w => u w 0) 0
        (meridional (max 0 (min p.1 1) * p.2.1) p.2.2, t))
      (Set.univ ×ˢ {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1}) :=
    contDiffOn_zero.2 (continuousOn_clamped_integrand u t hu ht)
  have hCont := contDiffOn_zero.1
    (contDiffOn_parametric_intervalIntegral hopen (show (0:ℝ) ≤ 1 by norm_num) (0 : ℕ∞) hGc)
  refine hCont.congr fun y _ => ?_
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hs
  simp only [clamp_eq_self hs]

/-! ### Continuity of the radial quotient across the axis -/

/-- On a time slice of the unit cylinder, `radialQuotient` (the manuscript's `u_r/r`,
extended across the axis as in the paragraph after `eq:aniso:G`) is continuous on the whole
open disk of the meridional plane `{x₂ = 0}`, including the axis point `x₁ = x₃ = 0`. -/
theorem continuousOn_radialQuotient_plane (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun y : ℝ × ℝ => radialQuotient u (meridional y.1 y.2, t))
      {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1} := by
  refine (continuousOn_integral_spatialPartial u t hu ht).congr fun y hy => ?_
  exact radialQuotient_eq_integral u t hu haxi ht y.1 y.2 hy

/-- The restriction of `continuousOn_radialQuotient_plane` to the radial axis `x₃ = 0`
of the meridional plane. -/
theorem continuousOn_radialQuotient_slice (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun x₁ : ℝ => radialQuotient u (meridional x₁ 0, t)) (Set.Ioo (-1 : ℝ) 1) := by
  have hplane := continuousOn_radialQuotient_plane u t hu haxi ht
  have hemb : Continuous (fun x₁ : ℝ => (x₁, (0:ℝ))) := by fun_prop
  have hmaps : Set.MapsTo (fun x₁ : ℝ => (x₁, (0:ℝ))) (Set.Ioo (-1:ℝ) 1)
      {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1} := by
    intro x₁ hx₁
    have h1 : |x₁| < 1 := abs_lt.mpr hx₁
    have h2 : x₁ ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x₁).mpr h1
    simpa using h2
  exact hplane.comp' hemb.continuousOn hmaps

end CIV
