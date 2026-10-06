/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.MeridionalSlices
public import LeanPool.CIVAxisymmetric.Identities.RadialQuotientContinuous
public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric
public import LeanPool.CIVAxisymmetric.Analysis.SegmentQuotient
public import LeanPool.CIVAxisymmetric.Zoom.MeridionalSmallnessLemmas
public import LeanPool.CIVAxisymmetric.Zoom.AnisotropicConsequences
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The axis quotient, its integral representation, and the three-term selection

This file publishes the representation of the radial quotient `u_r / r` on the meridional
plane as an average of `∂_r u_r` along the segment from the axis (the paragraph after
`eq:aniso:circulation:pde`), together with the pointwise bounds this representation gives
on that segment, and the reflection-symmetric three-term selection used when
`MeridionalSmallness` fails (the paragraph after `eq:aniso:zoom:selected`).
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Smoothness and differentiability of an axial slice, at a general component -/

private lemma contDiffOn_axial_component (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) (k : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t) k) (vec3Ball (0 : Vec3) 1) := by
  have hemb : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => ((x, t) : Vec3 × ℝ))
      (vec3Ball (0 : Vec3) 1) := (contDiff_id.prodMk contDiff_const).contDiffOn
  have hmaps : Set.MapsTo (fun x : Vec3 => ((x, t) : Vec3 × ℝ)) (vec3Ball (0 : Vec3) 1)
      unitCylinder := by
    intro x hx
    unfold unitCylinder spaceTimeSet
    exact Set.mk_mem_prod hx ht
  exact contDiffOn_pi.1 (hu.comp hemb hmaps) k

private lemma differentiableAt_axial_component (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) (k : Fin 3) {p : Vec3} (hp : p ∈ vec3Ball (0 : Vec3) 1) :
    DifferentiableAt ℝ (fun x : Vec3 => u (x, t) k) p := by
  have hcd1 : ContDiffOn ℝ (1 : ℕ∞) (fun x : Vec3 => u (x, t) k) (vec3Ball (0 : Vec3) 1) :=
    (contDiffOn_axial_component u t hu ht k).of_le (by exact_mod_cast le_top)
  exact (hcd1.differentiableOn one_ne_zero).differentiableAt
    ((isOpen_vec3Ball 0 1).mem_nhds hp)

private lemma continuousOn_spatialPartial_axial_component (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) (k i : Fin 3) :
    ContinuousOn (fun p : Vec3 => spatialPartial (fun w => u w k) i (p, t))
      (vec3Ball (0 : Vec3) 1) := by
  have hcd1 : ContDiffOn ℝ (1 : ℕ∞) (fun x : Vec3 => u (x, t) k) (vec3Ball (0 : Vec3) 1) :=
    (contDiffOn_axial_component u t hu ht k).of_le (by exact_mod_cast le_top)
  exact (hcd1.continuousOn_fderiv_of_isOpen (isOpen_vec3Ball 0 1) le_rfl).clm_apply
    continuousOn_const

private lemma contDiffOn_spatialPartial_axial_component1 (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) (k i : Fin 3) :
    ContDiffOn ℝ (1 : ℕ∞) (fun p : Vec3 => spatialPartial (fun w => u w k) i (p, t))
      (vec3Ball (0 : Vec3) 1) := by
  have hcd2 : ContDiffOn ℝ (2 : ℕ∞) (fun x : Vec3 => u (x, t) k) (vec3Ball (0 : Vec3) 1) :=
    (contDiffOn_axial_component u t hu ht k).of_le (by exact_mod_cast le_top)
  have hfd : ContDiffOn ℝ (1 : ℕ∞) (fderiv ℝ (fun x : Vec3 => u (x, t) k)) (vec3Ball (0 : Vec3)
    1) :=
    hcd2.fderiv_of_isOpen (isOpen_vec3Ball 0 1) (by norm_num)
  exact hfd.clm_apply contDiffOn_const

private lemma differentiableAt_spatialPartial_axial_component (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) (k i : Fin 3) {p : Vec3} (hp : p ∈ vec3Ball (0 : Vec3) 1) :
    DifferentiableAt ℝ (fun x : Vec3 => spatialPartial (fun w => u w k) i (x, t)) p :=
  ((contDiffOn_spatialPartial_axial_component1 u t hu ht k i).differentiableOn
    one_ne_zero).differentiableAt
    ((isOpen_vec3Ball 0 1).mem_nhds hp)

/-! ### The meridional segment through the axis -/

private lemma hasDerivAt_meridional_shift (x₃ s : ℝ) :
    HasDerivAt (fun a : ℝ => meridional a x₃) (basisVec 0 : Vec3) s := by
  have heq : (fun a : ℝ => meridional a x₃)
      = fun a : ℝ => a • (basisVec 0 : Vec3) + x₃ • basisVec 2 := by
    funext a; rw [meridional_eq]
  rw [heq]
  simpa using (hasDerivAt_id s).smul_const (basisVec 0 : Vec3) |>.add_const (x₃ • basisVec 2)

/-! ### The integral representation of the radial quotient -/

/-- The manuscript's `u_r/r`, extended across the axis, is the average of the radial
derivative `∂_r u_r` along the segment from the axis to `(x₁, x₃)` (the paragraph after
`eq:aniso:circulation:pde`). Public form of the `radialQuotient_eq_integral`. -/
theorem radialQuotient_eq_integral (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0)
    (x₁ x₃ : ℝ) (hx : x₁ ^ 2 + x₃ ^ 2 < 1) :
    radialQuotient u (meridional x₁ x₃, t) =
      ∫ s in (0 : ℝ)..1, spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t) := by
  have hx3 : |x₃| < 1 := (sq_lt_one_iff_abs_lt_one x₃).mp (by nlinarith only [hx, sq_nonneg x₁])
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => u (meridional (s * x₁) x₃, t) 0)
        (x₁ * spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t)) s := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith only [hs.1], hs.2⟩
    have hmem : meridional (s * x₁) x₃ ∈ vec3Ball (0 : Vec3) 1 :=
      meridional_scale_mem_vec3Ball hx hs1
    have hdiff := differentiableAt_axial_component u t hu ht 0 hmem
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_meridional_scale x₁ x₃ s)
    rw [show (fderiv ℝ (fun x : Vec3 => u (x, t) 0) (meridional (s * x₁) x₃))
        (x₁ • basisVec 0) =
        x₁ * spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t) from by
      rw [map_smul, smul_eq_mul]; rfl] at hcomp
    exact hcomp
  have hint : IntervalIntegrable
      (fun s => x₁ * spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t))
      MeasureTheory.volume 0 1 := by
    have hcont := continuousOn_spatialPartial_axial_component u t hu ht 0 0
    have hpath : Continuous (fun s : ℝ => meridional (s * x₁) x₃) := by
      unfold meridional; fun_prop
    have hmaps : Set.MapsTo (fun s : ℝ => meridional (s * x₁) x₃) (Set.uIcc (0 : ℝ) 1)
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

/-! ### Bound 1: the radial quotient on a segment through the axis -/

/-- `|u_r/r| ≤ M` at `(x₁, x₃)` whenever `|∂_r u_r| ≤ M` along the segment
`{(s x₁, x₃) : s ∈ [0, 1]}` from the axis, via the integral representation
`radialQuotient_eq_integral` (the paragraph after `eq:aniso:circulation:pde`). -/
theorem abs_radialQuotient_le_of_segment_bound (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0)
    (x₁ x₃ M : ℝ) (hx : x₁ ^ 2 + x₃ ^ 2 < 1)
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t)| ≤ M) :
    |radialQuotient u (meridional x₁ x₃, t)| ≤ M := by
  rw [radialQuotient_eq_integral u t hu haxi ht x₁ x₃ hx]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M)
    (f := fun s => spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t))
    (fun s hs => by
      rw [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
      simpa [Real.norm_eq_abs] using hM s ⟨hs.1.le, hs.2⟩)
  simpa [Real.norm_eq_abs] using hbound

/-! ### Second partial derivatives along the meridional segment -/

private lemma sq_le_of_mem_uIcc_zero {x₁ s : ℝ} (hs : s ∈ Set.uIcc (0 : ℝ) x₁) :
    s ^ 2 ≤ x₁ ^ 2 := by
  rcases le_total (0 : ℝ) x₁ with h | h
  · rw [Set.uIcc_of_le h] at hs
    nlinarith only [hs.1, hs.2]
  · rw [Set.uIcc_of_ge h] at hs
    nlinarith only [hs.1, hs.2]

private lemma meridional_shift_mem_vec3Ball {x₁ x₃ s : ℝ} (hx : x₁ ^ 2 + x₃ ^ 2 < 1)
    (hs : s ∈ Set.uIcc (0 : ℝ) x₁) : meridional s x₃ ∈ vec3Ball (0 : Vec3) 1 := by
  have hs2 := sq_le_of_mem_uIcc_zero hs
  rw [mem_vec3Ball, sub_zero]
  unfold vec3EuclideanNorm
  simp only [meridional, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Matrix.cons_val]
  have hpos : (0 : ℝ) ≤ s ^ 2 + x₃ ^ 2 := by positivity
  rw [Real.sqrt_lt hpos (by norm_num)]
  nlinarith only [hs2, hx]

private lemma hasDerivAt_second_partial_segment (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) (k i : Fin 3) (x₃ s : ℝ)
    (hmem : meridional s x₃ ∈ vec3Ball (0 : Vec3) 1) :
    HasDerivAt (fun a : ℝ => spatialPartial (fun w => u w k) i (meridional a x₃, t))
      (spatialSecondPartial (fun w => u w k) i 0 (meridional s x₃, t)) s := by
  have hdiff := differentiableAt_spatialPartial_axial_component u t hu ht k i hmem
  exact hdiff.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_meridional_shift x₃ s)

/-! ### Bound 2: `∂_z u_r / x₁` on a segment through the axis -/

/-- `|∂_z u_r / x₁| ≤ M` at `(x₁, x₃)` with `x₁ ≠ 0` whenever `|∂_r ∂_z u_r| ≤ M` along the
segment from the axis, since `∂_z u_r` vanishes on the axis (`spatialPartial_two_zero_axis`). -/
theorem abs_spatialPartial_two_zero_div_le_of_segment_bound (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0)
    (x₁ x₃ M : ℝ) (hx : x₁ ^ 2 + x₃ ^ 2 < 1) (hx1 : x₁ ≠ 0)
    (hM : ∀ a ∈ Set.uIcc (0 : ℝ) x₁,
      |spatialSecondPartial (fun w => u w 0) 2 0 (meridional a x₃, t)| ≤ M) :
    |spatialPartial (fun w => u w 0) 2 (meridional x₁ x₃, t) / x₁| ≤ M := by
  have hu1 : ContDiffOn ℝ (1 : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  have hmem0 : ((meridional 0 x₃, t) : ParabolicPoint) ∈ unitCylinder :=
    ⟨meridional_shift_mem_vec3Ball hx Set.left_mem_uIcc, ht⟩
  have hg0 : spatialPartial (fun w => u w 0) 2 (meridional (0 : ℝ) x₃, t) = 0 :=
    spatialPartial_two_zero_axis haxi hu1 hmem0 (meridional_apply_zero 0 x₃) (by simp [meridional])
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) x₁,
      DifferentiableAt ℝ (fun a : ℝ => spatialPartial (fun w => u w 0) 2 (meridional a x₃, t)) s :=
    fun s hs => (hasDerivAt_second_partial_segment u t hu ht 0 2 x₃ s
      (meridional_shift_mem_vec3Ball hx hs)).differentiableAt
  have hMd : ∀ s ∈ Set.uIcc (0 : ℝ) x₁,
      |deriv (fun a : ℝ => spatialPartial (fun w => u w 0) 2 (meridional a x₃, t)) s| ≤ M :=
    fun s hs => by
      rw [(hasDerivAt_second_partial_segment u t hu ht 0 2 x₃ s
        (meridional_shift_mem_vec3Ball hx hs)).deriv]
      exact hM s hs
  exact abs_div_le_of_deriv_bound hg0 hd hMd hx1

/-! ### Bound 3: `∂_r u_z / x₁` on a segment through the axis -/

/-- `|∂_r u_z / x₁| ≤ M` at `(x₁, x₃)` with `x₁ ≠ 0` whenever `|∂_r ∂_r u_z| ≤ M` along the
segment from the axis, since `∂_r u_z` vanishes on the axis (`spatialPartial_zero_two_axis`). -/
theorem abs_spatialPartial_zero_two_div_le_of_segment_bound (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0)
    (x₁ x₃ M : ℝ) (hx : x₁ ^ 2 + x₃ ^ 2 < 1) (hx1 : x₁ ≠ 0)
    (hM : ∀ a ∈ Set.uIcc (0 : ℝ) x₁,
      |spatialSecondPartial (fun w => u w 2) 0 0 (meridional a x₃, t)| ≤ M) :
    |spatialPartial (fun w => u w 2) 0 (meridional x₁ x₃, t) / x₁| ≤ M := by
  have hu1 : ContDiffOn ℝ (1 : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  have hmem0 : ((meridional 0 x₃, t) : ParabolicPoint) ∈ unitCylinder :=
    ⟨meridional_shift_mem_vec3Ball hx Set.left_mem_uIcc, ht⟩
  have hg0 : spatialPartial (fun w => u w 2) 0 (meridional (0 : ℝ) x₃, t) = 0 :=
    spatialPartial_zero_two_axis haxi hu1 hmem0 (meridional_apply_zero 0 x₃) (by simp [meridional])
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) x₁,
      DifferentiableAt ℝ (fun a : ℝ => spatialPartial (fun w => u w 2) 0 (meridional a x₃, t)) s :=
    fun s hs => (hasDerivAt_second_partial_segment u t hu ht 2 0 x₃ s
      (meridional_shift_mem_vec3Ball hx hs)).differentiableAt
  have hMd : ∀ s ∈ Set.uIcc (0 : ℝ) x₁,
      |deriv (fun a : ℝ => spatialPartial (fun w => u w 2) 0 (meridional a x₃, t)) s| ≤ M :=
    fun s hs => by
      rw [(hasDerivAt_second_partial_segment u t hu ht 2 0 x₃ s
        (meridional_shift_mem_vec3Ball hx hs)).deriv]
      exact hM s hs
  exact abs_div_le_of_deriv_bound hg0 hd hMd hx1

/-! ### Parity of the derivative fields under the meridional reflection -/

private lemma spatialPartial_zero_zero_reflect {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu1 : ContDiffOn ℝ (1 : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {x₁ x₃ t : ℝ} (hz : ((meridional x₁ x₃ : Vec3), t) ∈ unitCylinder) :
    spatialPartial (fun w => u w 0) 0 (meridional (-x₁) x₃, t)
      = spatialPartial (fun w => u w 0) 0 (meridional x₁ x₃, t) := by
  let z : ParabolicPoint := (meridional x₁ x₃, t)
  have hz1 : z.1 = meridional x₁ x₃ := rfl
  have hz2 : z.2 = t := rfl
  have hz' : ((meridional (-x₁) x₃ : Vec3), t) ∈ unitCylinder := by
    have h := rotZ_mem_unitCylinder Real.pi hz
    rw [hz1] at h
    rwa [rotZ_pi_meridional] at h
  have hkey := fderiv_comp_rotZ haxi hu1 hz Real.pi (basisVec 0)
  rw [hz1, hz2, rotZ_pi_meridional, rotZ_pi_basisVec_zero, map_neg] at hkey
  have hcomp := congrFun hkey 0
  rw [Pi.neg_apply, rotZ_apply_zero, Real.cos_pi, Real.sin_pi] at hcomp
  rw [spatialPartial_eq_fderiv_apply hu1 hz' 0 0, spatialPartial_eq_fderiv_apply hu1 hz 0 0]
  linarith only [hcomp]

private lemma spatialPartial_two_two_reflect {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu1 : ContDiffOn ℝ (1 : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {x₁ x₃ t : ℝ} (hz : ((meridional x₁ x₃ : Vec3), t) ∈ unitCylinder) :
    spatialPartial (fun w => u w 2) 2 (meridional (-x₁) x₃, t)
      = spatialPartial (fun w => u w 2) 2 (meridional x₁ x₃, t) := by
  let z : ParabolicPoint := (meridional x₁ x₃, t)
  have hz1 : z.1 = meridional x₁ x₃ := rfl
  have hz2 : z.2 = t := rfl
  have hz' : ((meridional (-x₁) x₃ : Vec3), t) ∈ unitCylinder := by
    have h := rotZ_mem_unitCylinder Real.pi hz
    rw [hz1] at h
    rwa [rotZ_pi_meridional] at h
  have hkey := fderiv_comp_rotZ haxi hu1 hz Real.pi (basisVec 2)
  rw [hz1, hz2, rotZ_pi_meridional, rotZ_pi_basisVec_two] at hkey
  have hcomp := congrFun hkey 2
  rw [rotZ_apply_two] at hcomp
  rw [spatialPartial_eq_fderiv_apply hu1 hz' 2 2, spatialPartial_eq_fderiv_apply hu1 hz 2 2]
  exact hcomp

private lemma spatialPartial_zero_two_reflect {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu1 : ContDiffOn ℝ (1 : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {x₁ x₃ t : ℝ} (hz : ((meridional x₁ x₃ : Vec3), t) ∈ unitCylinder) :
    spatialPartial (fun w => u w 0) 2 (meridional (-x₁) x₃, t)
      = -spatialPartial (fun w => u w 0) 2 (meridional x₁ x₃, t) := by
  let z : ParabolicPoint := (meridional x₁ x₃, t)
  have hz1 : z.1 = meridional x₁ x₃ := rfl
  have hz2 : z.2 = t := rfl
  have hz' : ((meridional (-x₁) x₃ : Vec3), t) ∈ unitCylinder := by
    have h := rotZ_mem_unitCylinder Real.pi hz
    rw [hz1] at h
    rwa [rotZ_pi_meridional] at h
  have hkey := fderiv_comp_rotZ haxi hu1 hz Real.pi (basisVec 2)
  rw [hz1, hz2, rotZ_pi_meridional, rotZ_pi_basisVec_two] at hkey
  have hcomp := congrFun hkey 0
  rw [rotZ_apply_zero, Real.cos_pi, Real.sin_pi] at hcomp
  rw [spatialPartial_eq_fderiv_apply hu1 hz' 0 2, spatialPartial_eq_fderiv_apply hu1 hz 0 2]
  linarith only [hcomp]

private lemma radialQuotient_reflect {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    {x₁ x₃ t : ℝ} (hz : ((meridional x₁ x₃ : Vec3), t) ∈ unitCylinder) :
    radialQuotient u (meridional (-x₁) x₃, t) = radialQuotient u (meridional x₁ x₃, t) := by
  by_cases hx1 : x₁ = 0
  · subst hx1; simp
  · have h1 : (meridional (-x₁) x₃ : Vec3) 0 = -x₁ := by simp [meridional]
    have h2 : (meridional x₁ x₃ : Vec3) 0 = x₁ := by simp [meridional]
    simp only [radialQuotient, h1, h2]
    rw [apply_meridional_reflect_zero haxi hz]
    split_ifs with h1'
    · exact absurd h1' (neg_ne_zero.mpr hx1)
    · rw [div_neg, neg_div, neg_neg]

/-- Each summand of `meridionalQuantity` is invariant under the reflection `x₁ ↦ -x₁` of the
meridional plane, so the quantity itself is even: `∂_r u_r` and `∂_z u_z` are even, `u_r/r` is
even, and `∂_z u_r` is odd (so `|∂_z u_r|` is even). -/
theorem meridionalQuantity_reflect {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu1 : ContDiffOn ℝ (1 : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {x₁ x₃ t : ℝ} (hz : ((meridional x₁ x₃ : Vec3), t) ∈ unitCylinder) :
    meridionalQuantity u (meridional (-x₁) x₃, t) = meridionalQuantity u (meridional x₁ x₃, t) := by
  unfold meridionalQuantity
  rw [spatialPartial_zero_zero_reflect haxi hu1 hz, radialQuotient_reflect haxi hz,
    spatialPartial_two_two_reflect haxi hu1 hz, spatialPartial_zero_two_reflect haxi hu1 hz,
    abs_neg]

/-! ### `(-t)^h → 0` for a general positive exponent -/

/-- `(-t)^h → 0` as `t ↑ 0`, for any positive real exponent `h`. Unlike
`tendsto_zoom_lengths`, whose exponents are the fixed `1/2`, `2h` and `1 - 2h`, this holds
for an arbitrary positive `h`. -/
theorem tendsto_neg_rpow_nhdsWithin_zero {h : ℝ} (hh : 0 < h) :
    Filter.Tendsto (fun t : ℝ => (-t) ^ h) (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds 0) := by
  have h_cont : ContinuousAt (fun x : ℝ => x ^ h) 0 :=
    Real.continuousAt_rpow_const (x := 0) (q := h) (Or.inr hh.le)
  have h_neg_tendsto : Filter.Tendsto (fun t : ℝ => -t) (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds 0)
    := by
    have hc : Filter.Tendsto (fun t : ℝ => -t) (nhds (0 : ℝ)) (nhds 0) := by
      have := (continuous_neg (G := ℝ)).continuousAt (x := 0)
      simpa using this.tendsto
    exact hc.mono_left nhdsWithin_le_nhds
  have h_rpow_tendsto : Filter.Tendsto (fun x : ℝ => x ^ h) (nhds (0 : ℝ)) (nhds ((0 : ℝ) ^ h)) :=
    h_cont.tendsto
  have h_zero : (0 : ℝ) ^ h = 0 := Real.zero_rpow (ne_of_gt hh)
  have h_rpow_tendsto0 : Filter.Tendsto (fun x : ℝ => x ^ h) (nhds (0 : ℝ)) (nhds 0) := by
    simpa [h_zero] using h_rpow_tendsto
  exact h_rpow_tendsto0.comp h_neg_tendsto

/-! ### Membership helpers for the reflection -/

private lemma meridional_abs_mem_vec3Ball {ρ x₁ x₃ : ℝ}
    (hmem : meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ) :
    meridional |x₁| x₃ ∈ vec3Ball (0 : Vec3) ρ := by
  rw [mem_vec3Ball, sub_zero] at hmem ⊢
  unfold vec3EuclideanNorm at hmem ⊢
  simpa [meridional, Fin.sum_univ_three, sq_abs] using hmem

private lemma vec3Ball_subset_of_le {ρ : ℝ} (hρ : ρ ≤ 1) :
    vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1 := by
  intro x hx
  rw [mem_vec3Ball] at hx ⊢
  linarith only [hx, hρ]

/-! ### The three-term selection from a failure of meridional smallness -/

/-- If `MeridionalSmallness ρ u` fails, the first three terms of `meridionalQuantity`
alone — dropping `|∂_z u_r|`, which the anisotropic Type II bounds force to zero after
multiplication by `-t` — still exceed a fixed positive constant along a sequence approaching
the singular time, with the radial coordinate taken nonnegative by the reflection symmetry of
the meridional plane. The selected points lie in `vec3Ball 0 ρ` and the selected times in
`Ioo (-1) 0`, the times increase strictly to the singular time, and the inequality holds at
every index: the tail on which it holds is reindexed from the start. This is the selection
used after `eq:aniso:zoom:selected`. -/
theorem exists_seq_three_terms {ρ h C : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hb : AnisotropicBounds C h u) (hh : 0 < h)
    (hρ : ρ ≤ 1) (hnot : ¬ MeridionalSmallness ρ u) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ t x₁ x₃ : ℕ → ℝ, (∀ n, 0 ≤ x₁ n) ∧ StrictMono t ∧
      Filter.Tendsto t Filter.atTop (nhds 0) ∧
      (∀ n, meridional (x₁ n) (x₃ n) ∈ vec3Ball (0 : Vec3) ρ) ∧
      (∀ n, t n ∈ Set.Ioo (-1 : ℝ) 0) ∧
      ∀ n, c₀ < (-(t n)) *
        (|spatialPartial (fun w => u w 0) 0 (meridional (x₁ n) (x₃ n), t n)| +
          |radialQuotient u (meridional (x₁ n) (x₃ n), t n)| +
          |spatialPartial (fun w => u w 2) 2 (meridional (x₁ n) (x₃ n), t n)|) := by
  have hu1 : ContDiffOn ℝ (1 : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  obtain ⟨c₀, hc₀, t, x₁, x₃, ht_mono, ht_mem, ht_tendsto, hseq⟩ :=
    exists_seq_of_not_meridionalSmallness hnot
  have hz : ∀ n, ((meridional (|x₁ n|) (x₃ n) : Vec3), t n) ∈ unitCylinder := by
    intro n
    exact ⟨vec3Ball_subset_of_le hρ (meridional_abs_mem_vec3Ball (hseq n).1), ht_mem n⟩
  have hQ : ∀ n, meridionalQuantity u (meridional (|x₁ n|) (x₃ n), t n)
      = meridionalQuantity u (meridional (x₁ n) (x₃ n), t n) := by
    intro n
    rcases le_total (0 : ℝ) (x₁ n) with hpos | hneg
    · rw [abs_of_nonneg hpos]
    · rw [abs_of_nonpos hneg]
      have hz0 : ((meridional (-(x₁ n)) (x₃ n) : Vec3), t n) ∈ unitCylinder := by
        have := hz n
        rwa [abs_of_nonpos hneg] at this
      have hrefl := meridionalQuantity_reflect haxi hu1 (x₁ := -(x₁ n)) (x₃ := x₃ n) (t := t n) hz0
      rw [neg_neg] at hrefl
      exact hrefl.symm
  have hbound : ∀ n, (-(t n)) *
      |spatialPartial (fun w => u w 0) 2 (meridional (|x₁ n|) (x₃ n), t n)|
      ≤ C * (-(t n)) ^ h := fun n => neg_t_mul_abs_dz_ur_le hb (hz n)
  have hlow : ∀ n, c₀ - C * (-(t n)) ^ h < (-(t n)) *
      (|spatialPartial (fun w => u w 0) 0 (meridional (|x₁ n|) (x₃ n), t n)| +
        |radialQuotient u (meridional (|x₁ n|) (x₃ n), t n)| +
        |spatialPartial (fun w => u w 2) 2 (meridional (|x₁ n|) (x₃ n), t n)|) := by
    intro n
    have hineq' : c₀ < (-(t n)) * meridionalQuantity u (meridional (|x₁ n|) (x₃ n), t n) := by
      rw [hQ n]; exact (hseq n).2
    unfold meridionalQuantity at hineq'
    have hb' := hbound n
    nlinarith only [hineq', hb']
  have ht_within : Filter.Tendsto t Filter.atTop (nhdsWithin (0 : ℝ) (Set.Iio 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within t ht_tendsto
      (Filter.Eventually.of_forall (fun n => (ht_mem n).2))
  have h_rpow_tendsto : Filter.Tendsto (fun n => C * (-(t n)) ^ h) Filter.atTop (nhds 0) := by
    have hcomp := (tendsto_neg_rpow_nhdsWithin_zero hh).comp ht_within
    have hC0 : Filter.Tendsto (fun n : ℕ => C * (-(t n)) ^ h) Filter.atTop (nhds (C * 0)) :=
      hcomp.const_mul C
    simpa using hC0
  have hc₀half : (0 : ℝ) < c₀ / 2 := by linarith only [hc₀]
  have hevent := h_rpow_tendsto.eventually_lt_const hc₀half
  have hfinal : ∀ᶠ n in Filter.atTop, c₀ / 2 < (-(t n)) *
      (|spatialPartial (fun w => u w 0) 0 (meridional (|x₁ n|) (x₃ n), t n)| +
        |radialQuotient u (meridional (|x₁ n|) (x₃ n), t n)| +
        |spatialPartial (fun w => u w 2) 2 (meridional (|x₁ n|) (x₃ n), t n)|) := by
    refine hevent.mono (fun n hn => ?_)
    have hln := hlow n
    linarith only [hln, hn]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hfinal
  refine ⟨c₀ / 2, hc₀half, fun n => t (n + N), fun n => |x₁ (n + N)|, fun n => x₃ (n + N),
    fun n => abs_nonneg _, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a b hab => ht_mono (by omega)
  · exact ht_tendsto.comp (Filter.tendsto_add_atTop_nat N)
  · exact fun n => meridional_abs_mem_vec3Ball (hseq (n + N)).1
  · exact fun n => ht_mem (n + N)
  · exact fun n => hN (n + N) (Nat.le_add_left N n)

end CIV
