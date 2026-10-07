/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.MeridionalSlices
public import LeanPool.CIVAxisymmetric.Identities.Vorticity
public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric
public import LeanPool.CIVAxisymmetric.Identities.RadialQuotientContinuous

/-! ### Smoothness of a spatial partial derivative -/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The azimuthal vorticity `ω_θ = ∂_z u_r - ∂_r u_z` of `eq:aniso:vorticity`. -/
@[expose] def azimuthalVorticity (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  curlComp u 1 z

/-- `Ω = ω_θ / r`, extended continuously across the axis. -/
@[expose] def potentialVorticity (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  if z.1 0 = 0 then spatialPartial (azimuthalVorticity u) 0 z else azimuthalVorticity u z / z.1 0

/-- Off the axis, the potential vorticity is the quotient `ω_θ / r`. -/
theorem potentialVorticity_eq_div (u : ParabolicPoint → Vec3) {z : ParabolicPoint}
    (hr : z.1 0 ≠ 0) : potentialVorticity u z = azimuthalVorticity u z / z.1 0 := by
  unfold potentialVorticity
  split_ifs with h
  · exact absurd h hr
  · rfl

/-- The azimuthal vorticity of a smooth axisymmetric field vanishes on the axis. -/
theorem azimuthalVorticity_axis {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (h0 : z.1 0 = 0) (h1 : z.1 1 = 0) :
    azimuthalVorticity u z = 0 := by
  unfold azimuthalVorticity
  rw [curlComp_one, spatialPartial_two_zero_axis haxi hu hz h0 h1,
    spatialPartial_zero_two_axis haxi hu hz h0 h1, sub_zero]



/-- On the open unit cylinder, a spatial partial derivative of a `C^∞` scalar field is again
`C^∞`. This is the scalar analogue of `spatialPartial_eq_fderiv_apply`: since `spatialPartial g i`
already unfolds to the value at `basisVec i` of the derivative of the spatial slice
`x ↦ g (x, z.2)`, its regularity follows from differentiating the joint smoothness of that
slice under the parameter `z`. -/
private lemma contDiffOn_spatialPartial {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial g i z) unitCylinder := by
  have hS : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Vec3 × ℝ) × Vec3 => ((p.2, p.1.2) : Vec3 × ℝ)) :=
    contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst)
  intro z₀ hz₀
  have hgAt : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => g w) z₀ :=
    hg.contDiffAt (isOpen_unitCylinder_prod.mem_nhds hz₀)
  have hf : ContDiffAt ℝ (⊤ : ℕ∞)
      (Function.uncurry (fun z : Vec3 × ℝ => fun x : Vec3 => g (x, z.2))) (z₀, z₀.1) :=
    hgAt.comp (z₀, z₀.1) hS.contDiffAt
  have hp : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => z.1) z₀ := contDiff_fst.contDiffAt
  have hderiv : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => fderiv ℝ (fun x : Vec3 => g (x, z.2)) z.1) z₀ :=
    ContDiffAt.fderiv hf hp (by simp)
  exact (hderiv.clm_apply contDiffAt_const).contDiffWithinAt

/-- The azimuthal vorticity of a smooth field is smooth on the open unit cylinder. -/
theorem contDiffOn_azimuthalVorticity {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => azimuthalVorticity u z) unitCylinder := by
  have h0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial (fun w => u w 0) 2 z)
      unitCylinder := contDiffOn_spatialPartial (contDiffOn_component hu 0) 2
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial (fun w => u w 2) 0 z)
      unitCylinder := contDiffOn_spatialPartial (contDiffOn_component hu 2) 0
  exact (h0.sub h2).congr fun z _ => rfl

/-! ### The meridional segment through the axis -/

private lemma mem_prod_of_mem_unitCylinder_meridional {x₁ x₃ t : ℝ}
    (hz : (meridional x₁ x₃, t) ∈ unitCylinder) :
    x₁ ^ 2 + x₃ ^ 2 < 1 ∧ t ∈ Set.Ioo (-1 : ℝ) 0 := by
  rw [unitCylinder, spaceTimeSet] at hz
  unfold ParabolicPoint at hz
  rw [Set.mem_prod] at hz
  obtain ⟨hball, ht⟩ := hz
  refine ⟨?_, ht⟩
  rw [mem_vec3Ball, sub_zero] at hball
  have hnorm : vec3EuclideanNorm (meridional x₁ x₃) = Real.sqrt (x₁ ^ 2 + x₃ ^ 2) := by
    unfold vec3EuclideanNorm meridional
    simp [Fin.sum_univ_three]
  rw [hnorm] at hball
  have hlt := (Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)).mp hball
  simpa using hlt

/-! ### Smoothness of the axial slice of the azimuthal vorticity -/

private lemma contDiffOn_axial_slice_azimuthalVorticity (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => azimuthalVorticity u (x, t))
      (vec3Ball (0 : Vec3) 1) := by
  have hemb : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => ((x, t) : Vec3 × ℝ))
      (vec3Ball (0 : Vec3) 1) := (contDiff_id.prodMk contDiff_const).contDiffOn
  have hmaps : Set.MapsTo (fun x : Vec3 => ((x, t) : Vec3 × ℝ)) (vec3Ball (0 : Vec3) 1)
      unitCylinder := by
    intro x hx
    unfold unitCylinder spaceTimeSet
    exact Set.mk_mem_prod hx ht
  exact (contDiffOn_azimuthalVorticity hu).comp hemb hmaps

private lemma differentiableAt_axial_slice_azimuthalVorticity (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) {p : Vec3} (hp : p ∈ vec3Ball (0 : Vec3) 1) :
    DifferentiableAt ℝ (fun x : Vec3 => azimuthalVorticity u (x, t)) p := by
  have hcd1 : ContDiffOn ℝ (1 : ℕ∞) (fun x : Vec3 => azimuthalVorticity u (x, t))
      (vec3Ball (0 : Vec3) 1) :=
    (contDiffOn_axial_slice_azimuthalVorticity u t hu ht).of_le (by exact_mod_cast le_top)
  exact (hcd1.differentiableOn one_ne_zero).differentiableAt
    ((isOpen_vec3Ball 0 1).mem_nhds hp)

private lemma continuousOn_spatialPartial_axial_azimuthalVorticity (u : ParabolicPoint → Vec3)
    (t : ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun p : Vec3 => spatialPartial (azimuthalVorticity u) 0 (p, t))
      (vec3Ball (0 : Vec3) 1) := by
  have hcd1 : ContDiffOn ℝ (1 : ℕ∞) (fun x : Vec3 => azimuthalVorticity u (x, t))
      (vec3Ball (0 : Vec3) 1) :=
    (contDiffOn_axial_slice_azimuthalVorticity u t hu ht).of_le (by exact_mod_cast le_top)
  exact (hcd1.continuousOn_fderiv_of_isOpen (isOpen_vec3Ball 0 1) le_rfl).clm_apply
    continuousOn_const

/-! ### The integral representation of the potential vorticity -/

private lemma azimuthalVorticity_eq_integral (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0)
    (x₁ x₃ : ℝ) (hx : x₁ ^ 2 + x₃ ^ 2 < 1) :
    potentialVorticity u (meridional x₁ x₃, t) =
      ∫ s in (0:ℝ)..1, spatialPartial (azimuthalVorticity u) 0 (meridional (s * x₁) x₃, t) := by
  have hx3 : |x₃| < 1 := (sq_lt_one_iff_abs_lt_one x₃).mp (by nlinarith only [hx, sq_nonneg x₁])
  have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => azimuthalVorticity u (meridional (s * x₁) x₃, t))
        (x₁ * spatialPartial (azimuthalVorticity u) 0 (meridional (s * x₁) x₃, t)) s := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith only [hs.1], hs.2⟩
    have hmem : meridional (s * x₁) x₃ ∈ vec3Ball (0 : Vec3) 1 :=
      meridional_scale_mem_vec3Ball hx hs1
    have hdiff := differentiableAt_axial_slice_azimuthalVorticity u t hu ht hmem
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_meridional_scale x₁ x₃ s)
    rw [show (fderiv ℝ (fun x : Vec3 => azimuthalVorticity u (x, t)) (meridional (s * x₁) x₃))
        (x₁ • basisVec 0) =
        x₁ * spatialPartial (azimuthalVorticity u) 0 (meridional (s * x₁) x₃, t) from by
      rw [map_smul, smul_eq_mul]; rfl] at hcomp
    exact hcomp
  have hint : IntervalIntegrable
      (fun s => x₁ * spatialPartial (azimuthalVorticity u) 0 (meridional (s * x₁) x₃, t))
      MeasureTheory.volume 0 1 := by
    have hcont := continuousOn_spatialPartial_axial_azimuthalVorticity u t hu ht
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
  have hz0 : ((meridional 0 x₃, t) : ParabolicPoint) ∈ unitCylinder :=
    mem_unitCylinder_meridional x₃ hx3 t ht
  rw [azimuthalVorticity_axis haxi (hu.of_le (by simp)) hz0 (by simp [meridional])
    (by simp [meridional]), sub_zero, intervalIntegral.integral_const_mul] at hFTC
  simp only [potentialVorticity, meridional_apply_zero]
  split_ifs with hx1
  · subst hx1
    simp only [mul_zero]
    rw [intervalIntegral.integral_const]
    simp
  · rw [div_eq_iff hx1, mul_comm]
    exact hFTC.symm

/-- Explicit mean-value bound for the potential vorticity: if the radial derivative of the
azimuthal vorticity is bounded by `M` along the segment from the axis to `(x₁, x₃)`, so is the
potential vorticity `Ω` itself at `(x₁, x₃)`. -/
theorem abs_potentialVorticity_le {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {x₁ x₃ t M : ℝ} (hz : (meridional x₁ x₃, t) ∈ unitCylinder)
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |spatialPartial (azimuthalVorticity u) 0 (meridional (s * x₁) x₃, t)| ≤ M) :
    |potentialVorticity u (meridional x₁ x₃, t)| ≤ M := by
  obtain ⟨hx, ht⟩ := mem_prod_of_mem_unitCylinder_meridional hz
  rw [azimuthalVorticity_eq_integral u t hu haxi ht x₁ x₃ hx]
  have hle : ‖∫ s in (0:ℝ)..1, spatialPartial (azimuthalVorticity u) 0
      (meridional (s * x₁) x₃, t)‖ ≤ M * |(1:ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    rw [Real.norm_eq_abs]
    exact hM s (Set.Ioc_subset_Icc_self hs)
  simpa using hle

/-! ### Continuity of the parametric integral, jointly on the meridional plane -/

private lemma continuousOn_clamped_integrand_azimuthalVorticity (u : ParabolicPoint → Vec3)
    (t : ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
        spatialPartial (azimuthalVorticity u) 0
          (meridional (max 0 (min p.1 1) * p.2.1) p.2.2, t))
      (Set.univ ×ˢ {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1}) := by
  have hspat := continuousOn_spatialPartial_axial_azimuthalVorticity u t hu ht
  have hq : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      meridional (max 0 (min p.1 1) * p.2.1) p.2.2) := by
    unfold meridional
    fun_prop
  have hmaps : Set.MapsTo (fun p : ℝ × (ℝ × ℝ) => meridional (max 0 (min p.1 1) * p.2.1) p.2.2)
      (Set.univ ×ˢ {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1}) (vec3Ball (0 : Vec3) 1) := by
    rintro ⟨s, y⟩ ⟨-, hy⟩
    exact meridional_scale_mem_vec3Ball hy (abs_clamp_le_one s)
  exact hspat.comp' hq.continuousOn hmaps

private lemma continuousOn_integral_spatialPartial_azimuthalVorticity (u : ParabolicPoint → Vec3)
    (t : ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun y : ℝ × ℝ =>
        ∫ s in (0:ℝ)..1, spatialPartial (azimuthalVorticity u) 0 (meridional (s * y.1) y.2, t))
      {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1} := by
  have hopen : IsOpen {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hGc : ContDiffOn ℝ (0 : ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => spatialPartial (azimuthalVorticity u) 0
        (meridional (max 0 (min p.1 1) * p.2.1) p.2.2, t))
      (Set.univ ×ˢ {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1}) :=
    contDiffOn_zero.2 (continuousOn_clamped_integrand_azimuthalVorticity u t hu ht)
  have hCont := contDiffOn_zero.1
    (contDiffOn_parametric_intervalIntegral hopen (show (0:ℝ) ≤ 1 by norm_num) (0 : ℕ∞) hGc)
  refine hCont.congr fun y _ => ?_
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hs
  simp only [clamp_eq_self hs]

/-- On a time slice of the unit cylinder, the potential vorticity `Ω = ω_θ / r` (the paragraph
after `eq:aniso:circulation:pde`) is continuous on the whole open disk of the meridional plane
`{x₂ = 0}`, including the axis point `x₁ = x₃ = 0`. -/
theorem continuousOn_potentialVorticity_plane (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun y : ℝ × ℝ => potentialVorticity u (meridional y.1 y.2, t))
      {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1} := by
  refine (continuousOn_integral_spatialPartial_azimuthalVorticity u t hu ht).congr fun y hy => ?_
  exact azimuthalVorticity_eq_integral u t hu haxi ht y.1 y.2 hy

end CIV
