/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.VorticityEquation

/-!
# The potential vorticity equation

`eq:aniso:q` is the equation satisfied by the potential vorticity `Ω = ω_θ / r` of an
axisymmetric classical solution. It is `eq:aniso:theta` divided by `r`: the stretching term
`(u_r / r) ω_θ` of the azimuthal vorticity equation is exactly the term produced by the
radial transport of the quotient, and the cylindrical Laplacian obeys the operator identity

`r⁻¹ (∂_r² + r⁻¹ ∂_r - r⁻²) (r Ω) = (∂_r² + 3 r⁻¹ ∂_r) Ω`,

so the first-order radial term acquires the coefficient `3`.

Away from the axis `Ω` agrees with the quotient `ω_θ / r` on a full neighbourhood, so its
classical derivatives are those of the quotient; the quotient rules below are obtained from
the product rule against the radial weight `r⁻¹`, whose only nonvanishing classical
derivative in the meridional plane is the radial one.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Derivatives of a function of the radial coordinate -/

/-- The classical spatial partial derivatives of a scalar function of the first coordinate are
read off its one-dimensional derivative. -/
private lemma spatialPartial_comp_radius {psi : ℝ → ℝ} {d : ℝ} {z : ParabolicPoint}
    (hpsi : HasDerivAt psi d (z.1 0)) (i : Fin 3) :
    spatialPartial (fun w : ParabolicPoint => psi (w.1 0)) i z = d * (basisVec i 0 : ℝ) := by
  have hproj : HasFDerivAt (fun y : Vec3 => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0) z.1 :=
    hasFDerivAt_apply (𝕜 := ℝ) 0 z.1
  have hcomp : HasFDerivAt (fun y : Vec3 => psi (y 0))
      (d • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0) z.1 :=
    hpsi.comp_hasFDerivAt z.1 hproj
  show fderiv ℝ (fun y : Vec3 => psi (y 0)) z.1 (basisVec i) = _
  rw [hcomp.fderiv]
  simp [ContinuousLinearMap.proj_apply]

/-- A scalar function of the first coordinate is differentiable wherever it is. -/
private lemma differentiableAt_comp_radius {psi : ℝ → ℝ} {d : ℝ} {x : Vec3}
    (hpsi : HasDerivAt psi d (x 0)) :
    DifferentiableAt ℝ (fun y : Vec3 => psi (y 0)) x := by
  have hproj : HasFDerivAt (fun y : Vec3 => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0) x :=
    hasFDerivAt_apply (𝕜 := ℝ) 0 x
  have hcomp : HasFDerivAt (fun y : Vec3 => psi (y 0))
      (d • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0) x :=
    hpsi.comp_hasFDerivAt x hproj
  exact hcomp.differentiableAt

/-- The radial weight `r⁻¹` is differentiable off the axis. -/
private lemma differentiableAt_invRadius {x : Vec3} (hx : x 0 ≠ 0) :
    DifferentiableAt ℝ (fun y : Vec3 => (y 0)⁻¹) x :=
  differentiableAt_comp_radius (hasDerivAt_inv hx)

/-- The radial derivative of the weight `r⁻¹` is `-r⁻²`. -/
private lemma spatialPartial_invRadius_zero {z : ParabolicPoint} (hr : z.1 0 ≠ 0) :
    spatialPartial (fun w : ParabolicPoint => (w.1 0)⁻¹) 0 z = -((z.1 0)⁻¹) ^ 2 := by
  rw [spatialPartial_comp_radius (psi := fun r : ℝ => r⁻¹) (hasDerivAt_inv hr) 0, basisVec_apply]
  norm_num

/-- The vertical derivative of the weight `r⁻¹` vanishes. -/
private lemma spatialPartial_invRadius_two {z : ParabolicPoint} (hr : z.1 0 ≠ 0) :
    spatialPartial (fun w : ParabolicPoint => (w.1 0)⁻¹) 2 z = 0 := by
  rw [spatialPartial_comp_radius (psi := fun r : ℝ => r⁻¹) (hasDerivAt_inv hr) 2, basisVec_apply]
  norm_num

/-! ### Classical derivatives see only the off-axis branch -/

/-- Two scalars agreeing on the part of the unit cylinder off the axis have the same spatial
partial derivatives there. -/
private lemma spatialPartial_congr_offAxis {g h : ParabolicPoint → ℝ}
    (heq : ∀ w : ParabolicPoint, w ∈ unitCylinder → w.1 0 ≠ 0 → g w = h w)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (hr : z.1 0 ≠ 0) (i : Fin 3) :
    spatialPartial g i z = spatialPartial h i z := by
  have hopen : IsOpen (vec3Ball (0 : Vec3) 1 ∩ {y : Vec3 | y 0 ≠ 0}) :=
    (isOpen_vec3Ball 0 1).inter (isOpen_ne.preimage (continuous_apply 0))
  have hev : (fun y : Vec3 => g (y, z.2)) =ᶠ[nhds z.1] fun y : Vec3 => h (y, z.2) := by
    filter_upwards [hopen.mem_nhds (show z.1 ∈ vec3Ball (0 : Vec3) 1 ∩ {y : Vec3 | y 0 ≠ 0} from
      ⟨hz.1, hr⟩)] with y hy
    exact heq (y, z.2) ⟨hy.1, hz.2⟩ hy.2
  show fderiv ℝ (fun y : Vec3 => g (y, z.2)) z.1 (basisVec i)
    = fderiv ℝ (fun y : Vec3 => h (y, z.2)) z.1 (basisVec i)
  rw [hev.fderiv_eq]

/-- Two scalars agreeing on the part of the unit cylinder off the axis have the same second
spatial partial derivatives there. -/
private lemma spatialSecondPartial_congr_offAxis {g h : ParabolicPoint → ℝ}
    (heq : ∀ w : ParabolicPoint, w ∈ unitCylinder → w.1 0 ≠ 0 → g w = h w)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (hr : z.1 0 ≠ 0) (i j : Fin 3) :
    spatialSecondPartial g i j z = spatialSecondPartial h i j z := by
  show spatialPartial (fun w : ParabolicPoint => spatialPartial g i w) j z
    = spatialPartial (fun w : ParabolicPoint => spatialPartial h i w) j z
  exact spatialPartial_congr_offAxis
    (fun w hw hwr => spatialPartial_congr_offAxis heq hw hwr i) hz hr j

/-- Two scalars agreeing off the axis have the same time derivative there. -/
private lemma timePartial_congr_offAxis {g h : ParabolicPoint → ℝ}
    (heq : ∀ w : ParabolicPoint, w.1 0 ≠ 0 → g w = h w)
    {z : ParabolicPoint} (hr : z.1 0 ≠ 0) :
    timePartial g z = timePartial h z := by
  have hfun : (fun s : ℝ => g (z.1, s)) = fun s : ℝ => h (z.1, s) :=
    funext fun s => heq (z.1, s) hr
  show fderiv ℝ (fun s : ℝ => g (z.1, s)) z.2 1 = fderiv ℝ (fun s : ℝ => h (z.1, s)) z.2 1
  rw [hfun]

/-- The time slice of a jointly smooth scalar field is differentiable on the cylinder. -/
private lemma differentiableAt_timeSliceScalar {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    DifferentiableAt ℝ (fun s : ℝ => g (z.1, s)) z.2 := by
  have hjoint : DifferentiableAt ℝ (fun w : Vec3 × ℝ => g w) z :=
    (hg.differentiableOn (by norm_num) z hz).differentiableAt
      (isOpen_unitCylinder_prod.mem_nhds hz)
  exact hjoint.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2).differentiableAt

/-! ### The quotient rules for the radial weight -/

/-- Radial derivative of the radial quotient `a / r`. -/
private lemma spatialPartial_radQuot_zero {a : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hda : DifferentiableAt ℝ (fun y : Vec3 => a (y, z.2)) z.1) (hr : z.1 0 ≠ 0) :
    spatialPartial (fun v : ParabolicPoint => a v * (v.1 0)⁻¹) 0 z
      = (spatialPartial a 0 z - a z * (z.1 0)⁻¹) * (z.1 0)⁻¹ := by
  rw [spatialPartial_mul_of_differentiableAt (g := a)
      (h := fun v : ParabolicPoint => (v.1 0)⁻¹) (i := 0) hda (differentiableAt_invRadius hr),
    spatialPartial_invRadius_zero hr]
  ring

/-- Vertical derivative of the radial quotient `a / r`. -/
private lemma spatialPartial_radQuot_two {a : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hda : DifferentiableAt ℝ (fun y : Vec3 => a (y, z.2)) z.1) (hr : z.1 0 ≠ 0) :
    spatialPartial (fun v : ParabolicPoint => a v * (v.1 0)⁻¹) 2 z
      = spatialPartial a 2 z * (z.1 0)⁻¹ := by
  rw [spatialPartial_mul_of_differentiableAt (g := a)
      (h := fun v : ParabolicPoint => (v.1 0)⁻¹) (i := 2) hda (differentiableAt_invRadius hr),
    spatialPartial_invRadius_two hr]
  ring

/-- Time derivative of the radial quotient `a / r`; the radius does not depend on time. -/
private lemma timePartial_radQuot {a : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hda : DifferentiableAt ℝ (fun s : ℝ => a (z.1, s)) z.2) :
    timePartial (fun v : ParabolicPoint => a v * (v.1 0)⁻¹) z
      = timePartial a z * (z.1 0)⁻¹ := by
  have hfun : (fun v : ParabolicPoint => a v * (v.1 0)⁻¹)
      = fun v : ParabolicPoint => (fun y : Vec3 => (y 0)⁻¹) v.1 * a v := by
    funext v
    exact mul_comm _ _
  rw [hfun, timePartial_space_weight_mul (fun y : Vec3 => (y 0)⁻¹) hda]
  ring

/-- Second radial derivative of the radial quotient `a / r`. -/
private lemma spatialSecondPartial_radQuot_zero {a : ParabolicPoint → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => a w) unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (hr : z.1 0 ≠ 0) :
    spatialSecondPartial (fun v : ParabolicPoint => a v * (v.1 0)⁻¹) 0 0 z
      = spatialSecondPartial a 0 0 z * (z.1 0)⁻¹
        - 2 * ((spatialPartial a 0 z - a z * (z.1 0)⁻¹) * ((z.1 0)⁻¹) ^ 2) := by
  have ha1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => a w) unitCylinder := ha.of_le (by norm_num)
  have ha0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial a 0 w) unitCylinder :=
    contDiffOn_spatialPartial ha 0
  have ha01 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => spatialPartial a 0 w) unitCylinder :=
    ha0.of_le (by norm_num)
  have hinner : ∀ w : ParabolicPoint, w ∈ unitCylinder → w.1 0 ≠ 0 →
      spatialPartial (fun v : ParabolicPoint => a v * (v.1 0)⁻¹) 0 w
        = (spatialPartial a 0 w - a w * (w.1 0)⁻¹) * (w.1 0)⁻¹ :=
    fun w hw hwr => spatialPartial_radQuot_zero (differentiableAt_spatialSlice ha1 hw) hwr
  have hstep : spatialSecondPartial (fun v : ParabolicPoint => a v * (v.1 0)⁻¹) 0 0 z
      = spatialPartial (fun w : ParabolicPoint =>
          (spatialPartial a 0 w - a w * (w.1 0)⁻¹) * (w.1 0)⁻¹) 0 z := by
    show spatialPartial
        (fun w : ParabolicPoint => spatialPartial (fun v : ParabolicPoint => a v * (v.1 0)⁻¹) 0 w)
        0 z = _
    exact spatialPartial_congr_offAxis hinner hz hr 0
  have hda : DifferentiableAt ℝ (fun y : Vec3 => a (y, z.2)) z.1 :=
    differentiableAt_spatialSlice ha1 hz
  have hda0 : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial a 0 (y, z.2)) z.1 :=
    differentiableAt_spatialSlice ha01 hz
  have hdinv : DifferentiableAt ℝ (fun y : Vec3 => (y 0)⁻¹) z.1 := differentiableAt_invRadius hr
  have hdc : DifferentiableAt ℝ
      (fun y : Vec3 => spatialPartial a 0 (y, z.2) - a (y, z.2) * (y 0)⁻¹) z.1 :=
    hda0.sub (hda.mul hdinv)
  rw [hstep, spatialPartial_mul_of_differentiableAt
      (g := fun w : ParabolicPoint => spatialPartial a 0 w - a w * (w.1 0)⁻¹)
      (h := fun v : ParabolicPoint => (v.1 0)⁻¹) (i := 0) hdc hdinv,
    spatialPartial_invRadius_zero hr,
    spatialPartial_sub_of_differentiableAt
      (g := fun w : ParabolicPoint => spatialPartial a 0 w)
      (h := fun v : ParabolicPoint => a v * (v.1 0)⁻¹) (i := 0) hda0 (hda.mul hdinv),
    spatialPartial_radQuot_zero hda hr]
  simp only [spatialSecondPartial]
  ring

/-- Second vertical derivative of the radial quotient `a / r`. -/
private lemma spatialSecondPartial_radQuot_two {a : ParabolicPoint → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => a w) unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (hr : z.1 0 ≠ 0) :
    spatialSecondPartial (fun v : ParabolicPoint => a v * (v.1 0)⁻¹) 2 2 z
      = spatialSecondPartial a 2 2 z * (z.1 0)⁻¹ := by
  have ha1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => a w) unitCylinder := ha.of_le (by norm_num)
  have ha2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial a 2 w) unitCylinder :=
    contDiffOn_spatialPartial ha 2
  have ha21 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => spatialPartial a 2 w) unitCylinder :=
    ha2.of_le (by norm_num)
  have hinner : ∀ w : ParabolicPoint, w ∈ unitCylinder → w.1 0 ≠ 0 →
      spatialPartial (fun v : ParabolicPoint => a v * (v.1 0)⁻¹) 2 w
        = spatialPartial a 2 w * (w.1 0)⁻¹ :=
    fun w hw hwr => spatialPartial_radQuot_two (differentiableAt_spatialSlice ha1 hw) hwr
  have hstep : spatialSecondPartial (fun v : ParabolicPoint => a v * (v.1 0)⁻¹) 2 2 z
      = spatialPartial (fun w : ParabolicPoint => spatialPartial a 2 w * (w.1 0)⁻¹) 2 z := by
    show spatialPartial
        (fun w : ParabolicPoint => spatialPartial (fun v : ParabolicPoint => a v * (v.1 0)⁻¹) 2 w)
        2 z = _
    exact spatialPartial_congr_offAxis hinner hz hr 2
  have hda2 : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial a 2 (y, z.2)) z.1 :=
    differentiableAt_spatialSlice ha21 hz
  rw [hstep, spatialPartial_mul_of_differentiableAt
      (g := fun w : ParabolicPoint => spatialPartial a 2 w)
      (h := fun v : ParabolicPoint => (v.1 0)⁻¹) (i := 2) hda2 (differentiableAt_invRadius hr),
    spatialPartial_invRadius_two hr]
  simp only [spatialSecondPartial]
  ring

/-! ### The potential vorticity equation -/

/-- The potential vorticity equation `eq:aniso:q`: away from the axis, the material derivative
of the potential vorticity `Ω = ω_θ / r` of a classical, forced, axisymmetric solution equals
its rescaled cylindrical Laplacian `∂_r² Ω + 3 r⁻¹ ∂_r Ω + ∂_z² Ω`, the source
`∂_z (u_θ² / r²)`, and the potential vorticity of the force. -/
theorem potential_vorticity_pde (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (z : ParabolicPoint) (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    timePartial (potentialVorticity u) z
        + u z 0 * spatialPartial (potentialVorticity u) 0 z
        + u z 2 * spatialPartial (potentialVorticity u) 2 z
      = spatialSecondPartial (potentialVorticity u) 0 0 z
        + 3 / z.1 0 * spatialPartial (potentialVorticity u) 0 z
        + spatialSecondPartial (potentialVorticity u) 2 2 z
        + spatialPartial (fun w => (u w 1) ^ 2 / (w.1 0) ^ 2) 2 z
        + potentialVorticity f z := by
  have huTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1
  have ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => azimuthalVorticity u w) unitCylinder :=
    contDiffOn_azimuthalVorticity huTop
  have ha1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => azimuthalVorticity u w) unitCylinder :=
    ha.of_le (by norm_num)
  have hda : DifferentiableAt ℝ (fun y : Vec3 => azimuthalVorticity u (y, z.2)) z.1 :=
    differentiableAt_spatialSlice ha1 hz
  have hQeq : ∀ w : ParabolicPoint, w.1 0 ≠ 0 →
      potentialVorticity u w = azimuthalVorticity u w * (w.1 0)⁻¹ := by
    intro w hw
    rw [potentialVorticity_eq_div u hw, div_eq_mul_inv]
  have hQeqOn : ∀ w : ParabolicPoint, w ∈ unitCylinder → w.1 0 ≠ 0 →
      potentialVorticity u w = azimuthalVorticity u w * (w.1 0)⁻¹ := fun w _ hw => hQeq w hw
  -- The classical derivatives of `Ω` are those of the off-axis quotient.
  have hOt : timePartial (potentialVorticity u) z
      = timePartial (azimuthalVorticity u) z * (z.1 0)⁻¹ := by
    rw [timePartial_congr_offAxis (g := potentialVorticity u)
      (h := fun v : ParabolicPoint => azimuthalVorticity u v * (v.1 0)⁻¹) hQeq hr]
    exact timePartial_radQuot (differentiableAt_timeSliceScalar ha hz)
  have hO0 : spatialPartial (potentialVorticity u) 0 z
      = (spatialPartial (azimuthalVorticity u) 0 z - azimuthalVorticity u z * (z.1 0)⁻¹)
        * (z.1 0)⁻¹ := by
    rw [spatialPartial_congr_offAxis (g := potentialVorticity u)
      (h := fun v : ParabolicPoint => azimuthalVorticity u v * (v.1 0)⁻¹) hQeqOn hz hr 0]
    exact spatialPartial_radQuot_zero hda hr
  have hO2 : spatialPartial (potentialVorticity u) 2 z
      = spatialPartial (azimuthalVorticity u) 2 z * (z.1 0)⁻¹ := by
    rw [spatialPartial_congr_offAxis (g := potentialVorticity u)
      (h := fun v : ParabolicPoint => azimuthalVorticity u v * (v.1 0)⁻¹) hQeqOn hz hr 2]
    exact spatialPartial_radQuot_two hda hr
  have hO00 : spatialSecondPartial (potentialVorticity u) 0 0 z
      = spatialSecondPartial (azimuthalVorticity u) 0 0 z * (z.1 0)⁻¹
        - 2 * ((spatialPartial (azimuthalVorticity u) 0 z - azimuthalVorticity u z * (z.1 0)⁻¹)
            * ((z.1 0)⁻¹) ^ 2) := by
    rw [spatialSecondPartial_congr_offAxis (g := potentialVorticity u)
      (h := fun v : ParabolicPoint => azimuthalVorticity u v * (v.1 0)⁻¹) hQeqOn hz hr 0 0]
    exact spatialSecondPartial_radQuot_zero ha hz hr
  have hO22 : spatialSecondPartial (potentialVorticity u) 2 2 z
      = spatialSecondPartial (azimuthalVorticity u) 2 2 z * (z.1 0)⁻¹ := by
    rw [spatialSecondPartial_congr_offAxis (g := potentialVorticity u)
      (h := fun v : ParabolicPoint => azimuthalVorticity u v * (v.1 0)⁻¹) hQeqOn hz hr 2 2]
    exact spatialSecondPartial_radQuot_two ha hz hr
  -- The source term carries the radial weight `r⁻²` through the vertical derivative.
  have hBsq : DifferentiableAt ℝ (fun y : Vec3 => (u (y, z.2) 1) ^ 2) z.1 :=
    ((differentiableAt_pi.1
      (differentiableAt_spatialSlice (huTop.of_le (by norm_num)) hz)) 1).pow 2
  have hpt : ∀ b s : ℝ, b / s ^ 2 = b * s⁻¹ * s⁻¹ := by
    intro b s
    rw [div_eq_mul_inv, sq, mul_inv, mul_assoc]
  have hsrcfun : (fun w : ParabolicPoint => (u w 1) ^ 2 / (w.1 0) ^ 2)
      = fun w : ParabolicPoint => ((u w 1) ^ 2 * (w.1 0)⁻¹) * (w.1 0)⁻¹ :=
    funext fun w => hpt ((u w 1) ^ 2) (w.1 0)
  have hsrc : spatialPartial (fun w : ParabolicPoint => (u w 1) ^ 2 / (w.1 0) ^ 2) 2 z
      = spatialPartial (fun w : ParabolicPoint => (u w 1) ^ 2) 2 z * (z.1 0)⁻¹ * (z.1 0)⁻¹ := by
    rw [hsrcfun,
      spatialPartial_radQuot_two (a := fun w : ParabolicPoint => (u w 1) ^ 2 * (w.1 0)⁻¹)
        (hBsq.mul (differentiableAt_invRadius hr)) hr,
      spatialPartial_radQuot_two (a := fun w : ParabolicPoint => (u w 1) ^ 2) hBsq hr]
  -- The potential vorticity of the force is the quotient of the azimuthal curl.
  have hforce : potentialVorticity f z
      = (spatialPartial (fun w => f w 0) 2 z - spatialPartial (fun w => f w 2) 0 z)
        * (z.1 0)⁻¹ := by
    rw [potentialVorticity_eq_div f hr, div_eq_mul_inv]
    rfl
  have hPDE := azimuthal_vorticity_pde u p f hsol haxi z hz hplane hr
  rw [hOt, hO0, hO2, hO00, hO22, hsrc, hforce]
  linear_combination (z.1 0)⁻¹ * hPDE

end CIV
