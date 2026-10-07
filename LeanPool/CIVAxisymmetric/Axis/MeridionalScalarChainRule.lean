/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ChainRule

/-!
# Meridional embedding chain rule

The meridional embedding `(r, z) ↦ (r, 0, z)` of `CIV.meridional` threads a scalar field's
`r`- and `z`-derivatives along straight lines in `Vec3` into Fréchet derivatives on the
full spatial domain. The first-order theorems (`hasDerivAt_comp_meridional_fst`,
`hasDerivAt_comp_meridional_snd`) are the unit-speed special case of
`CIV.hasDerivAt_meridional_fst`/`hasDerivAt_meridional_snd` from `CIV.Zoom.ChainRule`.

The second-order theorems (`hasDerivAt_deriv_comp_meridional_fst`,
`hasDerivAt_deriv_comp_meridional_snd`) give the derivative of the derivative, which
`CIV.axisMaximumPrinciple` needs for its hypotheses (`lem:aniso:axis`).
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- First-order chain rule for a scalar composed with the `r`-directed meridional embedding.
The embedding's derivative is the public `CIV.hasDerivAt_meridional_fst` of
`CIV.Zoom.ChainRule` at unit radial speed. -/
theorem hasDerivAt_comp_meridional_fst {g : Vec3 → ℝ} {r₀ x₃ : ℝ}
    (hg : DifferentiableAt ℝ g (meridional r₀ x₃)) :
    HasDerivAt (fun r : ℝ => g (meridional r x₃))
      (fderiv ℝ g (meridional r₀ x₃) (basisVec 0)) r₀ :=
  hg.hasFDerivAt.comp_hasDerivAt r₀
    (by simpa using hasDerivAt_meridional_fst 1 x₃ r₀)

/-- First-order chain rule for a scalar composed with the `z`-directed meridional embedding.
The embedding's derivative is the public `CIV.hasDerivAt_meridional_snd` of
`CIV.Zoom.ChainRule` at unit vertical speed and zero offset. -/
theorem hasDerivAt_comp_meridional_snd {g : Vec3 → ℝ} {x₁ z₀ : ℝ}
    (hg : DifferentiableAt ℝ g (meridional x₁ z₀)) :
    HasDerivAt (fun z : ℝ => g (meridional x₁ z))
      (fderiv ℝ g (meridional x₁ z₀) (basisVec 2)) z₀ :=
  hg.hasFDerivAt.comp_hasDerivAt z₀
    (by simpa using hasDerivAt_meridional_snd x₁ 0 1 z₀)

/-- The preimage of the unit ball under the `r`-directed meridional embedding is open. -/
theorem isOpen_meridional_fst_preimage (x₃ : ℝ) :
    IsOpen {r : ℝ | meridional r x₃ ∈ vec3Ball (0 : Vec3) 1} := by
  have hcont : Continuous (fun r : ℝ => meridional r x₃) := by unfold meridional; fun_prop
  exact (isOpen_vec3Ball 0 1).preimage hcont

/-- The preimage of the unit ball under the `z`-directed meridional embedding is open. -/
theorem isOpen_meridional_snd_preimage (x₁ : ℝ) :
    IsOpen {z : ℝ | meridional x₁ z ∈ vec3Ball (0 : Vec3) 1} := by
  have hcont : Continuous (fun z : ℝ => meridional x₁ z) := by unfold meridional; fun_prop
  exact (isOpen_vec3Ball 0 1).preimage hcont

/-- Second-order chain rule for a scalar composed with the `r`-directed meridional embedding:
the second derivative of `r ↦ g (meridional r x₃)` at `r₀` is the corresponding iterated
Fréchet derivative of `g`. -/
theorem hasDerivAt_deriv_comp_meridional_fst {g : Vec3 → ℝ} {r₀ x₃ : ℝ}
    (hg : ContDiffOn ℝ 2 g (vec3Ball (0 : Vec3) 1))
    (hmem : meridional r₀ x₃ ∈ vec3Ball (0 : Vec3) 1) :
    HasDerivAt (fun r : ℝ => deriv (fun r' : ℝ => g (meridional r' x₃)) r)
      (fderiv ℝ (fun y : Vec3 => fderiv ℝ g y (basisVec 0)) (meridional r₀ x₃) (basisVec 0))
      r₀ := by
  have hg1 : DifferentiableOn ℝ g (vec3Ball (0 : Vec3) 1) :=
    (hg.of_le (by norm_num)).differentiableOn_one
  have heq : (fun r : ℝ => deriv (fun r' : ℝ => g (meridional r' x₃)) r)
      =ᶠ[nhds r₀] (fun r : ℝ => fderiv ℝ g (meridional r x₃) (basisVec 0)) := by
    filter_upwards [(isOpen_meridional_fst_preimage x₃).mem_nhds hmem] with r hr
    exact (hasDerivAt_comp_meridional_fst
      (hg1.differentiableAt ((isOpen_vec3Ball 0 1).mem_nhds hr))).deriv
  have h_contDiff_fderiv : ContDiffOn ℝ 1 (fderiv ℝ g) (vec3Ball (0 : Vec3) 1) :=
    hg.fderiv_of_isOpen (isOpen_vec3Ball 0 1) (by norm_num)
  have h_diff_fderiv : DifferentiableAt ℝ (fderiv ℝ g) (meridional r₀ x₃) :=
    (h_contDiff_fderiv.differentiableOn_one).differentiableAt
      ((isOpen_vec3Ball 0 1).mem_nhds hmem)
  have hgd : DifferentiableAt ℝ (fun y : Vec3 => fderiv ℝ g y (basisVec 0)) (meridional r₀ x₃) :=
    h_diff_fderiv.clm_apply (differentiableAt_const _)
  exact (hasDerivAt_comp_meridional_fst hgd).congr_of_eventuallyEq heq

/-- Second-order chain rule for a scalar composed with the `z`-directed meridional embedding. -/
theorem hasDerivAt_deriv_comp_meridional_snd {g : Vec3 → ℝ} {x₁ z₀ : ℝ}
    (hg : ContDiffOn ℝ 2 g (vec3Ball (0 : Vec3) 1))
    (hmem : meridional x₁ z₀ ∈ vec3Ball (0 : Vec3) 1) :
    HasDerivAt (fun z : ℝ => deriv (fun z' : ℝ => g (meridional x₁ z')) z)
      (fderiv ℝ (fun y : Vec3 => fderiv ℝ g y (basisVec 2)) (meridional x₁ z₀) (basisVec 2))
      z₀ := by
  have hg1 : DifferentiableOn ℝ g (vec3Ball (0 : Vec3) 1) :=
    (hg.of_le (by norm_num)).differentiableOn_one
  have heq : (fun z : ℝ => deriv (fun z' : ℝ => g (meridional x₁ z')) z)
      =ᶠ[nhds z₀] (fun z : ℝ => fderiv ℝ g (meridional x₁ z) (basisVec 2)) := by
    filter_upwards [(isOpen_meridional_snd_preimage x₁).mem_nhds hmem] with z hz
    exact (hasDerivAt_comp_meridional_snd
      (hg1.differentiableAt ((isOpen_vec3Ball 0 1).mem_nhds hz))).deriv
  have h_contDiff_fderiv : ContDiffOn ℝ 1 (fderiv ℝ g) (vec3Ball (0 : Vec3) 1) :=
    hg.fderiv_of_isOpen (isOpen_vec3Ball 0 1) (by norm_num)
  have h_diff_fderiv : DifferentiableAt ℝ (fderiv ℝ g) (meridional x₁ z₀) :=
    (h_contDiff_fderiv.differentiableOn_one).differentiableAt
      ((isOpen_vec3Ball 0 1).mem_nhds hmem)
  have hgd : DifferentiableAt ℝ (fun y : Vec3 => fderiv ℝ g y (basisVec 2)) (meridional x₁ z₀) :=
    h_diff_fderiv.clm_apply (differentiableAt_const _)
  exact (hasDerivAt_comp_meridional_snd hgd).congr_of_eventuallyEq heq

end CIV
