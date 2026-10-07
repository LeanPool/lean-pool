/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.ScalarSystemSwirl
public import LeanPool.CIVAxisymmetric.Identities.Vorticity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The weighted swirl component of the scalar Navier–Stokes equation

For `ψ = (−t)^η u_θ` on the meridional plane `{x₂ = 0}` off the axis, the weighted
swirl equation of `lem:aniso:closure` is:
`∂_t ψ + u_r ∂_r ψ + u_z ∂_z ψ − (∂_r² ψ + r⁻¹ ∂_r ψ + ∂_z² ψ) + (r⁻² + u_r/r + η/(−t)) ψ =
(−t)^η f_θ`.

The weight depends only on time, so spatial derivatives factor through it. The time derivative
picks up the extra term `η/(−t) ψ` from differentiating the weight. As in
`scalar_nse_swirl`, the rotation invariance of the pressure is not assumed: it follows from
the axisymmetry of the velocity and of the force (`pressure_rotZ_invariant`).
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



theorem weighted_swirl_pde (η : ℝ)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder)
    (z : ParabolicPoint) (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    timePartial (fun w => (-w.2) ^ η * u w 1) z
        + u z 0 * spatialPartial (fun w => (-w.2) ^ η * u w 1) 0 z
        + u z 2 * spatialPartial (fun w => (-w.2) ^ η * u w 1) 2 z
        - (spatialSecondPartial (fun w => (-w.2) ^ η * u w 1) 0 0 z
            + spatialPartial (fun w => (-w.2) ^ η * u w 1) 0 z / z.1 0
            + spatialSecondPartial (fun w => (-w.2) ^ η * u w 1) 2 2 z)
        + (1 / (z.1 0) ^ 2 + u z 0 / z.1 0 + η / (-z.2)) * ((-z.2) ^ η * u z 1)
      = (-z.2) ^ η * f z 1 := by
  -- smoothness from the classical solution hypothesis
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hsol.1.of_le (by decide)
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hsol.1.of_le (by decide)
  -- the time coordinate is strictly negative on the unit cylinder
  have hz_time : z.2 ∈ Ioo (-1 : ℝ) 0 := hz.2
  have hpos : 0 < -z.2 := by
    rcases hz_time with ⟨hleft, hright⟩
    linarith only [hright]
  have hneg : -z.2 ≠ 0 := by linarith only [hpos]
  -- spatial derivative factoring at any point in unitCylinder
  have h_spatial_factor_at (w : ParabolicPoint) (hw : w ∈ unitCylinder) (i : Fin 3) :
      spatialPartial (fun w' => (-w'.2) ^ η * u w' 1) i w =
        (-w.2) ^ η * spatialPartial (fun w' => u w' 1) i w := by
    dsimp [spatialPartial]
    have h_diff : DifferentiableAt ℝ (fun x : Vec3 => u (x, w.2) 1) w.1 :=
      differentiableAt_spatialSlice (contDiffOn_component hu1 1) hw
    rw [fderiv_const_mul h_diff ((-w.2) ^ η)]
    simp
  -- C^2 for the swirl component on the spatial slice
  have h_contDiff_spatial : ContDiffOn ℝ 2 (fun y : Vec3 => u (y, z.2) 1) (vec3Ball 0 1) :=
    contDiffOn_spatialSlice (contDiffOn_component hu2 1) hz.2
  -- fderiv of the spatial slice is C^1
  have h_contDiff_fderiv : ContDiffOn ℝ 1 (fderiv ℝ (fun y : Vec3 => u (y, z.2) 1))
      (vec3Ball 0 1) :=
    h_contDiff_spatial.fderiv_of_isOpen (isOpen_vec3Ball 0 1) (by norm_num)
  -- differentiability of the fderiv at z.1
  have h_diff_fderiv : DifferentiableAt ℝ (fderiv ℝ (fun y : Vec3 => u (y, z.2) 1)) z.1 :=
    (h_contDiff_fderiv.differentiableOn_one).differentiableAt
      ((isOpen_vec3Ball 0 1).mem_nhds hz.1)
  -- differentiability of spatialPartial in space (for second derivative factoring)
  have h_diff_spatialSecond (i : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => spatialPartial (fun w => u w 1) i (x, z.2)) z.1 := by
    dsimp [spatialPartial]
    have h_const_basis : DifferentiableAt ℝ (fun _ : Vec3 => basisVec i) z.1 :=
      differentiableAt_const _
    exact h_diff_fderiv.clm_apply h_const_basis
  -- spatial second derivative factoring lemma
  have h_spatialSecond_factor (i : Fin 3) :
      spatialSecondPartial (fun w => (-w.2) ^ η * u w 1) i i z =
        (-z.2) ^ η * spatialSecondPartial (fun w => u w 1) i i z := by
    -- Restate both sides directly as the iterated `fderiv` that `spatialSecondPartial` and
    -- the outer `spatialPartial` unfold to: `show` reaches this form by defeq without letting
    -- `dsimp` unfold the *inner* `spatialPartial` occurrence as well, which would leave no
    -- `spatialPartial`-headed subterm for `h_eventually.fderiv_eq` to rewrite.
    change fderiv ℝ (fun x : Vec3 => spatialPartial (fun w => (-w.2) ^ η * u w 1) i (x, z.2)) z.1
        (basisVec i) =
      (-z.2) ^ η * fderiv ℝ (fun x : Vec3 => spatialPartial (fun w => u w 1) i (x, z.2)) z.1
        (basisVec i)
    -- rewrite the inner spatialPartial using h_spatial_factor_at, restated at points of the
    -- open ball `vec3Ball 0 1` rather than through `unitCylinder` directly: `ParabolicPoint`
    -- and `Vec3 × ℝ` carry different topological-space instances even though the carrier
    -- type is the same, so membership must be built from the ball/interval pieces of
    -- `unitCylinder`, never from `IsOpen.mem_nhds` applied at a `ParabolicPoint`-typed point.
    have h_eventually : (fun x : Vec3 => spatialPartial (fun w' => (-w'.2) ^ η * u w' 1) i (x, z.2))
        =ᶠ[nhds z.1] (fun x : Vec3 => (-z.2) ^ η * spatialPartial (fun w' => u w' 1) i (x, z.2))
          := by
      filter_upwards [(isOpen_vec3Ball 0 1).mem_nhds hz.1] with x hx
      have hxu : (x, z.2) ∈ unitCylinder := ⟨hx, hz.2⟩
      exact h_spatial_factor_at (x, z.2) hxu i
    rw [h_eventually.fderiv_eq]
    rw [fderiv_const_mul (h_diff_spatialSecond i) ((-z.2) ^ η)]
    simp
  -- HasDerivAt of the weight function t ↦ (-t)^η at z.2
  have h_weight_hasDerivAt : HasDerivAt (fun t : ℝ => (-t) ^ η) (-η * (-z.2) ^ (η - 1)) z.2 := by
    have h_neg : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) z.2 := by
      simpa [neg_one_mul] using (hasDerivAt_id z.2).const_mul (-1)
    have h_rpow : HasDerivAt (fun t : ℝ => t ^ η) (η * (-z.2) ^ (η - 1)) (-z.2) :=
      Real.hasDerivAt_rpow_const (Or.inl hneg)
    have h_comp : HasDerivAt (fun t : ℝ => (-t) ^ η) (η * (-z.2) ^ (η - 1) * (-1)) z.2 :=
      h_rpow.comp z.2 h_neg
    rw [show η * (-z.2) ^ (η - 1) * (-1) = -η * (-z.2) ^ (η - 1) from by ring] at h_comp
    exact h_comp
  -- differentiability of the time slice of u at z.2
  have h_diff_time_slice : DifferentiableAt ℝ (fun s : ℝ => u (z.1, s) 1) z.2 := by
    have h_cont : ContDiffOn ℝ 1 (fun s : ℝ => u (z.1, s)) (Ioo (-1 : ℝ) 0) :=
      hu1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun s hs => ⟨hz.1, hs⟩)
    have h_diff_at : DifferentiableAt ℝ (fun s : ℝ => u (z.1, s)) z.2 :=
      h_cont.differentiableOn_one.differentiableAt (isOpen_Ioo.mem_nhds hz.2)
    exact differentiableAt_pi.1 h_diff_at 1
  -- time derivative expansion of the product (-t)^η * u_θ
  have h_timePartial_expand :
      timePartial (fun w => (-w.2) ^ η * u w 1) z =
        (-z.2) ^ η * (-η / (-z.2)) * u z 1 +
        (-z.2) ^ η * timePartial (fun w => u w 1) z := by
    -- `timePartial g z` unfolds to `deriv (fun s => g (z.1, s)) z.2` on both sides; working
    -- with `deriv` and `HasDerivAt.mul` avoids ever unfolding to the raw `fderiv _ _ 1`
    -- continuous-linear-map application, which is defeq but not syntactically the same term.
    change deriv (fun s : ℝ => (-s) ^ η * u (z.1, s) 1) z.2 =
        (-z.2) ^ η * (-η / (-z.2)) * u z 1 +
        (-z.2) ^ η * deriv (fun s : ℝ => u (z.1, s) 1) z.2
    have h_prod_hasDeriv : HasDerivAt (fun s : ℝ => (-s) ^ η * u (z.1, s) 1)
        ((-η * (-z.2) ^ (η - 1)) * u z 1 +
          (-z.2) ^ η * deriv (fun s : ℝ => u (z.1, s) 1) z.2) z.2 :=
      h_weight_hasDerivAt.mul h_diff_time_slice.hasDerivAt
    rw [h_prod_hasDeriv.deriv, Real.rpow_sub_one hneg η]
    ring
  -- spatial factoring instances at z
  have h0 : spatialPartial (fun w => (-w.2) ^ η * u w 1) 0 z =
      (-z.2) ^ η * spatialPartial (fun w => u w 1) 0 z := h_spatial_factor_at z hz 0
  have h2 : spatialPartial (fun w => (-w.2) ^ η * u w 1) 2 z =
      (-z.2) ^ η * spatialPartial (fun w => u w 1) 2 z := h_spatial_factor_at z hz 2
  have h00 : spatialSecondPartial (fun w => (-w.2) ^ η * u w 1) 0 0 z =
      (-z.2) ^ η * spatialSecondPartial (fun w => u w 1) 0 0 z := h_spatialSecond_factor 0
  have h22 : spatialSecondPartial (fun w => (-w.2) ^ η * u w 1) 2 2 z =
      (-z.2) ^ η * spatialSecondPartial (fun w => u w 1) 2 2 z := h_spatialSecond_factor 2
  -- the base (unweighted) swirl equation
  have h_swirl := scalar_nse_swirl u p f hsol haxi hfaxi z hz hplane hr
  -- combine: substitute the weight-factoring identities and `η(−t)^{η-1} = (η/(−t))(−t)^η`
  -- cancels exactly against the `η/(−t)` coefficient already present in the statement, leaving
  -- `(−t)^η` times the base swirl equation.
  linear_combination h_timePartial_expand + (u z 0 - 1 / z.1 0) * h0 + u z 2 * h2 - h00 - h22
    + (-z.2) ^ η * h_swirl

end CIV
