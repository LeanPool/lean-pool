/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.AffineEigenfunctionBarycenter
public import LeanPool.CutoffRigidity.GibbsOperatorAffineRepresentative
public import LeanPool.CutoffRigidity.AffineEigenmapGaussian

/-! # Simultaneous potential splitting along the full affine eigen-row space

The actual centered directional drift vanishes after subtracting the
quadratic potential in every affine eigen-direction. Integrating that
identity removes the full subspace, rather than only one chosen direction.
The center is the genuine Gibbs barycenter.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The barycenter of the Gibbs measure used to center the splitting coordinates. -/
@[expose] noncomputable def affineSplittingCenter (V : E → ℝ) : E :=
  ∫ x, x ∂gibbsMeasure volume V

/-- The centered potential after subtracting the quadratic confinement. -/
@[expose] noncomputable def affineCenteredResidual (V : E → ℝ) (ρ : ℝ) (x : E) : ℝ :=
  V (x+affineSplittingCenter V)-ρ/2*‖x‖^2

/-- The centered potential restricted to the orthogonal complement of the affine eigen-rows. -/
@[expose] noncomputable def affineComplementPotential (V : E → ℝ) (ρ : ℝ)
    (x : (affineEigenRows V ρ)ᗮ) : ℝ := V ((x:E)+affineSplittingCenter V)

theorem contDiff_affineCenteredResidual {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) :
    ContDiff ℝ 2 (affineCenteredResidual V ρ) := by
  exact (hV.comp (contDiff_id.add contDiff_const)).sub (contDiff_const.mul (contDiff_norm_sq ℝ))

theorem contDiff_affineComplementPotential {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) :
    ContDiff ℝ 2 (affineComplementPotential V ρ) := by
  exact hV.comp (((affineEigenRows V ρ)ᗮ.subtypeL.contDiff).add contDiff_const)

theorem affineEigenRows_directional_drift_about_mean
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (v : affineEigenRows V ρ) (x : E) :
    fderiv ℝ V x (v:E) = ρ*inner ℝ (v:E) (x-affineSplittingCenter V) := by
  have hh := (affine_eigenfunction_iff_drift V (v:E) (affineEigenConstant V ρ v) ρ).mp
    (affineEigenRows_eigenfunction V hρ v) x
  rw [affineEigenConstant_eq_neg_inner_mean hV ρ hρ hHess hp] at hh
  rw [← inner_gradient_left,real_inner_comm]
  change inner ℝ (v:E) (gradient V x) = _
  rw [hh,inner_sub_right]
  rfl

theorem affineCenteredResidual_fderiv_row_zero
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (v : affineEigenRows V ρ) (y : E) : fderiv ℝ (affineCenteredResidual V ρ) y (v:E)=0 := by
  have hVd := hV.differentiable (by norm_num)
  have hshift : HasFDerivAt (fun z : E => V (z+affineSplittingCenter V))
      (fderiv ℝ V (y+affineSplittingCenter V)) y := by
    convert! (hVd (y+affineSplittingCenter V)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).add_const (affineSplittingCenter V)) using 1
  have hnorm := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hquad := hnorm.const_mul (ρ/2)
  change fderiv ℝ ((fun z : E => V (z+affineSplittingCenter V)) -
    (fun z : E => ρ/2*‖z‖^2)) y (v:E)=0
  rw [(hshift.sub hquad).fderiv]
  simp only [sub_apply,smul_apply,smul_eq_mul]
  rw [affineEigenRows_directional_drift_about_mean hV ρ hρ hHess hp v]
  simp only [add_sub_cancel_right,innerSL_apply_apply]
  rw [real_inner_comm y (v:E)]
  ring

/-- The actual residual is invariant along every vector in the full
finite-dimensional affine eigen-row space. -/
theorem affineCenteredResidual_invariant_rows
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (v : affineEigenRows V ρ) (y : E) :
    affineCenteredResidual V ρ (y+(v:E))=affineCenteredResidual V ρ y := by
  let F := fun s : ℝ => affineCenteredResidual V ρ (y+s•(v:E))
  have hd (s : ℝ) : HasDerivAt F 0 s := by
    have hline : HasDerivAt (fun r : ℝ => y+r•(v:E)) (v:E) s := by
      simpa only [one_smul,id_eq] using ((hasDerivAt_id s).smul_const (v:E)).const_add y
    have hh := ((contDiff_affineCenteredResidual hV ρ).differentiable (by norm_num)
      (y+s•(v:E))).hasFDerivAt.comp_hasDerivAt s hline
    convert! hh using 1
    exact (affineCenteredResidual_fderiv_row_zero hV ρ hρ hHess hp v (y+s•(v:E))).symm
  have hh := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) 1 0
  simpa only [F,one_smul,zero_smul,add_zero] using hh

/-- The simultaneous full-subspace potential decomposition, with the true
Gibbs barycenter as center and an actual complementary potential. -/
theorem potential_split_affineEigenRows
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (v : affineEigenRows V ρ) (w : (affineEigenRows V ρ)ᗮ) :
    V ((v:E)+(w:E)+affineSplittingCenter V) = ρ/2*‖v‖^2+affineComplementPotential V ρ w := by
  have hh := affineCenteredResidual_invariant_rows hV ρ hρ hHess hp v (w:E)
  have hi : inner ℝ (v:E) (w:E)=0 := Submodule.inner_right_of_mem_orthogonal v.property w.property
  have hn : ‖(w:E)+(v:E)‖^2=‖w‖^2+‖v‖^2 := by
    have hi' : inner ℝ (w:E) (v:E)=0 := by rw [real_inner_comm]; exact hi
    rw [norm_add_sq_real,hi']
    simp only [Submodule.norm_coe,mul_zero,add_zero]
  dsimp only [affineCenteredResidual] at hh
  rw [hn] at hh
  have he : (w:E)+(v:E)+affineSplittingCenter V=(v:E)+(w:E)+affineSplittingCenter V := by abel
  rw [he] at hh
  simp only [Submodule.norm_coe] at hh
  dsimp only [affineComplementPotential]
  linarith

end CutoffRigidity
