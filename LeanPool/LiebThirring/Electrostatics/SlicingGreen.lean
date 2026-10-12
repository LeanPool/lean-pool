/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.SlicingDivergence
public import LeanPool.LiebThirring.Analysis.FundamentalSolutionIntegrationByParts

/-!
# Green's second identity on an open Voronoi cell

Compact tests eliminate outer boundary terms. The genuine-face terms follow
from the directional cell identity proved by line slicing.
-/

public section

open Set MeasureTheory InnerProductSpace Laplacian

namespace LiebThirring

/-- A coordinate component of the vector field in Green’s identity. -/
@[expose] noncomputable def slicingGreenComponent (g f : Position → ℝ)
    (a : Fin 3) (x : Position) : ℝ :=
  g x * fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ a) -
    f x * fderiv ℝ g x (EuclideanSpace.basisFun (Fin 3) ℝ a)

theorem contDiff_slicingGreenComponent {g f : Position → ℝ}
    (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f) (a : Fin 3) :
    ContDiff ℝ 1 (slicingGreenComponent g f a) :=
  ((hg.of_le (by norm_num)).mul ((hf.fderiv_right (by norm_num)).clm_apply contDiff_const)).sub
    ((hf.of_le (by norm_num)).mul ((hg.fderiv_right (by norm_num)).clm_apply contDiff_const))

theorem hasCompactSupport_slicingGreenComponent {g f : Position → ℝ}
    (hfc : HasCompactSupport f) (a : Fin 3) :
    HasCompactSupport (slicingGreenComponent g f a) :=
  (hfc.fderiv_apply ℝ _).mul_left.sub hfc.mul_right

theorem fderiv_slicingGreenComponent {g f : Position → ℝ}
    (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f) (a : Fin 3) (x : Position) :
    fderiv ℝ (slicingGreenComponent g f a) x (EuclideanSpace.basisFun (Fin 3) ℝ a) =
      g x * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ a) -
      f x * fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ a) := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ a
  have hdg := (hg.fderiv_right (by norm_num)).clm_apply
    (contDiff_const : ContDiff ℝ 1 (fun _ : Position => e))
  have hdf := (hf.fderiv_right (by norm_num)).clm_apply
    (contDiff_const : ContDiff ℝ 1 (fun _ : Position => e))
  unfold slicingGreenComponent
  rw [fderiv_fun_sub ((hg.differentiable (by norm_num) x).fun_mul (hdf.differentiable one_ne_zero
    x))
    ((hf.differentiable (by norm_num) x).fun_mul (hdg.differentiable one_ne_zero x)),
    fderiv_fun_mul (hg.differentiable (by norm_num) x) (hdf.differentiable one_ne_zero x),
    fderiv_fun_mul (hf.differentiable (by norm_num) x) (hdg.differentiable one_ne_zero x)]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul,
    fderiv_directional_fderiv hg, fderiv_directional_fderiv hf]
  ring

theorem laplacian_green_eq_sum {g f : Position → ℝ}
    (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f) (x : Position) :
    g x * Δ f x - f x * Δ g x =
      ∑ a : Fin 3, fderiv ℝ (slicingGreenComponent g f a) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 3) ℝ),
    laplacian_eq_iteratedFDeriv_orthonormalBasis g (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [fderiv_slicingGreenComponent hg hf, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mul_sum, Finset.sum_sub_distrib]

/-- Green's second identity with explicit directed genuine-face integrals. -/
theorem voronoiCell_compact_green {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k : Fin M) (g f : Position → ℝ)
    (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x in voronoiCell R k, g x * Δ f x - f x * Δ g x) =
      ∑ l : {l : Fin M // l ≠ k}, ∫ x in voronoiFace R k l.val,
        (∑ a : Fin 3, bisectorNormal R k l.val a * slicingGreenComponent g f a x)
        ∂bisectorSurfaceMeasure R hR k l.val l.property.symm := by
  classical
  have hc (a : Fin 3) := contDiff_slicingGreenComponent hg hf a
  have hsc (a : Fin 3) := hasCompactSupport_slicingGreenComponent (g := g) hfc a
  have hi (a : Fin 3) := integrable_compact_directional_derivative _ (hc a) (hsc a)
    (EuclideanSpace.basisFun (Fin 3) ℝ a)
  simp_rw [laplacian_green_eq_sum hg hf]
  rw [integral_finsetSum _ (fun a _ => (hi a).integrableOn)]
  simp_rw [voronoiCell_compact_directional_integral R hR k _ _ (hc _) (hsc _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun a _ =>
    ((integrable_compact_bisectorSurfaceMeasure R hR k l.val l.property.symm _
      (hc a).continuous (hsc a)).const_mul _).integrableOn)]

end LiebThirring

end
