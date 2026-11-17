/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Operator

/-! # Coordinate matrices of total Hessians

Standard-basis matrices, their total gradient-derivative identification,
local smoothness and affine changes. Row orientation and nonsmooth total
conventions are retained, including dimension zero.
-/

@[expose] public section

noncomputable section
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities.Probability.Stein
/-- The Hessian matrix `(∇²φ)_{ij}(y) = D²φ(y)(e_i, e_j)` of `φ` in the standard basis. -/
noncomputable def hessianMatrix {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : Probability.Stein.KernelMatrix n := fun i j =>
  bilinearIteratedFDerivTwo ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)

/--
Matrix of a gradient derivative: row `r` is the input direction and column `s` the dual coordinate.
-/
def gradientDerivativeMatrix {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun r s =>
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
    (L (EuclideanSpace.basisFun (Fin n) ℝ r)) (EuclideanSpace.basisFun (Fin n) ℝ s)

/--
The total coordinate Hessian is the matrix of the total gradient derivative, even at nonsmooth
points. -/
theorem hessianMatrix_eq_gradientDerivativeMatrix {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = gradientDerivativeMatrix (fderiv ℝ (gradient u) x) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  have he : fderiv ℝ u = T ∘ gradient u :=
    funext fun y => (T.apply_symm_apply (fderiv ℝ u y)).symm
  have hd : fderiv ℝ (fderiv ℝ u) x = T.toContinuousLinearMap.comp (fderiv ℝ (gradient u) x) :=
    (congrArg (fun f => fderiv ℝ f x) he).trans T.comp_fderiv
  ext r s
  change
    fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ r)
        (EuclideanSpace.basisFun (Fin n) ℝ s) =
      T (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ r))
        (EuclideanSpace.basisFun (Fin n) ℝ s)
  rw [hd]
  rfl

/-- The coordinate matrix depends continuously on the linear operator. -/
theorem continuous_gradientDerivativeMatrix {n : ℕ} :
    Continuous (gradientDerivativeMatrix (n := n)) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro s
  let T := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  exact (T.continuous.comp (continuous_id.clm_apply continuous_const)).clm_apply
    continuous_const

/-- The coordinate Hessian matrix is the standard-basis entry matrix of the Hessian operator
`Analysis.BakryEmery.hessianOperator` (specialization bridge; the two objects keep their roles). -/
theorem hessianMatrix_eq_operatorEntry_hessianOperator {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (y : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    hessianMatrix φ y i j =
      Analysis.operatorEntry (EuclideanSpace.basisFun (Fin n) ℝ) (hessianOperator φ y) i j :=
  (operatorEntry_hessianOperator (EuclideanSpace.basisFun (Fin n) ℝ) hφ y i j).symm

/-- `D²φ(y)(u, v) = ⟪D(∇φ)(y) u, v⟫`. -/
theorem hessian_eq_inner_fderiv_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (y u v : E) : bilinearIteratedFDerivTwo ℝ φ y u v = ⟪fderiv ℝ (gradient φ) y u, v⟫ := by
  have hg : ContDiff ℝ 1 (gradient φ) := contDiff_gradient hφ (by norm_num)
  have hfun : (fun x : E => fderiv ℝ φ x v) = fun x => ⟪gradient φ x, v⟫ := by
    funext x
    exact inner_gradient_left.symm
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hφ, hfun,
    fderiv_inner_apply ℝ (hg.differentiable one_ne_zero y) (differentiableAt_const v)]
  simp

/-- Chain rule in coordinates: `∂_i (f ∘ ∇φ)(y) = ∑_j (∇²φ)_{ij}(y) (∂_j f)(∇φ y)`. -/
theorem chain_coordinate {n : ℕ} {φ f : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hf : ContDiff ℝ 1 f) (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    fderiv ℝ (f ∘ gradient φ) y (EuclideanSpace.basisFun (Fin n) ℝ i) =
      ∑ j, hessianMatrix φ y i j * gradient f (gradient φ y) j := by
  have hg : ContDiff ℝ 1 (gradient φ) := contDiff_gradient hφ (by norm_num)
  rw [fderiv_comp y (hf.differentiable one_ne_zero _) (hg.differentiable one_ne_zero _)]
  change
    fderiv ℝ f (gradient φ y) (fderiv ℝ (gradient φ) y (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      _
  rw [← inner_gradient_left, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hcoord :
    fderiv ℝ (gradient φ) y (EuclideanSpace.basisFun (Fin n) ℝ i) j = hessianMatrix φ y i j := by
    rw [hessianMatrix, hessian_eq_inner_fderiv_gradient hφ]
    exact
      (EuclideanSpace.inner_basisFun_real (Fin n)
          (fderiv ℝ (gradient φ) y (EuclideanSpace.basisFun (Fin n) ℝ i)) j).symm
  rw [hcoord]
  simp only [Real.inner_apply, mul_comm]

/-- Continuity of the Hessian entries. -/
theorem hessian_entry_continuous {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (i j : Fin n) : Continuous (fun y => hessianMatrix φ y i j) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  exact
    ((h1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const


section AffineHessian
open Matrix
open scoped ContDiff

/-- The canonical Hessian under a local C2 affine change is its actual matrix congruence. -/
theorem hessianMatrix_comp_affine_at {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (c x : EuclideanSpace ℝ (Fin n)) (hu : ContDiffAt ℝ 2 u (L x + c)) :
    let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let A := LinearMap.toMatrix e e L.toLinearMap
    hessianMatrix (fun y => u (L y + c)) x = Aᵀ * hessianMatrix u (L x + c) * A := by
  dsimp only
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let B : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) :=
    bilinearIteratedFDerivTwo ℝ u (L x + c)
  have hm :
    hessianMatrix (fun y => u (L y + c)) x =
      LinearMap.BilinForm.toMatrix e (LinearMap.BilinForm.comp B L.toLinearMap L.toLinearMap) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    change
      bilinearIteratedFDerivTwo ℝ (fun y => u (L y + c)) x (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        bilinearIteratedFDerivTwo ℝ u (L x + c) (L (EuclideanSpace.basisFun (Fin n) ℝ i))
          (L (EuclideanSpace.basisFun (Fin n) ℝ j))
    exact bilinearIteratedFDerivTwo_comp_affine_at L c x _ _ hu
  rw [hm, LinearMap.BilinForm.toMatrix_comp e e]
  have hB : LinearMap.BilinForm.toMatrix e B = hessianMatrix u (L x + c) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rw [hB]

end AffineHessian

end FunctionalInequalities.Probability.Stein

/-! ## Pointwise linearity of the coordinate Hessian

Local C2 hypotheses suffice, including dimension zero. These ordinary calculus
identities support CNS1984 section 2 and Lemma5.1 without PDE or measure inputs.
-/

namespace FunctionalInequalities.Analysis

open Probability.Stein

theorem hessianMatrix_const_mul_of_contDiffAt {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (c : ℝ) (hu : ContDiffAt ℝ 2 u x) :
    hessianMatrix (fun y => c * u y) x = c • hessianMatrix u x := by
  ext i k
  change bilinearIteratedFDerivTwo ℝ (c • u) x _ _ = c * bilinearIteratedFDerivTwo ℝ u x _ _
  simp only [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, iteratedFDeriv_const_smul_apply hu,
    _root_.smul_apply, smul_eq_mul]

theorem hessianMatrix_add_of_contDiffAt {n : ℕ} {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    hessianMatrix (fun y => u y + v y) x = hessianMatrix u x + hessianMatrix v x := by
  ext i j
  simp only [hessianMatrix, Matrix.add_apply, bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ 2 (u + v) x) _ = _
  rw [iteratedFDeriv_add_apply hu hv, add_apply]

theorem hessianMatrix_sub_of_contDiffAt {n : ℕ} {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    hessianMatrix (fun y => u y - v y) x = hessianMatrix u x - hessianMatrix v x := by
  ext i j
  simp only [hessianMatrix, Matrix.sub_apply, bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ 2 (u - v) x) _ = _
  rw [iteratedFDeriv_sub_apply hu hv, sub_apply]

theorem hessianMatrix_const_fun {n : ℕ} (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (fun _ : EuclideanSpace ℝ (Fin n) => a) x = 0 := by
  ext i j
  simp [hessianMatrix, bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    iteratedFDeriv_const_of_ne (by norm_num : (2 : ℕ) ≠ 0)]

theorem hessianMatrix_neg_of_contDiffAt {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hu : ContDiffAt ℝ 2 u x) :
    hessianMatrix (fun y => -u y) x = -hessianMatrix u x := by
  have h := hessianMatrix_sub_of_contDiffAt (u := fun _ => (0 : ℝ)) contDiffAt_const hu
  rw [hessianMatrix_const_fun, zero_sub] at h
  simpa only [zero_sub] using h

section PositiveDefinite

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/--
A positive definite coordinate Hessian matrix makes the Hessian bilinear form positive on nonzero
vectors. -/
theorem bilinearIteratedFDerivTwo_pos_of_hessianMatrix_posDef {u : E → ℝ} {x : E}
    (hp : (hessianMatrix u x).PosDef) (v : E) (hv : v ≠ 0) :
    0 < bilinearIteratedFDerivTwo ℝ u x v v := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hz : (fun i => v i) ≠ 0 := by
    intro h
    apply hv
    ext i
    exact congrFun h i
  have h := hp.dotProduct_mulVec_pos hz
  have he : (∑ i, v i • b i) = v := b.sum_repr v
  rw [← he]
  rw [bilinear_sum_smul_sum_smul]
  simpa only [b, hessianMatrix, dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using h

end PositiveDefinite

end FunctionalInequalities.Analysis
