/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianCDF
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.Hadamard

/-!
# Hessian of the Gaussian-quantile interpolation functional

All differential statements are on the open probability box. The coefficients
are arbitrary; NP16 uses the three coefficients `(p,1-p,-σ)`. Working first
with an arbitrary finite index exposes the diagonal and rank-one terms.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix

namespace EhrhardGaussian.Ehrhard

variable {ι : Type*} [Fintype ι]

/-- The open box of probability coordinates. -/
def probabilityBox : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioo (0 : ℝ) 1}

omit [Fintype ι] in
/-- The box of coordinate probabilities strictly between zero and one is open. -/
theorem isOpen_probabilityBox [Finite ι] : IsOpen (probabilityBox (ι := ι)) :=
  by
    have h := isOpen_iInter_of_finite (fun i : ι => (isOpen_Ioo (a := (0 : ℝ)) (b := 1)).preimage
      (by fun_prop : Continuous (fun x : ι → ℝ => x i)))
    convert h using 1
    ext x
    simp only [probabilityBox, mem_ofPred_eq, mem_iInter, mem_preimage]

/-- The linear combination of Gaussian quantiles denoted `Ξ` by NP16. -/
def quantileLinear (θ x : ι → ℝ) : ℝ := ∑ i, θ i * gaussianCDFChart.symm (x i)

/-- The interpolation functional `Φ(R Ξ)`, evaluated on the probability box. -/
def gaussianFunctional (θ : ι → ℝ) (R : ℝ) (x : ι → ℝ) : ℝ :=
  gaussianCDF (R * quantileLinear θ x)

/-- Linear functional represented by the indicated coordinate coefficients. -/
def coordinateForm (c : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, c i • ContinuousLinearMap.proj i

/-- The coordinate linear form evaluates as the sum of the weighted coordinates. -/
theorem coordinateForm_apply (c v : ι → ℝ) : coordinateForm c v = ∑ i, c i * v i := by
  simp only [coordinateForm, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The derivative of a linear quantile combination is the coordinate form weighted by inverse
Gaussian densities. -/
theorem hasFDerivAt_quantileLinear (θ : ι → ℝ) {x : ι → ℝ} (hx : x ∈ probabilityBox) :
    HasFDerivAt (quantileLinear θ)
      (coordinateForm (fun i => θ i / gaussianPDFReal 0 1 (gaussianCDFChart.symm (x i)))) x := by
  have hterm (i : ι) : HasFDerivAt (fun y : ι → ℝ => θ i * gaussianCDFChart.symm (y i))
      ((θ i / gaussianPDFReal 0 1 (gaussianCDFChart.symm (x i))) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i)) x := by
    have h := ((hasDerivAt_gaussianCDFChart_symm (hx i)).const_mul (θ i)).hasFDerivAt.comp x
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ι => ℝ) i x)
    dsimp only [Function.comp_def] at h
    convert h using 1
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  exact HasFDerivAt.fun_sum (fun i _ => hterm i)

/-- The derivative of the Gaussian functional follows the Gaussian density and inverse-density chain
rule. -/
theorem hasFDerivAt_gaussianFunctional (θ : ι → ℝ) (R : ℝ)
    {x : ι → ℝ} (hx : x ∈ probabilityBox) :
    HasFDerivAt (gaussianFunctional θ R)
      (coordinateForm (fun i => R * θ i * gaussianPDFReal 0 1 (R * quantileLinear θ x) /
        gaussianPDFReal 0 1 (gaussianCDFChart.symm (x i)))) x := by
  have h := (hasDerivAt_gaussianCDF (R * quantileLinear θ x)).hasFDerivAt.comp x
    ((hasFDerivAt_quantileLinear θ hx).const_mul R)
  dsimp only [Function.comp_def] at h
  convert h using 1
  · rfl
  · ext v
    simp only [coordinateForm_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The coordinate gradient of the interpolation functional. -/
def functionalGradient (θ : ι → ℝ) (R : ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  R * θ i * gaussianPDFReal 0 1 (R * quantileLinear θ x) /
    gaussianPDFReal 0 1 (gaussianCDFChart.symm (x i))

/-- Each coordinate of the Gaussian functional gradient has the explicit derivative given by its
Hessian row. -/
theorem hasFDerivAt_functionalGradient (θ : ι → ℝ) (R : ℝ) (i : ι)
    {x : ι → ℝ} (hx : x ∈ probabilityBox) :
    HasFDerivAt (fun y => functionalGradient θ R y i)
      ((R * θ i * gaussianPDFReal 0 1 (R * quantileLinear θ x) *
          (gaussianCDFChart.symm (x i) /
            (gaussianPDFReal 0 1 (gaussianCDFChart.symm (x i))) ^ 2)) •
          ContinuousLinearMap.proj i -
        (R ^ 3 * quantileLinear θ x * θ i *
            gaussianPDFReal 0 1 (R * quantileLinear θ x) /
            gaussianPDFReal 0 1 (gaussianCDFChart.symm (x i))) •
          coordinateForm (fun j => θ j /
            gaussianPDFReal 0 1 (gaussianCDFChart.symm (x j)))) x := by
  have heval := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ι => ℝ) i x
  have hinv := (hasDerivAt_inv_gaussianDensity_quantile (hx i)).hasFDerivAt.comp x heval
  have hφ : HasDerivAt (gaussianPDFReal 0 1)
      (-(R * quantileLinear θ x * gaussianPDFReal 0 1 (R * quantileLinear θ x)))
      (R * quantileLinear θ x) := by
    simpa only [Pi.neg_def, neg_neg] using
      (hasDerivAt_neg_gaussianPDFReal (R * quantileLinear θ x)).neg
  have houter := hφ.hasFDerivAt.comp x ((hasFDerivAt_quantileLinear θ hx).const_mul R)
  have h := (houter.const_mul (R * θ i)).mul hinv
  simp only [Pi.mul_def, Function.comp_def] at h
  convert h using 1
  · funext y
    exact div_eq_mul_inv _ _
  · ext v
    simp only [sub_apply, add_apply,
      smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    ring

variable [DecidableEq ι]

/-- A coordinate linear form evaluated on a coordinate unit vector equals its corresponding
coefficient. -/
theorem coordinateForm_single (c : ι → ℝ) (i : ι) :
    coordinateForm c (Pi.single i 1) = c i := by
  simp [coordinateForm_apply, Pi.single_apply]

/-- The Hessian, as iterated Fréchet derivatives on coordinate vectors. -/
def coordinateHessian (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single j 1)

/-- The coordinate Hessian of the Gaussian functional has its explicit diagonal-minus-rank-one
formula. -/
theorem coordinateHessian_gaussianFunctional (θ : ι → ℝ) (R : ℝ)
    {x : ι → ℝ} (hx : x ∈ probabilityBox) (i j : ι) :
    coordinateHessian (gaussianFunctional θ R) x i j =
      gaussianPDFReal 0 1 (R * quantileLinear θ x) *
        ((if i = j then R * θ i * gaussianCDFChart.symm (x i) else 0) -
          R ^ 3 * quantileLinear θ x * θ i * θ j) /
        (gaussianPDFReal 0 1 (gaussianCDFChart.symm (x i)) *
          gaussianPDFReal 0 1 (gaussianCDFChart.symm (x j))) := by
  have heq : (fun y => fderiv ℝ (gaussianFunctional θ R) y (Pi.single i 1)) =ᶠ[𝓝 x]
      (fun y => functionalGradient θ R y i) := by
    filter_upwards [isOpen_probabilityBox.mem_nhds hx] with y hy
    rw [(hasFDerivAt_gaussianFunctional θ R hy).fderiv, coordinateForm_single]
    rfl
  rw [coordinateHessian, Matrix.of_apply, heq.fderiv_eq,
    (hasFDerivAt_functionalGradient θ R i hx).fderiv]
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, coordinateForm_single]
  have hi := (gaussianPDFReal_pos 0 1 (gaussianCDFChart.symm (x i)) (by norm_num)).ne'
  have hj := (gaussianPDFReal_pos 0 1 (gaussianCDFChart.symm (x j)) (by norm_num)).ne'
  by_cases hij : i = j
  · subst j
    simp only [Pi.single_eq_same, ite_true]
    field_simp
  · rw [Pi.single_eq_of_ne hij, ite_eq_right hij, mul_zero, zero_sub]
    field_simp
    ring

/-- The covariance-weighted Hessian, with the diagonal congruence exhibited.
For NP16's triple the diagonal in the middle is
`diag(p*u,(1-p)*v,-σ^3*w)`, since the covariance diagonal is `(1,1,σ²)`.
No nonsingularity of the covariance is needed for this identity. -/
theorem covariance_hessian_gaussianFunctional (A : Matrix ι ι ℝ) (θ : ι → ℝ) (R : ℝ)
    {x : ι → ℝ} (hx : x ∈ probabilityBox) :
    A ⊙ coordinateHessian (gaussianFunctional θ R) x =
      (R * gaussianPDFReal 0 1 (R * quantileLinear θ x)) •
        (Matrix.diagonal (fun i => (gaussianPDFReal 0 1 (gaussianCDFChart.symm (x i)))⁻¹) *
          (Matrix.diagonal (fun i => A i i * θ i * gaussianCDFChart.symm (x i)) -
            (R ^ 2 * quantileLinear θ x) • (A ⊙ Matrix.vecMulVec θ θ)) *
          Matrix.diagonal (fun i => (gaussianPDFReal 0 1 (gaussianCDFChart.symm (x i)))⁻¹)) := by
  ext i j
  rw [Matrix.hadamard_apply, coordinateHessian_gaussianFunctional θ R hx]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.sub_apply, Matrix.hadamard_apply, Matrix.vecMulVec_apply]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, ite_true, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [Matrix.diagonal_apply_ne _ hij, ite_eq_right hij,
      div_eq_mul_inv, mul_inv_rev]
    ring

end EhrhardGaussian.Ehrhard

end
