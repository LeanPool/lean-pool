/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Composition
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.WeakDerivative
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Piola
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.LipschitzBall
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.ChainRule
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Products
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Basic.Real.Star

/-!
# Weak inverse-Hessian generator identities

The two weak integration-by-parts identities for the inverse-Hessian generator
`L f = tr((∇²u)⁻¹ ∇²f) − DV(∇u)(∇f)` of a `C^{1,1}` Monge–Ampère solution `u`
(`det ∇²u = e^{−u + V(∇u)}` almost everywhere, the exponent Lipschitz), tested against `C²`
compactly supported
functions with the weight `e^{−u}` (Letwin arXiv:2607.24164v1, equation (2.2), weak `C^{1,1}`
counterpart):

* `integral_mul_generator_eq_neg_energy`, `integral_mul_generator_eq_neg_energy'`.

The proof applies the weak inverse-Hessian divergence identity and the inverse-Hessian integrability
interface of
`Analysis/Matrix/Piola.lean` to weighted gradient tests. Its one-use supports are private: the
Lipschitz constant and
compact support of the test `η e^{−u} ∂ᵢw`, its almost-everywhere derivative (with two coordinate
lemmas reproduced
privately from `Analysis/BakryEmery/Hessian/Weak.lean`, which requires only differentiability of the
gradient at the
point), and a finite inverse-matrix cancellation. The almost-everywhere chain derivative of the
Monge–Ampère exponent `−u + V(∇u)` is also public as `ae_fderiv_mongeAmpere_exponent`,
for use by the actual-source weak Monge–Ampère identification bridge. No `C²` regularity of `u` or
`w` is used. These are supporting identities; Letwin Theorems 2.5 and 1.2
are not proved here.
The inverse-calculus assembly additionally proves weak (2.5) from a Lipschitz log-det
representative, a Lipschitz gradient and a given weak local-L2 Hessian tensor. No C2 regularity or
desired inverse formula is assumed. The fixed-object weak Piola row divergence
`ae_inverse_hessian_row_divergence_of_weak_derivative` is also proved here; the second evolution
(2.6) and
bounded testing are in `IntegrationByParts/WeakHessian/{Weighted,Testing,Directional}`. These
analytic identities are separate from the quantitative moment-potential bounds, whose producers
retain their own source hypotheses.
-/

@[expose] public section

noncomputable section

section WeightedGradientTest

open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis

/-- Compactly supported weighted derivative test for the weak Letwin generator identity.
No global bound on the gradient of w is assumed. -/
private theorem exists_lipschitz_compact_exp_gradient_test {n : ℕ}
    {u w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w)) (i : Fin n) :
    ∃ L : NNReal,
      LipschitzWith L (fun x => η x * Real.exp (-u x) *
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) ∧
      HasCompactSupport (fun x => η x * Real.exp (-u x) *
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  let γ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => η x * Real.exp (-u x)
  have hγ : ContDiff ℝ 1 γ := hη.mul hu.neg.exp
  have hγc : HasCompactSupport γ := hηc.mul_right
  obtain ⟨Kγ, hKγ⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hγc hγ one_ne_zero
  let e : EuclideanSpace ℝ (Fin n) :=
    EuclideanSpace.basisFun (Fin n) ℝ i
  have hcoord :
      LipschitzWith (‖(innerSL ℝ) e‖₊ * Gw)
        (fun x => fderiv ℝ w x e) := by
    simpa [Function.comp_def, inner_gradient_left] using
      (((innerSL ℝ) e).lipschitzWith.comp hGw)
  obtain ⟨⟨L, hL⟩, _⟩ :=
    FunctionalInequalities.Probability.Diffusion.exists_lipschitzWith_smul_of_locallyLipschitz
      hKγ hγc hcoord.locallyLipschitz
  refine ⟨L, ?_, ?_⟩
  · simpa only [smul_eq_mul] using hL
  · exact hγc.mul_right

end FunctionalInequalities.Analysis

end WeightedGradientTest

section WeightedGradientTestDerivative

open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis

/-- Almost-everywhere derivative of the actual weighted gradient test for Letwin (2.2).
Only C1 u and eta and a Lipschitz gradient of w are needed. -/
private theorem ae_fderiv_exp_gradient_test {n : ℕ}
    {u w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hη : ContDiff ℝ 1 η)
    {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w)) (i : Fin n) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j : Fin n,
      fderiv ℝ (fun y => η y * Real.exp (-u y) *
        fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        Real.exp (-u x) *
          (fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ j) *
              fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) -
            η x * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) *
              fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) +
            η x * hessianMatrix w x j i) := by
  filter_upwards [hGw.ae_differentiableAt
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hx
  have hux : DifferentiableAt ℝ u x :=
    (hu.differentiable one_ne_zero).differentiableAt
  have hηx : DifferentiableAt ℝ η x :=
    (hη.differentiable one_ne_zero).differentiableAt
  have hfd : DifferentiableAt ℝ (fderiv ℝ w) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ i) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i)).differentiableAt
  have hcomponent :
      DifferentiableAt ℝ
        (fun y => fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x :=
    hfd.clm_apply hc
  have he :
      fderiv ℝ (fun y => η y * Real.exp (-u y) *
        fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x =
      (η x * Real.exp (-u x)) •
          fderiv ℝ
            (fun y => fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x +
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) •
          (η x • (Real.exp (-u x) • (-fderiv ℝ u x)) +
            Real.exp (-u x) • fderiv ℝ η x) :=
    ((hηx.hasFDerivAt.mul hux.hasFDerivAt.neg.exp).mul
      hcomponent.hasFDerivAt).fderiv
  intro j
  rw [he]
  simp only [_root_.add_apply, _root_.smul_apply, _root_.neg_apply, smul_eq_mul]
  rw [hessian_coord_of_gradient_diff (i := j) (j := i) hx]
  ring

end FunctionalInequalities.Analysis

end WeightedGradientTestDerivative


section InverseMatrixCancellation

open scoped BigOperators

namespace FunctionalInequalities.Analysis

/-- Finite inverse-Hessian cancellation for the weak Letwin (2.2) test.
All analytic data are replaced by arbitrary finite matrices and coordinate vectors. -/
private theorem sum_inv_gradient_test_sub_chain_eq {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hdet : IsUnit A.det)
    (a : ℝ) (b p q r : Fin n → ℝ) :
    (∑ i, ∑ j, A⁻¹ i j * (b j * r i - a * p j * r i + a * B j i)) -
      (∑ i, ∑ j, A⁻¹ i j * (-p j + ∑ k, A j k * q k) * (a * r i)) =
      (∑ i, ∑ j, A⁻¹ i j * b i * r j) +
        a * ((A⁻¹ * B).trace - ∑ i, q i * r i) := by
  have hsymm (i j : Fin n) : A⁻¹ i j = A⁻¹ j i := by
    simpa only [star_trivial] using hA.inv.apply j i
  have hcancel (i : Fin n) :
      (∑ j, A⁻¹ i j * (∑ k, A j k * q k)) = q i := by
    calc
      (∑ j, A⁻¹ i j * (∑ k, A j k * q k)) =
          ∑ k, (∑ j, A⁻¹ i j * A j k) * q k := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = q i := by
        simp only [← Matrix.mul_apply, Matrix.nonsing_inv_mul A hdet]
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
        simp
  have henergy :
      (∑ i, ∑ j, A⁻¹ i j * b j * r i) =
        ∑ i, ∑ j, A⁻¹ i j * b i * r j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j i]
  have htrace :
      (A⁻¹ * B).trace = ∑ i, ∑ j, A⁻¹ i j * B j i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  calc
    (∑ i, ∑ j, A⁻¹ i j * (b j * r i - a * p j * r i + a * B j i)) -
        (∑ i, ∑ j, A⁻¹ i j * (-p j + ∑ k, A j k * q k) * (a * r i)) =
        ∑ i, ∑ j,
          (A⁻¹ i j * b j * r i + a * (A⁻¹ i j * B j i) -
            a * (A⁻¹ i j * (∑ k, A j k * q k) * r i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, ∑ j, A⁻¹ i j * b j * r i) +
          a * (∑ i, ∑ j, A⁻¹ i j * B j i) -
          a * (∑ i, q i * r i) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, hcancel]
    _ = (∑ i, ∑ j, A⁻¹ i j * b i * r j) +
          a * ((A⁻¹ * B).trace - ∑ i, q i * r i) := by
      rw [henergy, ← htrace]
      ring

end FunctionalInequalities.Analysis

end InverseMatrixCancellation

section GeneratorIdentities

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

private abbrev coord {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)

private def weightedTest {n : ℕ}
    (u a f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  a x * Real.exp (-u x) * coord f i x

private def energyDensity {n : ℕ}
    (u a f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j * coord a i x * coord f j x) *
    Real.exp (-u x)

private def generatorDensity {n : ℕ}
    (u V a f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  a x * (((hessianMatrix u x)⁻¹ * hessianMatrix f x).trace -
    fderiv ℝ V (gradient u x) (gradient f x)) * Real.exp (-u x)

private lemma coord_eq_gradient {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    coord f i x = gradient f x i := by
  calc
    coord f i x =
        ⟪gradient f x, EuclideanSpace.basisFun (Fin n) ℝ i⟫ :=
      inner_gradient_left.symm
    _ = gradient f x i :=
      EuclideanSpace.inner_basisFun_real (Fin n) (gradient f x) i

private lemma drift_eq_sum {n : ℕ}
    (u V f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ V (gradient u x) (gradient f x) =
      ∑ i, coord V i (gradient u x) * coord f i x := by
  calc
    fderiv ℝ V (gradient u x) (gradient f x) =
        ⟪gradient V (gradient u x), gradient f x⟫ :=
      inner_gradient_left.symm
    _ = ∑ i, ⟪gradient V (gradient u x) i, gradient f x i⟫ :=
      PiLp.inner_apply _ _
    _ = ∑ i, coord V i (gradient u x) * coord f i x := by
      simp only [Real.inner_apply, coord_eq_gradient]

private lemma measurable_coord {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) :
    Measurable (coord f i) :=
  (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.basisFun (Fin n) ℝ i)).measurable.comp
      (measurable_fderiv ℝ f)

private lemma coord_bound {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖coord f i x‖ ≤ (L : ℝ) * ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ :=
  ((fderiv ℝ f x).le_opNorm
    (EuclideanSpace.basisFun (Fin n) ℝ i)).trans
      (mul_le_mul_of_nonneg_right
        (norm_fderiv_le_of_lipschitz ℝ hf)
        (norm_nonneg (EuclideanSpace.basisFun (Fin n) ℝ i)))

private lemma continuous_coord {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (coord f i) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

private lemma continuous_coord_of_lipschitz_gradient {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hf : LipschitzWith L (gradient f)) (i : Fin n) :
    Continuous (coord f i) := by
  change Continuous
    (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i))
  simpa [Function.comp_def, inner_gradient_left] using
    ((((innerSL ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i)).lipschitzWith.comp
      hf).continuous)

private lemma integrable_inv_test_derivative {n : ℕ}
    {u F ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G L : NNReal} (hG : LipschitzWith G (gradient u))
    (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (hψ : LipschitzWith L ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin n) :
    Integrable (fun x => (hessianMatrix u x)⁻¹ i j * coord ψ j x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact integrable_inv_hessianMatrix_mul_of_bounded_compact hG hF hdet
    (measurable_coord ψ j)
    (hψc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ j))
    (coord_bound hψ j) i j

private lemma integrable_inv_chain_test {n : ℕ}
    {u F ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G LF L : NNReal} (hG : LipschitzWith G (gradient u))
    (hF : LipschitzWith LF F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (hψ : LipschitzWith L ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin n) :
    Integrable
      (fun x => (hessianMatrix u x)⁻¹ i j * coord F j x * ψ x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuous hψ.continuous
  have hb (x : EuclideanSpace ℝ (Fin n)) :
      ‖coord F j x * ψ x‖ ≤
        ((LF : ℝ) * ‖EuclideanSpace.basisFun (Fin n) ℝ j‖) * C := by
    rw [norm_mul]
    exact mul_le_mul (coord_bound hF j x) (hC x) (norm_nonneg _)
      (mul_nonneg LF.coe_nonneg (norm_nonneg _))
  have hi :=
    integrable_inv_hessianMatrix_mul_of_bounded_compact hG hF.continuous hdet
      ((measurable_coord F j).mul hψ.continuous.measurable)
      (hψc.mul_left :
        HasCompactSupport (fun x => coord F j x * ψ x))
      hb i j
  change Integrable
    (fun x => (hessianMatrix u x)⁻¹ i j * (coord F j x * ψ x))
    (volume : Measure (EuclideanSpace ℝ (Fin n))) at hi
  simpa only [mul_assoc] using hi

private lemma integrable_energy {n : ℕ}
    {u F a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (ha : ∀ i, Continuous (coord a i))
    (hf : ∀ j, Continuous (coord f j))
    (hc : ∀ i j, HasCompactSupport
      (fun x => coord a i x * coord f j x * Real.exp (-u x))) :
    Integrable (energyDensity u a f)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hi (i j : Fin n) :
      Integrable
        (fun x => (hessianMatrix u x)⁻¹ i j *
          (coord a i x * coord f j x * Real.exp (-u x)))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hcont : Continuous
        (fun x => coord a i x * coord f j x * Real.exp (-u x)) :=
      ((ha i).mul (hf j)).mul
        (Real.continuous_exp.comp hu.continuous.neg)
    obtain ⟨C, hC⟩ := (hc i j).exists_bound_of_continuous hcont
    exact integrable_inv_hessianMatrix_mul_of_bounded_compact
      hG hF hdet hcont.measurable (hc i j) hC i j
  have hs := integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))
  have he :
      (fun x => ∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
        (coord a i x * coord f j x * Real.exp (-u x))) =
        energyDensity u a f := by
    funext x
    simp only [energyDensity, Finset.sum_mul, mul_assoc]
  rw [he] at hs
  exact hs

private lemma smooth_test_derivative {n : ℕ}
    {u a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (ha : ContDiff ℝ 1 a)
    (hf : ContDiff ℝ 2 f) (i j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    coord (weightedTest u a f i) j x =
      Real.exp (-u x) *
        (coord a j x * coord f i x -
          a x * coord u j x * coord f i x +
          a x * hessianMatrix f x j i) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hfdx := (hfd.differentiable one_ne_zero).differentiableAt (x := x)
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ i) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i)).differentiableAt
  have hcomponent : DifferentiableAt ℝ (coord f i) x :=
    hfdx.clm_apply hc
  have hcoord :
      coord (coord f i) j x = hessianMatrix f x j i := by
    have he := congrArg
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.basisFun (Fin n) ℝ j))
      (fderiv_clm_apply hfdx hc)
    change
      fderiv ℝ
        (fun y => fderiv ℝ f y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
        (EuclideanSpace.basisFun (Fin n) ℝ j) =
          hessianMatrix f x j i
    simpa [hessianMatrix, bilinearIteratedFDerivTwo] using he
  have hux : DifferentiableAt ℝ u x :=
    hu.differentiable one_ne_zero x
  have hax : DifferentiableAt ℝ a x :=
    ha.differentiable one_ne_zero x
  have he :
      fderiv ℝ (weightedTest u a f i) x =
        (a x * Real.exp (-u x)) • fderiv ℝ (coord f i) x +
          coord f i x •
            (a x • (Real.exp (-u x) • (-fderiv ℝ u x)) +
              Real.exp (-u x) • fderiv ℝ a x) :=
    ((hax.hasFDerivAt.mul hux.hasFDerivAt.neg.exp).mul
      hcomponent.hasFDerivAt).fderiv
  change fderiv ℝ (weightedTest u a f i) x
    (EuclideanSpace.basisFun (Fin n) ℝ j) = _
  rw [he]
  simp only [_root_.add_apply, _root_.smul_apply, _root_.neg_apply, smul_eq_mul]
  change
    (a x * Real.exp (-u x)) * coord (coord f i) j x +
      coord f i x *
        (a x * (Real.exp (-u x) * (-coord u j x)) +
          Real.exp (-u x) * coord a j x) = _
  rw [hcoord]
  ring

private lemma assemble_generator {n : ℕ}
    {u V a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (ht : ∀ i, ∃ L : NNReal,
      LipschitzWith L (weightedTest u a f i) ∧
        HasCompactSupport (weightedTest u a f i))
    (hd : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j,
      coord (weightedTest u a f i) j x =
        Real.exp (-u x) *
          (coord a j x * coord f i x -
            a x * coord u j x * coord f i x +
            a x * hessianMatrix f x j i))
    (hE : Integrable (energyDensity u a f)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∫ x, generatorDensity u V a f x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -∫ x, energyDensity u a f x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let F : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => -u x + V (gradient u x)
  let P (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    (hessianMatrix u x)⁻¹ i j * coord (weightedTest u a f i) j x
  let Q (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    (hessianMatrix u x)⁻¹ i j * coord F j x * weightedTest u a f i x
  let S (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    ∑ i, ∑ j, (P i j x - Q i j x)
  have hP (i j : Fin n) :
      Integrable (P i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨L, hL, hc⟩ := ht i
    exact integrable_inv_test_derivative hG hF.continuous hdet hL hc i j
  have hQ (i j : Fin n) :
      Integrable (Q i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨L, hL, hc⟩ := ht i
    exact integrable_inv_chain_test hG hF hdet hL hc i j
  have hrowInt (i : Fin n) :
      Integrable (fun x => ∑ j, (P i j x - Q i j x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_finsetSum Finset.univ (fun j _ => (hP i j).sub (hQ i j))
  have hS : Integrable S (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_finsetSum Finset.univ (fun i _ => hrowInt i)
  have hrow (i : Fin n) :
      (∫ x, ∑ j, (P i j x - Q i j x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 0 := by
    rw [integral_finsetSum Finset.univ
      (f := fun j x => P i j x - Q i j x)
      (fun j _ => (hP i j).sub (hQ i j))]
    have hs (j : Fin n) :
        (∫ x, P i j x - Q i j x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
            (∫ x, P i j x) - ∫ x, Q i j x :=
      integral_sub (hP i j) (hQ i j)
    simp only [hs, Finset.sum_sub_distrib]
    apply sub_eq_zero.mpr
    obtain ⟨L, hL, hc⟩ := ht i
    exact sum_integral_inv_hessianMatrix_mul_fderiv_eq hu hG hF hdet hL hc i
  have hz : (∫ x, S x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 0 := by
    change (∫ x, ∑ i, ∑ j, (P i j x - Q i j x)) = 0
    rw [integral_finsetSum Finset.univ
      (f := fun i x => ∑ j, (P i j x - Q i j x))
      (fun i _ => hrowInt i)]
    simp only [hrow, Finset.sum_const_zero]
  have hdall :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ i j,
        coord (weightedTest u a f i) j x =
          Real.exp (-u x) *
            (coord a j x * coord f i x -
              a x * coord u j x * coord f i x +
              a x * hessianMatrix f x j i) :=
    ae_all_iff.mpr hd
  have heq :
      S =ᵐ[volume] (fun x => energyDensity u a f x + generatorDensity u V a f x) := by
    filter_upwards [hdall, ae_fderiv_mongeAmpere_exponent hu hG hV,
      hG.ae_differentiableAt
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))),
      hdet] with x hxD hxF hxG hxdet
    have hA := hessianMatrix_isHermitian_of_differentiableAt_gradient hu hxG
    have hunit : IsUnit (hessianMatrix u x).det := by
      rw [hxdet]
      exact isUnit_iff_ne_zero.mpr (Real.exp_ne_zero _)
    have hc := sum_inv_gradient_test_sub_chain_eq
      (hessianMatrix u x) (hessianMatrix f x) hA hunit
      (a x) (fun i => coord a i x) (fun i => coord u i x)
      (fun i => coord V i (gradient u x)) (fun i => coord f i x)
    calc
      S x =
          Real.exp (-u x) *
            ((∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
                (coord a j x * coord f i x -
                  a x * coord u j x * coord f i x +
                  a x * hessianMatrix f x j i)) -
              (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
                (-coord u j x +
                  ∑ k, hessianMatrix u x j k * coord V k (gradient u x)) *
                (a x * coord f i x))) := by
        dsimp only [S]
        rw [mul_sub]
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [P, Q]
        rw [hxD i j]
        have hj :
            coord F j x =
              -coord u j x +
                ∑ k, hessianMatrix u x j k * coord V k (gradient u x) :=
          hxF j
        rw [hj]
        dsimp only [weightedTest]
        ring
      _ = energyDensity u a f x + generatorDensity u V a f x := by
        rw [hc]
        dsimp only [energyDensity, generatorDensity]
        rw [drift_eq_sum u V f x]
        ring
  have hcombined :
      Integrable (fun x => energyDensity u a f x + generatorDensity u V a f x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hS.congr heq
  have hgen : Integrable (generatorDensity u V a f)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hi := hcombined.sub hE
    change Integrable
      (fun x => (energyDensity u a f x + generatorDensity u V a f x) -
        energyDensity u a f x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) at hi
    simpa only [add_sub_cancel_left] using hi
  have hsum :
      (∫ x, energyDensity u a f x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
        (∫ x, generatorDensity u V a f x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 0 := by
    rw [← integral_add hE hgen, ← integral_congr_ae heq]
    exact hz
  linarith

private lemma energy_swap {n : ℕ}
    {u a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) :
    energyDensity u a f =ᵐ[volume] energyDensity u f a := by
  classical
  filter_upwards [hG.ae_differentiableAt
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hx
  have hA := (hessianMatrix_isHermitian_of_differentiableAt_gradient hu hx).inv
  have hs (i j : Fin n) :
      (hessianMatrix u x)⁻¹ j i = (hessianMatrix u x)⁻¹ i j := by
    simpa only [star_trivial] using hA.apply i j
  unfold energyDensity
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs i j]
  ring

/-- C1 compact multiplier version of the closed weak generator identity.
Weak-source support for Letwin A.4; no new regularity hypothesis on u. -/
theorem integral_mul_generator_eq_neg_energy_of_contDiff_one {n : ℕ}
    {u V w η : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) {LF : NNReal}
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ x,
        η x *
            (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
              fderiv ℝ V (gradient u x) (gradient w x)) *
          Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      -∫ x,
          (∑ i,
              ∑ j,
                (hessianMatrix u x)⁻¹ i j * fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
                  fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) *
            Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hη1 : ContDiff ℝ 1 η := hη
  have hE : Integrable (energyDensity u η w) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply
      integrable_energy hu hG hF.continuous hdet (continuous_coord hη1) (continuous_coord hw)
    intro i j
    exact
      ((hηc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).mul_right :
          HasCompactSupport (fun x => coord η i x * coord w j x)).mul_right
  exact
    assemble_generator hu hG hV hF hdet
      (fun i => exists_lipschitz_compact_exp_gradient_test hu hη1 hηc hGw i)
      (fun i => ae_fderiv_exp_gradient_test hu hη1 hGw i) hE

/-- **The Hessian-metric generator at `C^{1,1}` is symmetric** (Letwin arXiv:2607.24164v1 (2.2),
weak form): for the `C^{1,1}` Monge–Ampère solution `u` (`det ∇²u = e^{−u + V(∇u)}` a.e., the right
side
Lipschitz), with `L f := tr((∇²u)⁻¹ ∇²f) − DV(∇u)(∇f)`, every `w ∈ C¹` with Lipschitz gradient and
every `η ∈ C²` with compact
support satisfy `∫ η (L w) e^{−u} = −∫ ⟨(∇²u)⁻¹ ∇η, ∇w⟩ e^{−u}`. -/
theorem integral_mul_generator_eq_neg_energy {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ x,
        η x *
            (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
              fderiv ℝ V (gradient u x) (gradient w x)) *
          Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      -∫ x,
          (∑ i,
              ∑ j,
                (hessianMatrix u x)⁻¹ i j * fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
                  fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) *
            Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact
    integral_mul_generator_eq_neg_energy_of_contDiff_one hu hG hV hF hdet hw hGw
      (hη.of_le (by norm_num)) hηc

/-- The same identity with the roles exchanged (`η` inside the generator, `w` outside). -/
theorem integral_mul_generator_eq_neg_energy' {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ x, w x * (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      -∫ x, (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
          fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hηfd : ContDiff ℝ 1 (fderiv ℝ η) :=
    hη.fderiv_right (by norm_num)
  have ht (i : Fin n) :
      ∃ L : NNReal, LipschitzWith L (weightedTest u w η i) ∧
        HasCompactSupport (weightedTest u w η i) := by
    have hc : HasCompactSupport (weightedTest u w η i) :=
      (hηc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).mul_left
    have hd : ContDiff ℝ 1 (weightedTest u w η i) :=
      (hw.mul hu.neg.exp).mul (hηfd.clm_apply contDiff_const)
    obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hd one_ne_zero
    exact ⟨L, hL, hc⟩
  have hd (i : Fin n) :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j,
        coord (weightedTest u w η i) j x =
          Real.exp (-u x) *
            (coord w j x * coord η i x -
              w x * coord u j x * coord η i x +
              w x * hessianMatrix η x j i) :=
    Eventually.of_forall (fun x j => smooth_test_derivative hu hw hη i j x)
  have hE : Integrable (energyDensity u w η)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_energy hu hG hF.continuous hdet
      (continuous_coord_of_lipschitz_gradient hGw) (continuous_coord hη1)
    intro i j
    exact
      ((hηc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).mul_left :
        HasCompactSupport (fun x => coord w i x * coord η j x)).mul_right
  change (∫ x, generatorDensity u V w η x) =
    -∫ x, energyDensity u η w x
  calc
    (∫ x, generatorDensity u V w η x) =
        -∫ x, energyDensity u w η x :=
      assemble_generator hu hG hV hF hdet ht hd hE
    _ = -∫ x, energyDensity u η w x := by
      rw [integral_congr_ae (energy_swap (a := w) (f := η) hu hG)]

end FunctionalInequalities.Analysis

end GeneratorIdentities

section GeneratorIntegrability

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

private lemma weak_generator_compact_hessian_entry {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hηc : HasCompactSupport η) (i j : Fin n) :
    HasCompactSupport (fun x => hessianMatrix η x i j) := by
  change HasCompactSupport
    ((fun A : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      A (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) ∘
      fderiv ℝ (fderiv ℝ η))
  exact ((hηc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).comp_left (by simp)

private lemma weak_generator_compact_apply {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hgc : HasCompactSupport g) :
    HasCompactSupport (fun x => A x (g x)) := by
  apply hgc.mono'
  intro x hx
  by_contra hn
  have hz : g x = 0 := image_eq_zero_of_notMem_tsupport hn
  apply hx
  change A x (g x) = 0
  rw [hz, map_zero]

/-- Genuine integrability for the weak inverse-Hessian generator, its exchanged
test density and the absolute RHS of the Hessian-increment energy estimate. -/
theorem integrable_weak_generator_densities {n : ℕ}
    {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : Continuous (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : Continuous w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    Integrable (fun x => η x *
      (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => w x *
      (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x =>
      |η x + (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have he : Continuous (fun x => Real.exp (-u x)) :=
    Real.continuous_exp.comp hu.neg
  have hDV : Continuous (fun x => fderiv ℝ V (gradient u x)) :=
    (hV.continuous_fderiv one_ne_zero).comp hG.continuous
  have hgradη : Continuous (gradient η) :=
    BakryEmery.continuous_gradient (hη.of_le (by norm_num))
  have htrace :
      ∀ {f a : EuclideanSpace ℝ (Fin n) → ℝ},
        (∀ i j, Integrable
          (fun x => (hessianMatrix u x)⁻¹ i j *
            (a x * hessianMatrix f x j i))
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
        Integrable
          (fun x => a x * ((hessianMatrix u x)⁻¹ * hessianMatrix f x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro f a hi
    have hs := integrable_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))
    apply hs.congr
    filter_upwards [] with x
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hηe : Continuous (fun x => η x * Real.exp (-u x)) :=
    hη.continuous.mul he
  have hηec : HasCompactSupport (fun x => η x * Real.exp (-u x)) :=
    hηc.mul_right
  obtain ⟨B, hB⟩ := hηec.exists_bound_of_continuous hηe
  have hwt : Integrable
      (fun x => (η x * Real.exp (-u x)) *
        ((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply htrace
    intro i j
    apply integrable_inv_hessianMatrix_mul_of_bounded_compact hG hF hdet
      (hηe.measurable.mul (measurable_hessianMatrix_entry w j i))
      hηec.mul_right (C := B * (Gw : ℝ)) ?_ i j
    intro x
    change ‖(η x * Real.exp (-u x)) * hessianMatrix w x j i‖ ≤ B * (Gw : ℝ)
    rw [norm_mul]
    exact mul_le_mul (hB x)
      (norm_hessianMatrix_entry_le_of_lipschitz_gradient hGw x j i)
      (norm_nonneg _) (le_trans (norm_nonneg _) (hB x))
  have hwd : Integrable
      (fun x => η x * fderiv ℝ V (gradient u x) (gradient w x) *
        Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    ((hη.continuous.mul (hDV.clm_apply hGw.continuous)).mul he).integrable_of_hasCompactSupport
      (hηc.mul_right.mul_right)
  have hfirst : Integrable
      (fun x => η x *
        (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
          fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply (hwt.sub hwd).congr
    filter_upwards [] with x
    change
      (η x * Real.exp (-u x)) *
          ((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
        η x * fderiv ℝ V (gradient u x) (gradient w x) * Real.exp (-u x) =
      η x * (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x)
    ring
  have hηdc : HasCompactSupport
      (fun x => fderiv ℝ V (gradient u x) (gradient η x)) :=
    weak_generator_compact_apply (fun x => fderiv ℝ V (gradient u x))
      (BakryEmery.hasCompactSupport_gradient hηc)
  have hprimed :
      ∀ {a : EuclideanSpace ℝ (Fin n) → ℝ}, Continuous a →
        Integrable
          (fun x => a x *
            (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
              fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a ha
    have hat : Integrable
        (fun x => (a x * Real.exp (-u x)) *
          ((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply htrace
      intro i j
      have hc : Continuous
          (fun x => (a x * Real.exp (-u x)) * hessianMatrix η x j i) :=
        (ha.mul he).mul (hessian_entry_continuous hη j i)
      have hcc : HasCompactSupport
          (fun x => (a x * Real.exp (-u x)) * hessianMatrix η x j i) :=
        (weak_generator_compact_hessian_entry hηc j i).mul_left
      obtain ⟨C, hC⟩ := hcc.exists_bound_of_continuous hc
      exact integrable_inv_hessianMatrix_mul_of_bounded_compact
        hG hF hdet hc.measurable hcc hC i j
    have had : Integrable
        (fun x => a x * fderiv ℝ V (gradient u x) (gradient η x) *
          Real.exp (-u x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      ((ha.mul (hDV.clm_apply hgradη)).mul he).integrable_of_hasCompactSupport
        (hηdc.mul_left.mul_right)
    apply (hat.sub had).congr
    filter_upwards [] with x
    change
      (a x * Real.exp (-u x)) *
          ((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        a x * fderiv ℝ V (gradient u x) (gradient η x) * Real.exp (-u x) =
      a x * (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x)
    ring
  refine ⟨hfirst, hprimed hw, ?_⟩
  have hLη : Integrable
      (fun x => (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [one_mul] using
      (hprimed (a := fun _ => (1 : ℝ)) continuous_const)
  have hsum : Integrable
      (fun x => (η x +
        (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
          fderiv ℝ V (gradient u x) (gradient η x))) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply ((hηe.integrable_of_hasCompactSupport hηec).add hLη).congr
    filter_upwards [] with x
    exact (add_mul _ _ _).symm
  simpa only [abs_mul, Real.abs_exp] using hsum.abs

end FunctionalInequalities.Analysis

end GeneratorIntegrability


section WeakInverseDerivative
open MeasureTheory Set Filter Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise
open FunctionalInequalities.Probability.Stein
namespace FunctionalInequalities.Analysis

/-- A Lipschitz log-det representative and the given weak Hessian tensor
produce the explicit weak inverse derivative. This is weak Letwin (2.5), not (2.6). -/
theorem hasWeakDerivAlong_inverse_hessian_of_logdet {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hG : LipschitzWith G (gradient u)) (hF : LipschitzWith LF F)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧ Real.log (hessianMatrix u x).det = F x)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
        (fun x => -(((hessianMatrix u x)⁻¹ *
          (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
          (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  classical
  let H := hessianMatrix u
  let R : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ := fun x => (H x)⁻¹
  have hbound (a b : Fin n) : MemLp (fun x => H x a b)
      (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_top_of_bound (measurable_hessianMatrix_entry u a b).aestronglyMeasurable
      (G : ℝ) (Filter.Eventually.of_forall fun x =>
        norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x a b)
  have hC (k i j : Fin n) := exists_weak_hessian_adjugate_derivative hbound hT k i j
  choose dc hdc hdc2 using hC
  have hExp : Continuous (fun x => Real.exp (-F x)) := Real.continuous_exp.comp hF.continuous.neg
  have hExpTop (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (fun x => Real.exp (-F x)) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hExp.continuousOn
    exact memLp_top_of_bound hExp.aestronglyMeasurable C
      ((ae_restrict_mem hS.measurableSet).mono fun x hx => hC x hx)
  have hInv (i j : Fin n) : (fun x => R x i j) =ᵐ[
      (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => Real.exp (-F x) * (H x).adjugate i j) := by
    filter_upwards [hdata] with x hx
    have hdet : (H x).det = Real.exp (F x) := by
      rw [← hx.2, Real.exp_log hx.1.det_pos]
    simp only [R, Matrix.inv_def, hdet, Ring.inverse_eq_inv, Matrix.smul_apply,
      smul_eq_mul, Real.exp_neg]
  have hRtop (i j : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (fun x => R x i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    MemLp.ae_eq (ae_restrict_of_ae (hInv i j).symm)
      ((hExpTop S hS).fun_mul ((memLp_hessian_adjugate_top hG i j).restrict S))
  let DR : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun k x => Matrix.of fun a b =>
      (-Real.exp (-F x) * fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ k)) *
        (H x).adjugate a b + Real.exp (-F x) * dc k a b x
  have hD (k i j : Fin n) :
      HasWeakDerivAlong (fun x => R x i j) (fun x => DR k x i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => DR k x i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    have hs := hasWeakDerivAlong_exp_neg_of_lipschitz hF
      (EuclideanSpace.basisFun (Fin n) ℝ k)
    have hp := hs.1.mul_of_locally_bounded (hdc k i j) hExpTop
      (fun S _ => (memLp_hessian_adjugate_top hG i j).restrict S) hs.2 (hdc2 k i j)
    exact ⟨hp.1.congr_ae (hInv i j).symm Filter.EventuallyEq.rfl, hp.2⟩
  have hRA : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), R x * H x = 1 := by
    filter_upwards [hdata] with x hx
    exact Matrix.nonsing_inv_mul (H x) (isUnit_iff_ne_zero.mpr (ne_of_gt hx.1.det_pos))
  intro k i j
  let DT : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun x => Matrix.of fun a b => T x k a b
  have hEq := ae_weak_matrix_inverse_derivative (A := H) (R := R) (DA := DT) (DR := DR k)
    (fun a b => (hT k a b).1) (fun a b => (hD k a b).1)
    (fun a b S _ => (hbound a b).restrict S) hRtop
    (fun a b => (hT k a b).2) (fun a b => (hD k a b).2) hRA
  have hij : (fun x => DR k x i j) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => -((R x * DT x * R x) i j)) := by
    filter_upwards [hEq] with x hx
    simpa only [Matrix.neg_apply] using congrArg (fun M => M i j) hx
  refine ⟨(hD k i j).1.congr_ae Filter.EventuallyEq.rfl hij, ?_, hRtop i j⟩
  intro S hS
  exact MemLp.ae_eq (ae_restrict_of_ae hij) ((hD k i j).2 S hS)

end FunctionalInequalities.Analysis
end WeakInverseDerivative

section WeakInverseRowDivergence
open MeasureTheory Set
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis

/--
Weak Piola row divergence of the inverse Hessian at a fixed weak inverse-derivative object: for a C1
potential with Lipschitz gradient whose Hessian determinant is `exp F` a.e. with `F` Lipschitz, each
row of
given inverse-Hessian weak derivatives sums to `-(H⁻¹ ∇F)` a.e., and `H⁻¹ ∇F` is L2 on compact sets.
-/
theorem ae_inverse_hessian_row_divergence_of_weak_derivative {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} (hC1 : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) {LF : NNReal} (hF : LipschitzWith LF F)
    (hdet :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).det = Real.exp (F x))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hInv :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
            (fun x =>
              -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                    (hessianMatrix u x)⁻¹)
                  i j))
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          (∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp
                  (fun x =>
                    -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                          (hessianMatrix u x)⁻¹)
                        i j))
                  2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            ∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ b : Fin n,
      (∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp
              (fun x =>
                ∑ a : Fin n,
                  (hessianMatrix u x)⁻¹ b a *
                    fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ a))
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          (∑ a : Fin n,
              -(((hessianMatrix u x)⁻¹ * (Matrix.of fun c d => T x a c d) *
                    (hessianMatrix u x)⁻¹)
                  b a)) =
            -(∑ a : Fin n,
                (hessianMatrix u x)⁻¹ b a *
                  fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ a)) := by
  intro b
  let R : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ := fun x => (hessianMatrix u x)⁻¹
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let D : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun a x =>
    -((R x * (Matrix.of fun c d => T x a c d) * R x) b a)
  let z : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun a x => R x b a * fderiv ℝ F x (e a)
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∑ a, z a x
  have hFLip : LipschitzWith LF F := hF
  have hDfMeas (a : Fin n) : Measurable (fun x => fderiv ℝ F x (e a)) :=
    (show Continuous (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A (e a)) from
          continuous_id.clm_apply continuous_const).measurable.comp
      (measurable_fderiv ℝ F)
  have hDfBound (a : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ‖fderiv ℝ F x (e a)‖ ≤ (LF : ℝ) := by
    have hh := (fderiv ℝ F x).le_opNorm (e a)
    rw [e.norm_eq_one a, mul_one] at hh
    exact hh.trans (norm_fderiv_le_of_lipschitz ℝ hFLip)
  have hz2 (a : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (z a) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    have hdf2 :
      MemLp (fun x => fderiv ℝ F x (e a)) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      MemLp.of_bound (hDfMeas a).aestronglyMeasurable (LF : ℝ)
        (Filter.Eventually.of_forall (hDfBound a))
    exact ((hInv a b a).2.2 S hS).fun_mul hdf2
  have hg2 (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    exact memLp_finsetSum Finset.univ (fun a _ => hz2 a S hS)
  have hzLocal (a : Fin n) :
    LocallyIntegrable (z a) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hz2 a S hS).integrable (by norm_num)
  have hgLocal : LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_finsetSum Finset.univ (fun a _ => hzLocal a)
  have hDLocal (a : Fin n) :
    LocallyIntegrable (D a) (volume : Measure (EuclideanSpace ℝ (Fin n))) := (hInv a b a).1.2.1
  have hsumLocal :
    LocallyIntegrable (fun x => ∑ a, D a x) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_finsetSum Finset.univ (fun a _ => hDLocal a)
  refine ⟨hg2, ?_⟩
  apply ae_eq_of_integral_contDiff_smul_eq hsumLocal hgLocal.neg
  intro ψ hψ hψc
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨Lψ, hψLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ1 one_ne_zero
  have hPiola := sum_integral_inv_hessianMatrix_mul_fderiv_eq hC1 hG hFLip hdet hψLip hψc b
  have hDi (a : Fin n) :
    Integrable (fun x => D a x * ψ x) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul, mul_comm] using
      (hDLocal a).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
  have hzi (a : Fin n) :
    Integrable (fun x => z a x * ψ x) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul, mul_comm] using
      (hzLocal a).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
  have hweak : (∑ a, ∫ x, R x b a * fderiv ℝ ψ x (e a)) = -(∑ a, ∫ x, D a x * ψ x) := by
    calc
      _ = ∑ a, -(∫ x, D a x * ψ x) := by
        apply Finset.sum_congr rfl
        intro a _
        exact (hInv a b a).1.2.2 ψ hψ1 hψc
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hID : (∫ x, (∑ a, D a x) * ψ x) = ∑ a, ∫ x, D a x * ψ x := by
    simp only [Finset.sum_mul]
    exact integral_finsetSum Finset.univ (fun a _ => hDi a)
  have hIz : (∫ x, g x * ψ x) = ∑ a, ∫ x, z a x * ψ x := by
    change (∫ x, (∑ a, z a x) * ψ x) = _
    simp only [Finset.sum_mul]
    exact integral_finsetSum Finset.univ (fun a _ => hzi a)
  have hEq : (∫ x, (∑ a, D a x) * ψ x) = -(∫ x, g x * ψ x) := by
    rw [hID, hIz]
    change (∑ a, ∫ x, R x b a * fderiv ℝ ψ x (e a)) = (∑ a, ∫ x, z a x * ψ x) at hPiola
    linarith only [hweak, hPiola]
  simpa only [smul_eq_mul, Pi.neg_apply, mul_neg, integral_neg, mul_comm] using hEq

end FunctionalInequalities.Analysis
end WeakInverseRowDivergence
