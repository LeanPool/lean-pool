/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsEnergy
public import LeanPool.CutoffRigidity.GeneratorIntertwining
public import LeanPool.CutoffRigidity.CurvatureMonotonicity
public import LeanPool.CutoffRigidity.AffineRigidity
public import LeanPool.CutoffRigidity.EuclideanDerivatives
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Euclidean weighted Bochner commutation and integration

These are actual differential identities for the Langevin operator. The
integrated statement keeps its integration-domain hypotheses explicit; it
does not claim the regularity and domain extension for spectral eigenfunctions.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Coordinate mixed partials agree for a C² function. -/
theorem coordinateDerivative_commute {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (i j : Fin d) (x : E) :
    coordinateDerivative i (coordinateDerivative j f) x =
      coordinateDerivative j (coordinateDerivative i f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  unfold coordinateDerivative
  rw [second_fderiv_apply_const hd, second_fderiv_apply_const hd]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq _ _

/-- One coordinate derivative commutes past a repeated coordinate derivative
for C³ functions. -/
theorem coordinateDerivative_triple_commute {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (i j : Fin d) (x : E) :
    coordinateDerivative i (coordinateDerivative j (coordinateDerivative j f)) x =
      coordinateDerivative j (coordinateDerivative j (coordinateDerivative i f)) x := by
  have hDj : ContDiff ℝ 2 (coordinateDerivative j f) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  rw [coordinateDerivative_commute hDj i j]
  have hfun : coordinateDerivative i (coordinateDerivative j f) =
      coordinateDerivative j (coordinateDerivative i f) :=
    funext (coordinateDerivative_commute (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) i j)
  rw [hfun]

/-- The actual Langevin differential expression expanded in standard coordinates. -/
theorem langevin_eq_coordinate_sum (V f : E → ℝ) (x : E) :
    langevinDifferentialOperator V f x =
      (∑ j : Fin d, coordinateDerivative j (coordinateDerivative j f) x) -
        ∑ j : Fin d, coordinateDerivative j V x * coordinateDerivative j f x := by
  rw [langevinDifferentialOperator, euclideanLaplacian, inner_gradient_eq_sum_fderiv_single]
  rfl

/-- The derivative of the actual Laplacian commutes with a coordinate derivative. -/
theorem coordinateDerivative_laplacian {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (i : Fin d) (x : E) :
    coordinateDerivative i (euclideanLaplacian f) x =
      euclideanLaplacian (coordinateDerivative i f) x := by
  have hD2 (j : Fin d) : ContDiff ℝ 1 (coordinateDerivative j (coordinateDerivative j f)) := by
    apply contDiff_coordinateDerivative
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  unfold coordinateDerivative at ⊢
  change fderiv ℝ (fun y => ∑ j : Fin d,
    coordinateDerivative j (coordinateDerivative j f) y) x (EuclideanSpace.single i 1) = _
  rw [fderiv_fun_sum (fun j _ => (hD2 j).differentiable (by norm_num) x)]
  simp only [sum_apply]
  change (∑ j : Fin d, coordinateDerivative i (coordinateDerivative j (coordinateDerivative j f))
    x) = _
  simp_rw [coordinateDerivative_triple_commute hf i]
  rfl

/-- Differentiating the actual gradient drift is the coordinate product rule. -/
theorem coordinateDerivative_gradient_inner {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (i : Fin d) (x : E) :
    coordinateDerivative i (fun y => inner ℝ (gradient V y) (gradient f y)) x =
      ∑ j : Fin d,
        (coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j f x +
          coordinateDerivative j V x * coordinateDerivative i (coordinateDerivative j f) x) := by
  have hDV (j : Fin d) : Differentiable ℝ (coordinateDerivative j V) := by
    apply (contDiff_coordinateDerivative (n := 1) ?_ j).differentiable (by norm_num)
    convert hV using 1
    norm_num
  have hDf (j : Fin d) : Differentiable ℝ (coordinateDerivative j f) := by
    apply (contDiff_coordinateDerivative (n := 1) ?_ j).differentiable (by norm_num)
    convert hf using 1
    norm_num
  have hfun : (fun y => inner ℝ (gradient V y) (gradient f y)) =
      fun y => ∑ j : Fin d, coordinateDerivative j V y * coordinateDerivative j f y := by
    funext y
    exact inner_gradient_eq_sum_fderiv_single V f y
  unfold coordinateDerivative at ⊢
  rw [hfun, fderiv_fun_sum
    (A := fun j y => coordinateDerivative j V y * coordinateDerivative j f y)
    (fun j _ => by fun_prop)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fderiv_fun_mul (hDV j x) (hDf j x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  unfold coordinateDerivative
  ring

/-- The actual weighted Bochner commutator: differentiating the Langevin
operator adds exactly the Hessian-potential drift term. -/
theorem coordinateDerivative_langevin_commutator {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) (i : Fin d) (x : E) :
    coordinateDerivative i (langevinDifferentialOperator V f) x =
      langevinDifferentialOperator V (coordinateDerivative i f) x -
        ∑ j : Fin d,
          coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j f x := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hD2 (j : Fin d) : Differentiable ℝ (coordinateDerivative j (coordinateDerivative j f)) := by
    have hc : ContDiff ℝ 1 (coordinateDerivative j (coordinateDerivative j f)) := by
      apply contDiff_coordinateDerivative
      apply contDiff_coordinateDerivative
      convert hf using 1
      norm_num
    exact hc.differentiable (by norm_num)
  have hLap : Differentiable ℝ (euclideanLaplacian f) := by
    change Differentiable ℝ (fun y => ∑ j : Fin d, coordinateDerivative j (coordinateDerivative j
      f) y)
    fun_prop
  have hInner : Differentiable ℝ (fun y => inner ℝ (gradient V y) (gradient f y)) :=
    (differentiable_gradient_of_contDiff_two hV).inner ℝ
      (differentiable_gradient_of_contDiff_two hf2)
  change fderiv ℝ (fun y => euclideanLaplacian f y - inner ℝ (gradient V y) (gradient f y)) x
    (EuclideanSpace.single i 1) = _
  rw [fderiv_fun_sub (hLap x) (hInner x), sub_apply]
  change coordinateDerivative i (euclideanLaplacian f) x -
    coordinateDerivative i (fun y => inner ℝ (gradient V y) (gradient f y)) x = _
  rw [coordinateDerivative_laplacian hf, coordinateDerivative_gradient_inner hV hf2,
    langevin_eq_coordinate_sum]
  simp_rw [coordinateDerivative_commute hf2 i, Finset.sum_add_distrib]
  unfold euclideanLaplacian coordinateDerivative
  ring

/-- Explicit integration domain for the Bochner calculation. These are
integrability conditions on actual derivatives, not a Bochner identity or
spectral hypothesis. Extending them to spectral eigenfunctions is separate. -/
structure BochnerIntegrationDomain (V f : E → ℝ) : Prop where
  first_second : ∀ i j : Fin d, Integrable
    (fun x => coordinateDerivative i f x * coordinateDerivative j (coordinateDerivative i f) x)
    (gibbsMeasure volume V)
  first_third : ∀ i j : Fin d, Integrable
    (fun x => coordinateDerivative i f x *
      coordinateDerivative j (coordinateDerivative j (coordinateDerivative i f)) x)
    (gibbsMeasure volume V)
  second_square : ∀ i j : Fin d, Integrable
    (fun x => (coordinateDerivative j (coordinateDerivative i f) x) ^ 2)
    (gibbsMeasure volume V)
  first_drift_second : ∀ i j : Fin d, Integrable
    (fun x => coordinateDerivative i f x * coordinateDerivative j V x *
      coordinateDerivative j (coordinateDerivative i f) x)
    (gibbsMeasure volume V)
  potential_hessian : ∀ i j : Fin d, Integrable
    (fun x => coordinateDerivative i f x * coordinateDerivative i (coordinateDerivative j V) x *
      coordinateDerivative j f x) (gibbsMeasure volume V)

/-- Weighted integrated Bochner identity in coordinate form, proved from
the actual commutator and coordinate Gibbs integration by parts. -/
theorem integrated_bochner_coordinate_identity {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) (hdom : BochnerIntegrationDomain V f) :
    -(∫ x, inner ℝ (gradient f x) (gradient (langevinDifferentialOperator V f) x)
      ∂gibbsMeasure volume V) =
      (∫ x, ∑ i : Fin d, ∑ j : Fin d,
        (coordinateDerivative j (coordinateDerivative i f) x) ^ 2 ∂gibbsMeasure volume V) +
      (∫ x, ∑ i : Fin d, ∑ j : Fin d,
        coordinateDerivative i f x * coordinateDerivative i (coordinateDerivative j V) x *
          coordinateDerivative j f x ∂gibbsMeasure volume V) := by
  let A (i : Fin d) (x : E) := coordinateDerivative i f x *
    langevinDifferentialOperator V (coordinateDerivative i f) x
  let B (i j : Fin d) (x : E) := coordinateDerivative i f x *
    coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j f x
  let C (i j : Fin d) (x : E) := (coordinateDerivative j (coordinateDerivative i f) x) ^ 2
  have hAi (i : Fin d) : Integrable (A i) (gibbsMeasure volume V) := by
    have heq : A i = fun x =>
        (∑ j : Fin d, coordinateDerivative i f x *
          coordinateDerivative j (coordinateDerivative j (coordinateDerivative i f)) x) -
        ∑ j : Fin d, coordinateDerivative i f x * coordinateDerivative j V x *
          coordinateDerivative j (coordinateDerivative i f) x := by
      funext x
      dsimp only [A]
      rw [langevin_eq_coordinate_sum, mul_sub, Finset.mul_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [heq]
    exact (integrable_finsetSum _ (fun j _ => hdom.first_third i j)).sub
      (integrable_finsetSum _ (fun j _ => hdom.first_drift_second i j))
  have hBi (i : Fin d) : Integrable (fun x => ∑ j : Fin d, B i j x) (gibbsMeasure volume V) :=
    integrable_finsetSum _ (fun j _ => hdom.potential_hessian i j)
  have hCi (i : Fin d) : Integrable (fun x => ∑ j : Fin d, C i j x) (gibbsMeasure volume V) :=
    integrable_finsetSum _ (fun j _ => hdom.second_square i j)
  have henergy (i : Fin d) : (∫ x, A i x ∂gibbsMeasure volume V) =
      -(∫ x, ∑ j : Fin d, C i j x ∂gibbsMeasure volume V) := by
    have hDi : ContDiff ℝ 2 (coordinateDerivative i f) := by
      apply contDiff_coordinateDerivative
      convert hf using 1
      norm_num
    have hh := integral_mul_langevin_eq_neg_gradient_inner (hV.differentiable (by norm_num))
      (hDi.differentiable (by norm_num)) hDi
      (hdom.first_second i) (hdom.first_third i)
      (fun j => by simpa only [pow_two, coordinateDerivative] using hdom.second_square i j)
      (hdom.first_drift_second i)
    simp_rw [inner_gradient_eq_sum_fderiv_single] at hh
    simpa only [A, C, coordinateDerivative, pow_two] using hh
  have hIA : (∫ x, ∑ i : Fin d, A i x ∂gibbsMeasure volume V) =
      -(∫ x, ∑ i : Fin d, ∑ j : Fin d, C i j x ∂gibbsMeasure volume V) := by
    rw [integral_finsetSum _ (fun i _ => hAi i), integral_finsetSum _ (fun i _ => hCi i)]
    simp_rw [henergy]
    exact Finset.sum_neg_distrib (fun i : Fin d => ∫ x, ∑ j : Fin d, C i j x ∂gibbsMeasure volume V)
  have hpoint (x : E) :
      inner ℝ (gradient f x) (gradient (langevinDifferentialOperator V f) x) =
        (∑ i : Fin d, A i x) - ∑ i : Fin d, ∑ j : Fin d, B i j x := by
    calc
      _ = ∑ i : Fin d, (A i x - ∑ j : Fin d, B i j x) := by
        rw [inner_gradient_eq_sum_fderiv_single]
        apply Finset.sum_congr rfl
        intro i hi
        change coordinateDerivative i f x * coordinateDerivative i (langevinDifferentialOperator V
          f) x = _
        rw [coordinateDerivative_langevin_commutator hV hf, mul_sub, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [B]
        ring
      _ = _ := Finset.sum_sub_distrib (fun i => A i x) (fun i => ∑ j : Fin d, B i j x)
  have hIL := integral_congr_ae (μ := gibbsMeasure volume V) (Filter.Eventually.of_forall hpoint)
  rw [integral_sub (integrable_finsetSum _ (fun i _ => hAi i))
    (integrable_finsetSum _ (fun i _ => hBi i)), hIA] at hIL
  change -(_) = _ + _
  dsimp only [B, C] at hIL
  linarith

/-- Contract the actual potential Hessian against an arbitrary vector. -/
theorem hessian_vector_coordinate_contraction {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (x z : E) :
    (∑ i : Fin d, z i * (∑ j : Fin d,
      coordinateDerivative i (coordinateDerivative j V) x * z j)) =
      fderiv ℝ (fderiv ℝ V) x z z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ V) x :=
    ((hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [bilinear_euclidean_coordinate_expansion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show coordinateDerivative i (coordinateDerivative j V) x =
    fderiv ℝ (fderiv ℝ V) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) from
      second_fderiv_apply_const hd _ _]
  ring

/-- The coordinate potential term is the actual Hessian evaluated twice on
the actual gradient, without an abstract tensor standing in for it. -/
theorem hessian_gradient_coordinate_contraction {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (f : E → ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x) =
      ∑ i : Fin d, ∑ j : Fin d,
        coordinateDerivative i f x * coordinateDerivative i (coordinateDerivative j V) x *
          coordinateDerivative j f x := by
  have h := (hessian_vector_coordinate_contraction hV x (gradient f x)).symm
  have hg (i : Fin d) : coordinateDerivative i f x = gradient f x i :=
    fderiv_single_eq_gradient_coordinate f x i
  simpa only [← hg, Finset.mul_sum, mul_assoc] using h

/-- The weighted integrated Bochner identity in Hessian form. Its domain
premises remain explicit; the paper's spectral-domain extension is separate. -/
theorem integrated_bochner_identity {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) (hdom : BochnerIntegrationDomain V f) :
    -(∫ x, inner ℝ (gradient f x) (gradient (langevinDifferentialOperator V f) x)
      ∂gibbsMeasure volume V) =
      (∫ x, ∑ i : Fin d, ∑ j : Fin d,
        (coordinateDerivative j (coordinateDerivative i f) x) ^ 2 ∂gibbsMeasure volume V) +
      (∫ x, fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x) ∂gibbsMeasure volume V) := by
  simpa only [← hessian_gradient_coordinate_contraction hV f] using
    integrated_bochner_coordinate_identity hV hf hdom

/-- The actual Hessian curvature lower bound yields the integrated Bochner
inequality used in the rigidity proof, on the explicit integration domain. -/
theorem integrated_bochner_inequality {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) (hdom : BochnerIntegrationDomain V f)
    (hgrad : Integrable (fun x => ‖gradient f x‖ ^ 2) (gibbsMeasure volume V))
    (ρ : ℝ) (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ρ * (∫ x, ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) +
      (∫ x, ∑ i : Fin d, ∑ j : Fin d,
        (coordinateDerivative j (coordinateDerivative i f) x) ^ 2 ∂gibbsMeasure volume V) ≤
      -(∫ x, inner ℝ (gradient f x) (gradient (langevinDifferentialOperator V f) x)
        ∂gibbsMeasure volume V) := by
  have hHint : Integrable
      (fun x => fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x))
      (gibbsMeasure volume V) := by
    simp_rw [hessian_gradient_coordinate_contraction hV f]
    exact integrable_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => hdom.potential_hessian i j))
  have hbound := integral_mono (hgrad.const_mul ρ) hHint (fun x => hHess x (gradient f x))
  rw [integral_const_mul] at hbound
  rw [integrated_bochner_identity hV hf hdom]
  linarith

/-- At equality of curvature and eigenvalue, the paper's cancellation forces
the integrated squared Hessian to vanish on the explicit smooth domain. -/
theorem eigenfunction_hessian_square_integral_zero {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) (hdom : BochnerIntegrationDomain V f)
    (hgrad : Integrable (fun x => ‖gradient f x‖ ^ 2) (gibbsMeasure volume V))
    (ρ : ℝ) (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) :
    (∫ x, ∑ i : Fin d, ∑ j : Fin d,
      (coordinateDerivative j (coordinateDerivative i f) x) ^ 2 ∂gibbsMeasure volume V) = 0 := by
  have hfun : langevinDifferentialOperator V f = fun x => -ρ * f x := funext heigen
  have hg (x : E) : gradient (langevinDifferentialOperator V f) x = -ρ • gradient f x := by
    apply ext_inner_right ℝ
    intro y
    rw [inner_gradient_left, hfun, fderiv_const_mul ((hf.differentiable (by norm_num)) x),
      smul_apply, smul_eq_mul, inner_smul_left, inner_gradient_left]
    simp
  have hI : -(∫ x, inner ℝ (gradient f x) (gradient (langevinDifferentialOperator V f) x)
      ∂gibbsMeasure volume V) = ρ * (∫ x, ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) := by
    simp_rw [hg, inner_smul_right, real_inner_self_eq_norm_sq]
    rw [integral_const_mul]
    ring
  have hbound := integrated_bochner_inequality hV hf hdom hgrad ρ hHess
  rw [hI] at hbound
  have hnonneg : 0 ≤ (∫ x, ∑ i : Fin d, ∑ j : Fin d,
      (coordinateDerivative j (coordinateDerivative i f) x) ^ 2 ∂gibbsMeasure volume V) :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => sq_nonneg _)))
  linarith

/-- Full support and continuity upgrade the Bochner integral cancellation
to vanishing of the genuine Hessian at every point, on the explicit domain. -/
theorem smooth_eigenfunction_hessian_zero {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) (hdom : BochnerIntegrationDomain V f)
    (hgrad : Integrable (fun x => ‖gradient f x‖ ^ 2) (gibbsMeasure volume V))
    (ρ : ℝ) (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) (x : E) :
    fderiv ℝ (fderiv ℝ f) x = 0 := by
  have hcontD (i j : Fin d) : Continuous (coordinateDerivative j (coordinateDerivative i f)) := by
    have hc : ContDiff ℝ 1 (coordinateDerivative j (coordinateDerivative i f)) := by
      apply contDiff_coordinateDerivative
      apply contDiff_coordinateDerivative
      convert hf using 1
      norm_num
    exact hc.continuous
  have hcont : Continuous (fun y => ∑ i : Fin d, ∑ j : Fin d,
      (coordinateDerivative j (coordinateDerivative i f) y) ^ 2) := by fun_prop
  have hint : Integrable (fun y => ∑ i : Fin d, ∑ j : Fin d,
      (coordinateDerivative j (coordinateDerivative i f) y) ^ 2) (gibbsMeasure volume V) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hdom.second_square i j))
  have hz := eigenfunction_hessian_square_integral_zero hV hf hdom hgrad ρ hHess heigen
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun y => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))) hint).mp hz
  have hfun : (fun y => ∑ i : Fin d, ∑ j : Fin d,
      (coordinateDerivative j (coordinateDerivative i f) y) ^ 2) = fun _ => (0 : ℝ) := by
    apply gibbsMeasure_eq_of_ae_eq volume hV.continuous.measurable hcont continuous_const
    simpa only [Pi.zero_def] using hae
  have hentries (i j : Fin d) : coordinateDerivative j (coordinateDerivative i f) x = 0 := by
    have hx := congrFun hfun x
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
        Finset.sum_nonneg (fun j _ => sq_nonneg
          (coordinateDerivative j (coordinateDerivative i f) x)))).mp hx i (Finset.mem_univ i)
    have helem := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => sq_nonneg
        (coordinateDerivative j (coordinateDerivative i f) x))).mp hrow j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp helem
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have hcoef (i j : Fin d) :
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0 := by
    rw [← second_fderiv_apply_const hd]
    exact hentries j i
  ext u v
  change fderiv ℝ (fderiv ℝ f) x u v = 0
  rw [bilinear_euclidean_coordinate_expansion]
  simp_rw [hcoef]
  simp

/-- The paper's final affine conclusion from Bochner rigidity, for actual
smooth eigenfunctions satisfying the explicit integration-domain conditions.
No statement about the full spectral eigenspace is asserted here. -/
theorem smooth_eigenfunction_is_affine {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) (hdom : BochnerIntegrationDomain V f)
    (hgrad : Integrable (fun x => ‖gradient f x‖ ^ 2) (gibbsMeasure volume V))
    (ρ : ℝ) (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) (x : E) :
    f x = f 0 + inner ℝ (gradient f 0) x := by
  exact eq_affine_inner_gradient_of_contDiff_two_of_hessian_zero
    (hf.of_le (by norm_num)) (smooth_eigenfunction_hessian_zero hV hf hdom hgrad ρ hHess heigen) x

/-- Continuous compactly supported test functions lie in the actual Gibbs
integration domain, without a global moment assumption. -/
theorem integrable_gibbs_of_continuous_hasCompactSupport {V g : E → ℝ}
    (hV : Continuous V) (hg : Continuous g) (hcomp : HasCompactSupport g) :
    Integrable g (gibbsMeasure volume V) := by
  rw [integrable_gibbsMeasure_iff volume hV.measurable]
  have hc : Continuous (fun x => Real.exp (-V x) * g x) := (Real.continuous_exp.comp hV.neg).mul hg
  have hs : HasCompactSupport (fun x => Real.exp (-V x) * g x) := by
    simpa only [Pi.mul_def] using hcomp.mul_left (f := fun x => Real.exp (-V x))
  exact hc.integrable_of_hasCompactSupport hs

/-- All explicit Bochner integration premises are discharged on the
compactly supported C³ core. Passing from this core to L² spectral
eigenfunctions still requires cutoff/domain convergence estimates. -/
theorem bochnerIntegrationDomain_of_hasCompactSupport {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) (hcomp : HasCompactSupport f) :
    BochnerIntegrationDomain V f := by
  have hf1 (i : Fin d) : ContDiff ℝ 2 (coordinateDerivative i f) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hf2 (i j : Fin d) : ContDiff ℝ 1 (coordinateDerivative j (coordinateDerivative i f)) := by
    apply contDiff_coordinateDerivative
    convert hf1 i using 1
    norm_num
  have hf3 (i j k : Fin d) : ContDiff ℝ 0
      (coordinateDerivative k (coordinateDerivative j (coordinateDerivative i f))) := by
    apply contDiff_coordinateDerivative
    convert hf2 i j using 1
    norm_num
  have hV1 (i : Fin d) : ContDiff ℝ 1 (coordinateDerivative i V) := by
    apply contDiff_coordinateDerivative
    convert hV using 1
    norm_num
  have hV2 (i j : Fin d) : ContDiff ℝ 0 (coordinateDerivative i (coordinateDerivative j V)) := by
    apply contDiff_coordinateDerivative
    convert hV1 j using 1
    norm_num
  have hc1 (i : Fin d) : HasCompactSupport (coordinateDerivative i f) :=
    hcomp.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hc2 (i j : Fin d) : HasCompactSupport (coordinateDerivative j (coordinateDerivative i f)) :=
    (hc1 i).fderiv_apply ℝ (EuclideanSpace.single j 1)
  have hcf1 (i : Fin d) := (hf1 i).continuous
  have hcf2 (i j : Fin d) := (hf2 i j).continuous
  have hcf3 (i j k : Fin d) := (hf3 i j k).continuous
  have hcV1 (i : Fin d) := (hV1 i).continuous
  have hcV2 (i j : Fin d) := (hV2 i j).continuous
  constructor
  · intro i j
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    simpa only [Pi.mul_def] using (hc1 i).mul_right (f' := coordinateDerivative j
      (coordinateDerivative i f))
  · intro i j
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    simpa only [Pi.mul_def] using (hc1 i).mul_right
      (f' := coordinateDerivative j (coordinateDerivative j (coordinateDerivative i f)))
  · intro i j
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    simpa only [pow_two, Pi.mul_def] using (hc2 i j).mul_right
      (f' := coordinateDerivative j (coordinateDerivative i f))
  · intro i j
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    simpa only [Pi.mul_def] using ((hc1 i).mul_right
      (f' := coordinateDerivative j V)).mul_right
        (f' := coordinateDerivative j (coordinateDerivative i f))
  · intro i j
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    simpa only [Pi.mul_def] using ((hc1 i).mul_right
      (f' := coordinateDerivative i (coordinateDerivative j V))).mul_right
        (f' := coordinateDerivative j f)

end CutoffRigidity
