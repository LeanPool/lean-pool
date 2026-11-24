/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalProductCurrents
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateWedgeAssoc
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ClosedProductCurrents
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrents
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicPullback
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialIndependence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.CoordinateDensityGeometry
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothPshHessian
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothDDCHessianPositivity

/-!
# `dd^c`, closedness and the Bedford--Taylor products of local currents

For the currents of bidimension `(q,q)` of `Pending.LocalProductCurrents` (linear maps from the
constant `(q,q)`-forms `Λ_q` to the distributions on an open `U ⊆ ℂⁿ`), this file proves the
positivity and closedness part of `bt:recursive-product` (`demailly-cadg:III.3.2`).

* **Coordinates.**  Fix the standard real basis `b_a` of `ℂⁿ` with coordinate forms `e^a`, and put
  `P_{ab} = Π₁₁(e^a ∧ e^b ∘ i)`, a real `(1,1)`-form, symmetric in `a, b` (`isOneOne_coeffForm`,
  `coeffForm_comm`).  For a `C²` function, `dd^c u(z) = -(1/4π) ∑_{a,b} ∂_a∂_b u(z) P_{ab}`
  (`smoothDDC_eq_sum`).
* **`dd^c` of a current**: `(dd^c S)(γ) = -(1/4π) ∑_{a,b} ∂_a ∂_b S(γ ∧ P_{ab})` (`ddc`); on a test
  function `(dd^c S)(γ)(φ) = S(γ ∧ dd^c φ)` (`ddc_apply_apply`).
* **Closedness** (`IsClosedCurrent`): `∑_a ∂_a S(γ ∧ Π₁₁(e^a ∧ ℓ)) = 0` for every real linear form
  `ℓ` and every `γ ∈ Λ_q`.  This is `⟨S, d(φ ℓ ∧ γ)⟩ = 0`, the `(q+1,q+1)`-part of
  `d(φ ℓ ∧ γ) = dφ ∧ ℓ ∧ γ` being `∑_a ∂_aφ Π₁₁(e^a ∧ ℓ) ∧ γ`.  `IsClosedCurrent.ddc_eq_zero`
  (`dd^c S = 0` for closed `S`); `isClosedCurrent_ddc` (`dd^c S` is closed for every `S`: the
  derivatives `∂_c∂_a∂_b` are symmetric and the cyclic sum of `Π₁₁(e^c ∧ ℓ) ∧ P_{ab}` vanishes,
  `cyclic_testForm_coeffForm`, by associativity of the exterior product).
* **Product rule** (`IsClosedCurrent.sum_mulTest_dTest`): for closed `S` and smooth `g`,
  `dd^c(g S) = dd^c g ∧ S`; `ddcMul_apply_of_contDiff`.
* **Positivity** (`IsPositive.isPositive_ddc_mulBorel`): for `T` positive and closed and `u`
    locally
  bounded PSH on `U` (extended by zero), `dd^c(u T)` is positive: radial regularization `u_j ↓ u`
  on a relatively compact neighbourhood of the supports
    (`exists_decreasingMollifierApproximation`),
  the smooth case (`IsPositive.sum_hess_nonneg`) and bounded convergence for the coefficient
  measures of `T`.
* **The recursion** (`btProduct`, `isPositive_btProduct`): `B(u₀, …, u_{q-1}; T) =
  dd^c(u₀ dd^c(u₁ ⋯ dd^c(u_{q-1} T)))` is a positive closed current of bidimension `(r,r)` for `T`
  positive closed of bidimension `(r+q, r+q)`; it is unchanged by adding constants to the
    potentials
  (`btProduct_add_const`); in top degree it is a positive Radon measure
  (`exists_measure_btProduct`), in particular for `T = [1]` (`oneCurrent`, positive and closed,
  `exists_measure_btProduct_oneCurrent`).

Not here (the remaining clauses of `bt:recursive-product`): locality on open subsets, agreement
with the smooth wedge product for several smooth potentials at once, and commutation with smooth
closed strongly positive forms.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  LocalProductCurrents CoordinateWedgeAssoc ClosedProductCurrents

variable {n : ℕ}

local notation "E" => ComplexModel n

/-! ### Coordinates and the coefficient forms of `dd^c` -/

section Coordinates

variable (n) in
/-- The standard real basis `e₀, i e₀, e₁, i e₁, …` of `ℂⁿ`. -/
abbrev realBasis : Module.Basis (Fin (n * 2)) ℝ E := coordinateRealBasis n

variable (n) in
/-- The coordinate linear form `x ↦ x_a` of the standard real basis. -/
def coordCLM (a : Fin (n * 2)) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((realBasis n).coord a)

@[simp] theorem coordCLM_apply (a : Fin (n * 2)) (v : E) :
    coordCLM n a v = (realBasis n).repr v a := rfl

theorem sum_coordCLM_smul (v : E) : ∑ a, coordCLM n a v • realBasis n a = v :=
  (realBasis n).sum_repr v

/-- The two-form `Π₁₁(e^a ∧ ℓ)` for a real linear form `ℓ`. -/
def testForm (a : Fin (n * 2)) (ℓ : E →L[ℝ] ℝ) : RealForm n 2 :=
  pi11 (coordinateWedge (oneForm n (coordCLM n a)) (oneForm n ℓ))

theorem isOneOne_testForm (a : Fin (n * 2)) (ℓ : E →L[ℝ] ℝ) : IsOneOne (testForm a ℓ) :=
  isOneOne_pi11 _

theorem testForm_apply (a : Fin (n * 2)) (ℓ : E →L[ℝ] ℝ) (u v : E) :
    testForm a ℓ ![u, v] = (coordCLM n a u * ℓ v - coordCLM n a v * ℓ u +
      (coordCLM n a (Complex.I • u) * ℓ (Complex.I • v) -
        coordCLM n a (Complex.I • v) * ℓ (Complex.I • u))) / 2 := by
  rw [testForm, pi11_apply, coordinateWedge_one_one_apply, coordinateWedge_one_one_apply]
  simp only [oneForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

variable (n) in
/-- `e^b ∘ i`, the coordinate form composed with the complex structure. -/
def coordJ (b : Fin (n * 2)) : E →L[ℝ] ℝ := (coordCLM n b).comp (complexJ n)

@[simp] theorem coordJ_apply (b : Fin (n * 2)) (v : E) :
    coordJ n b v = coordCLM n b (Complex.I • v) := rfl

/-- The coefficient forms `P_{ab} = Π₁₁(e^a ∧ e^b ∘ i)` of `dd^c`. -/
def coeffForm (a b : Fin (n * 2)) : RealForm n 2 := testForm a (coordJ n b)

theorem isOneOne_coeffForm (a b : Fin (n * 2)) : IsOneOne (coeffForm a b) :=
  isOneOne_testForm a _

theorem coeffForm_apply (a b : Fin (n * 2)) (u v : E) :
    coeffForm a b ![u, v] = (coordCLM n a u * coordCLM n b (Complex.I • v) -
      coordCLM n a v * coordCLM n b (Complex.I • u) -
      coordCLM n a (Complex.I • u) * coordCLM n b v +
      coordCLM n a (Complex.I • v) * coordCLM n b u) / 2 := by
  rw [coeffForm, testForm_apply]
  simp only [coordJ_apply, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
  ring

/-- `P_{ab}` is symmetric in `a, b`. -/
theorem coeffForm_comm (a b : Fin (n * 2)) : coeffForm a b = coeffForm (n := n) b a := by
  ext w
  rw [eq_vec_two w, coeffForm_apply, coeffForm_apply]
  ring

/-- Bilinear expansion in the real basis. -/
theorem sum_sum_coord_mul (H : E →L[ℝ] E →L[ℝ] ℝ) (x y : E) :
    ∑ a, ∑ b, coordCLM n a x * coordCLM n b y * H (realBasis n a) (realBasis n b) = H x y := by
  have hx : H x = ∑ a, coordCLM n a x • H (realBasis n a) := by
    conv_lhs => rw [← sum_coordCLM_smul x]
    simp only [map_sum, map_smul]
  have hy : ∀ a, H (realBasis n a) y =
      ∑ b, coordCLM n b y * H (realBasis n a) (realBasis n b) := by
    intro a
    conv_lhs => rw [← sum_coordCLM_smul y]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hx, _root_.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [_root_.smul_apply, hy, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **`dd^c` in coordinates**: `dd^c u(z) = -(1/4π) ∑_{a,b} ∂_a∂_b u(z) P_{ab}`. -/
theorem smoothDDC_eq_sum {u : E → ℝ} {z : E} (hu : ContDiffAt ℝ 2 u z) :
    smoothDDC u z = ∑ a, ∑ b,
      (-(1 / (4 * Real.pi)) * realHessian u z (realBasis n a) (realBasis n b)) •
        coeffForm a b := by
  have hs : ∀ v w : E, realHessian u z v w = realHessian u z w v := by
    intro v w
    simpa only [realHessian_eq_fderiv] using hu.isSymmSndFDerivAt (by norm_num) v w
  have hH : ∀ v w : E, realHessian u z v w = fderiv ℝ (fderiv ℝ u) z v w :=
    fun v w => realHessian_eq_fderiv u z v w
  ext w
  rw [eq_vec_two w, smoothDDC_apply_eq_realHessian hu]
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, coeffForm_apply]
  set H := fderiv ℝ (fderiv ℝ u) z
  have hexp : ∀ x y : E, ∑ a, ∑ b, coordCLM n a x * coordCLM n b y *
      realHessian u z (realBasis n a) (realBasis n b) = realHessian u z x y := by
    intro x y
    simp only [hH]
    exact sum_sum_coord_mul H x y
  have key : ∀ a b : Fin (n * 2),
      -(1 / (4 * Real.pi)) * realHessian u z (realBasis n a) (realBasis n b) *
        ((coordCLM n a (w 0) * coordCLM n b (Complex.I • w 1) -
          coordCLM n a (w 1) * coordCLM n b (Complex.I • w 0) -
          coordCLM n a (Complex.I • w 0) * coordCLM n b (w 1) +
          coordCLM n a (Complex.I • w 1) * coordCLM n b (w 0)) / 2) =
      -(1 / (8 * Real.pi)) *
        (coordCLM n a (w 0) * coordCLM n b (Complex.I • w 1) *
            realHessian u z (realBasis n a) (realBasis n b) -
          coordCLM n a (w 1) * coordCLM n b (Complex.I • w 0) *
            realHessian u z (realBasis n a) (realBasis n b) -
          coordCLM n a (Complex.I • w 0) * coordCLM n b (w 1) *
            realHessian u z (realBasis n a) (realBasis n b) +
          coordCLM n a (Complex.I • w 1) * coordCLM n b (w 0) *
            realHessian u z (realBasis n a) (realBasis n b)) := by
    intro a b
    field_simp
    ring
  simp_rw [key, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, hexp]
  rw [hs (Complex.I • w 0) (w 1), hs (Complex.I • w 1) (w 0)]
  field_simp
  ring

end Coordinates

/-! ### Derivatives of test functions and distributions -/

section Derivatives

variable {U : Opens (ComplexModel n)}

/-- The derivative of a test function in the direction `v`. -/
abbrev dTest (v : E) (φ : 𝓓(U, ℝ)) : 𝓓(U, ℝ) :=
  TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ

theorem dTest_apply (v : E) (φ : 𝓓(U, ℝ)) (x : E) : dTest v φ x = fderiv ℝ φ x v := by
  rw [dTest, TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact ((φ.contDiff.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv

/-- The derivative of a distribution in the direction `v`. -/
abbrev dDist (v : E) : 𝓓'(U, ℝ) →L[ℝ] 𝓓'(U, ℝ) :=
  Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v

theorem dDist_apply (v : E) (T : 𝓓'(U, ℝ)) (φ : 𝓓(U, ℝ)) : dDist v T φ = -T (dTest v φ) :=
  Distribution.lineDerivCLM_apply

theorem dDist_comm (v w : E) (T : 𝓓'(U, ℝ)) : dDist v (dDist w T) = dDist w (dDist v T) :=
  LocalCurrents.distribution_derivatives_commute U T v w

/-- The derivative `x ↦ Dg(x) v` of a smooth function. -/
def dFun (v : E) (g : E → ℝ) : E → ℝ := fun x => fderiv ℝ g x v

theorem contDiff_dFun {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (v : E) : ContDiff ℝ ∞ (dFun v g) :=
  (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The test function `φ g` for a globally smooth `g`. -/
def mulTest {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (φ : 𝓓(U, ℝ)) : 𝓓(U, ℝ) where
  toFun x := φ x * g x
  contDiff' := φ.contDiff.mul hg
  hasCompactSupport' := φ.hasCompactSupport.mul_right
  tsupport_subset' := (tsupport_mul_subset_left).trans φ.tsupport_subset

@[simp] theorem mulTest_apply {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (φ : 𝓓(U, ℝ)) (x : E) :
    mulTest hg φ x = φ x * g x := rfl

theorem mulTest_add {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (φ ψ : 𝓓(U, ℝ)) :
    mulTest hg (φ + ψ) = mulTest hg φ + mulTest hg ψ := by
  ext x
  simp [add_mul]

/-- **Leibniz rule for test functions**: `∂_v(φ g) = (∂_v φ) g + φ ∂_v g`. -/
theorem dTest_mulTest {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (v : E) (φ : 𝓓(U, ℝ)) :
    dTest v (mulTest hg φ) = mulTest hg (dTest v φ) + mulTest (contDiff_dFun hg v) φ := by
  ext x
  have hφ : DifferentiableAt ℝ (φ : E → ℝ) x :=
    (φ.contDiff.differentiable (by simp)).differentiableAt
  have hgd : DifferentiableAt ℝ g x := (hg.differentiable (by simp)).differentiableAt
  rw [dTest_apply]
  change fderiv ℝ (fun y => φ y * g y) x v =
    mulTest hg (dTest v φ) x + mulTest (contDiff_dFun hg v) φ x
  rw [mulTest_apply, mulTest_apply, dTest_apply]
  have hd : HasFDerivAt (fun y => φ y * g y)
      (φ x • fderiv ℝ g x + g x • fderiv ℝ (φ : E → ℝ) x) x :=
    hφ.hasFDerivAt.mul hgd.hasFDerivAt
  rw [hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, dFun]
  ring

end Derivatives

/-! ### `dd^c` and closedness of currents -/

section DDC

variable {U : Opens (ComplexModel n)} {q : ℕ}

theorem wedgeLM_congr {β β' : RealForm n 2} (hβ : IsOneOne β) (hβ' : IsOneOne β') (h : β = β')
    (γ : formSpan n q) : wedgeLM q hβ γ = wedgeLM q hβ' γ := by
  subst h
  rfl

/-- **`dd^c` of a current** of bidimension `(q+1,q+1)`:
`(dd^c S)(γ) = -(1/4π) ∑_{a,b} ∂_a ∂_b S(γ ∧ P_{ab})`. -/
def ddc (S : LocalProductCurrent n U (q + 1)) : LocalProductCurrent n U q :=
  ∑ a, ∑ b, (-(1 / (4 * Real.pi))) •
    (((dDist (realBasis n a)).comp (dDist (realBasis n b))).toLinearMap ∘ₗ S ∘ₗ
      wedgeLM q (isOneOne_coeffForm a b))

theorem ddc_apply (S : LocalProductCurrent n U (q + 1)) (γ : formSpan n q) :
    ddc S γ = ∑ a, ∑ b, (-(1 / (4 * Real.pi))) •
      dDist (realBasis n a) (dDist (realBasis n b) (S (wedgeLM q (isOneOne_coeffForm a b) γ)))
        := by
  simp [ddc, LinearMap.sum_apply]

/-- On a test function, `(dd^c S)(γ)(φ) = -(1/4π) ∑_{a,b} S(γ ∧ P_{ab})(∂_b ∂_a φ)`. -/
theorem ddc_apply_apply (S : LocalProductCurrent n U (q + 1)) (γ : formSpan n q)
    (φ : 𝓓(U, ℝ)) :
    ddc S γ φ = ∑ a, ∑ b, (-(1 / (4 * Real.pi))) *
      S (wedgeLM q (isOneOne_coeffForm a b) γ)
        (dTest (realBasis n b) (dTest (realBasis n a) φ)) := by
  rw [ddc_apply]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul, dDist_apply, neg_neg]

theorem ddc_add (S S' : LocalProductCurrent n U (q + 1)) : ddc (S + S') = ddc S + ddc S' := by
  ext γ φ
  simp only [ddc_apply_apply, LinearMap.add_apply, _root_.add_apply, mul_add,
    Finset.sum_add_distrib]

theorem ddc_smul (c : ℝ) (S : LocalProductCurrent n U (q + 1)) : ddc (c • S) = c • ddc S := by
  ext γ φ
  simp only [ddc_apply_apply, LinearMap.smul_apply, _root_.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Closedness** of a current of bidimension `(q+1,q+1)`: for every real linear form `ℓ` and
`γ ∈ Λ_q`, `∑_a ∂_a S(γ ∧ Π₁₁(e^a ∧ ℓ)) = 0`, i.e. `⟨S, d(φ ℓ ∧ γ)⟩ = 0` for all test
functions `φ`. -/
def IsClosedCurrent (S : LocalProductCurrent n U (q + 1)) : Prop :=
  ∀ (ℓ : E →L[ℝ] ℝ) (γ : formSpan n q),
    ∑ a, dDist (realBasis n a) (S (wedgeLM q (isOneOne_testForm a ℓ) γ)) = 0

theorem IsClosedCurrent.apply_eq_zero {S : LocalProductCurrent n U (q + 1)}
    (hS : IsClosedCurrent S) (ℓ : E →L[ℝ] ℝ) (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
    ∑ a, S (wedgeLM q (isOneOne_testForm a ℓ) γ) (dTest (realBasis n a) φ) = 0 := by
  have h := congrArg (fun T : 𝓓'(U, ℝ) => T φ) (hS ℓ γ)
  simp only [_root_.sum_apply, dDist_apply, Finset.sum_neg_distrib,
    _root_.zero_apply] at h
  linarith

theorem isClosedCurrent_zero : IsClosedCurrent (0 : LocalProductCurrent n U (q + 1)) := by
  intro ℓ γ
  simp

theorem IsClosedCurrent.add {S S' : LocalProductCurrent n U (q + 1)} (hS : IsClosedCurrent S)
    (hS' : IsClosedCurrent S') : IsClosedCurrent (S + S') := by
  intro ℓ γ
  simp only [LinearMap.add_apply, map_add, Finset.sum_add_distrib, hS ℓ γ, hS' ℓ γ, add_zero]

theorem IsClosedCurrent.smul {S : LocalProductCurrent n U (q + 1)} (hS : IsClosedCurrent S)
    (c : ℝ) : IsClosedCurrent (c • S) := by
  intro ℓ γ
  simp only [LinearMap.smul_apply, map_smul, ← Finset.smul_sum, hS ℓ γ, smul_zero]

/-- `dd^c S = 0` for a closed current `S`. -/
theorem IsClosedCurrent.ddc_eq_zero {S : LocalProductCurrent n U (q + 1)}
    (hS : IsClosedCurrent S) : ddc S = 0 := by
  ext γ : 1
  rw [ddc_apply, LinearMap.zero_apply]
  simp_rw [← Finset.smul_sum]
  rw [Finset.sum_comm]
  have h : ∀ b : Fin (n * 2), ∑ a, dDist (realBasis n a)
      (dDist (realBasis n b) (S (wedgeLM q (isOneOne_coeffForm a b) γ))) = 0 := by
    intro b
    simp_rw [dDist_comm (realBasis n _) (realBasis n b)]
    rw [← map_sum]
    have := hS (coordJ n b) γ
    rw [show (∑ a, dDist (realBasis n a) (S (wedgeLM q (isOneOne_coeffForm a b) γ))) =
      ∑ a, dDist (realBasis n a) (S (wedgeLM q (isOneOne_testForm a (coordJ n b)) γ)) from rfl,
      this, map_zero]
  rw [Finset.sum_eq_zero fun b _ => h b, smul_zero]

end DDC

/-! ### The product rule `dd^c(g S) = dd^c g ∧ S` for closed `S` and smooth `g` -/

section ProductRule

variable {U : Opens (ComplexModel n)} {q : ℕ}

/-- The second derivative `x ↦ D²g(x)(b_a, b_b)`. -/
abbrev hessFun (a b : Fin (n * 2)) (g : E → ℝ) : E → ℝ :=
  dFun (realBasis n a) (dFun (realBasis n b) g)

theorem contDiff_hessFun {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (a b : Fin (n * 2)) :
    ContDiff ℝ ∞ (hessFun a b g) :=
  contDiff_dFun (contDiff_dFun hg _) _

theorem hessFun_apply {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (a b : Fin (n * 2)) (x : E) :
    hessFun a b g x = realHessian g x (realBasis n a) (realBasis n b) := by
  rw [realHessian_eq_fderiv]
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  change fderiv ℝ (fun y => fderiv ℝ g y (realBasis n b)) x (realBasis n a) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- **The product rule.**  For a closed current `S` and a smooth function `g`,
`∑_{a,b} S(γ ∧ P_{ab})(g ∂_b∂_a φ) = ∑_{a,b} S(γ ∧ P_{ab})(φ ∂_a∂_b g)`: the first-order terms
of `∂_b∂_a(g φ)` are killed by closedness. -/
theorem IsClosedCurrent.sum_mulTest_dTest {S : LocalProductCurrent n U (q + 1)}
    (hS : IsClosedCurrent S) {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (γ : formSpan n q)
    (φ : 𝓓(U, ℝ)) :
    ∑ a, ∑ b, S (wedgeLM q (isOneOne_coeffForm a b) γ)
        (mulTest hg (dTest (realBasis n b) (dTest (realBasis n a) φ))) =
      ∑ a, ∑ b, S (wedgeLM q (isOneOne_coeffForm a b) γ)
        (mulTest (contDiff_hessFun hg a b) φ) := by
  have e1 : ∀ a b : Fin (n * 2), mulTest hg (dTest (realBasis n b) (dTest (realBasis n a) φ)) =
      dTest (realBasis n b) (mulTest hg (dTest (realBasis n a) φ)) -
        (dTest (realBasis n a) (mulTest (contDiff_dFun hg (realBasis n b)) φ) -
          mulTest (contDiff_hessFun hg a b) φ) := by
    intro a b
    rw [dTest_mulTest, dTest_mulTest]
    abel
  simp_rw [e1, map_sub, Finset.sum_sub_distrib]
  have hA : ∑ a, ∑ b, S (wedgeLM q (isOneOne_coeffForm a b) γ)
      (dTest (realBasis n b) (mulTest hg (dTest (realBasis n a) φ))) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    have h := hS.apply_eq_zero (coordJ n a) γ (mulTest hg (dTest (realBasis n a) φ))
    rw [← h]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [wedgeLM_congr (isOneOne_coeffForm a b) (isOneOne_testForm b (coordJ n a))
      (coeffForm_comm a b)]
  have hB : ∑ a, ∑ b, S (wedgeLM q (isOneOne_coeffForm a b) γ)
      (dTest (realBasis n a) (mulTest (contDiff_dFun hg (realBasis n b)) φ)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    exact hS.apply_eq_zero (coordJ n b) γ (mulTest (contDiff_dFun hg (realBasis n b)) φ)
  rw [hA, hB]
  ring

/-- `dd^c(g S)` on a test function, for a closed `S` represented by itself on `g φ`:
`-(1/4π) ∑ S(γ ∧ P_{ab})(g ∂_b∂_a φ) = S(γ ∧ dd^c g)(φ)`, written in coordinates. -/
theorem IsClosedCurrent.sum_mulTest_ddc {S : LocalProductCurrent n U (q + 1)}
    (hS : IsClosedCurrent S) {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (γ : formSpan n q)
    (φ : 𝓓(U, ℝ)) :
    ∑ a, ∑ b, (-(1 / (4 * Real.pi))) * S (wedgeLM q (isOneOne_coeffForm a b) γ)
        (mulTest hg (dTest (realBasis n b) (dTest (realBasis n a) φ))) =
      ∑ a, ∑ b, (-(1 / (4 * Real.pi))) * S (wedgeLM q (isOneOne_coeffForm a b) γ)
        (mulTest (contDiff_hessFun hg a b) φ) := by
  simp_rw [← Finset.mul_sum]
  rw [hS.sum_mulTest_dTest hg γ φ]

end ProductRule

/-! ### Positivity of `dd^c(u T)` -/

section Positivity

variable {U : Opens (ComplexModel n)} {q : ℕ}

theorem tsupport_dTest_subset (v : E) (φ : 𝓓(U, ℝ)) : tsupport (dTest v φ) ⊆ tsupport φ := by
  have h : (dTest v φ : E → ℝ) = fun x => fderiv ℝ (φ : E → ℝ) x v := funext (dTest_apply v φ)
  rw [h]
  exact tsupport_fderiv_apply_subset ℝ v

/-- The `dd^c` of a smooth PSH function is a semipositive `(1,1)`-form. -/
theorem isSemipositiveOneOne_smoothDDC {A : Opens (ComplexModel n)} {f : E → ℝ}
    (hs : ContDiffOn ℝ ∞ f A) (hp : PlurisubharmonicOn (fun z => (f z : EReal)) A) {x : E}
    (hx : x ∈ A) : IsSemipositiveOneOne (smoothDDC f x) := by
  have h2 : ContDiffAt ℝ 2 f x :=
    (hs.contDiffAt (A.isOpen.mem_nhds hx)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact SmoothDDCHessianPositivity.isSemipositiveOneOne_smoothDDC_of_leviForm
    h2 (leviForm_nonneg_of_contDiffOn_plurisubharmonicOn hs hp hx)

/-- **Positivity in the smooth case.**  For a positive current `T`, a smooth `g` whose `dd^c` is
semipositive wherever one of the `φ_k` is nonzero, and a strongly positive variable test form
`∑ φ_k γ_k`, the value of `dd^c g ∧ T` on it is `≥ 0`. -/
theorem IsPositive.sum_hess_nonneg {T : LocalProductCurrent n U (q + 1)} (hT : IsPositive T)
    {g : E → ℝ} (hg : ContDiff ℝ ∞ g) {ι : Type} [Fintype ι] (γ : ι → formSpan n q)
    (φ : ι → 𝓓(U, ℝ)) (hγ : ∀ x, ∑ k, φ k x • (γ k : RealForm n (2 * q)) ∈ spCone q)
    (hsemi : ∀ x, (∃ k, φ k x ≠ 0) → IsSemipositiveOneOne (smoothDDC g x)) :
    0 ≤ ∑ k, ∑ a, ∑ b, (-(1 / (4 * Real.pi))) *
      T (wedgeLM q (isOneOne_coeffForm a b) (γ k)) (mulTest (contDiff_hessFun hg a b) (φ k)) := by
  classical
  set c : ℝ := -(1 / (4 * Real.pi))
  let J := ι × Fin (n * 2) × Fin (n * 2)
  let γ' : J → formSpan n (q + 1) := fun j => wedgeLM q (isOneOne_coeffForm j.2.1 j.2.2) (γ j.1)
  let φ' : J → 𝓓(U, ℝ) := fun j => c • mulTest (contDiff_hessFun hg j.2.1 j.2.2) (φ j.1)
  have hpos := hT J γ' φ' (fun x => ?_)
  · have e : ∑ j : J, T (γ' j) (φ' j) = ∑ k, ∑ a, ∑ b, c *
        T (wedgeLM q (isOneOne_coeffForm a b) (γ k)) (mulTest (contDiff_hessFun hg a b) (φ k))
          := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [γ', φ', map_smul, smul_eq_mul]
    rw [← e]
    exact hpos
  · have hsum : ∑ j : J, φ' j x • (γ' j : RealForm n (2 * (q + 1))) =
        coordinateWedge (∑ k, φ k x • (γ k : RealForm n (2 * q))) (smoothDDC g x) := by
      have hc2 : ContDiffAt ℝ 2 g x :=
        hg.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      have hL : ∑ j : J, φ' j x • (γ' j : RealForm n (2 * (q + 1))) =
          ∑ k, ∑ a, ∑ b, (φ k x * (c * realHessian g x (realBasis n a) (realBasis n b))) •
            coordinateWedge (γ k : RealForm n (2 * q)) (coeffForm a b) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        simp only [γ', φ', coe_wedgeLM_apply, FunLike.coe_smul, Pi.smul_apply,
          mulTest_apply, smul_eq_mul, hessFun_apply hg]
        congr 1
        ring
      have hR : coordinateWedge (∑ k, φ k x • (γ k : RealForm n (2 * q))) (smoothDDC g x) =
          ∑ a, ∑ b, ∑ k, (φ k x * (c * realHessian g x (realBasis n a) (realBasis n b))) •
            coordinateWedge (γ k : RealForm n (2 * q)) (coeffForm a b) := by
        rw [smoothDDC_eq_sum hc2, ← wedgeBilin_apply, map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_smul, map_sum, LinearMap.sum_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, LinearMap.smul_apply, wedgeBilin_apply, smul_smul]
        congr 1
        ring
      rw [hL, hR, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
    rw [hsum]
    by_cases hx : ∃ k, φ k x ≠ 0
    · exact wedge_mem_spCone (hγ x) (hsemi x hx)
    · push Not at hx
      simp only [hx, zero_smul, Finset.sum_const_zero]
      rw [← wedgeBilin_apply, map_zero, LinearMap.zero_apply]
      exact (spCone (n := n) (q + 1)).zero_mem

/-- A smooth cutoff taking values in `[0, 1]` and equal to one near a compact set. -/
theorem exists_cutoff_with_bounds {K W : Set E} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x ∈ K, χ =ᶠ[𝓝 x] 1) ∧ tsupport χ ⊆ W ∧
      ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := by
  obtain ⟨f, h0, h1, h01⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (I := 𝓘(ℝ, E))
    (n := (⊤ : ℕ∞)) hW.isClosed_compl hK.isClosed (disjoint_compl_left_iff_subset.mpr hKW)
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, fun x hx => ?_, fun x hx => ?_, h01⟩
  · exact (eventually_nhdsSet_iff_forall.mp h1) x hx
  · by_contra hxW
    exact (notMem_tsupport_iff_eventuallyEq.mpr ((eventually_nhdsSet_iff_forall.mp h0) x hxW)) hx

/-- A smooth cutoff equal to one near a compact set, supported in an open neighbourhood. -/
theorem exists_cutoff {K W : Set E} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x ∈ K, χ =ᶠ[𝓝 x] 1) ∧ tsupport χ ⊆ W := by
  obtain ⟨χ, hχ, hone, hsupp, -⟩ := exists_cutoff_with_bounds hK hW hKW
  exact ⟨χ, hχ, hone, hsupp⟩

/-- The extension by zero of a locally bounded PSH function on `U` is measurable. -/
theorem measurable_indicator_of_isLocallyBoundedPshOn {u : E → ℝ}
    (hu : IsLocallyBoundedPshOn U u) : Measurable ((U : Set E).indicator u) := by
  apply measurable_of_restrict_of_restrict_compl U.isOpen.measurableSet
  · have husc : UpperSemicontinuous
        ((U : Set E).domRestrict (fun z => (u z : EReal))) :=
      upperSemicontinuousOn_iff_restrict.mpr hu.1.upperSemicontinuousOn
    have hm := husc.measurable
    have e : (U : Set E).domRestrict ((U : Set E).indicator u) =
        fun x => EReal.toReal ((U : Set E).domRestrict (fun z => (u z : EReal)) x) := by
      funext x
      simp
    rw [e]
    exact measurable_ereal_toReal.comp hm
  · have e : (U : Set E)ᶜ.domRestrict ((U : Set E).indicator u) = fun _ => 0 := by
      funext x
      exact Set.indicator_of_notMem x.2 _
    rw [e]
    exact measurable_const

theorem isLocallyBoundedOn_indicator {u : E → ℝ} (hu : IsLocallyBoundedPshOn U u) :
    IsLocallyBoundedOn ((U : Set E).indicator u) U := by
  intro K hK hKU
  obtain ⟨C, -, hC⟩ := hu.exists_compact_abs_bound hK hKU
  exact ⟨C, fun x hx => by rw [Set.indicator_of_mem (hKU hx)]; exact hC x hx⟩

/-- **Positivity of `dd^c(u T)`** for a positive closed current `T` of bidimension `(q+1,q+1)` and
    a
locally bounded PSH function `u` on `U` (extended by zero): smooth PSH approximations
`u_j ↓ u` (radial regularization) give `dd^c(u_j T) = dd^c u_j ∧ T ≥ 0` by the product rule, and
bounded convergence for the coefficient measures passes positivity to the limit. -/
theorem IsPositive.isPositive_ddc_mulBorel {T : LocalProductCurrent n U (q + 1)}
    (hT : IsPositive T) (hTc : IsClosedCurrent T) {u : E → ℝ} (hu : IsLocallyBoundedPshOn U u) :
    IsPositive (ddc (mulBorel T ((U : Set E).indicator u))) := by
  classical
  intro ι _ γ φ hγ
  set u' := (U : Set E).indicator u with hu'
  have hum : Measurable u' := measurable_indicator_of_isLocallyBoundedPshOn hu
  have hub : IsLocallyBoundedOn u' U := isLocallyBoundedOn_indicator hu
  set c : ℝ := -(1 / (4 * Real.pi)) with hc
  -- the compact set carrying all the test functions
  set K : Set E := ⋃ k, tsupport (φ k) with hKdef
  have hK : IsCompact K := isCompact_iUnion fun k => (φ k).hasCompactSupport
  have hKU : K ⊆ U := iUnion_subset fun k => (φ k).tsupport_subset
  obtain ⟨V, hVo, hKV, hVcl, hVc⟩ := exists_open_between_and_isCompact_closure hK U.isOpen hKU
  let A : Opens E := ⟨V, hVo⟩
  have hA : RelativelyCompactIn A U := ⟨hVc, hVcl⟩
  obtain ⟨f, hfs, hfanti, hflim⟩ :=
    HolomorphicPullback.exists_decreasingMollifierApproximation hu hA
  obtain ⟨χ, hχ, hχ1, hχA⟩ := exists_cutoff hK hVo hKV
  set g : ℕ → E → ℝ := fun j x => χ x * f j x with hgdef
  have hgs : ∀ j, ContDiff ℝ ∞ (g j) := fun j =>
    contDiff_mul_of_tsupport_subset hVo hχ hχA (hfs j).1
  have hgK : ∀ j, ∀ x ∈ K, g j =ᶠ[𝓝 x] f j := fun j x hx =>
    (hχ1 x hx).mono fun y hy => by simp [g, hy]
  -- uniform bounds on `K`
  obtain ⟨M₁, -, hM₁⟩ := hu.exists_compact_abs_bound hK hKU
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn ((hfs 0).1.continuousOn.mono hKV)
  set M := max M₁ M₂
  have hfb : ∀ j, ∀ x ∈ K, |g j x| ≤ M := by
    intro j x hx
    rw [(hgK j x hx).eq_of_nhds]
    have hxA : x ∈ A := hKV hx
    have h1 : f j x ≤ f 0 x := hfanti x hxA (Nat.zero_le j)
    have h2 : u x ≤ f j x := (hfanti x hxA).le_of_tendsto (hflim x hxA) j
    have hM1 := hM₁ x hx
    have hM2 : |f 0 x| ≤ M₂ := by simpa [Real.norm_eq_abs] using hM₂ x hx
    rw [abs_le] at hM1 hM2 ⊢
    constructor <;> [linarith [le_max_left M₁ M₂]; linarith [le_max_right M₁ M₂]]
  -- notation for the tests and densities
  let ψ : ι → Fin (n * 2) → Fin (n * 2) → 𝓓(U, ℝ) := fun k a b =>
    dTest (realBasis n b) (dTest (realBasis n a) (φ k))
  have hψK : ∀ k a b, tsupport (ψ k a b) ⊆ K := fun k a b =>
    ((tsupport_dTest_subset _ _).trans (tsupport_dTest_subset _ _)).trans
      (subset_iUnion (fun k => tsupport (φ k)) k)
  let γ' : ι → Fin (n * 2) → Fin (n * 2) → formSpan n (q + 1) := fun k a b =>
    wedgeLM q (isOneOne_coeffForm a b) (γ k)
  -- the value to be shown nonnegative
  have htarget : ∑ k, ddc (mulBorel T u') (γ k) (φ k) =
      ∑ k, ∑ a, ∑ b, c * ∫ x, ψ k a b x * (u' x * hT.density (γ' k a b) x) ∂hT.traceMeasure := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ddc_apply_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mulBorel_apply hT hum hub]
  -- the approximating values are nonnegative
  set L : ℕ → ℝ := fun j => ∑ k, ∑ a, ∑ b,
    c * ∫ x, ψ k a b x * (g j x * hT.density (γ' k a b) x) ∂hT.traceMeasure with hLdef
  have hLnonneg : ∀ j, 0 ≤ L j := by
    intro j
    have e : L j = ∑ k, ∑ a, ∑ b, c * T (γ' k a b) (mulTest (hgs j) (ψ k a b)) := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => ?_
      rw [hT.apply_eq_integral_density]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [mulTest_apply]
      ring
    rw [e]
    have e2 : ∀ k, ∑ a, ∑ b, c * T (γ' k a b) (mulTest (hgs j) (ψ k a b)) =
        ∑ a, ∑ b, c * T (γ' k a b) (mulTest (contDiff_hessFun (hgs j) a b) (φ k)) :=
      fun k => hTc.sum_mulTest_ddc (hgs j) (γ k) (φ k)
    simp_rw [e2]
    refine IsPositive.sum_hess_nonneg hT (hgs j) γ φ hγ fun x ⟨k, hk⟩ => ?_
    have hxK : x ∈ K := subset_iUnion (fun k => tsupport (φ k)) k (subset_tsupport _ hk)
    rw [smoothDDC_congr (hgK j x hxK)]
    exact isSemipositiveOneOne_smoothDDC (hfs j).1 (hfs j).2.1 (hKV hxK)
  -- convergence of each coefficient integral
  have hlim : Tendsto L atTop (𝓝 (∑ k, ∑ a, ∑ b,
      c * ∫ x, ψ k a b x * (u' x * hT.density (γ' k a b) x) ∂hT.traceMeasure)) := by
    refine tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun a _ =>
      tendsto_finsetSum _ fun b _ => (Tendsto.const_mul c ?_)
    obtain ⟨C, hC0, hC⟩ := hT.exists_abs_density_le (γ' k a b)
    set fd := hT.density (γ' k a b)
    set ψ₀ := ψ k a b
    have hψ0 : ∀ x, x ∉ K → ψ₀ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hψK k a b h)
    refine tendsto_integral_of_dominated_convergence (fun x => ‖ψ₀ x * (M * C)‖) (fun j => ?_)
      ?_ (fun j => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact ψ₀.continuous.aestronglyMeasurable.mul
        ((hgs j).continuous.aestronglyMeasurable.mul
          (hT.measurable_density _).aestronglyMeasurable)
    · exact (hT.integrable_mul_of_bounded ψ₀.continuous ψ₀.hasCompactSupport ψ₀.tsupport_subset
        aestronglyMeasurable_const ⟨|M * C|, fun x _ => le_rfl⟩).norm
    · by_cases hx : x ∈ K
      · have h1 : |g j x * fd x| ≤ M * C := by
          rw [abs_mul]
          exact mul_le_mul (hfb j x hx) (hC x) (abs_nonneg _) ((abs_nonneg _).trans (hfb j x hx))
        calc ‖ψ₀ x * (g j x * fd x)‖ = |ψ₀ x| * |g j x * fd x| := by
              rw [Real.norm_eq_abs, abs_mul]
          _ ≤ |ψ₀ x| * |M * C| :=
              mul_le_mul_of_nonneg_left (h1.trans (le_abs_self _)) (abs_nonneg _)
          _ = ‖ψ₀ x * (M * C)‖ := by rw [Real.norm_eq_abs, abs_mul (ψ₀ x)]
      · simp [hψ0 x hx]
    · by_cases hx : x ∈ K
      · have hxA : x ∈ A := hKV hx
        have hconv : Tendsto (fun j => g j x) atTop (𝓝 (u' x)) := by
          rw [show u' x = u x from Set.indicator_of_mem (hKU hx) u]
          refine (hflim x hxA).congr fun j => ?_
          exact ((hgK j x hx).eq_of_nhds).symm
        exact (hconv.mul_const (fd x)).const_mul (ψ₀ x)
      · simp only [hψ0 x hx, zero_mul]
        exact tendsto_const_nhds
  rw [htarget]
  exact ge_of_tendsto hlim (Eventually.of_forall hLnonneg)

end Positivity

/-! ### `dd^c S` is closed -/

section Closed

variable {U : Opens (ComplexModel n)} {q : ℕ}

theorem oneForm_compJ (ℓ : E →L[ℝ] ℝ) :
    (oneForm n ℓ).compContinuousLinearMap (complexJ n) = oneForm n (ℓ.comp (complexJ n)) := by
  ext v
  rfl

/-- `Π₁₁(e^c ∧ ℓ) = ½ (e^c ∧ ℓ + (e^c ∘ i) ∧ (ℓ ∘ i))`. -/
theorem testForm_eq (c : Fin (n * 2)) (ℓ : E →L[ℝ] ℝ) :
    testForm c ℓ = (1 / 2 : ℝ) • (coordinateWedge (oneForm n (coordCLM n c)) (oneForm n ℓ) +
      coordinateWedge (oneForm n (coordJ n c)) (oneForm n (ℓ.comp (complexJ n)))) := by
  rw [testForm, pi11, coordinateWedge_compContinuousLinearMap, oneForm_compJ, oneForm_compJ]
  rfl

theorem coordJ_compJ (b : Fin (n * 2)) : (coordJ n b).comp (complexJ n) = -coordCLM n b := by
  ext v
  simp [coordJ, smul_smul]

/-- `P_{ab} = ½ (e^a ∧ (e^b ∘ i) + e^b ∧ (e^a ∘ i))`. -/
theorem coeffForm_eq (a b : Fin (n * 2)) :
    coeffForm a b = (1 / 2 : ℝ) • (coordinateWedge (oneForm n (coordCLM n a)) (oneForm n (coordJ n
      b)) +
      coordinateWedge (oneForm n (coordCLM n b)) (oneForm n (coordJ n a))) := by
  rw [coeffForm, testForm_eq, coordJ_compJ]
  congr 2
  have hneg : oneForm n (-coordCLM n b) = -oneForm n (coordCLM n b) := by
    ext v
    rfl
  rw [hneg, coordinateWedge_neg_right, coordinateWedge_comm_one (oneForm n (coordJ n a))]
  simp

/-- The four-form identity behind `d (dd^c) = 0`:
`∑_{cyc} (x_c ∧ ℓ + y_c ∧ m) ∧ (x_a ∧ y_b + x_b ∧ y_a) = 0` for one-forms. -/
theorem cyclic_four_identity (xa xb xc ya yb yc l m : RealForm n 1) :
    (coordinateWedge (coordinateWedge xc l + coordinateWedge yc m)
        (coordinateWedge xa yb + coordinateWedge xb ya) : RealForm n ((1 + 1) + (1 + 1))) +
      coordinateWedge (coordinateWedge xa l + coordinateWedge ya m)
        (coordinateWedge xb yc + coordinateWedge xc yb) +
      coordinateWedge (coordinateWedge xb l + coordinateWedge yb m)
        (coordinateWedge xc ya + coordinateWedge xa yc) = 0 := by
  simp only [coordinateWedge_add_left, coordinateWedge_add_right]
  rw [coordinateWedge_two_two_swap13 xa l xc yb, coordinateWedge_two_two_swap13 xb l xc ya,
    coordinateWedge_two_two_swap13 xb l xa yc, coordinateWedge_two_two_swap14 yb m xa yc,
    coordinateWedge_two_two_swap14 ya m xb yc, coordinateWedge_two_two_swap14 yb m xc ya]
  abel

/-- The cyclic sum `Π₁₁(e^c ∧ ℓ) ∧ P_{ab} + Π₁₁(e^a ∧ ℓ) ∧ P_{bc} + Π₁₁(e^b ∧ ℓ) ∧ P_{ca}`
vanishes. -/
theorem cyclic_testForm_coeffForm (ℓ : E →L[ℝ] ℝ) (a b c : Fin (n * 2)) :
    (coordinateWedge (testForm c ℓ) (coeffForm a b) : RealForm n (2 + 2)) +
      coordinateWedge (testForm a ℓ) (coeffForm b c) +
      coordinateWedge (testForm b ℓ) (coeffForm c a) = 0 := by
  rw [testForm_eq, testForm_eq, testForm_eq, coeffForm_eq, coeffForm_eq, coeffForm_eq]
  simp only [coordinateWedge_smul_left, coordinateWedge_smul_right, smul_smul, ← smul_add]
  have h := cyclic_four_identity (oneForm n (coordCLM n a)) (oneForm n (coordCLM n b))
    (oneForm n (coordCLM n c)) (oneForm n (coordJ n a)) (oneForm n (coordJ n b))
    (oneForm n (coordJ n c)) (oneForm n ℓ) (oneForm n (ℓ.comp (complexJ n)))
  rw [show (coordinateWedge (oneForm n (coordCLM n b)) (oneForm n (coordJ n c)) +
      coordinateWedge (oneForm n (coordCLM n c)) (oneForm n (coordJ n b)) : RealForm n 2) =
      coordinateWedge (oneForm n (coordCLM n b)) (oneForm n (coordJ n c)) +
      coordinateWedge (oneForm n (coordCLM n c)) (oneForm n (coordJ n b)) from rfl] at h
  convert congrArg (fun F => ((1 / 2 : ℝ) * (1 / 2)) • F) h using 1
  · module

theorem dDist_comm3 (c a b : Fin (n * 2)) (T : 𝓓'(U, ℝ)) :
    dDist (realBasis n c) (dDist (realBasis n a) (dDist (realBasis n b) T)) =
      dDist (realBasis n a) (dDist (realBasis n b) (dDist (realBasis n c) T)) := by
  rw [dDist_comm (realBasis n c) (realBasis n a), dDist_comm (realBasis n c) (realBasis n b)]

/-- **`dd^c S` is closed** for every current `S` of bidimension `(q+2,q+2)`
(`d dd^c = 0`, from `∂_c∂_a∂_b` symmetric and the cyclic identity). -/
theorem isClosedCurrent_ddc (S : LocalProductCurrent n U (q + 2)) : IsClosedCurrent (ddc S) := by
  intro ℓ γ
  set X : Fin (n * 2) → Fin (n * 2) → Fin (n * 2) → 𝓓'(U, ℝ) := fun c a b =>
    S (wedgeLM (q + 1) (isOneOne_coeffForm a b) (wedgeLM q (isOneOne_testForm c ℓ) γ)) with hX
  set D : Fin (n * 2) → Fin (n * 2) → Fin (n * 2) → 𝓓'(U, ℝ) → 𝓓'(U, ℝ) := fun c a b T =>
    dDist (realBasis n c) (dDist (realBasis n a) (dDist (realBasis n b) T)) with hDdef
  have hsum : ∑ c, dDist (realBasis n c) (ddc S (wedgeLM q (isOneOne_testForm c ℓ) γ)) =
      (-(1 / (4 * Real.pi))) • ∑ c, ∑ a, ∑ b, D c a b (X c a b) := by
    simp only [ddc_apply, map_sum, map_smul, Finset.smul_sum, hDdef, hX]
  rw [hsum]
  -- cyclic relabelling of the triple sum
  have hrel : ∀ F : Fin (n * 2) → Fin (n * 2) → Fin (n * 2) → 𝓓'(U, ℝ),
      ∑ c, ∑ a, ∑ b, F c a b = ∑ c, ∑ a, ∑ b, F a b c := by
    intro F
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  have hX0 : ∀ c a b, X c a b + X a b c + X b c a = 0 := by
    intro c a b
    simp only [hX, ← map_add]
    convert S.map_zero using 2
    ext1
    simp only [Submodule.coe_add, coe_wedgeLM_apply, Submodule.coe_zero]
    have h := sum_coordinateWedge_wedge_eq_zero (γ : RealForm n (2 * q))
      ![testForm c ℓ, testForm a ℓ, testForm b ℓ] ![coeffForm a b, coeffForm b c, coeffForm c a]
      (by simpa [Fin.sum_univ_three] using cyclic_testForm_coeffForm ℓ a b c)
    simpa [Fin.sum_univ_three] using h
  have hD : ∀ c a b T, D a b c T = D c a b T := fun c a b T => (dDist_comm3 c a b T).symm
  have hD' : ∀ c a b T, D b c a T = D c a b T := fun c a b T =>
    (hD a b c T).trans (hD c a b T)
  have h3 : (3 : ℝ) • ∑ c, ∑ a, ∑ b, D c a b (X c a b) = 0 := by
    have e1 := hrel (fun c a b => D c a b (X c a b))
    have e2 := hrel (fun c a b => D a b c (X a b c))
    calc (3 : ℝ) • ∑ c, ∑ a, ∑ b, D c a b (X c a b) =
        ∑ c, ∑ a, ∑ b, D c a b (X c a b) + ∑ c, ∑ a, ∑ b, D a b c (X a b c) +
          ∑ c, ∑ a, ∑ b, D b c a (X b c a) := by
          rw [← e1, ← e2, ← e1]
          module
      _ = ∑ c, ∑ a, ∑ b, D c a b (X c a b + X a b c + X b c a) := by
          simp only [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b _ => ?_
          rw [hD c a b, hD' c a b]
          simp only [hDdef, map_add]
      _ = 0 := by
          simp only [hX0, hDdef, map_zero, Finset.sum_const_zero]
  have h3' : ∑ c, ∑ a, ∑ b, D c a b (X c a b) = 0 := by
    have := congrArg (fun T => (1 / 3 : ℝ) • T) h3
    simpa [smul_smul] using this
  rw [h3', smul_zero]

end Closed

/-! ### The recursive Bedford--Taylor product -/

section Recursive

variable {U : Opens (ComplexModel n)}

/-- Closedness in every bidimension (a current of bidimension `(0,0)` has top degree and is
closed). -/
def IsClosedAny : (k : ℕ) → LocalProductCurrent n U k → Prop
  | 0, _ => True
  | _ + 1, S => IsClosedCurrent S

/-- `dd^c(u S)` for the extension by zero of `u` off `U`. -/
def ddcMul {k : ℕ} (S : LocalProductCurrent n U (k + 1)) (u : E → ℝ) : LocalProductCurrent n U k :=
  ddc (mulBorel S ((U : Set E).indicator u))

/-- **The recursive product** `B(u₀, …, u_{q-1}; T) = dd^c(u₀ dd^c(u₁ ⋯ dd^c(u_{q-1} T)))` of a
current `T` of bidimension `(r + q, r + q)`, a current of bidimension `(r,r)`; the innermost factor
is the last potential: `B(u; T) = B(u₀, …, u_{q-2}; dd^c(u_{q-1} T))`. -/
def btProduct : (q r : ℕ) → (Fin q → E → ℝ) → LocalProductCurrent n U (r + q) →
    LocalProductCurrent n U r
  | 0, _, _, T => T
  | q + 1, r, u, T => btProduct q r (Fin.init u) (ddcMul T (u (Fin.last q)))

@[simp] theorem btProduct_zero (r : ℕ) (u : Fin 0 → E → ℝ) (T : LocalProductCurrent n U (r + 0)) :
    btProduct 0 r u T = T := rfl

theorem btProduct_succ (q r : ℕ) (u : Fin (q + 1) → E → ℝ)
    (T : LocalProductCurrent n U (r + (q + 1))) :
    btProduct (q + 1) r u T = btProduct q r (Fin.init u) (ddcMul T (u (Fin.last q))) := rfl

/-- One step of the recursion preserves positivity and closedness. -/
theorem isPositive_ddcMul {m : ℕ} {T : LocalProductCurrent n U (m + 1)} (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {u : E → ℝ} (hu : IsLocallyBoundedPshOn U u) :
    IsPositive (ddcMul T u) ∧ IsClosedAny m (ddcMul T u) := by
  refine ⟨IsPositive.isPositive_ddc_mulBorel hT hTc hu, ?_⟩
  cases m with
  | zero => trivial
  | succ k => exact isClosedCurrent_ddc _

/-- **The recursive Bedford--Taylor product of locally bounded PSH functions against a positive
closed current is a positive closed current** (`demailly-cadg:III.3.2`). -/
theorem isPositive_btProduct : ∀ (q r : ℕ) (u : Fin q → E → ℝ)
    (T : LocalProductCurrent n U (r + q)), IsPositive T → IsClosedAny (r + q) T →
    (∀ i, IsLocallyBoundedPshOn U (u i)) →
    IsPositive (btProduct q r u T) ∧ IsClosedAny r (btProduct q r u T)
  | 0, r, u, T, hT, hTc, _ => ⟨hT, hTc⟩
  | q + 1, r, u, T, hT, hTc, hu => by
    obtain ⟨h1, h2⟩ := isPositive_ddcMul (m := r + q) hT hTc (hu (Fin.last q))
    exact isPositive_btProduct q r (Fin.init u) _ h1 h2 fun i => hu _

/-- The top-degree product `B(u₁, …, u_q; T)` of a positive closed current of bidimension `(q,q)`
is a positive Radon measure on `U`. -/
theorem exists_measure_btProduct {q : ℕ} (u : Fin q → E → ℝ)
    (T : LocalProductCurrent n U (0 + q)) (hT : IsPositive T) (hTc : IsClosedAny (0 + q) T)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    ∃ μ : Measure U, μ.Regular ∧ IsLocallyFiniteMeasure μ ∧
      ∀ φ : 𝓓(U, ℝ), ∫ x : U, φ x ∂μ = btProduct q 0 u T (kahlerPower n 0) φ :=
  (isPositive_btProduct q 0 u T hT hTc hu).1.positiveDistribution_trace.exists_regular_measure

/-- `u T` depends only on the values of `u` on `U`. -/
theorem mulBorel_congr {k : ℕ} {T : LocalProductCurrent n U k} (hT : IsPositive T)
    {u w : E → ℝ} (hu : Measurable u) (hub : IsLocallyBoundedOn u U) (hw : Measurable w)
    (hwb : IsLocallyBoundedOn w U) (h : ∀ x ∈ U, u x = w x) : mulBorel T u = mulBorel T w := by
  ext γ φ
  rw [mulBorel_apply hT hu hub, mulBorel_apply hT hw hwb]
  refine integral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hT.traceMeasure_compl] with x hx
  have hxU : x ∈ U := by simpa using hx
  rw [h x hxU]

/-- Adding a constant to the potential does not change `dd^c(u T)` for a positive closed `T`. -/
theorem ddcMul_add_const {m : ℕ} {T : LocalProductCurrent n U (m + 1)} (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {u : E → ℝ} (hu : IsLocallyBoundedPshOn U u) (c : ℝ) :
    ddcMul T (fun x => u x + c) = ddcMul T u := by
  have hum := measurable_indicator_of_isLocallyBoundedPshOn hu
  have hub := isLocallyBoundedOn_indicator hu
  have hcm : Measurable ((U : Set E).indicator (fun _ : E => c)) :=
    measurable_const.indicator U.isOpen.measurableSet
  have hcb : IsLocallyBoundedOn ((U : Set E).indicator (fun _ : E => c)) U := fun K _ hKU =>
    ⟨|c|, fun x hx => by rw [Set.indicator_of_mem (hKU hx)]⟩
  have hsum : (U : Set E).indicator (fun x => u x + c) =
      (U : Set E).indicator u + (U : Set E).indicator (fun _ : E => c) := by
    funext x
    by_cases hx : x ∈ (U : Set E) <;> simp [hx]
  have hconst : mulBorel T ((U : Set E).indicator (fun _ : E => c)) = c • T := by
    rw [mulBorel_congr hT hcm hcb measurable_const (fun K _ _ => ⟨|c|, fun _ _ => le_rfl⟩)
      (fun x hx => Set.indicator_of_mem hx _), mulBorel_const hT]
  rw [ddcMul, hsum, mulBorel_add hT hum hub hcm hcb, hconst, ddc_add, ddc_smul,
    hTc.ddc_eq_zero, smul_zero, add_zero, ddcMul]

/-- **The recursive product is unchanged by adding constants to the potentials.** -/
theorem btProduct_add_const : ∀ (q r : ℕ) (u : Fin q → E → ℝ) (c : Fin q → ℝ)
    (T : LocalProductCurrent n U (r + q)), IsPositive T → IsClosedAny (r + q) T →
    (∀ i, IsLocallyBoundedPshOn U (u i)) →
    btProduct q r (fun i x => u i x + c i) T = btProduct q r u T
  | 0, _, _, _, _, _, _, _ => rfl
  | q + 1, r, u, c, T, hT, hTc, hu => by
    rw [btProduct_succ, btProduct_succ]
    have hstep : ddcMul T ((fun i x => u i x + c i) (Fin.last q)) = ddcMul T (u (Fin.last q)) :=
      ddcMul_add_const (m := r + q) hT hTc (hu (Fin.last q)) (c (Fin.last q))
    rw [hstep]
    obtain ⟨h1, h2⟩ := isPositive_ddcMul (m := r + q) hT hTc (hu (Fin.last q))
    exact btProduct_add_const q r (Fin.init u) (Fin.init c) _ h1 h2 fun i => hu _

/-- **Agreement with the smooth product**: for a smooth `g`, `dd^c(g T)` is the current
`γ ↦ T(γ ∧ dd^c g)`, written in coordinates (`dd^c g = -(1/4π) ∑ ∂_a∂_b g P_{ab}`,
`smoothDDC_eq_sum`). -/
theorem ddcMul_apply_of_contDiff {m : ℕ} {T : LocalProductCurrent n U (m + 1)}
    (hT : IsPositive T) (hTc : IsClosedCurrent T) {g : E → ℝ} (hg : ContDiff ℝ ∞ g)
    (γ : formSpan n m) (φ : 𝓓(U, ℝ)) :
    ddcMul T g γ φ = ∑ a, ∑ b, (-(1 / (4 * Real.pi))) *
      T (wedgeLM m (isOneOne_coeffForm a b) γ) (mulTest (contDiff_hessFun hg a b) φ) := by
  have hgm : Measurable ((U : Set E).indicator g) :=
    hg.continuous.measurable.indicator U.isOpen.measurableSet
  have hgb : IsLocallyBoundedOn ((U : Set E).indicator g) U := fun K hK hKU => by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuous.continuousOn
    exact ⟨C, fun x hx => by
      rw [Set.indicator_of_mem (hKU hx)]
      simpa [Real.norm_eq_abs] using hC x hx⟩
  have hgb' : IsLocallyBoundedOn g U := fun K hK _ => by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuous.continuousOn
    exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩
  rw [ddcMul, mulBorel_congr hT hgm hgb hg.continuous.measurable hgb'
    (fun x hx => Set.indicator_of_mem hx g), ddc_apply_apply, ← hTc.sum_mulTest_ddc hg γ φ]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mulBorel_apply hT hg.continuous.measurable hgb', hT.apply_eq_integral_density]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [mulTest_apply]
  ring

/-! ### The current `[1]` of integration over `U` -/

/-- Lebesgue measure on `U` as a distribution: `φ ↦ ∫ φ`. -/
def lebesgueDist (U : Opens (ComplexModel n)) : 𝓓'(U, ℝ) :=
  regularDistribution volume (fun _ => (1 : ℝ)) (locallyIntegrableOn_const 1)

theorem lebesgueDist_apply (φ : 𝓓(U, ℝ)) : lebesgueDist U φ = ∫ x, φ x := by
  rw [lebesgueDist, regularDistribution_apply]
  simp

/-- `∫ ∂_v φ = 0` for a test function: the Lebesgue distribution has vanishing derivatives. -/
theorem dDist_lebesgueDist (v : E) : dDist v (lebesgueDist U) = 0 := by
  ext φ
  rw [dDist_apply, lebesgueDist_apply, _root_.zero_apply, neg_eq_zero]
  have hφ := φ.contDiff
  have hφc : Continuous (fun x => fderiv ℝ (φ : E → ℝ) x v) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hint : Integrable (fun x => fderiv ℝ (φ : E → ℝ) x v) volume :=
    hφc.integrable_of_hasCompactSupport (φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) v)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : E => (1 : ℝ)) (g := (φ : E → ℝ)) (v := v)
    (by simp) (by simpa using hint)
    (by simpa using (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport))
    (fun x _ => differentiableAt_const _)
    (fun x _ => (φ.contDiff.differentiable (by simp)).differentiableAt)
  have h0 : ∫ x, fderiv ℝ (φ : E → ℝ) x v = 0 := by simpa using hibp
  rw [← h0]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [dTest_apply]

variable (U) in
/-- **The current `[1]`** of bidimension `(n,n)`: `[1](γ)(φ) = (density of γ) ∫ φ`, integration of
`φ γ` over `U` with its complex orientation. -/
def oneCurrent : LocalProductCurrent n U n :=
  LinearMap.smulRight (TopDegreeDensity.topDensityLM n ∘ₗ (formSpan n n).subtype) (lebesgueDist U)

theorem oneCurrent_apply (γ : formSpan n n) (φ : 𝓓(U, ℝ)) :
    oneCurrent U γ φ = TopDegreeDensity.topDensity (γ : RealForm n (2 * n)) * ∫ x, φ x := by
  simp [oneCurrent, lebesgueDist_apply]

/-- `[1]` is positive: strongly positive forms of top degree have nonnegative density. -/
theorem isPositive_oneCurrent : IsPositive (oneCurrent U) := by
  intro ι _ γ φ hγ
  simp only [oneCurrent_apply]
  have hint : ∀ i, Integrable (fun x => (φ i : E → ℝ) x) volume := fun i =>
    (φ i).continuous.integrable_of_hasCompactSupport (φ i).hasCompactSupport
  have e : ∑ i, TopDegreeDensity.topDensity (γ i : RealForm n (2 * n)) * ∫ x, φ i x =
      ∫ x, TopDegreeDensity.topDensity (∑ i, φ i x • (γ i : RealForm n (2 * n))) := by
    rw [show (∑ i, TopDegreeDensity.topDensity (γ i : RealForm n (2 * n)) * ∫ x, φ i x) =
        ∑ i, ∫ x, TopDegreeDensity.topDensity (γ i : RealForm n (2 * n)) * φ i x from
      Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm,
      ← integral_finsetSum _ fun i _ => (hint i).const_mul _]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hlin := map_sum (TopDegreeDensity.topDensityLM n)
      (fun i => φ i x • (γ i : RealForm n (2 * n))) Finset.univ
    simp only [map_smul, smul_eq_mul] at hlin
    change _ = TopDegreeDensity.topDensityLM n _
    rw [hlin]
    refine Finset.sum_congr rfl fun i _ => ?_
    change TopDegreeDensity.topDensity _ * _ = φ i x * TopDegreeDensity.topDensity _
    ring
  rw [e]
  exact integral_nonneg fun x => TopDegreeDensity.topDensity_nonneg_of_mem_spCone (hγ x)

/-- `[1]` is closed. -/
theorem isClosedAny_oneCurrent : IsClosedAny n (oneCurrent U) := by
  cases n with
  | zero => trivial
  | succ k =>
    intro ℓ γ
    have h : ∀ a, oneCurrent U (wedgeLM k (isOneOne_testForm a ℓ) γ) =
        TopDegreeDensity.topDensity
          ((wedgeLM k (isOneOne_testForm a ℓ) γ : formSpan (k + 1) (k + 1)) :
            RealForm (k + 1) (2 * (k + 1))) • lebesgueDist U := fun a => rfl
    simp only [h, map_smul, dDist_lebesgueDist, smul_zero, Finset.sum_const_zero]

/-- `[1]` transported to the degree `0 + n` used by `btProduct`. -/
def oneCurrentOf {k : ℕ} (hk : k = n) : LocalProductCurrent n U k :=
  cast (congrArg (LocalProductCurrent n U) hk.symm) (oneCurrent U)

theorem isPositive_oneCurrentOf {k : ℕ} (hk : k = n) : IsPositive (oneCurrentOf (U := U) hk) := by
  subst hk
  exact isPositive_oneCurrent

theorem isClosedAny_oneCurrentOf {k : ℕ} (hk : k = n) :
    IsClosedAny k (oneCurrentOf (U := U) hk) := by
  subst hk
  exact isClosedAny_oneCurrent

/-- **The local Bedford--Taylor Monge--Ampère measure**: for locally bounded PSH functions
`u₁, …, u_n` on `U`, `dd^c u₁ ∧ ⋯ ∧ dd^c u_n = B(u₁, …, u_n; [1])` is a positive Radon measure on
`U`. -/
theorem exists_measure_btProduct_oneCurrent (u : Fin n → E → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    ∃ μ : Measure U, μ.Regular ∧ IsLocallyFiniteMeasure μ ∧
      ∀ φ : 𝓓(U, ℝ), ∫ x : U, φ x ∂μ =
        btProduct n 0 u (oneCurrentOf (U := U) (Nat.zero_add n)) (kahlerPower n 0) φ :=
  exists_measure_btProduct u _ (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hu

end Recursive

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
