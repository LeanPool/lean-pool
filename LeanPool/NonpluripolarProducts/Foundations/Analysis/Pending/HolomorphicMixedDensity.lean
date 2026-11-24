/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedCoefficientCongruence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.CoordinateDensityGeometry
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicDDC
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Complex

/-!
# Mixed Monge–Ampère densities under holomorphic maps

The complex Hessian extends to a sesquilinear form `hessForm u z v w` in
arbitrary directions. Through the covariance of `ddᶜ` it transforms under a
holomorphic map `F` by evaluation on `DF v, DF w`; in coordinates,
`H(p ∘ F) = Jᵀ H(p) JBar` with the complex Jacobian matrix `J`. With the
congruence of the mixed coefficient this gives
`MA(p ∘ F) = |det J|² · MA(p) ∘ F`, and `|det J|²` is the real Jacobian of `F`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Complex
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.HolomorphicMixedDensity

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- The complex Hessian in arbitrary directions. -/
def hessForm (u : ComplexModel n → ℝ) (z v w : ComplexModel n) : ℂ :=
  ((realHessian u z v w + realHessian u z (I • v) (I • w) : ℝ) : ℂ) / 4 +
    I * ((realHessian u z v (I • w) - realHessian u z (I • v) w : ℝ) : ℂ) / 4

theorem complexHessian_eq_hessForm (u : ComplexModel n → ℝ) (z : ComplexModel n) (j k : Fin n) :
    complexHessian u z j k = hessForm u z (coordinateVector j) (coordinateVector k) := rfl

section Sesquilinear

variable (u : ComplexModel n → ℝ) (z : ComplexModel n)

theorem realHessian_add_left' (a a' b : ComplexModel n) :
    realHessian u z (a + a') b = realHessian u z a b + realHessian u z a' b := by
  simp [realHessian_eq_fderiv]

theorem realHessian_add_right' (a b b' : ComplexModel n) :
    realHessian u z a (b + b') = realHessian u z a b + realHessian u z a b' := by
  simp [realHessian_eq_fderiv]

theorem realHessian_neg_left (a b : ComplexModel n) :
    realHessian u z (-a) b = -realHessian u z a b := by
  simp [realHessian_eq_fderiv]

theorem realHessian_neg_right (a b : ComplexModel n) :
    realHessian u z a (-b) = -realHessian u z a b := by
  simp [realHessian_eq_fderiv]

theorem hessForm_add_left (v v' w : ComplexModel n) :
    hessForm u z (v + v') w = hessForm u z v w + hessForm u z v' w := by
  simp only [hessForm, smul_add, realHessian_add_left']
  push_cast; ring

theorem hessForm_add_right (v w w' : ComplexModel n) :
    hessForm u z v (w + w') = hessForm u z v w + hessForm u z v w' := by
  simp only [hessForm, smul_add, realHessian_add_right']
  push_cast; ring

theorem hessForm_zero_left (w : ComplexModel n) : hessForm u z 0 w = 0 := by
  simp [hessForm, realHessian_eq_fderiv]

theorem hessForm_zero_right (v : ComplexModel n) : hessForm u z v 0 = 0 := by
  simp [hessForm, realHessian_eq_fderiv]

theorem hessForm_real_smul_left (r : ℝ) (v w : ComplexModel n) :
    hessForm u z (r • v) w = r * hessForm u z v w := by
  simp only [hessForm, smul_comm I r v, realHessian_smul_left]
  push_cast; ring

theorem hessForm_real_smul_right (r : ℝ) (v w : ComplexModel n) :
    hessForm u z v (r • w) = r * hessForm u z v w := by
  simp only [hessForm, smul_comm I r w, realHessian_smul_right]
  push_cast; ring

theorem hessForm_I_smul_left (v w : ComplexModel n) :
    hessForm u z (I • v) w = I * hessForm u z v w := by
  simp only [hessForm, smul_smul, I_mul_I, neg_one_smul, realHessian_neg_left]
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem hessForm_I_smul_right (v w : ComplexModel n) :
    hessForm u z v (I • w) = -I * hessForm u z v w := by
  simp only [hessForm, smul_smul, I_mul_I, neg_one_smul, realHessian_neg_right]
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem hessForm_smul_left (c : ℂ) (v w : ComplexModel n) :
    hessForm u z (c • v) w = c * hessForm u z v w := by
  have hc : c • v = c.re • v + c.im • (I • v) := by
    conv_lhs => rw [← re_add_im c]
    rw [add_smul, mul_comm, mul_smul]
    simp only [Complex.coe_smul]
    rw [smul_comm (c.im : ℝ) I v]
  rw [hc, hessForm_add_left, hessForm_real_smul_left, hessForm_real_smul_left,
    hessForm_I_smul_left]
  conv_rhs => rw [← re_add_im c]
  ring

theorem hessForm_smul_right (c : ℂ) (v w : ComplexModel n) :
    hessForm u z v (c • w) = star c * hessForm u z v w := by
  have hc : c • w = c.re • w + c.im • (I • w) := by
    conv_lhs => rw [← re_add_im c]
    rw [add_smul, mul_comm, mul_smul]
    simp only [Complex.coe_smul]
    rw [smul_comm (c.im : ℝ) I w]
  rw [hc, hessForm_add_right, hessForm_real_smul_right, hessForm_real_smul_right,
    hessForm_I_smul_right]
  conv_rhs => rw [← re_add_im c]
  simp only [star_add, star_mul', Complex.star_def, conj_ofReal, conj_I]
  ring

theorem hessForm_sum_left {ι : Type*} (s : Finset ι) (v : ι → ComplexModel n)
    (w : ComplexModel n) : hessForm u z (∑ a ∈ s, v a) w = ∑ a ∈ s, hessForm u z (v a) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hessForm_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, hessForm_add_left, ih, Finset.sum_insert ha]

theorem hessForm_sum_right {ι : Type*} (s : Finset ι) (v : ComplexModel n)
    (w : ι → ComplexModel n) : hessForm u z v (∑ a ∈ s, w a) = ∑ a ∈ s, hessForm u z v (w a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hessForm_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, hessForm_add_right, ih, Finset.sum_insert ha]

theorem eq_sum_coordinateVector (v : ComplexModel n) : v = ∑ a, v a • coordinateVector a := by
  ext j
  simp [coordinateVector, Pi.single_apply]

/-- **Expansion in coordinates.** -/
theorem hessForm_eq_sum (v w : ComplexModel n) :
    hessForm u z v w = ∑ a, ∑ b, v a * star (w b) * complexHessian u z a b := by
  conv_lhs => rw [eq_sum_coordinateVector v, eq_sum_coordinateVector w]
  rw [hessForm_sum_left]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [hessForm_sum_right]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [hessForm_smul_left, hessForm_smul_right, complexHessian_eq_hessForm]
  ring

end Sesquilinear

/-- The form through the actual `ddᶜ` two-form. -/
theorem hessForm_eq_smoothDDC {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) (v w : ComplexModel n) :
    hessForm u z v w = (Real.pi : ℂ) *
      ((smoothDDC u z ![v, I • w] : ℂ) - I * (smoothDDC u z ![v, w] : ℂ)) := by
  have hs (a b : ComplexModel n) : realHessian u z a b = realHessian u z b a := by
    simpa only [realHessian_eq_fderiv] using hu.isSymmSndFDerivAt (by norm_num) a b
  rw [smoothDDC_apply_eq_realHessian hu, smoothDDC_apply_eq_realHessian hu]
  simp only [smul_smul, I_mul_I, neg_one_smul, realHessian_neg_right, hessForm]
  rw [hs (I • w) (I • v), hs w (I • v)]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_im]
    field_simp [Real.pi_ne_zero]
    ring
  · simp only [Complex.add_im, Complex.div_ofNat_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.sub_re, Complex.sub_im,
      Complex.mul_re]
    field_simp [Real.pi_ne_zero]
    ring

/-- **Chain rule for the complex Hessian of a `C²` function under a holomorphic map.** -/
theorem hessForm_comp_holomorphic_two {k : ℕ} {F : ComplexModel k → ComplexModel n}
    {p : ComplexModel n → ℝ} {U : Set (ComplexModel k)} {V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℂ ∞ F U) (hp : ContDiffOn ℝ 2 p V)
    (hFV : MapsTo F U V) {y : ComplexModel k} (hy : y ∈ U) (v w : ComplexModel k) :
    hessForm (fun x ↦ p (F x)) y v w = hessForm p (F y) (fderiv ℝ F y v) (fderiv ℝ F y w) := by
  have hFy : DifferentiableAt ℂ F y :=
    ((hF y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hq2 : ContDiffAt ℝ 2 (fun x ↦ p (F x)) y :=
    ((hp.comp ((hF.restrict_scalars ℝ).of_le (by
      simp)) hFV) y hy).contDiffAt
      (hU.mem_nhds hy)
  have hp2 : ContDiffAt ℝ 2 p (F y) := (hp (F y) (hFV hy)).contDiffAt (hV.mem_nhds (hFV hy))
  have hnat (a b : ComplexModel k) :
      smoothDDC (fun x ↦ p (F x)) y ![a, b] =
        smoothDDC p (F y) ![fderiv ℝ F y a, fderiv ℝ F y b] := by
    have h := congrArg (fun A : (ComplexModel k) [⋀^Fin 2]→L[ℝ] ℝ ↦ A ![a, b])
      (HolomorphicDDC.smoothDDC_comp_two hU hV hF hp hFV hy)
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
    rw [h]
    congr 1
    ext i
    fin_cases i <;> rfl
  have hmapI : fderiv ℝ F y (I • w) = I • fderiv ℝ F y w := by
    rw [hFy.fderiv_restrictScalars ℝ]
    exact (fderiv ℂ F y).map_smul I w
  rw [hessForm_eq_smoothDDC hq2, hessForm_eq_smoothDDC hp2, hnat, hnat, hmapI]

/-- **Chain rule for holomorphic maps.** -/
theorem hessForm_comp_holomorphic {k : ℕ} {F : ComplexModel k → ComplexModel n}
    {p : ComplexModel n → ℝ} {U : Set (ComplexModel k)} {V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℂ ∞ F U) (hp : ContDiffOn ℝ ∞ p V)
    (hFV : MapsTo F U V) {y : ComplexModel k} (hy : y ∈ U) (v w : ComplexModel k) :
    hessForm (fun x ↦ p (F x)) y v w = hessForm p (F y) (fderiv ℝ F y v) (fderiv ℝ F y w) :=
  hessForm_comp_holomorphic_two hU hV hF
    (hp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hFV hy v w

/-- The complex Jacobian matrix `(∂Fₐ/∂zⱼ)`. -/
def jacobianMatrix (F : ComplexModel n → ComplexModel n) (y : ComplexModel n) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a j ↦ (fderiv ℝ F y (coordinateVector j)) a

/-- **`H(p ∘ F) = Jᵀ H(p) JBar`** for a holomorphic `F` and a `C²` function `p`. -/
theorem complexHessian_comp_holomorphic_two {F : ComplexModel n → ComplexModel n}
    {p : ComplexModel n → ℝ} {U V : Set (ComplexModel n)} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℂ ∞ F U) (hp : ContDiffOn ℝ 2 p V) (hFV : MapsTo F U V)
    {y : ComplexModel n} (hy : y ∈ U) :
    complexHessian (fun x ↦ p (F x)) y =
      (jacobianMatrix F y).transpose * complexHessian p (F y) *
        (jacobianMatrix F y).map (starRingEnd ℂ) := by
  ext j k
  rw [complexHessian_eq_hessForm, hessForm_comp_holomorphic_two hU hV hF hp hFV hy,
    hessForm_eq_sum]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, jacobianMatrix,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [Complex.star_def]
  ring

theorem complexHessian_comp_holomorphic {F : ComplexModel n → ComplexModel n}
    {p : ComplexModel n → ℝ} {U V : Set (ComplexModel n)} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℂ ∞ F U) (hp : ContDiffOn ℝ ∞ p V) (hFV : MapsTo F U V)
    {y : ComplexModel n} (hy : y ∈ U) :
    complexHessian (fun x ↦ p (F x)) y =
      (jacobianMatrix F y).transpose * complexHessian p (F y) * (jacobianMatrix F y).map
        (starRingEnd ℂ) :=
  complexHessian_comp_holomorphic_two hU hV hF
    (hp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hFV hy

/-- **Mixed densities under holomorphic maps.** -/
theorem mixedDensity_comp_holomorphic {F : ComplexModel n → ComplexModel n}
    {f : Fin n → ComplexModel n → ℝ} {U V : Set (ComplexModel n)} (hU : IsOpen U)
    (hV : IsOpen V) (hF : ContDiffOn ℂ ∞ F U) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) V)
    (hFV : MapsTo F U V) {y : ComplexModel n} (hy : y ∈ U) :
    mixedDensity (fun i x ↦ f i (F x)) y =
      Complex.normSq (jacobianMatrix F y).det * mixedDensity f (F y) := by
  simp only [mixedDensity]
  simp_rw [complexHessian_comp_holomorphic hU hV hF (hf _) hFV hy]
  have hd : ((jacobianMatrix F y).map (starRingEnd ℂ)).det = starRingEnd ℂ (jacobianMatrix F
    y).det :=
    ((starRingEnd ℂ).map_det _).symm
  rw [Pending.MixedMongeAmpere.mixedCoefficient_mul_mul, Matrix.det_transpose, hd,
    Complex.mul_conj, Complex.re_ofReal_mul, mul_div_assoc]

/-- The real Jacobian determinant of a holomorphic map is `|det J|²`. -/
theorem det_fderiv_eq_normSq {F : ComplexModel n → ComplexModel n} {y : ComplexModel n}
    (hF : DifferentiableAt ℂ F y) :
    (fderiv ℝ F y).det = Complex.normSq (jacobianMatrix F y).det := by
  let b := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  have hmat : jacobianMatrix F y = LinearMap.toMatrix b b (fderiv ℂ F y : _ →ₗ[ℂ] _) := by
    ext a j
    simp [jacobianMatrix, LinearMap.toMatrix_apply, b, coordinateVector,
      hF.fderiv_restrictScalars ℝ]
  rw [hmat, LinearMap.det_toMatrix, ContinuousLinearMap.det, hF.fderiv_restrictScalars ℝ,
    ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq]
  rfl

end SGPT.Foundations.Analysis.Pending.HolomorphicMixedDensity
