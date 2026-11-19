/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianLaplacian.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianDrift
public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalGradient
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure

/-! Coordinate Hessian and the constant Laplacian of the actual Hamiltonian. -/

@[expose] public section
open scoped BigOperators ComplexConjugate
open Filter Topology
namespace GinibrePoincare
noncomputable section

theorem fderiv_reciprocal_difference {n : ℕ} (z v : Configuration n)
    (j k : Fin n) (hne : z j - z k ≠ 0) :
    fderiv ℝ (fun x : Configuration n => (x j-x k)⁻¹) z v =
      -(z j-z k)⁻¹ * (v j-v k) * (z j-z k)⁻¹ := by
  let P : Configuration n →L[ℝ] ℂ := (ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ) -
    (ContinuousLinearMap.proj k : Configuration n →L[ℝ] ℂ)
  have h := ((hasFDerivAt_inv' (𝕜 := ℝ) hne).comp z P.hasFDerivAt).fderiv
  change (fderiv ℝ (Inv.inv ∘ P) z) v = _
  rw [h]
  simp only [P, ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.comp_apply,
    neg_apply, sub_apply, ContinuousLinearMap.proj_apply]
  ring

theorem differentiableAt_reciprocal_difference {n : ℕ} (z : Configuration n)
    (j k : Fin n) (hne : z j - z k ≠ 0) :
    DifferentiableAt ℝ (fun x : Configuration n => (x j-x k)⁻¹) z := by
  exact (differentiableAt_inv (𝕜 := ℝ) hne).comp z
    (((ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ).differentiableAt).sub
      (ContinuousLinearMap.proj k : Configuration n →L[ℝ] ℂ).differentiableAt)

theorem fderiv_re_mul_reciprocal_difference {n : ℕ} (z v : Configuration n)
    (j k : Fin n) (w : ℂ) (hne : z j - z k ≠ 0) :
    fderiv ℝ (fun x : Configuration n => (w*(x j-x k)⁻¹).re) z v =
      (w * (-(z j-z k)⁻¹ * (v j-v k) * (z j-z k)⁻¹)).re := by
  let T : ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.mulLeftRight ℝ ℂ w 1)
  have hf := differentiableAt_reciprocal_difference z j k hne
  have h := (T.hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  rw [show (fun x : Configuration n => (w*(x j-x k)⁻¹).re) =
      T ∘ (fun x : Configuration n => (x j-x k)⁻¹) by
    funext x; simp [T, ContinuousLinearMap.mulLeftRight_apply]]
  rw [h]
  change T (fderiv ℝ (fun x : Configuration n => (x j-x k)⁻¹) z v) = _
  rw [fderiv_reciprocal_difference z v j k hne]
  simp [T, ContinuousLinearMap.mulLeftRight_apply]

theorem fderiv_re_conj_coordinate_mul {n : ℕ} (z v : Configuration n)
    (j : Fin n) (w : ℂ) :
    fderiv ℝ (fun x : Configuration n => (conj (x j)*w).re) z v =
      (conj (v j)*w).re := by
  let T : Configuration n →L[ℝ] ℝ := Complex.reCLM.comp
    ((ContinuousLinearMap.mulLeftRight ℝ ℂ 1 w).comp
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj j)))
  rw [show (fun x : Configuration n => (conj (x j)*w).re) = T by
    funext x; simp [T, ContinuousLinearMap.mulLeftRight_apply]]
  rw [T.fderiv]
  simp [T, ContinuousLinearMap.mulLeftRight_apply]

theorem ginibreHamiltonian_coordinate_hessian {n : ℕ} (z v : Configuration n)
    (hz : CollisionFree z) (j : Fin n) (w : ℂ) :
    fderiv ℝ (fun x => fderiv ℝ (ginibreHamiltonian n) x (coordinateDirection j w)) z v =
      2*(n : ℝ)*(conj (v j)*w).re +
        2*∑ k ∈ Finset.univ.erase j,
          (w*(z j-z k)⁻¹*(v j-v k)*(z j-z k)⁻¹).re := by
  have heq : (fun x => fderiv ℝ (ginibreHamiltonian n) x (coordinateDirection j w)) =ᶠ[𝓝 z]
      (fun x => 2*(n : ℝ)*(conj (x j)*w).re -
        2*∑ k ∈ Finset.univ.erase j, (w*(x j-x k)⁻¹).re) := by
    filter_upwards [(isOpen_collisionFree n).mem_nhds hz] with x hx
    rw [fderiv_ginibreHamiltonian_coordinate x hx j w,
      fderiv_configurationNormSq_coordinate]
    rw [show (∑ k ∈ Finset.univ.erase j, w/(x j-x k)).re =
        ∑ k ∈ Finset.univ.erase j, (w*(x j-x k)⁻¹).re by
      simp only [div_eq_mul_inv]
      exact map_sum Complex.reCLM (fun k => w*(x j-x k)⁻¹) (Finset.univ.erase j)]
    ring
  rw [heq.fderiv_eq]
  have h1 : DifferentiableAt ℝ (fun x : Configuration n => (conj (x j)*w).re) z := by
    have hc := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z
      (ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ).differentiableAt).mul_const w
    exact Complex.reCLM.differentiableAt.comp z hc
  have h2 (k : Fin n) (hk : k ∈ Finset.univ.erase j) :
      DifferentiableAt ℝ (fun x : Configuration n => (w*(x j-x k)⁻¹).re) z := by
    have hne : z j-z k ≠ 0 := fun h => (Finset.mem_erase.mp hk).1
      (hz (sub_eq_zero.mp h)).symm
    exact Complex.reCLM.differentiableAt.comp z
      ((differentiableAt_reciprocal_difference z j k hne).const_mul w)
  rw [fderiv_fun_sub (h1.const_mul _) ((DifferentiableAt.fun_sum h2).const_mul _),
    fderiv_const_mul h1, fderiv_const_mul (DifferentiableAt.fun_sum h2), fderiv_fun_sum h2]
  simp only [sub_apply, smul_apply, smul_eq_mul, sum_apply]
  rw [fderiv_re_conj_coordinate_mul]
  have hsum : (∑ k ∈ Finset.univ.erase j,
      fderiv ℝ (fun x : Configuration n => (w*(x j-x k)⁻¹).re) z v) =
      -(∑ k ∈ Finset.univ.erase j, (w*(z j-z k)⁻¹*(v j-v k)*(z j-z k)⁻¹).re) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [fderiv_re_mul_reciprocal_difference z v j k w
      (fun h => (Finset.mem_erase.mp hk).1 (hz (sub_eq_zero.mp h)).symm)]
    simp only [mul_neg, neg_mul, Complex.neg_re, mul_assoc]
  rw [hsum]
  ring

theorem ginibreHamiltonian_coordinate_laplacian {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) (j : Fin n) :
    secondDirectionalDerivative (ginibreHamiltonian n) (realCoordinateDirection j) z +
      secondDirectionalDerivative (ginibreHamiltonian n) (imaginaryCoordinateDirection j) z =
      4*(n : ℝ) := by
  unfold secondDirectionalDerivative
  rw [show realCoordinateDirection j = coordinateDirection j 1 from rfl,
    show imaginaryCoordinateDirection j = coordinateDirection j Complex.I from rfl,
    ginibreHamiltonian_coordinate_hessian z (coordinateDirection j 1) hz j 1,
    ginibreHamiltonian_coordinate_hessian z (coordinateDirection j Complex.I) hz j Complex.I]
  have hs : (∑ k ∈ Finset.univ.erase j,
      (Complex.I*(z j-z k)⁻¹*
        (coordinateDirection j Complex.I j-coordinateDirection j Complex.I k)*(z j-z k)⁻¹).re) =
      -(∑ k ∈ Finset.univ.erase j,
        ((z j-z k)⁻¹*(z j-z k)⁻¹).re) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hkj := (Finset.mem_erase.mp hk).1
    simp only [coordinateDirection, ite_eq_right hkj, ite_true, sub_zero]
    have hi (a : ℂ) : Complex.I*a*Complex.I*a = -(a*a) := by
      calc Complex.I*a*Complex.I*a = (Complex.I*Complex.I)*(a*a) := by ring
           _ = -(a*a) := by simp only [Complex.I_mul_I, neg_one_mul]
    rw [hi, Complex.neg_re]
  rw [hs]
  have hs' : (∑ k ∈ Finset.univ.erase j,
      (1*(z j-z k)⁻¹*
        (coordinateDirection j 1 j-coordinateDirection j 1 k)*(z j-z k)⁻¹).re) =
      ∑ k ∈ Finset.univ.erase j, ((z j-z k)⁻¹*(z j-z k)⁻¹).re := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [coordinateDirection, ite_eq_right (Finset.mem_erase.mp hk).1,
        ite_true,
      sub_zero, one_mul, mul_one]
  rw [hs']
  simp only [coordinateDirection, ite_true, map_one, mul_one,
    Complex.one_re, Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg]
  ring

theorem ginibreHamiltonian_laplacian {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) :
    configurationLaplacian (ginibreHamiltonian n) z = 4*(n : ℝ)^2 := by
  unfold configurationLaplacian
  simp_rw [ginibreHamiltonian_coordinate_laplacian z hz]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end
end GinibrePoincare
