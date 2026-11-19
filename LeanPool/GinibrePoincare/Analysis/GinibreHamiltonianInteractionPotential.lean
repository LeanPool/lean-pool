/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianInteractionPotential.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUActionWeight
public import LeanPool.GinibrePoincare.Analysis.GinibreRadialGamma

/-! Actual interaction potential and its Euler derivative for the stationary OU
Girsanov correction. -/

@[expose] public section
open scoped BigOperators ContDiff ComplexConjugate
open Filter Topology
namespace GinibrePoincare
noncomputable section

/-- The logarithmic interaction potential `-log (vandermondeWeight z)`, minus the logarithm of
the squared modulus of the Vandermonde determinant. -/
def ginibreInteractionPotential (n : ℕ) (z : Configuration n) : ℝ :=
  -Real.log (vandermondeWeight z)

theorem ginibreInteractionPotential_contDiffAt (n : ℕ) (z : Configuration n)
    (hz : CollisionFree z) : ContDiffAt ℝ ∞ (ginibreInteractionPotential n) z :=
  (((contDiff_vandermondeWeight n).contDiffAt.log
    (ne_of_gt (vandermondeWeight_pos_of_collisionFree z hz))).neg)

theorem vandermondeWeight_real_smul (n : ℕ) (t : ℝ) (z : Configuration n) :
    vandermondeWeight (t • z) = t^(2*vandermondeDegree n)*vandermondeWeight z := by
  have he : t • z = globalPhase (t : ℂ) z := by ext i; simp [globalPhase, Complex.real_smul]
  rw [he]
  unfold vandermondeWeight
  rw [vandermonde_globalPhase, ← vandermondeDegree_eq_sum_Ioi_card,
    map_mul, map_pow, Complex.normSq_ofReal]
  rw [← pow_two, ← pow_mul]

theorem fderiv_vandermondeWeight_radial (n : ℕ) (z : Configuration n) :
    fderiv ℝ vandermondeWeight z z =
      (2*vandermondeDegree n : ℕ)*vandermondeWeight z := by
  have hscale : HasDerivAt (fun t : ℝ => t • z) z 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const z
  have hw : HasFDerivAt (vandermondeWeight : Configuration n → ℝ) (fderiv ℝ vandermondeWeight z) z
      := ((contDiff_vandermondeWeight n).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hw1 : HasFDerivAt (vandermondeWeight : Configuration n → ℝ) (fderiv ℝ vandermondeWeight z)
      ((1 : ℝ) • z) := by simpa using hw
  have hd := hw1.comp_hasDerivAt 1 hscale
  have hp := ((hasDerivAt_id (1 : ℝ)).pow (2*vandermondeDegree n)).mul_const (vandermondeWeight z)
  have he : (fun t : ℝ => vandermondeWeight (t • z)) =
      (fun t : ℝ => t^(2*vandermondeDegree n)*vandermondeWeight z) := by
    funext t; exact vandermondeWeight_real_smul n t z
  change HasDerivAt (fun t : ℝ => vandermondeWeight (t • z)) _ 1 at hd
  rw [he] at hd
  have hh := hd.unique hp
  simpa using hh

theorem fderiv_ginibreInteractionPotential_radial (n : ℕ) (z : Configuration n)
    (hz : CollisionFree z) :
    fderiv ℝ (ginibreInteractionPotential n) z z = -(2*vandermondeDegree n : ℕ) := by
  have hv : DifferentiableAt ℝ (vandermondeWeight : Configuration n → ℝ) z :=
      ((contDiff_vandermondeWeight n).differentiable (by simp)).differentiableAt
  unfold ginibreInteractionPotential
  rw [fderiv_fun_neg,
    fderiv.log hv (ne_of_gt (vandermondeWeight_pos_of_collisionFree z hz))]
  simp only [neg_apply, smul_apply, smul_eq_mul]
  rw [fderiv_vandermondeWeight_radial]
  field_simp [ne_of_gt (vandermondeWeight_pos_of_collisionFree z hz)]

theorem fderiv_ginibreInteractionPotential_coordinate {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) (j : Fin n) (w : ℂ) :
    fderiv ℝ (ginibreInteractionPotential n) z (coordinateDirection j w) =
      -2*(∑ k ∈ Finset.univ.erase j, w/(z j-z k)).re := by
  have hv : DifferentiableAt ℝ (vandermondeWeight : Configuration n → ℝ) z :=
    ((contDiff_vandermondeWeight n).differentiable (by simp)).differentiableAt
  unfold ginibreInteractionPotential
  rw [fderiv_fun_neg, fderiv.log hv (ne_of_gt (vandermondeWeight_pos_of_collisionFree z hz))]
  simp only [neg_apply, smul_apply, smul_eq_mul]
  rw [fderiv_vandermondeWeight_apply_coordinateDirection z hz j w]
  field_simp [ne_of_gt (vandermondeWeight_pos_of_collisionFree z hz)]

theorem ginibreInteractionPotential_coordinate_hessian {n : ℕ} (z v : Configuration n)
    (hz : CollisionFree z) (j : Fin n) (w : ℂ) :
    fderiv ℝ (fun x => fderiv ℝ (ginibreInteractionPotential n) x (coordinateDirection j w)) z v =
      2*∑ k ∈ Finset.univ.erase j,
        (w*(z j-z k)⁻¹*(v j-v k)*(z j-z k)⁻¹).re := by
  have heq : (fun x => fderiv ℝ (ginibreInteractionPotential n) x (coordinateDirection j w)) =ᶠ[𝓝 z]
      (fun x => -2*∑ k ∈ Finset.univ.erase j, (w*(x j-x k)⁻¹).re) := by
    filter_upwards [(isOpen_collisionFree n).mem_nhds hz] with x hx
    rw [fderiv_ginibreInteractionPotential_coordinate x hx j w]
    simp only [div_eq_mul_inv]
    congr 1
    exact map_sum Complex.reCLM _ _
  rw [heq.fderiv_eq]
  have h2 (k : Fin n) (hk : k ∈ Finset.univ.erase j) :
      DifferentiableAt ℝ (fun x : Configuration n => (w*(x j-x k)⁻¹).re) z := by
    have hne : z j-z k ≠ 0 := fun h => (Finset.mem_erase.mp hk).1
      (hz (sub_eq_zero.mp h)).symm
    exact Complex.reCLM.differentiableAt.comp z
      ((differentiableAt_reciprocal_difference z j k hne).const_mul w)
  rw [fderiv_const_mul (DifferentiableAt.fun_sum h2), fderiv_fun_sum h2]
  simp only [smul_apply, smul_eq_mul, sum_apply]
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

theorem ginibreInteractionPotential_coordinate_laplacian {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) (j : Fin n) :
    secondDirectionalDerivative (ginibreInteractionPotential n) (realCoordinateDirection j) z +
      secondDirectionalDerivative (ginibreInteractionPotential n) (imaginaryCoordinateDirection j) z
          =
      0 := by
  unfold secondDirectionalDerivative
  rw [show realCoordinateDirection j = coordinateDirection j 1 from rfl,
    show imaginaryCoordinateDirection j = coordinateDirection j Complex.I from rfl,
    ginibreInteractionPotential_coordinate_hessian z (coordinateDirection j 1) hz j 1,
    ginibreInteractionPotential_coordinate_hessian z (coordinateDirection j Complex.I) hz j
        Complex.I]
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
  ring

theorem ginibreInteractionPotential_laplacian {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) : configurationLaplacian (ginibreInteractionPotential n) z = 0 := by
  unfold configurationLaplacian
  simp_rw [ginibreInteractionPotential_coordinate_laplacian z hz]
  simp

/-- The interaction's actual OU Itô drift is constant. -/
theorem ginibreInteractionPotential_ou_generator {n : ℕ} (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z) :
    fderiv ℝ (ginibreInteractionPotential n) z ((-2*α/(n : ℝ)) • z) +
      (α/(n : ℝ)^2)*configurationLaplacian (ginibreInteractionPotential n) z =
    (2*α/(n : ℝ)) * (2*vandermondeDegree n : ℕ) := by
  rw [map_smul, fderiv_ginibreInteractionPotential_radial n z hz,
    ginibreInteractionPotential_laplacian z hz]
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring

theorem fderiv_ginibreInteractionPotential_realCoordinate {n : ℕ}
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    fderiv ℝ (ginibreInteractionPotential n) z (realCoordinateDirection j) =
      -2*(ginibreCoulombInteraction n z j).re := by
  rw [show realCoordinateDirection j = coordinateDirection j 1 from rfl,
    fderiv_ginibreInteractionPotential_coordinate z hz j 1, ginibreCoulombInteraction_re]
  simp only [one_div]
  congr 1
  exact map_sum Complex.reCLM _ _

theorem fderiv_ginibreInteractionPotential_imaginaryCoordinate {n : ℕ}
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    fderiv ℝ (ginibreInteractionPotential n) z (imaginaryCoordinateDirection j) =
      -2*(ginibreCoulombInteraction n z j).im := by
  rw [show imaginaryCoordinateDirection j = coordinateDirection j Complex.I from rfl,
    fderiv_ginibreInteractionPotential_coordinate z hz j Complex.I, ginibreCoulombInteraction_im]
  simp only [div_eq_mul_inv]
  rw [show (∑ k ∈ Finset.univ.erase j, Complex.I*(z j-z k)⁻¹).re =
      -(∑ k ∈ Finset.univ.erase j, ((z j-z k)⁻¹).im) by
    change Complex.reCLM (∑ k ∈ Finset.univ.erase j, Complex.I*(z j-z k)⁻¹) = _
    rw [map_sum Complex.reCLM]
    simp [Complex.mul_re, Finset.sum_neg_distrib]]

/-- Actual original-coordinate drift relative to the stationary OU reference. -/
theorem ginibreInteractionPotential_originalDrift_real {n : ℕ} (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    (ginibreLangevinDrift n α z j).re - (-2*α/(n : ℝ))* (z j).re =
      -(α/(n : ℝ)^2)*fderiv ℝ (ginibreInteractionPotential n) z (realCoordinateDirection j) := by
  rw [fderiv_ginibreInteractionPotential_realCoordinate z hz j]
  unfold ginibreLangevinDrift
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  ring

theorem ginibreInteractionPotential_originalDrift_imaginary {n : ℕ} (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    (ginibreLangevinDrift n α z j).im - (-2*α/(n : ℝ))* (z j).im =
      -(α/(n : ℝ)^2)*fderiv ℝ (ginibreInteractionPotential n) z (imaginaryCoordinateDirection j) :=
          by
  rw [fderiv_ginibreInteractionPotential_imaginaryCoordinate z hz j]
  unfold ginibreLangevinDrift
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  ring

end
end GinibrePoincare
