/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonian.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathDriftRegularity
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.HolomorphicVandermondeDivision
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! The actual logarithmic Ginibre Hamiltonian, smooth away from collisions. -/

@[expose] public section
open scoped BigOperators ContDiff ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- Logarithmic repulsion with the normalization of the actual Langevin drift. -/
def ginibreHamiltonian (n : ℕ) (z : Configuration n) : ℝ :=
  (n : ℝ) * configurationNormSq z - Real.log (vandermondeWeight z)

theorem contDiff_vandermondeWeight (n : ℕ) :
    ContDiff ℝ ∞ (vandermondeWeight : Configuration n → ℝ) := by
  have hr := Complex.reCLM.contDiff.comp (contDiff_vandermonde n)
  have hi := Complex.imCLM.contDiff.comp (contDiff_vandermonde n)
  convert! (hr.mul hr).add (hi.mul hi) using 1

theorem vandermondeWeight_pos_of_collisionFree {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) : 0 < vandermondeWeight z := by
  apply lt_of_le_of_ne (Complex.normSq_nonneg _)
  exact Ne.symm (fun h => ((collisionFree_iff_not_mem_collisionSet z).mp hz)
      ((vandermondeWeight_eq_zero_iff z).mp h))

theorem ginibreHamiltonian_contDiffAt (n : ℕ) (z : Configuration n)
    (hz : CollisionFree z) : ContDiffAt ℝ ∞ (ginibreHamiltonian n) z := by
  exact ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Configuration n => (n : ℝ)) z).mul
      (contDiff_configurationNormSq (n := n)).contDiffAt).sub
    ((contDiff_vandermondeWeight n).contDiffAt.log
      (ne_of_gt (vandermondeWeight_pos_of_collisionFree z hz)))

theorem ginibreHamiltonian_exp_neg {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) : Real.exp (-ginibreHamiltonian n z) = ginibreWeight n z := by
  unfold ginibreHamiltonian ginibreWeight gaussianWeight
  rw [neg_sub, Real.exp_sub, Real.exp_log (vandermondeWeight_pos_of_collisionFree z hz)]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  ring_nf

theorem fderiv_ginibreHamiltonian_coordinate {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) (j : Fin n) (w : ℂ) :
    fderiv ℝ (ginibreHamiltonian n) z (coordinateDirection j w) =
      (n : ℝ) * fderiv ℝ configurationNormSq z (coordinateDirection j w) -
        2 * (∑ k ∈ Finset.univ.erase j, w / (z j - z k)).re := by
  have hs : DifferentiableAt ℝ configurationNormSq z := ((contDiff_configurationNormSq (n :=
      n)).differentiable (by simp)).differentiableAt
  have hv : DifferentiableAt ℝ vandermondeWeight z := ((contDiff_vandermondeWeight n).differentiable
      (by simp)).differentiableAt
  have hp := vandermondeWeight_pos_of_collisionFree z hz
  unfold ginibreHamiltonian
  rw [fderiv_fun_sub (hs.const_mul _) (hv.log (ne_of_gt hp)), fderiv_const_mul hs,
    fderiv.log hv (ne_of_gt hp)]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  rw [fderiv_vandermondeWeight_apply_coordinateDirection z hz j w]
  field_simp

theorem fderiv_configurationNormSq_coordinate {n : ℕ} (z : Configuration n)
    (j : Fin n) (w : ℂ) :
    fderiv ℝ configurationNormSq z (coordinateDirection j w) =
      2 * (conj (z j) * w).re := by
  rw [fderiv_configurationNormSq_apply]
  congr 1
  unfold coordinateDirection
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    simp [hbj]
  · simp

theorem fderiv_ginibreHamiltonian_realCoordinate {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    fderiv ℝ (ginibreHamiltonian n) z (realCoordinateDirection j) =
      (n : ℝ) * ginibreRealDriftCoordinate n j z := by
  rw [show realCoordinateDirection j = coordinateDirection j 1 from rfl,
    fderiv_ginibreHamiltonian_coordinate z hz j 1,
    fderiv_configurationNormSq_coordinate]
  simp only [mul_one, Complex.conj_re, one_div]
  rw [show (∑ k ∈ Finset.univ.erase j, (z j-z k)⁻¹).re =
      ∑ k ∈ Finset.univ.erase j, ((z j-z k)⁻¹).re by
    exact map_sum Complex.reCLM _ _]
  unfold ginibreRealDriftCoordinate
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

theorem fderiv_ginibreHamiltonian_imaginaryCoordinate {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    fderiv ℝ (ginibreHamiltonian n) z (imaginaryCoordinateDirection j) =
      (n : ℝ) * ginibreImagDriftCoordinate n j z := by
  rw [show imaginaryCoordinateDirection j = coordinateDirection j Complex.I from rfl,
    fderiv_ginibreHamiltonian_coordinate z hz j Complex.I,
    fderiv_configurationNormSq_coordinate]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, neg_neg]
  simp_rw [div_eq_mul_inv]
  rw [show (∑ k ∈ Finset.univ.erase j, Complex.I * (z j-z k)⁻¹).re =
      -(∑ k ∈ Finset.univ.erase j, ((z j-z k)⁻¹).im) by
    change Complex.reCLM (∑ k ∈ Finset.univ.erase j, Complex.I * (z j-z k)⁻¹) = _
    rw [map_sum Complex.reCLM]
    simp [Complex.mul_re, Finset.sum_neg_distrib]]
  unfold ginibreImagDriftCoordinate
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  ring

end
end GinibrePoincare
