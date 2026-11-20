/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryQuadraticGenerator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.ComplexGeneratorCalculus
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Correspondence auxiliary quadratic generator

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `complexGinibrePregenerator_holomorphicQuadraticSum`.
-/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The literal symmetric holomorphic quadratic preceding Theorem 1.4. -/
def holomorphicQuadraticSum {n : ℕ} (z : Configuration n) : ℂ := ∑ j, z j ^ 2

private theorem quadraticSum_hasFDeriv (n : ℕ) (z : Configuration n) :
    HasFDerivAt holomorphicQuadraticSum
      (∑ j : Fin n, (2 * z j) • (ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ)) z := by
  unfold holomorphicQuadraticSum
  apply HasFDerivAt.fun_sum
  intro j hj
  convert ((ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ).hasFDerivAt.pow 2) using 1 <;>
    simp [pow_one]

private theorem quadraticSum_derivative (n : ℕ) (z v : Configuration n) :
    fderiv ℝ holomorphicQuadraticSum z v = ∑ j, 2 * z j * v j := by
  rw [(quadraticSum_hasFDeriv n z).fderiv]
  simp [smul_eq_mul]

private theorem quadraticSum_second (n : ℕ) (v z : Configuration n) :
    complexSecondDirectionalDerivative holomorphicQuadraticSum v z = ∑ j, 2 * v j * v j := by
  unfold complexSecondDirectionalDerivative
  have he : (fun w : Configuration n => fderiv ℝ holomorphicQuadraticSum w v) =
      (fun w => ∑ j, 2 * v j * w j) := by
    funext w
    rw [quadraticSum_derivative]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  let T : Configuration n →L[ℝ] ℂ := ∑ j : Fin n, (2 * v j) • ContinuousLinearMap.proj j
  change fderiv ℝ (fun w => ∑ j, 2 * v j * w j) z v = _
  have heT : (fun w => ∑ j, 2 * v j * w j) = T := by
    funext w
    simp [T, smul_eq_mul]
  rw [heT, T.fderiv]
  simp [T, smul_eq_mul]

/-- Exact non-polynomial pair-ratio formula for the actual Ginibre generator,
at speed `α=n`, valid with its literal totalized definition even at collisions. -/
theorem complexGinibrePregenerator_holomorphicQuadraticSum (n : ℕ)
    (z : Configuration n) :
    complexGinibrePregenerator n holomorphicQuadraticSum z =
      -4 * holomorphicQuadraticSum z +
      (4 / (n : ℂ)) * ∑ j : Fin n, ∑ k ∈ Finset.Ioi j,
        (z j - z k)^2 / (Complex.normSq (z j - z k) : ℂ) := by
  rw [complexGinibrePregenerator_eq_direct]
  · unfold directComplexGinibrePregenerator
    simp only [quadraticSum_second, quadraticSum_derivative]
    have hl (j : Fin n) :
        (∑ k : Fin n, 2 * realCoordinateDirection j k * realCoordinateDirection j k) +
        (∑ k : Fin n, 2 * imaginaryCoordinateDirection j k * imaginaryCoordinateDirection j k) = 0
            := by
      simp [realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection, mul_assoc]
    have hd (j : Fin n) :
        (∑ k : Fin n, 2 * z k * coordinateDirection j (z j) k) = 2 * z j ^ 2 := by
      simp [coordinateDirection, pow_two, mul_assoc]
    have hp (j k : Fin n) (hjk : k ∈ Finset.Ioi j) :
        (∑ l : Fin n, 2 * z l * coulombPairDirection j k z l) =
          2 * (z j-z k)^2 / (Complex.normSq (z j-z k) : ℂ) := by
      simp only [coulombPairDirection, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      simp [coordinateDirection]
      ring
    simp only [hl, Finset.sum_const_zero, mul_zero, zero_sub, hd]
    have hpsum : (∑ j : Fin n, ∑ k ∈ Finset.Ioi j,
      ∑ l : Fin n, 2*z l*coulombPairDirection j k z l) =
      ∑ j : Fin n, ∑ k ∈ Finset.Ioi j,
        2*(z j-z k)^2/(Complex.normSq (z j-z k) : ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      exact hp j k hk
    rw [hpsum]
    simp only [Finset.mul_sum, holomorphicQuadraticSum]
    push_cast
    ring_nf
    rw [Finset.sum_neg_distrib]
    ring
  · exact fun z => (quadraticSum_hasFDeriv n z).differentiableAt
  · intro v
    let T : Configuration n →L[ℝ] ℂ := ∑ j : Fin n, (2*v j) • ContinuousLinearMap.proj j
    have he : (fun w : Configuration n => fderiv ℝ holomorphicQuadraticSum w v) = T := by
      funext w
      rw [quadraticSum_derivative]
      simp [T, smul_eq_mul, mul_comm, mul_left_comm]
    rw [he]
    exact T.differentiable

end
end GinibrePoincare
