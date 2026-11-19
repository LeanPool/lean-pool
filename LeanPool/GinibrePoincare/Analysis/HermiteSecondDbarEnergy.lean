/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteSecondDbarEnergy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteInverseSquareRoot
public import LeanPool.GinibrePoincare.Analysis.HermiteSecondDbarCombinatorics
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit

/-! # Second antiholomorphic Hermite energy after inverse square root

This file identifies the spectral weights occurring in Theorem 1.10 of
arXiv:2608.19358v2. Identification with weak second derivatives is a
separate analytic assertion; no such identification is assumed here.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- For finite Hermite polynomials the spectral second-lowering energy
is the actual integral of the squared second Wirtinger derivatives. -/
theorem finiteGaussianSecondDbarIntegralEnergy (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    (∑ k : Fin n, ∑ j : Fin n,
      ∫ z, conj (dbarComponent (dbarComponent (finiteHermiteFunction n hn c) k) j z) *
        dbarComponent (dbarComponent (finiteHermiteFunction n hn c) k) j z
        ∂complexGaussianMeasure n) =
      (c.sum (fun pq a => (n ^ 2 *
        (totalAntiDegree pq * (totalAntiDegree pq - 1)) : ℕ) * Complex.normSq a) : ℂ) := by
  have hc (k : Fin n) : dbarComponent (finiteHermiteFunction n hn c) k =
      finiteHermiteFunction n hn (loweredCoefficients n c k) := by
    funext z
    exact dbarComponent_finiteHermiteFunction n hn c k z
  simp_rw [hc, integral_conj_dbarComponent_finiteHermiteFunction_mul]
  have he := sum_norm_sq_second_lowered n hn c
  unfold Finsupp.sum at he ⊢
  dsimp only at he ⊢
  simpa only [Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_mul,
    Complex.ofReal_natCast] using congrArg (fun x : ℝ => (x : ℂ)) he

/-- The concrete finite inverse-square-root polynomial has exactly `n`
times the finite Hermite deficit as its second-derivative energy. -/
theorem finiteInverseSquareRoot_secondDbar_energy (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    (∑ k : Fin n, ∑ j : Fin n,
      ‖finiteHermiteCombination n hn (loweredCoefficients n
        (loweredCoefficients n (finiteHermiteInverseSquareRootCoefficients c) k) j)‖ ^ 2) =
      n * finiteHermiteDeficit hn c := by
  classical
  rw [sum_norm_sq_second_lowered, finiteHermiteDeficit_eq_sum]
  have hs : (finiteHermiteInverseSquareRootCoefficients c).support ⊆ c.support := by
    intro pq hp
    rw [Finsupp.mem_support_iff, finiteHermiteInverseSquareRootCoefficients_apply] at hp
    exact Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hp)
  rw [Finsupp.sum_of_support_subset _ hs _ (by simp)]
  unfold Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pq hpq
  rw [finiteHermiteInverseSquareRootCoefficients_apply, Complex.normSq_mul,
    Complex.normSq_ofReal, ← sq]
  by_cases hm : totalAntiDegree pq = 0
  · simp [hm]
  · rw [hermiteInverseSquareRootWeight_sq hn (Nat.pos_of_ne_zero hm)]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hm0 : (totalAntiDegree pq : ℝ) ≠ 0 := by exact_mod_cast hm
    push_cast
    field_simp

/-- Each positive mode has the second-lowering weight prescribed by
the number-operator normalization. -/
theorem secondHermiteWeight_inverseSquareRoot {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (k : ℕ) :
    (n : ℝ)^2 * (k + 1) * k *
      ‖gaussianHermiteMode hn (k + 1) (gaussianHermiteInverseSquareRoot hn g)‖ ^ 2 =
      n * k * positiveHermiteModeMass hn g k := by
  rw [norm_sq_gaussianHermiteMode_inverseSquareRoot hn g (Nat.succ_pos k)]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hk0 : ((k : ℝ) + 1) ≠ 0 := by positivity
  simp only [Nat.cast_mul, Nat.cast_succ,
    positiveHermiteModeMass]
  field_simp

/-- The second-lowering spectral series is exactly `n` times the
Hermite deficit series, for the actual Gaussian `L²` inverse square root. -/
theorem hasSum_secondHermiteWeight_inverseSquareRoot {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (E : ℝ)
    (hE : HasSum (fun k : ℕ => k * positiveHermiteModeMass hn g k) E) :
    HasSum (fun k : ℕ => (n : ℝ)^2 * (k + 1) * k *
      ‖gaussianHermiteMode hn (k + 1) (gaussianHermiteInverseSquareRoot hn g)‖ ^ 2)
      (n * E) := by
  exact (hE.mul_left (n : ℝ)).congr_fun fun k =>
    by rw [secondHermiteWeight_inverseSquareRoot]; ring

/-- No spectral summability hypothesis is needed for a genuine compact
smooth Gaussian function: its actual first-derivative energy controls
the full second-lowering series of the inverse square root. -/
theorem hasSum_secondHermiteWeight_inverseSquareRoot_smoothCompact
    {n : ℕ} (hn : 0 < n) (F : Configuration n → ℂ)
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) :
    HasSum (fun k : ℕ => (n : ℝ)^2 * (k + 1) * k *
      ‖gaussianHermiteMode hn (k + 1)
        (gaussianHermiteInverseSquareRoot hn (smoothCompactL2 F hF hc))‖ ^ 2)
      (n * (gaussianDbarEnergy n F -
        (‖smoothCompactL2 F hF hc‖ ^ 2 -
          ‖gaussianHermiteMode hn 0 (smoothCompactL2 F hF hc)‖ ^ 2))) := by
  apply hasSum_secondHermiteWeight_inverseSquareRoot hn
  have hs := hasSum_weighted_positiveHermiteModeMass_smoothCompact hn F hF hc
  have hp : HasSum (fun k => positiveHermiteModeMass hn (smoothCompactL2 F hF hc) k)
      (‖smoothCompactL2 F hF hc‖ ^ 2 -
        ‖gaussianHermiteMode hn 0 (smoothCompactL2 F hF hc)‖ ^ 2) := by
    have ht := (hasSum_nat_add_iff' 1).2
      (hasSum_norm_sq_gaussianHermiteMode hn (smoothCompactL2 F hF hc))
    simpa [positiveHermiteModeMass] using ht
  exact (hs.sub hp).congr_fun fun k => by ring

end
end GinibrePoincare
