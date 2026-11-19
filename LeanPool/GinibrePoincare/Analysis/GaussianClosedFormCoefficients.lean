/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianClosedFormCoefficients.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianClosedFormSolvability
public import LeanPool.GinibrePoincare.Analysis.HermiteSecondDbarCombinatorics
public import LeanPool.GinibrePoincare.Analysis.HermiteWeightedEnergy
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Quantitative coefficient estimate for the Gaussian closed-form solver

This module defines the canonical Hermite coefficient candidate for a
solution and proves its pointwise energy bound. It does not replace weak
closedness by coefficient assumptions or assert existence of a solution.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- Candidate inverse of the antiholomorphic differential: contract with
its adjoint and divide by the actual eigenvalue `n * totalAntiDegree pq`.
The holomorphic kernel coefficient is zero. -/
def gaussianClosedFormPotentialCoefficient {n : ℕ}
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n)) (hn : 0 < n)
    (pq : HermiteMultiIndex n) : ℂ :=
  ((n * totalAntiDegree pq : ℕ) : ℂ)⁻¹ *
    ∑ j : Fin n, (Real.sqrt (n * pq.2 j : ℕ) : ℂ) *
      gaussianHermiteCoefficient hn (α j) (lowerHermiteIndex j pq)

/-- Finite Cauchy–Schwarz with the concrete lowering weights. -/
theorem gaussianClosedFormNumerator_norm_sq_le {n : ℕ}
    (q : Fin n → ℕ) (a : Fin n → ℂ) :
    ‖∑ j : Fin n, (Real.sqrt (n * q j : ℕ) : ℂ) * a j‖ ^ 2 ≤
      ((n : ℝ) * ∑ j : Fin n, (q j : ℝ)) * ∑ j : Fin n, ‖a j‖ ^ 2 := by
  have hnorm : ‖∑ j : Fin n, (Real.sqrt (n * q j : ℕ) : ℂ) * a j‖ ≤
      ∑ j : Fin n, Real.sqrt (n * q j : ℕ) * ‖a j‖ := by
    calc
      _ ≤ ∑ j : Fin n, ‖(Real.sqrt (n * q j : ℕ) : ℂ) * a j‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Fin n => Real.sqrt (n * q j : ℕ)) (fun j => ‖a j‖)
  have hs : (∑ j : Fin n, Real.sqrt (n * q j : ℕ) ^ 2) =
      (n : ℝ) * ∑ j : Fin n, (q j : ℝ) := by
    simp_rw [Real.sq_sqrt (by positivity : 0 ≤ ((n * q _ : ℕ) : ℝ))]
    simp only [Nat.cast_mul, Finset.mul_sum]
  calc
    _ ≤ (∑ j : Fin n, Real.sqrt (n * q j : ℕ) * ‖a j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ _ := by simpa only [hs] using hcs

/-- Pointwise inverse-energy bound with the paper's exact eigenvalue.
This estimate holds for arbitrary form coefficients; closedness is needed
later to identify the candidate's derivative with the input form. -/
theorem gaussianClosedFormPotentialCoefficient_energy_bound {n : ℕ}
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n)) (hn : 0 < n)
    (pq : HermiteMultiIndex n) (hq : 0 < totalAntiDegree pq) :
    ((n * totalAntiDegree pq : ℕ) : ℝ) *
        ‖gaussianClosedFormPotentialCoefficient α hn pq‖ ^ 2 ≤
      ∑ j : Fin n, if pq.2 j = 0 then 0 else
        ‖gaussianHermiteCoefficient hn (α j) (lowerHermiteIndex j pq)‖ ^ 2 := by
  let d : ℝ := (n * totalAntiDegree pq : ℕ)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Nat.mul_pos hn hq
  let a : Fin n → ℂ := fun j => if pq.2 j = 0 then 0 else
    gaussianHermiteCoefficient hn (α j) (lowerHermiteIndex j pq)
  let S : ℂ := ∑ j : Fin n, (Real.sqrt (n * pq.2 j : ℕ) : ℂ) * a j
  have hs : ‖S‖ ^ 2 ≤ d * ∑ j : Fin n, ‖a j‖ ^ 2 := by
    convert gaussianClosedFormNumerator_norm_sq_le pq.2 a using 1
    simp [d, totalAntiDegree, Nat.cast_sum, Nat.cast_mul]
  have he : ‖gaussianClosedFormPotentialCoefficient α hn pq‖ = d⁻¹ * ‖S‖ := by
    unfold gaussianClosedFormPotentialCoefficient
    rw [norm_mul, norm_inv]
    congr 1
    · simp [d]
    · congr 1
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [a]
      by_cases h : pq.2 j = 0 <;> simp [h]
  have ha : (∑ j : Fin n, if pq.2 j = 0 then (0 : ℝ) else
      ‖gaussianHermiteCoefficient hn (α j) (lowerHermiteIndex j pq)‖ ^ 2) =
      ∑ j : Fin n, ‖a j‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [a]
    by_cases h : pq.2 j = 0 <;> simp [h]
  rw [he, ha]
  change d * (d⁻¹ * ‖S‖) ^ 2 ≤ ∑ j : Fin n, ‖a j‖ ^ 2
  have hid : d * (d⁻¹ * ‖S‖) ^ 2 = ‖S‖ ^ 2 / d := by
    field_simp
  rw [hid]
  exact (div_le_iff₀ hd).mpr (by simpa [mul_comm] using hs)

/-- Algebraic contraction identity for a single positive Hermite level.
Its compatibility premise is the finite curl identity; deriving that premise
from compact tests is intentionally a separate analytic step. -/
theorem gaussianClosedForm_contraction_of_compatible {n : ℕ}
    (hn : 0 < n) (q : Fin n → ℕ) (hq : 0 < ∑ k, q k)
    (a : Fin n → ℂ) (j : Fin n)
    (hcompat : ∀ k : Fin n, 0 < q k →
      (Real.sqrt (n * q j : ℕ) : ℂ) * a k =
        (Real.sqrt (n * q k : ℕ) : ℂ) * a j) :
    (Real.sqrt (n * q j : ℕ) : ℂ) *
      (((n * ∑ k, q k : ℕ) : ℂ)⁻¹ *
        ∑ k : Fin n, (Real.sqrt (n * q k : ℕ) : ℂ) * a k) = a j := by
  let κ : Fin n → ℂ := fun k => Real.sqrt (n * q k : ℕ)
  let d : ℂ := (n * ∑ k, q k : ℕ)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hn hq))
  have hsum : (∑ k : Fin n, κ k * (κ j * a k)) = d * a j := by
    calc
      _ = ∑ k : Fin n, ((n * q k : ℕ) : ℂ) * a j := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hqk : q k = 0
        · simp [κ, hqk]
        · rw [show κ j * a k = κ k * a j from hcompat k (Nat.pos_of_ne_zero hqk),
            ← mul_assoc]
          have hs : κ k * κ k = ((n * q k : ℕ) : ℂ) := by
            dsimp [κ]
            rw [← pow_two]
            exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ ((n * q k : ℕ) : ℝ))
          rw [hs]
      _ = d * a j := by
        rw [← Finset.sum_mul]
        congr 1
        simp [d, Nat.cast_mul, Nat.cast_sum, Finset.mul_sum]
  change κ j * (d⁻¹ * ∑ k : Fin n, κ k * a k) = a j
  calc
    _ = d⁻¹ * ∑ k : Fin n, κ k * (κ j * a k) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = d⁻¹ * (d * a j) := by rw [hsum]
    _ = a j := by rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]

/-- The positive-coordinate restriction removes the saturated lowering
collision: each input coefficient is counted exactly once. -/
theorem hasSum_gaussianClosedFormLoweredCoefficient {n : ℕ}
    (hn : 0 < n) (g : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) :
    HasSum (fun pq : HermiteMultiIndex n => if pq.2 j = 0 then 0 else
      ‖gaussianHermiteCoefficient hn g (lowerHermiteIndex j pq)‖ ^ 2)
      (‖g‖ ^ 2) := by
  let e := raiseHermiteIndexEquivPositive j
  let F : HermiteMultiIndex n → ℝ := fun pq => if pq.2 j = 0 then 0 else
    ‖gaussianHermiteCoefficient hn g (lowerHermiteIndex j pq)‖ ^ 2
  have hsSub : HasSum (fun pq : {pq : HermiteMultiIndex n // 0 < pq.2 j} => F pq)
      (‖g‖ ^ 2) := by
    apply e.hasSum_iff.mp
    convert hasSum_norm_sq_gaussianHermiteCoefficient hn g using 1
    funext pq
    have hlow : lowerHermiteIndex j (raiseHermiteIndex j pq) = pq := e.left_inv pq
    change (if (raiseHermiteIndex j pq).2 j = 0 then 0 else
      ‖gaussianHermiteCoefficient hn g (lowerHermiteIndex j (raiseHermiteIndex j pq))‖ ^ 2) =
        ‖gaussianHermiteCoefficient hn g pq‖ ^ 2
    have hp : (raiseHermiteIndex j pq).2 j ≠ 0 := by
      simp [raiseHermiteIndex, raiseAt]
    rw [ite_eq_right hp, hlow]
  have hsInd : Summable (({pq : HermiteMultiIndex n | 0 < pq.2 j} : Set _).indicator F) :=
    summable_subtype_iff_indicator.mp hsSub.summable
  have hFind : ({pq : HermiteMultiIndex n | 0 < pq.2 j} : Set _).indicator F = F := by
    funext pq
    simp only [Set.indicator, Set.mem_ofPred_eq]
    split_ifs with hq
    · rfl
    · simp [F, Nat.eq_zero_of_not_pos hq]
  have hsF : Summable F := by simpa only [hFind] using hsInd
  change HasSum F (‖g‖ ^ 2)
  rw [← hsSub.tsum_eq]
  convert hsF.hasSum using 1
  calc
    (∑' pq : {pq : HermiteMultiIndex n // 0 < pq.2 j}, F pq.1) =
        ∑' pq : HermiteMultiIndex n,
          ({pq : HermiteMultiIndex n | 0 < pq.2 j} : Set _).indicator F pq :=
      tsum_subtype {pq : HermiteMultiIndex n | 0 < pq.2 j} F
    _ = ∑' pq : HermiteMultiIndex n, F pq := by rw [hFind]

/-- The spectral candidate has the sharp coefficient majorant `1/n`. -/
theorem gaussianClosedFormPotentialCoefficient_norm_bound {n : ℕ}
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n)) (hn : 0 < n)
    (pq : HermiteMultiIndex n) :
    ‖gaussianClosedFormPotentialCoefficient α hn pq‖ ^ 2 ≤
      (n : ℝ)⁻¹ * ∑ j : Fin n, if pq.2 j = 0 then 0 else
        ‖gaussianHermiteCoefficient hn (α j) (lowerHermiteIndex j pq)‖ ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mul_comm (n : ℝ)⁻¹, ← div_eq_mul_inv]
  apply (le_div_iff₀ hnR).mpr
  by_cases hq : totalAntiDegree pq = 0
  · simp only [gaussianClosedFormPotentialCoefficient, hq, mul_zero,
      Nat.cast_zero, inv_zero, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    positivity
  · have hpos : 0 < totalAntiDegree pq := Nat.pos_of_ne_zero hq
    have hdegree : (n : ℝ) ≤ (n * totalAntiDegree pq : ℕ) := by
      exact_mod_cast Nat.le_mul_of_pos_right n hpos
    calc
      ‖gaussianClosedFormPotentialCoefficient α hn pq‖ ^ 2 * (n : ℝ) ≤
          ((n * totalAntiDegree pq : ℕ) : ℝ) *
            ‖gaussianClosedFormPotentialCoefficient α hn pq‖ ^ 2 := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hdegree (sq_nonneg _)
      _ ≤ _ := gaussianClosedFormPotentialCoefficient_energy_bound α hn pq hpos

/-- The canonical potential coefficients are genuinely square summable. -/
theorem summable_gaussianClosedFormPotentialCoefficient_norm_sq {n : ℕ}
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n)) (hn : 0 < n) :
    Summable (fun pq : HermiteMultiIndex n =>
      ‖gaussianClosedFormPotentialCoefficient α hn pq‖ ^ 2) := by
  have hs : Summable (fun pq : HermiteMultiIndex n =>
      ∑ j : Fin n, if pq.2 j = 0 then (0 : ℝ) else
        ‖gaussianHermiteCoefficient hn (α j) (lowerHermiteIndex j pq)‖ ^ 2) := by
    apply summable_sum
    intro j hj
    exact (hasSum_gaussianClosedFormLoweredCoefficient hn (α j) j).summable
  exact Summable.of_nonneg_of_le (fun pq => sq_nonneg _)
    (gaussianClosedFormPotentialCoefficient_norm_bound α hn) (hs.mul_left (n : ℝ)⁻¹)

/-- Genuine ℓ² data for the candidate; no solution or analytic coefficient
identity is assumed. -/
def gaussianClosedFormPotentialCoefficients {n : ℕ}
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n)) (hn : 0 < n) :
    lp (fun _ : HermiteMultiIndex n => ℂ) 2 :=
  ⟨gaussianClosedFormPotentialCoefficient α hn,
    memℓp_gen (by simpa using summable_gaussianClosedFormPotentialCoefficient_norm_sq α hn)⟩

/-- The actual Gaussian L² candidate for Remark 2.4. Its weak derivative
identification remains a separate analytic theorem. -/
def gaussianClosedFormPotential {n : ℕ}
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n)) (hn : 0 < n) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  (gaussianHermiteHilbertBasis n hn).repr.symm
    (gaussianClosedFormPotentialCoefficients α hn)

@[simp] theorem gaussianHermiteCoefficient_closedFormPotential {n : ℕ}
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n)) (hn : 0 < n)
    (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (gaussianClosedFormPotential α hn) pq =
      gaussianClosedFormPotentialCoefficient α hn pq := by
  simp [gaussianHermiteCoefficient, gaussianClosedFormPotential,
    gaussianClosedFormPotentialCoefficients]

/-- Sharp Gaussian L² bound for the explicitly synthesized potential.
Closedness is not needed for this bound; identification as a solution still
requires the distributional curl-to-coefficient bridge. -/
theorem gaussianClosedFormPotential_norm_sq_le {n : ℕ}
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n)) (hn : 0 < n) :
    ‖gaussianClosedFormPotential α hn‖ ^ 2 ≤
      (n : ℝ)⁻¹ * ∑ j : Fin n, ‖α j‖ ^ 2 := by
  have hnorm : ‖gaussianClosedFormPotential α hn‖ ^ 2 =
      ∑' pq : HermiteMultiIndex n, ‖gaussianClosedFormPotentialCoefficient α hn pq‖ ^ 2 := by
    rw [gaussianClosedFormPotential, LinearIsometryEquiv.norm_map]
    simpa [gaussianClosedFormPotentialCoefficients] using
      lp.norm_rpow_eq_tsum (by norm_num) (gaussianClosedFormPotentialCoefficients α hn)
  let f : Fin n → HermiteMultiIndex n → ℝ := fun j pq => if pq.2 j = 0 then 0 else
    ‖gaussianHermiteCoefficient hn (α j) (lowerHermiteIndex j pq)‖ ^ 2
  have hsf : ∀ j : Fin n, Summable (f j) := fun j =>
    (hasSum_gaussianClosedFormLoweredCoefficient hn (α j) j).summable
  have hs : Summable (fun pq => ∑ j : Fin n, f j pq) :=
    summable_sum (fun j _ => hsf j)
  have hsum : (∑' pq, ∑ j : Fin n, f j pq) = ∑ j : Fin n, ‖α j‖ ^ 2 := by
    rw [Summable.tsum_finsetSum (fun j _ => hsf j)]
    apply Finset.sum_congr rfl
    intro j hj
    exact (hasSum_gaussianClosedFormLoweredCoefficient hn (α j) j).tsum_eq
  rw [hnorm]
  calc
    _ ≤ ∑' pq, (n : ℝ)⁻¹ * ∑ j : Fin n, f j pq :=
      Summable.tsum_le_tsum (gaussianClosedFormPotentialCoefficient_norm_bound α hn)
        (summable_gaussianClosedFormPotentialCoefficient_norm_sq α hn)
        (hs.mul_left (n : ℝ)⁻¹)
    _ = _ := by rw [tsum_mul_left, hsum]

@[simp] theorem gaussianClosedFormPotentialCoefficient_zero_degree {n : ℕ}
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n)) (hn : 0 < n)
    (pq : HermiteMultiIndex n) (hq : totalAntiDegree pq = 0) :
    gaussianClosedFormPotentialCoefficient α hn pq = 0 := by
  simp [gaussianClosedFormPotentialCoefficient, hq]

end
end GinibrePoincare

