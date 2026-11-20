/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteHermiteDeficit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteEnergy
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-! # Finite Hermite deficit decomposition -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace GinibrePoincare
namespace ComplexHermite

noncomputable section

/-- The degree-zero part of a finite Hermite coefficient vector. -/
def zeroAntiCoefficients {n : ℕ} (c : HermiteMultiIndex n →₀ ℂ) :=
  coefficientsAtAntiDegree c 0

/-- The strictly positive antiholomorphic-degree part. -/
def positiveAntiCoefficients {n : ℕ} (c : HermiteMultiIndex n →₀ ℂ) :
    HermiteMultiIndex n →₀ ℂ :=
  c.filter fun pq => 0 < totalAntiDegree pq

theorem zero_add_positiveAntiCoefficients {n : ℕ}
    (c : HermiteMultiIndex n →₀ ℂ) :
    zeroAntiCoefficients c + positiveAntiCoefficients c = c := by
  ext pq
  by_cases h0 : totalAntiDegree pq = 0
  · simp [zeroAntiCoefficients, positiveAntiCoefficients,
      coefficientsAtAntiDegree, h0]
  · have hp : 0 < totalAntiDegree pq := Nat.pos_of_ne_zero h0
    simp [zeroAntiCoefficients, positiveAntiCoefficients,
      coefficientsAtAntiDegree, h0, hp]

/-- The finite Hermite vector splits into its degree-zero and positive
antiholomorphic-degree parts. -/
theorem finiteHermiteCombination_zero_add_positive (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    finiteHermiteCombination n hn c =
      finiteHermiteCombination n hn (zeroAntiCoefficients c) +
        finiteHermiteCombination n hn (positiveAntiCoefficients c) := by
  unfold finiteHermiteCombination
  rw [← map_add, zero_add_positiveAntiCoefficients]

/-- The two pieces in the zero/positive splitting are orthogonal. -/
theorem inner_zero_positiveAnti_eq_zero (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    inner ℂ (finiteHermiteCombination n hn (zeroAntiCoefficients c))
      (finiteHermiteCombination n hn (positiveAntiCoefficients c)) = 0 := by
  rw [inner_finiteHermiteCombination]
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro pq hpq
  have hz : totalAntiDegree pq = 0 := by
    have hnz := Finsupp.mem_support_iff.mp hpq
    by_contra hz
    apply hnz
    simp [zeroAntiCoefficients, coefficientsAtAntiDegree, hz]
  simp [positiveAntiCoefficients, hz]

/-- Exact Parseval/Pythagoras decomposition into degree zero and positive
degree. -/
theorem norm_sq_zero_add_positive (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    ‖finiteHermiteCombination n hn c‖ ^ 2 =
      ‖finiteHermiteCombination n hn (zeroAntiCoefficients c)‖ ^ 2 +
      ‖finiteHermiteCombination n hn (positiveAntiCoefficients c)‖ ^ 2 := by
  rw [finiteHermiteCombination_zero_add_positive]
  simp only [pow_two]
  apply norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
  exact inner_zero_positiveAnti_eq_zero n hn c

/-- The finite deficit after subtracting the positive-mode mass from the
normalized `dbar` energy. -/
def finiteHermiteDeficit {n : ℕ} (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) : ℝ :=
  (n : ℝ)⁻¹ * finiteDbarEnergy c -
    ‖finiteHermiteCombination n hn (positiveAntiCoefficients c)‖ ^ 2

/-- Exact coefficient form of the finite deficit: degree one cancels and
only degrees at least two remain. -/
theorem finiteHermiteDeficit_eq_sum (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    finiteHermiteDeficit hn c =
      c.sum fun pq a => (totalAntiDegree pq - 1 : ℕ) * Complex.normSq a := by
  unfold finiteHermiteDeficit finiteDbarEnergy
  rw [norm_sq_finiteHermiteCombination]
  rw [show (positiveAntiCoefficients c).sum
      (fun _ a => Complex.normSq a) =
      c.sum fun pq a => if 0 < totalAntiDegree pq then
        Complex.normSq a else 0 by
    classical
    unfold positiveAntiCoefficients Finsupp.sum
    have hsupp :
        (Finsupp.filter (fun pq => 0 < totalAntiDegree pq) c).support =
          c.support.filter (fun pq => 0 < totalAntiDegree pq) := by
      ext pq
      simp
    rw [hsupp, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro pq hpq
    by_cases h : 0 < totalAntiDegree pq <;> simp [h]]
  unfold Finsupp.sum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro pq hpq
  by_cases h0 : totalAntiDegree pq = 0
  · simp [h0]
  · have hp : 0 < totalAntiDegree pq := Nat.pos_of_ne_zero h0
    simp only [Nat.cast_mul, hp, ↓reduceIte, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h0),
      Nat.cast_one]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Complex.sq_norm]
    field_simp

/-- Squared norm of the finite piece of exact antiholomorphic degree `m`. -/
def finiteAntiDegreeMass (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (m : ℕ) : ℝ :=
  ‖finiteHermiteCombination n hn (coefficientsAtAntiDegree c m)‖ ^ 2

theorem finiteAntiDegreeMass_eq_sum (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (m : ℕ) :
    finiteAntiDegreeMass n hn c m =
      c.sum fun pq a => if totalAntiDegree pq = m then
        Complex.normSq a else 0 := by
  unfold finiteAntiDegreeMass
  rw [norm_sq_finiteHermiteCombination]
  classical
  unfold coefficientsAtAntiDegree Finsupp.sum
  have hsupp :
      (Finsupp.filter (fun pq => totalAntiDegree pq = m) c).support =
        c.support.filter (fun pq => totalAntiDegree pq = m) := by
    ext pq
    simp
  rw [hsupp, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro pq hpq
  by_cases h : totalAntiDegree pq = m <;> simp [h]

/-- The finite set of antiholomorphic degrees occurring in the support. -/
def activeAntiDegrees {n : ℕ} (c : HermiteMultiIndex n →₀ ℂ) : Finset ℕ :=
  c.support.image totalAntiDegree

/-- Regrouping of the exact deficit as the finite sum of degree-piece norms
with weights `m - 1`; only degrees at least two occur. -/
theorem finiteHermiteDeficit_eq_sum_degreeMass (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    finiteHermiteDeficit hn c =
      ∑ m ∈ (activeAntiDegrees c).filter (fun m => 2 ≤ m),
        (m - 1 : ℕ) * finiteAntiDegreeMass n hn c m := by
  rw [finiteHermiteDeficit_eq_sum]
  simp_rw [finiteAntiDegreeMass_eq_sum]
  unfold activeAntiDegrees Finsupp.sum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro pq hpq
  by_cases hp : 2 ≤ totalAntiDegree pq
  · have hmem : totalAntiDegree pq ∈
        (c.support.image totalAntiDegree).filter (fun m => 2 ≤ m) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨pq, hpq, rfl⟩, hp⟩
    rw [Finset.sum_eq_single (totalAntiDegree pq)]
    · simp
    · intro m hm hne
      simp [hne.symm]
    · intro hnot
      exact (hnot hmem).elim
  · have hz : totalAntiDegree pq - 1 = 0 := by omega
    simp [hp, hz]

/-- The finite degree-zero component belongs to the closed degree-zero
Hermite span. -/
theorem finiteHermiteCombination_zero_mem_closedSpan (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    finiteHermiteCombination n hn (zeroAntiCoefficients c) ∈
      hermiteAntiDegreeClosedSpan n hn 0 := by
  unfold finiteHermiteCombination zeroAntiCoefficients
  rw [Finsupp.linearCombination_apply]
  apply Submodule.sum_mem
  intro pq hpq
  apply Submodule.smul_mem
  apply hermiteL2Family_mem_antiDegreeClosedSpan
  have hpq0 := Finsupp.mem_support_iff.mp hpq
  by_contra h
  apply hpq0
  simp [coefficientsAtAntiDegree, h]

private theorem finiteHermiteCombination_positive_mem_orthogonal (n : ℕ)
    (hn : 0 < n) (c : HermiteMultiIndex n →₀ ℂ) :
    finiteHermiteCombination n hn (positiveAntiCoefficients c) ∈
      (hermiteAntiDegreeClosedSpan n hn 0 :
        Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)))ᗮ := by
  rw [show (hermiteAntiDegreeClosedSpan n hn 0 :
      Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)))ᗮ =
      (hermiteAntiDegreeSpan n hn 0)ᗮ by
    exact Submodule.orthogonal_closure _]
  rw [Submodule.mem_orthogonal']
  intro y hy
  unfold hermiteAntiDegreeSpan at hy
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · intro y hy
    obtain ⟨pq, hpq, rfl⟩ := hy
    unfold finiteHermiteCombination
    rw [(orthonormal_hermiteL2Family_gaussian n hn).inner_left_finsupp]
    have hz : ¬ 0 < totalAntiDegree pq := by
      have : totalAntiDegree pq = 0 := hpq
      omega
    simp [positiveAntiCoefficients, hz]
  · simp
  · intro x y hx hy hix hiy
    rw [inner_add_right, hix, hiy, add_zero]
  · intro a y hy hiy
    rw [inner_smul_right, hiy, mul_zero]

/-- The closed degree-zero projection of a finite Hermite combination is
exactly its degree-zero piece. -/
theorem starProjection_finiteHermiteCombination_eq_zeroPiece (n : ℕ)
    (hn : 0 < n) (c : HermiteMultiIndex n →₀ ℂ) :
    (hermiteAntiDegreeClosedSpan n hn 0).starProjection
        (finiteHermiteCombination n hn c) =
      finiteHermiteCombination n hn (zeroAntiCoefficients c) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact finiteHermiteCombination_zero_mem_closedSpan n hn c
  · rw [finiteHermiteCombination_zero_add_positive]
    simp only [add_sub_cancel_left]
    exact finiteHermiteCombination_positive_mem_orthogonal n hn c

/-- Distance from a finite Hermite combination to its degree-zero
orthogonal projection equals the norm of its positive-degree part. -/
theorem norm_sub_degreeZeroProjection_eq_positive (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    ‖finiteHermiteCombination n hn c -
        (hermiteAntiDegreeClosedSpan n hn 0).starProjection
          (finiteHermiteCombination n hn c)‖ =
      ‖finiteHermiteCombination n hn (positiveAntiCoefficients c)‖ := by
  rw [starProjection_finiteHermiteCombination_eq_zeroPiece,
    finiteHermiteCombination_zero_add_positive]
  simp

end
end ComplexHermite
end GinibrePoincare
