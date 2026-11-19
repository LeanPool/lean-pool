/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteInverseSquareRoot.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteWeightedEnergy
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianProductIntegral
public import LeanPool.GinibrePoincare.Analysis.HolomorphicVandermondeDivision
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-! # The inverse square root of the antiholomorphic number operator

The normalization is that of arXiv:2608.19358v2, Theorem 1.10:
the eigenvalue on antiholomorphic degree `m` is `n * m`.
The multiplier vanishes on the holomorphic kernel.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- The multiplier `(√(n m))⁻¹` attached to Hermite modes of total antiholomorphic degree `m`;
it equals `0` when `n m = 0`. -/
def hermiteInverseSquareRootWeight (n m : ℕ) : ℝ :=
  (Real.sqrt (n * m : ℕ))⁻¹

/-- The same multiplier applied to a finite coefficient vector. -/
def finiteHermiteInverseSquareRootCoefficients {n : ℕ}
    (c : HermiteMultiIndex n →₀ ℂ) : HermiteMultiIndex n →₀ ℂ :=
  Finsupp.onFinset c.support
    (fun pq => (hermiteInverseSquareRootWeight n (totalAntiDegree pq) : ℂ) * c pq)
    (by intro pq hp; exact Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hp))

@[simp] theorem finiteHermiteInverseSquareRootCoefficients_apply {n : ℕ}
    (c : HermiteMultiIndex n →₀ ℂ) (pq : HermiteMultiIndex n) :
    finiteHermiteInverseSquareRootCoefficients c pq =
      (hermiteInverseSquareRootWeight n (totalAntiDegree pq) : ℂ) * c pq := rfl

@[simp] theorem hermiteInverseSquareRootWeight_zero (n : ℕ) :
    hermiteInverseSquareRootWeight n 0 = 0 := by
  simp [hermiteInverseSquareRootWeight]

theorem hermiteInverseSquareRootWeight_nonneg (n m : ℕ) :
    0 ≤ hermiteInverseSquareRootWeight n m := by
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem hermiteInverseSquareRootWeight_le_one (n m : ℕ) :
    hermiteInverseSquareRootWeight n m ≤ 1 := by
  by_cases h : n * m = 0
  · simp [hermiteInverseSquareRootWeight, h]
  · have hp : (1 : ℝ) ≤ (n * m : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    have hs : (1 : ℝ) ≤ Real.sqrt (n * m : ℕ) := by
      simpa using Real.sqrt_le_sqrt hp
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hs)).mpr hs

/-- The `ℓ²` vector of Hermite coefficients of `g`, each multiplied by
`hermiteInverseSquareRootWeight n` of the total antiholomorphic degree of its index. -/
def gaussianHermiteInverseSquareRootCoefficients {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) : lp (fun _ : HermiteMultiIndex n => ℂ) 2 :=
  ⟨fun pq => (hermiteInverseSquareRootWeight n (totalAntiDegree pq) : ℂ) *
      gaussianHermiteCoefficient hn g pq,
    (lp.memℓp ((gaussianHermiteHilbertBasis n hn).repr g)).mono' (by
      intro pq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hermiteInverseSquareRootWeight_nonneg n _)]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (hermiteInverseSquareRootWeight_le_one n _))⟩

/-- Genuine Gaussian `L²` synthesis of `N_n⁻¹ᐟ²` on positive modes. -/
def gaussianHermiteInverseSquareRoot {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) : Lp ℂ 2 (complexGaussianMeasure n) :=
  (gaussianHermiteHilbertBasis n hn).repr.symm
    (gaussianHermiteInverseSquareRootCoefficients hn g)

@[simp] theorem gaussianHermiteCoefficient_inverseSquareRoot {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (gaussianHermiteInverseSquareRoot hn g) pq =
      (hermiteInverseSquareRootWeight n (totalAntiDegree pq) : ℂ) *
        gaussianHermiteCoefficient hn g pq := by
  simp [gaussianHermiteCoefficient, gaussianHermiteInverseSquareRoot,
    gaussianHermiteInverseSquareRootCoefficients]

theorem gaussianHermiteInverseSquareRoot_norm_le {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    ‖gaussianHermiteInverseSquareRoot hn g‖ ≤ ‖g‖ := by
  rw [gaussianHermiteInverseSquareRoot, LinearIsometryEquiv.norm_map]
  rw [← (gaussianHermiteHilbertBasis n hn).repr.norm_map g]
  apply lp.norm_mono (by norm_num)
  intro pq
  change ‖(hermiteInverseSquareRootWeight n (totalAntiDegree pq) : ℂ) *
    gaussianHermiteCoefficient hn g pq‖ ≤ ‖gaussianHermiteCoefficient hn g pq‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hermiteInverseSquareRootWeight_nonneg n _)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (hermiteInverseSquareRootWeight_le_one n _)

theorem gaussianHermiteCoefficient_ext {n : ℕ} (hn : 0 < n)
    {g h : Lp ℂ 2 (complexGaussianMeasure n)}
    (he : ∀ pq, gaussianHermiteCoefficient hn g pq = gaussianHermiteCoefficient hn h pq) :
    g = h := by
  apply (gaussianHermiteHilbertBasis n hn).repr.injective
  exact lp.ext (funext he)

/-- Finite synthesis agrees with the full Gaussian `L²` inverse square root. -/
theorem gaussianHermiteInverseSquareRoot_finiteHermiteCombination
    (n : ℕ) (hn : 0 < n) (c : HermiteMultiIndex n →₀ ℂ) :
    gaussianHermiteInverseSquareRoot hn (finiteHermiteCombination n hn c) =
      finiteHermiteCombination n hn (finiteHermiteInverseSquareRootCoefficients c) := by
  apply gaussianHermiteCoefficient_ext hn
  intro pq
  rw [gaussianHermiteCoefficient_inverseSquareRoot,
    gaussianHermiteCoefficient_finiteHermiteCombination,
    gaussianHermiteCoefficient_finiteHermiteCombination,
    finiteHermiteInverseSquareRootCoefficients_apply]

/-- Bounded linear operator implementing the full inverse square root. -/
def gaussianHermiteInverseSquareRootCLM {n : ℕ} (hn : 0 < n) :
    Lp ℂ 2 (complexGaussianMeasure n) →L[ℂ] Lp ℂ 2 (complexGaussianMeasure n) :=
  LinearMap.mkContinuous
    { toFun := gaussianHermiteInverseSquareRoot hn
      map_add' := by
        intro g h
        apply gaussianHermiteCoefficient_ext hn
        intro pq
        have ha (u v : Lp ℂ 2 (complexGaussianMeasure n)) :
            gaussianHermiteCoefficient hn (u + v) pq =
              gaussianHermiteCoefficient hn u pq + gaussianHermiteCoefficient hn v pq := by
          simp only [gaussianHermiteCoefficient_eq_inner, inner_add_right]
        rw [gaussianHermiteCoefficient_inverseSquareRoot, ha, ha,
          gaussianHermiteCoefficient_inverseSquareRoot,
          gaussianHermiteCoefficient_inverseSquareRoot, mul_add]
      map_smul' := by
        intro a g
        apply gaussianHermiteCoefficient_ext hn
        intro pq
        have ha (u : Lp ℂ 2 (complexGaussianMeasure n)) :
            gaussianHermiteCoefficient hn (a • u) pq =
              a * gaussianHermiteCoefficient hn u pq := by
          simp only [gaussianHermiteCoefficient_eq_inner, inner_smul_right]
        change gaussianHermiteCoefficient hn (gaussianHermiteInverseSquareRoot hn (a • g)) pq =
          gaussianHermiteCoefficient hn (a • gaussianHermiteInverseSquareRoot hn g) pq
        rw [gaussianHermiteCoefficient_inverseSquareRoot, ha, ha,
          gaussianHermiteCoefficient_inverseSquareRoot]
        ring }
    1 (by intro g; simpa using gaussianHermiteInverseSquareRoot_norm_le hn g)

@[simp] theorem gaussianHermiteInverseSquareRootCLM_apply {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianHermiteInverseSquareRootCLM hn g = gaussianHermiteInverseSquareRoot hn g := rfl

/-- The synthesized inverse square root acts on each Hermite level by
the paper's scalar `1 / sqrt(n * m)`. -/
theorem gaussianHermiteMode_inverseSquareRoot {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (m : ℕ) :
    gaussianHermiteMode hn m (gaussianHermiteInverseSquareRoot hn g) =
      (hermiteInverseSquareRootWeight n m : ℂ) • gaussianHermiteMode hn m g := by
  apply gaussianHermiteCoefficient_ext hn
  intro pq
  rw [gaussianHermiteCoefficient_eq_inner hn (gaussianHermiteMode hn m
    (gaussianHermiteInverseSquareRoot hn g)) pq, inner_basis_gaussianHermiteMode]
  rw [gaussianHermiteCoefficient_eq_inner hn
    ((hermiteInverseSquareRootWeight n m : ℂ) • gaussianHermiteMode hn m g) pq,
    inner_smul_right, inner_basis_gaussianHermiteMode]
  split_ifs with he
  · rw [gaussianHermiteCoefficient_inverseSquareRoot, he]
  · simp

@[simp] theorem gaussianHermiteMode_zero_inverseSquareRoot {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianHermiteMode hn 0 (gaussianHermiteInverseSquareRoot hn g) = 0 := by
  rw [gaussianHermiteMode_inverseSquareRoot, hermiteInverseSquareRootWeight_zero]
  simp

/-- Removing the holomorphic mode before applying the inverse square
root leaves the result unchanged, matching the projection in Theorem 1.10. -/
theorem gaussianHermiteInverseSquareRoot_positiveProjection {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianHermiteInverseSquareRoot hn (g - gaussianHermiteMode hn 0 g) =
      gaussianHermiteInverseSquareRoot hn g := by
  apply gaussianHermiteCoefficient_ext hn
  intro pq
  rw [gaussianHermiteCoefficient_inverseSquareRoot, gaussianHermiteCoefficient_inverseSquareRoot]
  have hc : gaussianHermiteCoefficient hn (g - gaussianHermiteMode hn 0 g) pq =
      gaussianHermiteCoefficient hn g pq -
        (if totalAntiDegree pq = 0 then gaussianHermiteCoefficient hn g pq else 0) := by
    rw [gaussianHermiteCoefficient_eq_inner, inner_sub_right,
      inner_basis_gaussianHermiteMode, ← gaussianHermiteCoefficient_eq_inner]
  rw [hc]
  by_cases hpq : totalAntiDegree pq = 0
  · simp [hpq]
  · simp [hpq]

theorem hermiteInverseSquareRootWeight_sq {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    hermiteInverseSquareRootWeight n m ^ 2 = ((n * m : ℕ) : ℝ)⁻¹ := by
  rw [hermiteInverseSquareRootWeight, inv_pow, Real.sq_sqrt]
  positivity

/-- Squared mode norms of the actual `L²` inverse square root. -/
theorem norm_sq_gaussianHermiteMode_inverseSquareRoot {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) {m : ℕ} (hm : 0 < m) :
    ‖gaussianHermiteMode hn m (gaussianHermiteInverseSquareRoot hn g)‖ ^ 2 =
      ((n * m : ℕ) : ℝ)⁻¹ * ‖gaussianHermiteMode hn m g‖ ^ 2 := by
  rw [gaussianHermiteMode_inverseSquareRoot, norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hermiteInverseSquareRootWeight_nonneg _ _),
    hermiteInverseSquareRootWeight_sq hn hm]

end
end GinibrePoincare
