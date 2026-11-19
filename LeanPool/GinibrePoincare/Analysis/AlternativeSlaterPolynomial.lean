/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeSlaterPolynomial.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeSlaterExpansion

/-!
# Alternative Slater polynomial

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `slater_zero_degree_polynomial_division`, `slaterL2_eq_zero_of_repeated`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory ComplexHermite
open scoped BigOperators

/-- Repeated orbital labels give the zero determinant. -/
theorem slaterDeterminant_eq_zero_of_repeated {n : ℕ} (hn : 0 < n)
    (pq : HermiteMultiIndex n) {i j : Fin n} (hij : i ≠ j)
    (hp : pq.1 i = pq.1 j) (hq : pq.2 i = pq.2 j) (z : Configuration n) :
    slaterDeterminant hn pq z = 0 := by
  unfold slaterDeterminant
  rw [Matrix.det_zero_of_row_eq
    (M := fun i j : Fin n => normalizedEval n hn (pq.1 i) (pq.2 i) (z j)) hij
    (by funext k; rw [hp, hq]), mul_zero]

/-- Every Slater polynomial transforms by the permutation sign. -/
theorem slaterDeterminant_permute {n : ℕ} (hn : 0 < n)
    (pq : HermiteMultiIndex n) (σ : ParticlePermutation n) (z : Configuration n) :
    slaterDeterminant hn pq (permute σ z) = permutationSign σ * slaterDeterminant hn pq z := by
  unfold slaterDeterminant
  let M : Matrix (Fin n) (Fin n) ℂ := fun i j => normalizedEval n hn (pq.1 i) (pq.2 i) (z j)
  change (Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ * (M.submatrix id σ).det =
    permutationSign σ * ((Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ * M.det)
  rw [Matrix.det_permute']
  simp only [permutationSign]
  ring

/-- Holomorphic polynomial represented by the all-zero antiholomorphic
Slater labels; this is the alternant in (4.5). -/
def slaterHolomorphicPolynomial (n : ℕ) (p : Fin n → ℕ) : ConfigurationPolynomial n :=
  MvPolynomial.C (Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ *
    Matrix.det (fun i j : Fin n =>
      MvPolynomial.C (oneDimNormalization n (p i) : ℂ) * (MvPolynomial.X j) ^ p i)

theorem eval_slaterHolomorphicPolynomial {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℕ) (z : Configuration n) :
    MvPolynomial.eval z (slaterHolomorphicPolynomial n p) = slaterDeterminant hn (p, 0) z := by
  unfold slaterHolomorphicPolynomial slaterDeterminant
  rw [map_mul, MvPolynomial.eval_C, RingHom.map_det (MvPolynomial.eval z)
    (fun i j : Fin n =>
      MvPolynomial.C (oneDimNormalization n (p i) : ℂ) * (MvPolynomial.X j) ^ p i)]
  congr 1
  congr 1
  ext i j
  change MvPolynomial.eval z
    (MvPolynomial.C (oneDimNormalization n (p i) : ℂ) * (MvPolynomial.X j) ^ p i) = _
  simp

theorem slaterHolomorphicPolynomial_alternating (n : ℕ) (hn : 0 < n)
    (p : Fin n → ℕ) : IsAlternatingConfigurationPolynomial (slaterHolomorphicPolynomial n p) := by
  intro σ
  apply MvPolynomial.funext
  intro z
  rw [eval_permuteConfigurationPolynomial, eval_slaterHolomorphicPolynomial hn,
    map_mul, MvPolynomial.eval_C, eval_slaterHolomorphicPolynomial hn,
    slaterDeterminant_permute]

/-- Exact polynomial Vandermonde divisibility (4.6), with a symmetric
holomorphic quotient, for each all-holomorphic Slater determinant. -/
theorem slater_zero_degree_polynomial_division {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℕ) :
    ∃ Q : ConfigurationPolynomial n, IsSymmetricConfigurationPolynomial Q ∧
      ∀ z, slaterDeterminant hn (p, 0) z = vandermonde z * MvPolynomial.eval z Q := by
  obtain ⟨Q, hQ, hfac⟩ := alternating_polynomial_vandermonde_division
    (slaterHolomorphicPolynomial_alternating n hn p)
  refine ⟨Q, hQ, fun z => ?_⟩
  rw [← eval_slaterHolomorphicPolynomial hn, hfac, map_mul, eval_polynomialVandermonde]

/-- A repeated orbital label also vanishes as a concrete Gaussian L² vector. -/
theorem slaterL2_eq_zero_of_repeated {n : ℕ} (hn : 0 < n)
    (pq : HermiteMultiIndex n) {i j : Fin n} (hij : i ≠ j)
    (hp : pq.1 i = pq.1 j) (hq : pq.2 i = pq.2 j) : slaterL2 hn pq = 0 := by
  apply Lp.ext
  filter_upwards [slaterL2_ae hn pq, Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)] with z hs hz
  rw [hs, hz, slaterDeterminant_eq_zero_of_repeated hn pq hij hp hq z]
  rfl

end
end GinibrePoincare

