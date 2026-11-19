/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeSlaterExpansion.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorHermiteLowering
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreCompatibility
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorSpectrum
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConstants
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-! # Hermite–Slater determinants and their ordered Parseval expansion

The paper indexes Slater vectors by unordered sets of distinct one-particle
indices. Here the determinant is also defined for every ordered tuple. Repeated
rows vanish, and each distinct unordered set occurs `n!` times, with signs.
Consequently all ordered coefficients are divided by `n!` in Parseval. This
avoids an arbitrary ordering choice and gives exactly the same polynomial proof.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory ComplexHermite
open scoped BigOperators

/-- Number of orderings of `n` distinct orbitals. -/
def slaterMultiplicity (n : ℕ) : ℝ := Fintype.card (ParticlePermutation n)

theorem slaterMultiplicity_pos (n : ℕ) : 0 < slaterMultiplicity n := by
  unfold slaterMultiplicity
  exact_mod_cast Fintype.card_pos

theorem slaterMultiplicity_eq_factorial (n : ℕ) : slaterMultiplicity n = n.factorial := by
  simp [slaterMultiplicity, ParticlePermutation, Fintype.card_perm]

/-- The actual determinant polynomial (4.1), with normalization `1/sqrt(n!)`. -/
def slaterDeterminant {n : ℕ} (hn : 0 < n) (pq : HermiteMultiIndex n)
    (z : Configuration n) : ℂ :=
  (Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ *
    Matrix.det (fun i j : Fin n => normalizedEval n hn (pq.1 i) (pq.2 i) (z j))

/-- The normalized Slater vector in the concrete Gaussian Hilbert space. -/
def slaterL2 {n : ℕ} (hn : 0 < n) (pq : HermiteMultiIndex n) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  (Real.sqrt (slaterMultiplicity n) : ℂ) •
    gaussianAlternationOperator n (hermiteL2Family n hn pq)

theorem slaterL2_mem_alternating {n : ℕ} (hn : 0 < n) (pq : HermiteMultiIndex n) :
    slaterL2 hn pq ∈ gaussianAlternatingL2 n :=
  (gaussianAlternatingL2 n).smul_mem _ (gaussianAlternationOperator_mem n _)

private theorem sign_star {n : ℕ} (σ : ParticlePermutation n) :
    star (permutationSign σ) = permutationSign σ := by
  unfold permutationSign
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- An alternating input pairs with the signed average exactly as with its
original tensor. This proves the coefficient relation used below. -/
theorem inner_gaussianAlternation_of_alternating {n : ℕ}
    (e w : Lp ℂ 2 (complexGaussianMeasure n))
    (hw : w ∈ gaussianAlternatingL2 n) :
    inner ℂ (gaussianAlternationOperator n e) w = inner ℂ e w := by
  have hterm (σ : ParticlePermutation n) :
      inner ℂ (permutationSign σ • gaussianPermutationL2 σ e) w = inner ℂ e w := by
    have h := (gaussianPermutationL2 σ).inner_map_map e w
    rw [hw σ, inner_smul_right] at h
    rw [inner_smul_left]
    change star (permutationSign σ) * _ = _
    rw [sign_star]
    exact h
  rw [gaussianAlternationOperator_apply, inner_smul_left, sum_inner]
  simp_rw [hterm]
  have hc : (Fintype.card (ParticlePermutation n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [hc]

/-- Slater coefficients are the determinant Hilbert pairings. -/
def slaterCoefficient {n : ℕ} (hn : 0 < n)
    (w : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) : ℂ :=
  inner ℂ (slaterL2 hn pq) w

theorem slaterCoefficient_eq_hermite {n : ℕ} (hn : 0 < n)
    (w : Lp ℂ 2 (complexGaussianMeasure n)) (hw : w ∈ gaussianAlternatingL2 n)
    (pq : HermiteMultiIndex n) :
    slaterCoefficient hn w pq =
      (Real.sqrt (slaterMultiplicity n) : ℂ) * gaussianHermiteCoefficient hn w pq := by
  rw [slaterCoefficient, slaterL2, inner_smul_left,
    inner_gaussianAlternation_of_alternating _ _ hw, gaussianHermiteCoefficient_eq_inner]
  rw [Complex.conj_ofReal]
  congr 1

/-- The determinant vectors give a complete convergent expansion of every
alternating Gaussian L² input, without polynomial regularity assumptions. -/
theorem hasSum_slater_expansion {n : ℕ} (hn : 0 < n)
    (w : Lp ℂ 2 (complexGaussianMeasure n)) (hw : w ∈ gaussianAlternatingL2 n) :
    HasSum (fun pq => (slaterMultiplicity n : ℂ)⁻¹ •
      (slaterCoefficient hn w pq • slaterL2 hn pq)) w := by
  have h := (gaussianHermiteHilbertBasis n hn).hasSum_repr w
  have hA := (gaussianAlternationOperator n).hasSum h
  rw [gaussianAlternationOperator_eq_self_of_mem hw] at hA
  apply hA.congr_fun
  intro pq
  rw [map_smul, gaussianHermiteHilbertBasis_apply]
  rw [slaterCoefficient_eq_hermite hn w hw, slaterL2]
  have hr : (Real.sqrt (slaterMultiplicity n) : ℂ) ^ 2 = (slaterMultiplicity n : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (le_of_lt (slaterMultiplicity_pos n))
  have hc : (slaterMultiplicity n : ℂ) ≠ 0 := by
    exact_mod_cast (slaterMultiplicity_pos n).ne'
  simp only [smul_smul]
  congr 1
  change (slaterMultiplicity n : ℂ)⁻¹ *
      ((Real.sqrt (slaterMultiplicity n) : ℂ) * gaussianHermiteCoefficient hn w pq *
        (Real.sqrt (slaterMultiplicity n) : ℂ)) = gaussianHermiteCoefficient hn w pq
  rw [show (slaterMultiplicity n : ℂ)⁻¹ *
      ((Real.sqrt (slaterMultiplicity n) : ℂ) * gaussianHermiteCoefficient hn w pq *
        (Real.sqrt (slaterMultiplicity n) : ℂ)) =
      (slaterMultiplicity n : ℂ)⁻¹ * (Real.sqrt (slaterMultiplicity n) : ℂ)^2 *
        gaussianHermiteCoefficient hn w pq by ring, hr, inv_mul_cancel₀ hc, one_mul]

theorem slaterCoefficient_norm_sq {n : ℕ} (hn : 0 < n)
    (w : Lp ℂ 2 (complexGaussianMeasure n)) (hw : w ∈ gaussianAlternatingL2 n)
    (pq : HermiteMultiIndex n) :
    ‖slaterCoefficient hn w pq‖ ^ 2 =
      slaterMultiplicity n * ‖gaussianHermiteCoefficient hn w pq‖ ^ 2 := by
  rw [slaterCoefficient_eq_hermite hn w hw, norm_mul, mul_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt (slaterMultiplicity_pos n))]

/-- Parseval (4.3), with the `n!` redundancy of ordered orbital labels explicit. -/
theorem hasSum_slater_parseval {n : ℕ} (hn : 0 < n)
    (w : Lp ℂ 2 (complexGaussianMeasure n)) (hw : w ∈ gaussianAlternatingL2 n) :
    HasSum (fun pq => ‖slaterCoefficient hn w pq‖ ^ 2 / slaterMultiplicity n) (‖w‖ ^ 2) := by
  convert hasSum_norm_sq_gaussianHermiteCoefficient hn w using 1
  funext pq
  rw [slaterCoefficient_norm_sq hn w hw]
  field_simp [(slaterMultiplicity_pos n).ne']

/-- The antiholomorphic-degree `d` coefficient mass of the determinant expansion. -/
def slaterDegreeMass {n : ℕ} (hn : 0 < n)
    (w : Lp ℂ 2 (complexGaussianMeasure n)) (d : ℕ) : ℝ :=
  ∑' pq : {pq : HermiteMultiIndex n // totalAntiDegree pq = d},
    ‖slaterCoefficient hn w pq.1‖ ^ 2 / slaterMultiplicity n

theorem slaterDegreeMass_eq_mode_norm {n : ℕ} (hn : 0 < n)
    (w : Lp ℂ 2 (complexGaussianMeasure n)) (hw : w ∈ gaussianAlternatingL2 n)
    (d : ℕ) :
    slaterDegreeMass hn w d = ‖gaussianHermiteMode hn d w‖ ^ 2 := by
  unfold slaterDegreeMass
  have he (pq : HermiteMultiIndex n) :
      ‖slaterCoefficient hn w pq‖ ^ 2 / slaterMultiplicity n =
        ‖gaussianHermiteCoefficient hn w pq‖ ^ 2 := by
    rw [slaterCoefficient_norm_sq hn w hw]
    field_simp [(slaterMultiplicity_pos n).ne']
  simp_rw [he]
  exact (hasSum_coefficient_norm_sq_of_totalAntiDegree hn w d).tsum_eq

/-- The packaged vectors are literally the normalized determinant polynomials. -/
theorem slaterL2_ae {n : ℕ} (hn : 0 < n) (pq : HermiteMultiIndex n) :
    (slaterL2 hn pq : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      slaterDeterminant hn pq := by
  let t : ParticlePermutation n → Lp ℂ 2 (complexGaussianMeasure n) := fun σ =>
    permutationSign σ • hermiteL2Family n hn (pq.1 ∘ σ.symm, pq.2 ∘ σ.symm)
  have ht : ∀ᵐ z ∂complexGaussianMeasure n, ∀ σ,
      t σ z = permutationSign σ *
        multivariateNormalized n hn (pq.1 ∘ σ.symm) (pq.2 ∘ σ.symm) z := by
    apply ae_all_iff.mpr
    intro σ
    filter_upwards [Lp.coeFn_smul (permutationSign σ)
        (hermiteL2Family n hn (pq.1 ∘ σ.symm, pq.2 ∘ σ.symm)),
      hermiteL2Family_coeFn n hn (pq.1 ∘ σ.symm, pq.2 ∘ σ.symm)] with z hs he
    change (permutationSign σ • hermiteL2Family n hn _) z = _
    rw [hs]
    change permutationSign σ * (hermiteL2Family n hn _) z = _
    rw [he]
  have hv : slaterL2 hn pq =
      ((Real.sqrt (slaterMultiplicity n) : ℂ) * (slaterMultiplicity n : ℂ)⁻¹) •
        ∑ σ, t σ := by
    unfold slaterL2
    rw [gaussianAlternationOperator_apply]
    simp_rw [gaussianPermutationL2_hermiteL2Family n hn _ pq.1 pq.2]
    rw [smul_smul]
    rfl
  have hdet (z : Configuration n) :
      (∑ σ : ParticlePermutation n, permutationSign σ *
        multivariateNormalized n hn (pq.1 ∘ σ.symm) (pq.2 ∘ σ.symm) z) =
      Matrix.det (fun i j : Fin n => normalizedEval n hn (pq.1 i) (pq.2 i) (z j)) := by
    rw [Matrix.det_apply' (M := fun i j : Fin n => normalizedEval n hn (pq.1 i) (pq.2 i) (z j))]
    let f : ParticlePermutation n → ℂ := fun σ => permutationSign σ *
      ∏ j, normalizedEval n hn (pq.1 (σ j)) (pq.2 (σ j)) (z j)
    change (∑ σ, permutationSign σ *
      ∏ j, normalizedEval n hn ((pq.1 ∘ σ.symm) j) ((pq.2 ∘ σ.symm) j) (z j)) = _
    calc
      _ = ∑ σ, f ((Equiv.inv (ParticlePermutation n)) σ) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        simp [f, permutationSign, Equiv.Perm.sign_inv]
      _ = ∑ σ, f σ := Equiv.sum_comp (Equiv.inv (ParticlePermutation n)) f
      _ = _ := by simp [f, permutationSign]
  rw [hv]
  filter_upwards [Lp.coeFn_smul
      ((Real.sqrt (slaterMultiplicity n) : ℂ) * (slaterMultiplicity n : ℂ)⁻¹)
      (∑ σ, t σ), Lp.coeFn_finsetSum Finset.univ t, ht] with z hs hsum ht
  rw [hs]
  change ((Real.sqrt (slaterMultiplicity n) : ℂ) * (slaterMultiplicity n : ℂ)⁻¹) *
      (∑ σ, t σ) z = _
  rw [hsum]
  simp only [Finset.sum_apply]
  simp_rw [ht]
  rw [hdet]
  unfold slaterDeterminant
  congr 1
  have hr : (Real.sqrt (slaterMultiplicity n) : ℂ)^2 = (slaterMultiplicity n : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (le_of_lt (slaterMultiplicity_pos n))
  have hc : (slaterMultiplicity n : ℂ) ≠ 0 := by exact_mod_cast (slaterMultiplicity_pos n).ne'
  have hs : (Real.sqrt (slaterMultiplicity n) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (slaterMultiplicity_pos n)).ne'
  field_simp
  exact hr

end
end GinibrePoincare

