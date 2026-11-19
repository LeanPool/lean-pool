/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBochnerKodairaInverseRoot.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBochnerKodairaPolynomial
public import LeanPool.GinibrePoincare.Analysis.HermiteSecondDbarWeakClosure

/-!
# Alternative Bochner Kodaira inverse root

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `bkInverseSquareRoot_total_energy`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace GinibrePoincare
noncomputable section
open ComplexHermite

theorem bkFinite_inverse_first_energy (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    (∑ j : Fin n, ‖finiteDbarComponentL2 n hn (finiteHermiteInverseSquareRootCoefficients c) j‖ ^ 2)
        =
      ‖finiteHermiteCombination n hn (positiveAntiCoefficients c)‖ ^ 2 := by
  classical
  simp only [finiteDbarComponentL2]
  rw [sum_norm_sq_lowered_eq_finiteDbarEnergy, norm_sq_finiteHermiteCombination]
  have hs : (finiteHermiteInverseSquareRootCoefficients c).support ⊆ c.support := by
    intro pq hp
    rw [Finsupp.mem_support_iff, finiteHermiteInverseSquareRootCoefficients_apply] at hp
    exact Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hp)
  have hp : (positiveAntiCoefficients c).support ⊆ c.support := by
    intro pq hpq
    rw [Finsupp.mem_support_iff] at hpq ⊢
    contrapose! hpq
    simp only [positiveAntiCoefficients, Finsupp.filter_apply]
    split_ifs <;> first | exact hpq | rfl
  unfold finiteDbarEnergy
  rw [Finsupp.sum_of_support_subset _ hs _ (by simp),
    Finsupp.sum_of_support_subset _ hp _ (by simp)]
  apply Finset.sum_congr rfl
  intro pq hpq
  rw [finiteHermiteInverseSquareRootCoefficients_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (hermiteInverseSquareRootWeight_nonneg n _), mul_pow]
  by_cases hm : totalAntiDegree pq = 0
  · simp [hm, positiveAntiCoefficients]
  · have hpos := Nat.pos_of_ne_zero hm
    rw [hermiteInverseSquareRootWeight_sq hn hpos]
    simp only [positiveAntiCoefficients]
    rw [Finsupp.filter_apply]
    simp only [hpos, ite_true]
    rw [← Complex.sq_norm]
    have hnm : (n * totalAntiDegree pq : ℝ) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast hn.ne') (by exact_mod_cast hm)
    push_cast
    field_simp

theorem bkFinite_inverse_number_norm (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    ‖finiteGaussianNumberL2 n hn (finiteHermiteInverseSquareRootCoefficients c)‖ ^ 2 =
      finiteDbarEnergy c := by
  classical
  rw [finiteGaussianNumberL2_norm_sq]
  have hs : (finiteHermiteInverseSquareRootCoefficients c).support ⊆ c.support := by
    intro pq hp
    rw [Finsupp.mem_support_iff, finiteHermiteInverseSquareRootCoefficients_apply] at hp
    exact Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hp)
  rw [Finsupp.sum_of_support_subset _ hs _ (by simp)]
  unfold finiteDbarEnergy Finsupp.sum
  apply Finset.sum_congr rfl
  intro pq hpq
  rw [finiteHermiteInverseSquareRootCoefficients_apply, Complex.normSq_mul,
    Complex.normSq_ofReal, ← sq]
  by_cases hm : totalAntiDegree pq = 0
  · simp [hm]
  · rw [hermiteInverseSquareRootWeight_sq hn (Nat.pos_of_ne_zero hm), ← Complex.sq_norm]
    have hnm : (n * totalAntiDegree pq : ℝ) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast hn.ne') (by exact_mod_cast hm)
    push_cast
    field_simp

theorem bkFinite_zero_mode (n : ℕ) (hn : 0 < n) (c : HermiteMultiIndex n →₀ ℂ) :
    gaussianHermiteMode hn 0 (finiteHermiteCombination n hn c) =
      finiteHermiteCombination n hn (zeroAntiCoefficients c) := by
  apply gaussianHermiteCoefficient_ext hn
  intro pq
  rw [gaussianHermiteCoefficient_eq_inner, inner_basis_gaussianHermiteMode,
    gaussianHermiteCoefficient_finiteHermiteCombination,
    gaussianHermiteCoefficient_finiteHermiteCombination]
  classical
  by_cases h : totalAntiDegree pq = 0 <;>
    simp [zeroAntiCoefficients, coefficientsAtAntiDegree, h]

/-- Apply the independently proved integrated BK identity to the actual finite
inverse number-square-root polynomial. -/
theorem bkFinite_inverse_second_energy (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    (∑ j : Fin n, ∑ k : Fin n,
      ‖gaussianInverseSquareRootSecondSynthesisCLM hn j k (finiteDbarComponentL2 n hn c j)‖ ^ 2) =
      (n : ℝ) * ((1 / (n : ℝ)) * ∑ j : Fin n, ‖finiteDbarComponentL2 n hn c j‖ ^ 2 -
        (‖finiteHermiteCombination n hn c‖ ^ 2 -
          ‖gaussianHermiteMode hn 0 (finiteHermiteCombination n hn c)‖ ^ 2)) := by
  change (∑ j : Fin n, ∑ k : Fin n,
      ‖gaussianInverseSquareRootSecondSynthesis hn (finiteDbarComponentL2 n hn c j) j k‖ ^ 2) = _
  simp_rw [gaussianInverseSquareRootSecondSynthesis_finite]
  have hBK := bkFinite_integrated_identity n hn (finiteHermiteInverseSquareRootCoefficients c)
  rw [bkFinite_inverse_number_norm, bkFinite_inverse_first_energy] at hBK
  rw [bkFinite_zero_mode]
  have hsplit := norm_sq_zero_add_positive n hn c
  have he := sum_norm_sq_lowered_eq_finiteDbarEnergy n hn c
  simp only [finiteDbarComponentL2] at he ⊢
  rw [he]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  nlinarith

/-- The independent Bochner–Kodaira derivative energy after inverse square
root, on the complete actual first weak-derivative coefficient domain.

The finite identity comes from differential commutators and genuine Gaussian
IBP, then bounded derivative synthesis passes it to the infinite graph.
The Hermite deficit identity of Theorem 1.9 is not used. -/
theorem bkInverseSquareRoot_total_energy {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hcoeff : ∀ j pq, gaussianHermiteCoefficient hn (D j) pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn g (raiseHermiteIndex j pq)) :
    (∑ j : Fin n, ∑ k : Fin n,
      ‖gaussianInverseSquareRootSecondSynthesisCLM hn j k (D j)‖ ^ 2) =
      n * ((1 / (n : ℝ)) * ∑ j : Fin n, ‖D j‖ ^ 2 -
        (‖g‖ ^ 2 - ‖gaussianHermiteMode hn 0 g‖ ^ 2)) := by
  classical
  let c := gaussianHermiteFiniteCoefficients hn g
  obtain ⟨hg, hD⟩ := gaussianHermiteFiniteCoefficients_tendsto hn g D hcoeff
  have hsecond (j k : Fin n) :
      Tendsto (fun s => gaussianInverseSquareRootSecondSynthesisCLM hn j k
        (finiteDbarComponentL2 n hn (c s) j)) atTop
        (𝓝 (gaussianInverseSquareRootSecondSynthesisCLM hn j k (D j))) :=
    ((gaussianInverseSquareRootSecondSynthesisCLM hn j k).continuous.tendsto _).comp (hD j)
  have hleft := tendsto_finsetSum Finset.univ (fun j _ =>
    tendsto_finsetSum Finset.univ (fun k _ => ((hsecond j k).norm).pow 2))
  have hzero : Tendsto (fun s => gaussianHermiteMode hn 0
      (finiteHermiteCombination n hn (c s))) atTop (𝓝 (gaussianHermiteMode hn 0 g)) := by
    simp_rw [gaussianHermiteMode_eq_antiDegreeProjection]
    exact ((hermiteAntiDegreeProjection n hn 0).continuous.tendsto _).comp hg
  have hright := (((tendsto_finsetSum Finset.univ
    (fun j _ => ((hD j).norm).pow 2)).const_mul (1 / (n : ℝ))).sub
      ((hg.norm.pow 2).sub (hzero.norm.pow 2))).const_mul (n : ℝ)
  have heq (s : Finset (HermiteMultiIndex n)) := bkFinite_inverse_second_energy n hn (c s)
  exact tendsto_nhds_unique hleft (hright.congr (fun s => (heq s).symm))

end
end GinibrePoincare

