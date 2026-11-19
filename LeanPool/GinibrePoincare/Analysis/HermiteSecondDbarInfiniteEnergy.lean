/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteSecondDbarInfiniteEnergy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteSecondDbarWeakClosure
public import LeanPool.GinibrePoincare.Endgame.SeriesDeficit

/-! # Exact infinite second-antiholomorphic energy

Strong finite Hermite graph approximation passes the finite second-derivative
energy formula to the genuine synthesized weak derivatives.
-/

@[expose] public section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace GinibrePoincare
noncomputable section
open ComplexHermite

theorem gaussianHermiteMode_zero_finite (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
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

/-- A norm-continuous expression for the finite deficit. -/
theorem finiteHermiteDeficit_graph_norm_formula (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    finiteHermiteDeficit hn c =
      (1 / (n : ℝ)) * ∑ j : Fin n, ‖finiteDbarComponentL2 n hn c j‖ ^ 2 -
      (‖finiteHermiteCombination n hn c‖ ^ 2 -
        ‖gaussianHermiteMode hn 0 (finiteHermiteCombination n hn c)‖ ^ 2) := by
  rw [gaussianHermiteMode_zero_finite]
  have hp := norm_sq_zero_add_positive n hn c
  have he := sum_norm_sq_lowered_eq_finiteDbarEnergy n hn c
  simp only [finiteDbarComponentL2] at he ⊢
  rw [he]
  unfold finiteHermiteDeficit
  rw [one_div]
  linarith

/-- The genuine infinite second-antiholomorphic energy is exactly `n`
times the first Gaussian deficit, on the complete first weak derivative domain. -/
theorem gaussianInverseSquareRootSecondSynthesis_total_energy {n : ℕ} (hn : 0 < n)
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
  have heq (s : Finset (HermiteMultiIndex n)) :
      (∑ j : Fin n, ∑ k : Fin n,
        ‖gaussianInverseSquareRootSecondSynthesisCLM hn j k
          (finiteDbarComponentL2 n hn (c s) j)‖ ^ 2) =
        n * ((1 / (n : ℝ)) * ∑ j : Fin n, ‖finiteDbarComponentL2 n hn (c s) j‖ ^ 2 -
          (‖finiteHermiteCombination n hn (c s)‖ ^ 2 -
            ‖gaussianHermiteMode hn 0 (finiteHermiteCombination n hn (c s))‖ ^ 2)) := by
    change (∑ j : Fin n, ∑ k : Fin n,
      ‖gaussianInverseSquareRootSecondSynthesis hn
        (finiteDbarComponentL2 n hn (c s) j) j k‖ ^ 2) = _
    simp_rw [gaussianInverseSquareRootSecondSynthesis_finite]
    rw [finiteInverseSquareRoot_secondDbar_energy, finiteHermiteDeficit_graph_norm_formula]
  exact tendsto_nhds_unique hleft (hright.congr (fun s => (heq s).symm))

/-- The norm-continuous energy is exactly the convergent Hermite deficit tail. -/
theorem gaussianInverseSquareRootSecondSynthesis_total_energy_modeTail {n : ℕ}
    (hn : 0 < n) (g : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hcoeff : ∀ j pq, gaussianHermiteCoefficient hn (D j) pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn g (raiseHermiteIndex j pq)) :
    Summable (fun k : ℕ => (k : ℝ) * positiveHermiteModeMass hn g k) ∧
    (∑ j : Fin n, ∑ k : Fin n,
      ‖gaussianInverseSquareRootSecondSynthesisCLM hn j k (D j)‖ ^ 2) =
      n * modeTail (positiveHermiteModeMass hn g) := by
  have he := hasSum_weighted_positiveHermiteModeMass_of_coefficient_raise hn g D hcoeff
  have hm := summable_positiveHermiteModeMass hn g
  have ht : Summable (fun k : ℕ => (k : ℝ) * positiveHermiteModeMass hn g k) := by
    exact (he.summable.sub hm).congr fun k => by ring
  refine ⟨ht, ?_⟩
  rw [gaussianInverseSquareRootSecondSynthesis_total_energy hn g D hcoeff]
  have hmass := norm_sq_eq_zeroMode_add_positiveModeMass hn g
  have htail := modeEnergy_eq_modeMass_add_modeTail (positiveHermiteModeMass hn g) hm ht
  unfold modeEnergy modeMass at htail
  simp only [Nat.cast_add, Nat.cast_one] at htail
  rw [he.tsum_eq] at htail
  congr 1
  linarith

end
end GinibrePoincare
