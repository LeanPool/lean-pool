/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondencePolynomialRealGaussian.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GaussianPolynomialIntegrability
public import Mathlib.Topology.Algebra.MvPolynomial
public import LeanPool.GinibrePoincare.Concrete.MeasureModel
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs
/-!
# Correspondence polynomial real Gaussian

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondencePolynomial_realGaussian_memLp`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal BigOperators
namespace GinibrePoincare
noncomputable section

/-- Arbitrary real multivariate polynomials are square integrable under any
actual Gaussian law on a finite real coordinate space. -/
theorem correspondencePolynomial_realGaussian_memLp {ι : Type*} [Finite ι]
    (μ : Measure (ι → ℝ)) [ProbabilityTheory.IsGaussian μ] (P : MvPolynomial ι ℝ) :
    MemLp (fun x => MvPolynomial.eval x P) 2 μ := by
  classical
  have := Fintype.ofFinite ι
  classical
  have he : (fun x => MvPolynomial.eval x P) =
      fun x => ∑ d ∈ P.support, MvPolynomial.eval x (MvPolynomial.monomial d (P.coeff d)) := by
    funext x
    conv_lhs => rw [P.as_sum]
    simp only [map_sum]
  rw [he]
  apply memLp_finsetSum
  intro d hd
  have hm := (MvPolynomial.continuous_eval (MvPolynomial.monomial d (P.coeff
      d))).aestronglyMeasurable (μ := μ)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi : Integrable (fun x : ι → ℝ => ‖x‖ ^ (2 * ∑ i, d i)) μ :=
    (ProbabilityTheory.IsGaussian.memLp_id μ ((2 * ∑ i, d i : ℕ) : ℝ≥0∞) (by
        finiteness)).integrable_norm_pow'
  apply (hi.const_mul (‖P.coeff d‖ ^ 2)).mono'
  · exact (MvPolynomial.continuous_eval (MvPolynomial.monomial d (P.coeff d))).norm.pow 2
      |>.aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [MvPolynomial.eval_monomial, norm_mul]
    rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
    simp only [norm_prod, norm_pow]
    have hb : (∏ i, ‖x i‖ ^ d i) ≤ ‖x‖ ^ (∑ i, d i) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_le_prod₀
      · intro i hi; positivity
      · intro i hi
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) _
    have hb2 := pow_le_pow_left₀ (by positivity : 0 ≤ ∏ i, ‖x i‖ ^ d i) hb 2
    rw [← pow_mul] at hb2
    rw [mul_pow]
    have he : (∑ i, d i) * 2 = 2 * (∑ i, d i) := Nat.mul_comm _ _
    rw [he] at hb2
    exact mul_le_mul_of_nonneg_left hb2 (sq_nonneg _)

end
end GinibrePoincare
