/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEDensityConvergence.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEDoubledLSI
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUERegularizedLimit
/-!
# Correspondence GUE density convergence

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueDoubledOrderedDensity_integrable`.
-/

@[expose] public section
open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal BigOperators
namespace GinibrePoincare
noncomputable section

/-- The doubled ordered density on `EuclideanSpace ℝ (Fin n × Fin 2)`: the Gaussian factor
`exp (-(n / 2) * ‖x‖ ^ 2)` times `∏_{i < j} gueOrderedPairWeight (x (j, 0) - x (i, 0))`. -/
def gueDoubledOrderedDensity (n : ℕ) (x : EuclideanSpace ℝ (Fin n × Fin 2)) : ℝ :=
  Real.exp (-(n : ℝ)/2*‖x‖^2)*∏ p ∈ guePairs n, gueOrderedPairWeight (x (p.2, 0)-x (p.1, 0))

/-- The polynomial `∏_{i < j} 2 * (1 + (X (j, 0) - X (i, 0)) ^ 2)`, used to dominate the pair
weights. -/
def gueDominationPolynomial (n : ℕ) : MvPolynomial (Fin n×Fin 2) ℝ :=
  ∏ p ∈ guePairs n, 2*(1+(MvPolynomial.X (p.2, 0)-MvPolynomial.X (p.1, 0))^2)

/-- The dominating function: `exp (-(n / 2) * ‖x‖ ^ 2)` times the value of
`gueDominationPolynomial n` at `x`. -/
def gueDoubledDomination (n : ℕ) (x : EuclideanSpace ℝ (Fin n × Fin 2)) : ℝ :=
  Real.exp (-(n : ℝ)/2*‖x‖^2)*MvPolynomial.eval (WithLp.ofLp x) (gueDominationPolynomial n)

theorem gueDominationPolynomial_eval (n : ℕ) (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    MvPolynomial.eval (WithLp.ofLp x) (gueDominationPolynomial n) =
      ∏ p ∈ guePairs n, 2*(1+(x (p.2, 0)-x (p.1, 0))^2) := by
  unfold gueDominationPolynomial
  simp only [map_prod, map_mul, map_ofNat, map_add, map_one, map_pow, map_sub, MvPolynomial.eval_X]

theorem gueDoubledRegularized_density_product (n : ℕ) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    Real.exp (-gueDoubledRegularizedPotential n ε x) =
      Real.exp (-(n : ℝ)/2*‖x‖^2)*∏ p ∈ guePairs n, Real.exp (-2*gueLogBarrier ε (x (p.2, 0)-x (p.1,
          0))) := by
  unfold gueDoubledRegularizedPotential
  rw [neg_add, Real.exp_add,← Finset.sum_neg_distrib, Real.exp_sum]
  congr 1
  · congr 1; ring
  · apply Finset.prod_congr rfl
    intro p hp
    congr 1
    ring

theorem gueDoubledRegularized_density_tendsto (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    Tendsto (fun k => Real.exp (-gueDoubledRegularizedPotential n (gueRegularizationScale k) x))
        atTop
      (nhds (gueDoubledOrderedDensity n x)) := by
  simp only [gueDoubledRegularized_density_product, gueDoubledOrderedDensity]
  exact tendsto_const_nhds.mul (tendsto_finsetProd _ fun p hp => gueRegularizedPairWeight_tendsto _)

theorem gueDoubledRegularized_density_bound (n k : ℕ)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    Real.exp (-gueDoubledRegularizedPotential n (gueRegularizationScale k) x) ≤ gueDoubledDomination
        n x := by
  rw [gueDoubledRegularized_density_product]
  unfold gueDoubledDomination
  rw [gueDominationPolynomial_eval]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Finset.prod_le_prod₀
  · intro p hp; exact (Real.exp_pos _).le
  · intro p hp; exact gueRegularizedPairWeight_bound k _

theorem gueDoubledDomination_integrable {n : ℕ} (hn : 0 < n) :
    Integrable (gueDoubledDomination n) volume := by
  convert gueGaussianPolynomial_integrable (by positivity : (0 : ℝ)<(n : ℝ)/2)
      (gueDominationPolynomial n) using 1
  funext x
  unfold gueDoubledDomination
  congr 2
  ring

theorem gueOrderedPairWeight_continuous : Continuous gueOrderedPairWeight := by
  have he : gueOrderedPairWeight = fun u : ℝ => (max u 0)^2 := by
    funext u
    by_cases hu : 0<u
    · simp only [gueOrderedPairWeight, ite_eq_left hu, max_eq_left hu.le]
    · simp only [gueOrderedPairWeight, ite_eq_right hu, max_eq_right (le_of_not_gt hu), zero_pow (by
        decide : 2≠0)]
  rw [he]
  exact (continuous_id.max continuous_const).pow 2

theorem gueDoubledOrderedDensity_continuous (n : ℕ) : Continuous (gueDoubledOrderedDensity n) := by
  unfold gueDoubledOrderedDensity
  apply Continuous.mul
  · fun_prop
  · apply continuous_finsetProd
    intro p hp
    have hd : Continuous (fun x : EuclideanSpace ℝ (Fin n×Fin 2) => x (p.2, 0)-x (p.1, 0)) := by
      convert ((PiLp.proj 2 (fun _ : Fin n×Fin 2 => ℝ) (p.2, 0) : EuclideanSpace ℝ (Fin n×Fin 2)
          →L[ℝ] ℝ).continuous).sub
        ((PiLp.proj 2 (fun _ : Fin n×Fin 2 => ℝ) (p.1, 0) : EuclideanSpace ℝ (Fin n×Fin 2) →L[ℝ]
            ℝ).continuous) using 1
      funext x
      rfl
    exact gueOrderedPairWeight_continuous.comp hd

theorem gueDoubledOrderedDensity_nonneg (n : ℕ) (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    0≤gueDoubledOrderedDensity n x := by
  unfold gueDoubledOrderedDensity gueOrderedPairWeight
  positivity

theorem gueDoubledOrderedDensity_integrable {n : ℕ} (hn : 0 < n) :
    Integrable (gueDoubledOrderedDensity n) volume := by
  apply (gueDoubledDomination_integrable hn).mono' (gueDoubledOrderedDensity_continuous
      n).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (gueDoubledOrderedDensity_nonneg n x)]
  exact le_of_tendsto (gueDoubledRegularized_density_tendsto n x)
    (Eventually.of_forall fun k => gueDoubledRegularized_density_bound n k x)

end
end GinibrePoincare
