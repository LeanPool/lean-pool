/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralSubstitutionFinite.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralLimitTransfer

/-!
# Ginibre Brownian integral substitution finite

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `actualMeanSquareLimit_finite_bounded_weights`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Multiplication by an actual bounded measurable random variable preserves
 mean-square convergence; no independence is required. -/
theorem actualMeanSquareLimit_bounded_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : ℕ → Ω → ℝ) (I A : Ω → ℝ)
    (hS : ∀ n, MemLp (S n) 2 P) (hI : MemLp I 2 P)
    (hA : AEStronglyMeasurable A P) (C : ℝ) (_ : 0 ≤ C)
    (hbound : ∀ ω, ‖A ω‖ ≤ C)
    (hlim : Tendsto (fun n => ∫ ω, (S n ω - I ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (A ω*(S n ω-I ω))^2 ∂P) atTop (𝓝 0) := by
  have hprod (n : ℕ) : MemLp (fun ω => A ω*(S n ω-I ω)) 2 P :=
    ((hS n).sub hI).of_le_mul (hA.mul ((hS n).sub hI).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound ω) (norm_nonneg _))
  have hle (n : ℕ) : (∫ ω, (A ω*(S n ω-I ω))^2 ∂P) ≤
      C^2*(∫ ω, (S n ω-I ω)^2 ∂P) := by
    rw [← integral_const_mul]
    apply integral_mono (hprod n).integrable_sq (((hS n).sub hI).integrable_sq.const_mul (C^2))
    intro ω
    have ha : (A ω)^2 ≤ C^2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        pow_le_pow_left₀ (norm_nonneg _) (hbound ω) 2
    simpa only [mul_pow, Pi.sub_apply] using mul_le_mul_of_nonneg_right ha (sq_nonneg (S n ω-I ω))
  apply squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) hle
  simpa using hlim.const_mul (C^2)

/-- Actual finite sums of L² errors that vanish in mean square also vanish. -/
theorem actualMeanSquareZero_finset_sum {Ω κ : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Finset κ) (E : κ → ℕ → Ω → ℝ)
    (hE : ∀ i n, MemLp (E i n) 2 P)
    (hlim : ∀ i, Tendsto (fun n => ∫ ω, (E i n ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (∑ i ∈ s, E i n ω)^2 ∂P) atTop (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hsum (n : ℕ) : MemLp (fun ω => ∑ k ∈ s, E k n ω) 2 P :=
      memLp_finsetSum s (fun k _ => hE k n)
    have hle (n : ℕ) : (∫ ω, (E i n ω+∑ k ∈ s, E k n ω)^2 ∂P) ≤
        2*(∫ ω, (E i n ω)^2 ∂P)+2*(∫ ω, (∑ k ∈ s, E k n ω)^2 ∂P) := by
      rw [← integral_const_mul,← integral_const_mul,← integral_add]
      · apply integral_mono ((hE i n).add (hsum n)).integrable_sq
          (((hE i n).integrable_sq.const_mul 2).add ((hsum n).integrable_sq.const_mul 2))
        intro ω
        dsimp only [Pi.add_apply]
        nlinarith [sq_nonneg (E i n ω-∑ k ∈ s, E k n ω)]
      · exact (hE i n).integrable_sq.const_mul 2
      · exact (hsum n).integrable_sq.const_mul 2
    apply squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) hle
    simpa using ((hlim i).const_mul 2).add (ih.const_mul 2)

theorem actualBoundedMultiplier_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A X : Ω → ℝ) (hA : AEStronglyMeasurable A P)
    (hX : MemLp X 2 P) (C : ℝ) (hbound : ∀ ω, ‖A ω‖ ≤ C) :
    MemLp (fun ω => A ω*X ω) 2 P := by
  exact hX.of_le_mul (hA.mul hX.aestronglyMeasurable)
    (Eventually.of_forall fun ω => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound ω) (norm_nonneg _))

/-- Actual finite sums with bounded random weights preserve the actual L² limit. -/
theorem actualMeanSquareLimit_finite_bounded_weights {Ω κ : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Finset κ) (S : κ → ℕ → Ω → ℝ) (I A : κ → Ω → ℝ)
    (hS : ∀ i n, MemLp (S i n) 2 P) (hI : ∀ i, MemLp (I i) 2 P)
    (hA : ∀ i, AEStronglyMeasurable (A i) P) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i ω, ‖A i ω‖ ≤ C)
    (hlim : ∀ i, Tendsto (fun n => ∫ ω, (S i n ω - I i ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,
      ((∑ i ∈ s, A i ω*S i n ω)-(∑ i ∈ s, A i ω*I i ω))^2 ∂P) atTop (𝓝 0) := by
  have hh := actualMeanSquareZero_finset_sum P s
    (fun i n ω => A i ω*(S i n ω-I i ω))
    (fun i n => actualBoundedMultiplier_memLp_two P (A i) _ (hA i)
      ((hS i n).sub (hI i)) C (hbound i))
    (fun i => actualMeanSquareLimit_bounded_mul P (S i) (I i) (A i)
      (hS i) (hI i) (hA i) C hC (hbound i) (hlim i))
  simpa only [mul_sub, Finset.sum_sub_distrib] using hh

end
end GinibrePoincare
