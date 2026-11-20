/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticAlternatingPhasePolynomial.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticHomogeneousPolynomial
public import LeanPool.GinibrePoincare.Analysis.GlobalPhaseAction
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-! # Potential-independent bottom alternating phase identification -/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem entire_alternating_phase_polynomial {n d : ℕ}
    (F : Configuration n → ℂ) (hF : Differentiable ℂ F) (hA : AnalyticAt ℂ F 0)
    (hAlt : IsAlternating F)
    (hp : ∀ (u : ℂ) (z : Configuration n), ‖u‖ = 1 → F (u • z) = u ^ d * F z) :
    ∃ P : ConfigurationPolynomial n, P.IsHomogeneous d ∧
      IsAlternatingConfigurationPolynomial P ∧ ∀ z, F z = MvPolynomial.eval z P := by
  obtain ⟨P, hP, he⟩ := entire_phase_has_homogeneous_mvPolynomial F hF hA hp
  refine ⟨P, hP, ?_, he⟩
  intro σ
  apply MvPolynomial.funext
  intro z
  rw [eval_permuteConfigurationPolynomial, ← he, map_mul, MvPolynomial.eval_C, ← he]
  exact hAlt σ z

/-- Every nonzero entire alternating phase eigenfunction has degree at
least the Vandermonde degree, for every potential. -/
theorem entire_alternating_phase_degree_lower_bound {n d : ℕ}
    (F : Configuration n → ℂ) (hF : Differentiable ℂ F) (hA : AnalyticAt ℂ F 0)
    (hAlt : IsAlternating F) (hne : F ≠ 0)
    (hp : ∀ (u : ℂ) (z : Configuration n), ‖u‖ = 1 → F (u • z) = u ^ d * F z) :
    vandermondeDegree n ≤ d := by
  obtain ⟨P, hP, hPA, he⟩ := entire_alternating_phase_polynomial F hF hA hAlt hp
  apply vandermondeDegree_le_of_homogeneous_alternating hP hPA
  intro hz
  apply hne
  funext z
  rw [he, hz, map_zero]
  rfl

/-- The bottom entire alternating phase is exactly the Vandermonde line,
without any Gaussian Hilbert-space restriction. -/
theorem entire_alternating_bottom_phase_is_vandermonde {n : ℕ}
    (F : Configuration n → ℂ) (hF : Differentiable ℂ F) (hA : AnalyticAt ℂ F 0)
    (hAlt : IsAlternating F)
    (hp : ∀ (u : ℂ) (z : Configuration n), ‖u‖ = 1 →
      F (u • z) = u ^ vandermondeDegree n * F z) :
    ∃ c : ℂ, ∀ z, F z = c * vandermonde z := by
  obtain ⟨P, hP, hPA, he⟩ := entire_alternating_phase_polynomial F hF hA hAlt hp
  by_cases hz : P = 0
  · refine ⟨0, fun z => ?_⟩
    rw [he, hz, map_zero, zero_mul]
  · obtain ⟨Q, hQ, hfactor⟩ := alternating_polynomial_vandermonde_division hPA
    have hc := quotient_eq_C_of_bottom_homogeneous_degree hP hz hfactor
    refine ⟨Q.coeff 0, fun z => ?_⟩
    rw [he, hfactor, hc, map_mul, MvPolynomial.eval_C, eval_polynomialVandermonde]
    simpa using mul_comm (vandermonde z) (Q.coeff 0)
end
end GinibrePoincare
