/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondencePolynomialDifferential.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondencePolynomialCoulomb
/-!
# Correspondence polynomial differential

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondencePolynomial_projected_derivative`,
`correspondencePolynomial_projected_memLp`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff
namespace GinibrePoincare
noncomputable section

/-- The real-linear coordinate `z ↦ z k.1` when `k.2 = 0`, and `z ↦ conj (z k.1)` otherwise. -/
def correspondencePolynomialCoordinate {n : ℕ} (k : Fin n × Fin 2) :
    Configuration n →L[ℝ] ℂ :=
  if k.2=0 then ContinuousLinearMap.proj k.1 else
    Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj k.1)

/-- The directional derivative of a mixed polynomial `P` along `v`:
`∑ k, C (correspondencePolynomialCoordinate k v) * pderiv k P`. -/
def correspondencePolynomialDerivative {n : ℕ} (P : GinibreMixedPolynomial n)
    (v : Configuration n) : GinibreMixedPolynomial n :=
  ∑ k : Fin n × Fin 2, MvPolynomial.C (correspondencePolynomialCoordinate k v) * MvPolynomial.pderiv
      k P

/-- Every real-direction derivative of an arbitrary mixed polynomial remains
an explicit mixed polynomial. -/
theorem correspondencePolynomial_derivative_eval {n : ℕ} (P : GinibreMixedPolynomial n)
    (z v : Configuration n) :
    fderiv ℝ (ginibreMixedPolynomialEval P) z v =
      ginibreMixedPolynomialEval (correspondencePolynomialDerivative P v) z := by
  let φ := fun k : Fin n × Fin 2 => (correspondencePolynomialCoordinate k : Configuration n → ℂ)
  have hcoord (k : Fin n × Fin 2) (y : Configuration n) : correspondencePolynomialCoordinate k y =
      if k.2=0 then y k.1 else conj (y k.1) := by
    unfold correspondencePolynomialCoordinate
    split_ifs <;> rfl
  have he : observablePolynomial φ P = ginibreMixedPolynomialEval P := by
    funext y
    simp only [observablePolynomial, ginibreMixedPolynomialEval, φ, hcoord]
  rw [← he, fderiv_observablePolynomial φ (fun k => (correspondencePolynomialCoordinate
      k).differentiable) P z v]
  simp only [φ, ContinuousLinearMap.fderiv]
  unfold ginibreMixedPolynomialEval correspondencePolynomialDerivative
  simp only [map_sum, map_mul, MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm]
  simp only [observablePolynomial, hcoord]

/-- The real projection of a mixed polynomial has polynomial real-direction
first and second derivatives. -/
theorem correspondencePolynomial_projected_derivative {n : ℕ}
    (P : GinibreMixedPolynomial n) (T : ℂ →L[ℝ] ℝ) (z v : Configuration n) :
    fderiv ℝ (fun y => T (ginibreMixedPolynomialEval P y)) z v =
      T (ginibreMixedPolynomialEval (correspondencePolynomialDerivative P v) z) := by
  have h := T.hasFDerivAt.comp z ((correspondencePolynomial_contDiff n P).differentiable (by simp)
      z).hasFDerivAt
  change fderiv ℝ (T ∘ ginibreMixedPolynomialEval P) z v = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [correspondencePolynomial_derivative_eval]

/-- Every projected polynomial and every constant-direction derivative are
in the concrete Ginibre L² space, including n=1. -/
theorem correspondencePolynomial_projected_memLp {n : ℕ} (hn : 0 < n)
    (P : GinibreMixedPolynomial n) (T : ℂ →L[ℝ] ℝ) :
    MemLp (fun z => T (ginibreMixedPolynomialEval P z)) 2 (ginibreMeasure n) :=
  T.comp_memLp' (correspondencePolynomial_ginibre_memLp hn P)

end
end GinibrePoincare
