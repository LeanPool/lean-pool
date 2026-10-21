/-
Copyright (c) 2026 PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PrimeNumberTheoremAnd contributors
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
Adapted from PrimeNumberTheoremAnd revision
`127b50e33f6033e2147921167a117af96d9ba4ea`, via Jason Davies's
Iwaniec linear sieve snapshot `c8d01549d2ae640b36ec198c1f0f6495f1b036cf`
(both Apache-2.0). Blueprint-only machinery is omitted.

Supporting lemmas for Iwaniec's sieve and its prime-number-theorem input.
-/

@[expose] public section

namespace IwaniecLinearSievePNT


open scoped Complex ComplexConjugate


/-
Now in Mathlib:
-/
/-
Let $f : \mathbb{C} \to \mathbb{C}$ be a function at $p \in \mathbb{C}$ with derivative $a$.
    Then the derivative of the function $g(z) = \overline{f(\overline{z})}$ at $\overline{p}$ is
    $\overline{a}$.
We proceed by case analysis on whether $f$ is differentiable at $p$. If $f$ is differentiable
    at $p$, then we can apply the previous theorem. If $f$ is not differentiable at $p$, then
    neither is $g$, and both derivatives have the default value of zero.
-/
theorem deriv_conj_conj' (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  trans deriv (conj ∘ f ∘ conj) (conj p)
  · rfl
  simp

/-
Conjugation symmetry of the derivative of the Riemann zeta function. Let $s \in \mathbb{C}$.
    Then $$\zeta'(\overline{s}) = \overline{\zeta'(s)}.$$
We apply the derivative conjugation symmetry to the Riemann zeta function and use the
    conjugation symmetry of the Riemann zeta function itself.
-/
theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  simp [← deriv_conj_conj']

theorem logDerivZeta_conj (s : ℂ) :
    (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  simp [deriv_riemannZeta_conj, riemannZeta_conj]

theorem logDerivZeta_conj' (s : ℂ) :
    (logDeriv riemannZeta) (conj s) = conj (logDeriv riemannZeta s) := logDerivZeta_conj s

/-
% TODO: Submit this to Mathlib.
-/
/-
The conjugation symmetry of the interval integral. Let $f : \mathbb{R} \to \mathbb{C}$ be a
    measurable function, and let $a, b \in \mathbb{R}$. Then
    $$\int_{a}^{b} \overline{f(x)} \, dx = \overline{\int_{a}^{b} f(x) \, dx}.$$
We unfold the interval integral into an integral over a uIoc and use the conjugation property
    of integrals.
-/
theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_conj, ← RCLike.conj_smul,
    ← intervalIntegral.intervalIntegral_eq_integral_uIoc]

end IwaniecLinearSievePNT
