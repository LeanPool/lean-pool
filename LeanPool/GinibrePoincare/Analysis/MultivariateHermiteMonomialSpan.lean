/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MultivariateHermiteMonomialSpan.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteMonomialSpan
public import Mathlib.Algebra.Algebra.Operations

/-! # Pointwise multivariate triangular inversion

This file tensors the one-variable rectangular span equality over the finitely
many coordinates.  Everything here concerns actual functions; no `L²`
quotient or integrability assertion is involved.
-/


@[expose] public section


open scoped BigOperators ComplexConjugate Pointwise

namespace GinibrePoincare
namespace ComplexHermite

noncomputable section

/-- Coordinatewise pullback of a one-variable function. -/
def coordinatePullback {n : ℕ} (i : Fin n) :
    (ℂ → ℂ) →ₗ[ℂ] ((Fin n → ℂ) → ℂ) where
  toFun f z := f (z i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinatePullback_apply {n : ℕ} (i : Fin n)
    (f : ℂ → ℂ) (z : Fin n → ℂ) :
    coordinatePullback i f z = f (z i) := rfl

/-- The finite rectangular span of multivariate normalized Hermite
functions. -/
def multivariateNormalizedRectangleSpan (n : ℕ) (hn : 0 < n)
    (P Q : Fin n → ℕ) : Submodule ℂ ((Fin n → ℂ) → ℂ) :=
  Submodule.span ℂ {f | ∃ p q : Fin n → ℕ,
    (∀ i, p i ≤ P i) ∧ (∀ i, q i ≤ Q i) ∧
      f = multivariateNormalized n hn p q}

/-- The finite rectangular span of coordinate/conjugate-coordinate
monomials. -/
def multivariateMixedMonomialRectangleSpan (n : ℕ)
    (P Q : Fin n → ℕ) : Submodule ℂ ((Fin n → ℂ) → ℂ) :=
  Submodule.span ℂ {f | ∃ p q : Fin n → ℕ,
    (∀ i, p i ≤ P i) ∧ (∀ i, q i ≤ Q i) ∧
      f = fun z ↦ ∏ i, z i ^ p i * (conj (z i)) ^ q i}

private def coordinateHermiteSet (n : ℕ) (hn : 0 < n)
    (P Q : Fin n → ℕ) (i : Fin n) : Set ((Fin n → ℂ) → ℂ) :=
  {f | ∃ a ≤ P i, ∃ b ≤ Q i,
    f = coordinatePullback i (normalizedEval n hn a b)}

private def coordinateMonomialSet (P Q : Fin n → ℕ) (i : Fin n) :
    Set ((Fin n → ℂ) → ℂ) :=
  {f | ∃ a ≤ P i, ∃ b ≤ Q i,
    f = coordinatePullback i (fun z : ℂ ↦ z ^ a * (conj z) ^ b)}

private theorem coordinateHermite_span_eq_coordinateMonomial_span
    (n : ℕ) (hn : 0 < n) (P Q : Fin n → ℕ) (i : Fin n) :
    Submodule.span ℂ (coordinateHermiteSet n hn P Q i) =
      Submodule.span ℂ (coordinateMonomialSet P Q i) := by
  rw [show coordinateHermiteSet n hn P Q i =
      coordinatePullback i ''
        {f | ∃ a ≤ P i, ∃ b ≤ Q i, f = normalizedEval n hn a b} by
    ext f
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨normalizedEval n hn a b, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩]
  rw [show coordinateMonomialSet P Q i =
      coordinatePullback i ''
        {f | ∃ a ≤ P i, ∃ b ≤ Q i,
          f = fun z : ℂ ↦ z ^ a * (conj z) ^ b} by
    ext f
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩]
  rw [← Submodule.map_span, ← Submodule.map_span]
  change (normalizedEvalRectangleSpan n hn (P i) (Q i)).map
      (coordinatePullback i) =
    (mixedMonomialRectangleSpan (P i) (Q i)).map (coordinatePullback i)
  rw [normalizedEvalRectangleSpan_eq_mixedMonomialRectangleSpan n hn]

private theorem hermite_generator_set_eq_prod (n : ℕ) (hn : 0 < n)
    (P Q : Fin n → ℕ) :
    {f | ∃ p q : Fin n → ℕ,
      (∀ i, p i ≤ P i) ∧ (∀ i, q i ≤ Q i) ∧
        f = multivariateNormalized n hn p q} =
      ∏ i, coordinateHermiteSet n hn P Q i := by
  ext f
  rw [Set.mem_fintype_prod]
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    refine ⟨fun i ↦ coordinatePullback i (normalizedEval n hn (p i) (q i)), ?_, ?_⟩
    · intro i
      exact ⟨p i, hp i, q i, hq i, rfl⟩
    · funext z
      simp [multivariateNormalized]
  · rintro ⟨g, hg, rfl⟩
    choose p hp q hq heq using hg
    refine ⟨p, q, hp, hq, ?_⟩
    funext z
    simp only [multivariateNormalized]
    simp only [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro i hi
    rw [heq i]
    rfl

private theorem monomial_generator_set_eq_prod (n : ℕ)
    (P Q : Fin n → ℕ) :
    {f | ∃ p q : Fin n → ℕ,
      (∀ i, p i ≤ P i) ∧ (∀ i, q i ≤ Q i) ∧
        f = fun z ↦ ∏ i, z i ^ p i * (conj (z i)) ^ q i} =
      ∏ i, coordinateMonomialSet P Q i := by
  ext f
  rw [Set.mem_fintype_prod]
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    refine ⟨fun i ↦ coordinatePullback i
      (fun z : ℂ ↦ z ^ p i * (conj z) ^ q i), ?_, ?_⟩
    · intro i
      exact ⟨p i, hp i, q i, hq i, rfl⟩
    · funext z
      simp only [Finset.prod_apply, coordinatePullback_apply]
  · rintro ⟨g, hg, rfl⟩
    choose p hp q hq heq using hg
    refine ⟨p, q, hp, hq, ?_⟩
    funext z
    simp only [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro i hi
    rw [heq i]
    rfl

/-- Pointwise multivariate triangular inversion: on every finite index
rectangle, normalized tensor Hermites and coordinate/conjugate-coordinate
monomials have exactly the same complex linear span. -/
theorem multivariateNormalizedRectangleSpan_eq_mixedMonomialRectangleSpan
    (n : ℕ) (hn : 0 < n) (P Q : Fin n → ℕ) :
    multivariateNormalizedRectangleSpan n hn P Q =
      multivariateMixedMonomialRectangleSpan n P Q := by
  rw [multivariateNormalizedRectangleSpan,
    multivariateMixedMonomialRectangleSpan,
    hermite_generator_set_eq_prod n hn P Q,
    monomial_generator_set_eq_prod n P Q]
  rw [← Submodule.prod_span, ← Submodule.prod_span]
  apply Finset.prod_congr rfl
  intro i hi
  exact coordinateHermite_span_eq_coordinateMonomial_span n hn P Q i

end
end ComplexHermite
end GinibrePoincare
