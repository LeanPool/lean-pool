/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!

# Definitions of the triangular Hilbert form and Fourier partial sums

-/

@[expose] public noncomputable section

namespace Triangular

open Topology Filter MeasureTheory

/-- The three cyclic factors divided by their signed linear denominator. -/
def cyclicIntegrand (F₀ F₁ F₂ : ℝ × ℝ → ℂ) (q : (ℝ × ℝ) × ℝ) : ℂ :=
  F₀ q.1 * F₁ (q.1.2, q.2) * F₂ (q.2, q.1.1) / ((q.1.1 + q.1.2 + q.2 : ℝ) : ℂ)

/-- The region outside the symmetric cutoff around the singular plane. -/
def cutoffSet (ε : ℝ) : Set ((ℝ × ℝ) × ℝ) := {q | ε < |q.1.1 + q.1.2 + q.2|}

/-- The cyclic integrand extended by zero on the excluded region. -/
def truncatedIntegrand (F₀ F₁ F₂ : ℝ × ℝ → ℂ) (ε : ℝ) : (ℝ × ℝ) × ℝ → ℂ :=
  (cutoffSet ε).indicator (cyclicIntegrand F₀ F₁ F₂)

lemma truncatedIntegrand_apply (F₀ F₁ F₂ : ℝ × ℝ → ℂ) (ε : ℝ) (q : (ℝ × ℝ) × ℝ) :
    truncatedIntegrand F₀ F₁ F₂ ε q =
      if ε < |q.1.1 + q.1.2 + q.2| then cyclicIntegrand F₀ F₁ F₂ q else 0 := by
  simp only [truncatedIntegrand, Set.indicator_apply, cutoffSet, Set.mem_ofPred_eq]

/-- The triangular Hilbert trilinear form with a symmetric lower cutoff. -/
def truncatedForm (F₀ F₁ F₂ : ℝ × ℝ → ℂ) (ε : ℝ) : ℂ :=
  ∫ q in cutoffSet ε, cyclicIntegrand F₀ F₁ F₂ q

lemma truncatedForm_eq_integral (F₀ F₁ F₂ : ℝ × ℝ → ℂ) (ε : ℝ) :
    truncatedForm F₀ F₁ F₂ ε = ∫ q, truncatedIntegrand F₀ F₁ F₂ ε q := by
  have measurable : MeasurableSet (cutoffSet ε) := measurableSet_lt measurable_const (by fun_prop)
  rw [truncatedForm, truncatedIntegrand, integral_indicator measurable]

/-- The triangular Hilbert trilinear form, the principal value of `truncatedForm`.

**Note:** That the principal value limit exists for Schwartz functions is
the content of `Auto.tendsto_truncatedForm`. -/
def T (F₀ F₁ F₂ : ℝ × ℝ → ℂ) : ℂ := limUnder (𝓝[>] 0) (truncatedForm F₀ F₁ F₂)

/-- The partial sums of the Fourier series of a 1-periodic function. -/
def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, fourierCoeffOn zero_lt_one f n * fourier n (x : UnitAddCircle)

end Triangular

end
