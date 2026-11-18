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

open Topology Filter

/-- Truncated triangular Hilbert transform as a trilinear form -/
def truncatedForm (F₀ F₁ F₂ : ℝ × ℝ → ℂ) (ε : ℝ) : ℂ :=
  ∫ p in {((x, y), z) : (ℝ × ℝ) × ℝ | ε < |x + y + z|},
    let ((x, y), z) := p
    F₀ (x, y) * F₁ (y, z) * F₂ (z, x) / (x + y + z : ℝ)

/-- The triangular Hilbert trilinear form, the principal value of `truncatedForm`.

**Note:** That the principal value limit exists for Schwartz functions is
the content of `Auto.tendsto_truncatedForm`. -/
def T (F₀ F₁ F₂ : ℝ × ℝ → ℂ) : ℂ := limUnder (𝓝[>] 0) (truncatedForm F₀ F₁ F₂)

/-- The partial sums of the Fourier series of a 1-periodic function. -/
def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, fourierCoeffOn zero_lt_one f n * fourier n (x : UnitAddCircle)

end Triangular

end
