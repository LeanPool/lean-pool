/-
Copyright (c) 2026 Lukas Liehr, Mitchell A. Taylor, Peiyang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
-/
module

public import LeanPool.GrothendieckBessel.AbstractBessel
public import LeanPool.GrothendieckBessel.UnitIntervalRealization

/-!
# Countable Grothendieck--Bessel Gram theorem
Adapted for Lean Pool from the Apache-2.0 upstream formalization, with module-system,
Mathlib API, and compilation changes.
-/

@[expose] public section


noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace GrothendieckBessel

/-- Proof implementation for the single TeX-shaped public theorem. -/
theorem main_proof
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : ℕ → H) (hx : BesselSequenceBoundOne x) :
    ∃ f : ℕ → ℝ → ℂ,
      (∀ j, AEStronglyMeasurable (f j) μ) ∧
      (∀ j t, t ∈ unitInterval → ‖f j t‖ ≤ 1) ∧
      ∀ j k,
        ⟪x k, x j⟫_ℂ =
          ∫ t in unitInterval, f j t * star (f k t) := by
  have hgram : FiniteHermitianPositiveContraction (besselGram x) :=
    besselGram_finite_positive_contraction x hx
  rcases countable_unit_interval_realization (besselGram x) hgram with
    ⟨f, hfMeas, hfBound, hfMoment⟩
  refine ⟨f, hfMeas, hfBound, ?_⟩
  intro j k
  have h := hfMoment j k
  simpa [besselGram, l2InnerOn, μOn] using h.symm

end GrothendieckBessel
