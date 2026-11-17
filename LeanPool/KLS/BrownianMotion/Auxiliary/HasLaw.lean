/-
Copyright (c) 2026 BrownianMotion contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BrownianMotion contributors
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: removed `hasLaw_map`, now provided by
-- Mathlib v4.35.0 (Probability/HasLaw.lean) with the same statement; see vendor/port.patch.
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Gaussian laws under measurable maps -/


@[expose] public section

open MeasureTheory ENNReal WithLp

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section HasLaw

variable {𝓧} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧} {μ : Measure 𝓧} {P : Measure Ω}

section dirac

-- don't upstream this: it's too specific. Delete it here eventually.
lemma HasLaw.ae_eq_const_of_gaussianReal {X : Ω → ℝ} {μ : ℝ} (hX : HasLaw X (gaussianReal μ 0) P) :
    ∀ᵐ ω ∂P, X ω = μ := by
  rw [gaussianReal_zero_var] at hX
  exact hX.ae_eq_of_dirac

end dirac

end HasLaw

end ProbabilityTheory
