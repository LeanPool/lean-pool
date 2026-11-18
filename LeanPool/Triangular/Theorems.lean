/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import LeanPool.Triangular.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

import LeanPool.Triangular.Auto.Carleson

/-!
# Boundedness of the triangular Hilbert transform and Carleson's theorem
-/

public section

namespace Triangular

open MeasureTheory SchwartzMap Topology Filter Function

/-- The triangular Hilbert transform is bounded on `L³ × L³ × L³`.
*Implementation notes:*
We formulate the bound as an a priori estimate on Schwartz functions as is common practice.
-/
theorem triangular_ht_bound :
    ∃ C : ℝ, ∀ F₀ F₁ F₂ : 𝓢(ℝ × ℝ, ℂ),
      ‖T F₀ F₁ F₂‖ₑ ≤ ENNReal.ofReal C * eLpNorm F₀ 3 * eLpNorm F₁ 3 * eLpNorm F₂ 3 :=
  Auto.triangular_ht_bound

/-- **Carleson's theorem** for continuous functions. The Fourier series of a continuous
1-periodic function converges pointwise almost everywhere. -/
theorem classical_carleson (f : ℝ → ℂ) (hf : Continuous f) (hper : Periodic f 1) :
    ∀ᵐ x, Tendsto (fun N ↦ fourierPartialSum f N x) atTop (𝓝 (f x)) :=
  Auto.classical_carleson f hf hper

end Triangular

end
