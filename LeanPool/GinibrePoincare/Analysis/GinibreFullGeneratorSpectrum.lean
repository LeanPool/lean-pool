/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-poincare.

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

public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! # The spectrum of a positive Hilbert-space contraction -/

@[expose] public section

namespace GinibrePoincare
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive Hilbert-space contraction has real spectrum in the unit interval. -/
theorem ginibreFull_positive_contraction_spectrum (R : H →L[ℂ] H)
    (hp : R.IsPositive) (hnorm : ‖R‖ ≤ 1) : spectrum ℝ R ⊆ Set.Icc 0 1 := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  let := hH
  intro r hr
  have hpos : 0 ≤ R := ContinuousLinearMap.nonneg_iff_isPositive.mpr hp
  exact ⟨spectrum_nonneg_of_nonneg hpos hr,
    (Real.le_norm_self r).trans ((spectrum.norm_le_norm_of_mem hr).trans hnorm)⟩

end
end GinibrePoincare
