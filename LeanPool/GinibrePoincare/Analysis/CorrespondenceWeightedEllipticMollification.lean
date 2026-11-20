/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticMollification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.LebesgueL2Mollification
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Strong L² convergence of normalized bump averages

The averages are actual Bochner integrals of translated L² functions under
Lebesgue measure. Strong continuity of translation gives convergence as the
mollifier radius tends to zero. Identification with pointwise convolution is
a separate step.

The arguments live in `LeanPool.GinibrePoincare.Analysis.LebesgueL2Mollification`
(`l2Translate`, `l2BumpAverage`); this file specializes them to a finite-dimensional real
inner-product space with its Lebesgue `volume`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Translation of `u` by `y` in Lebesgue `L²`: the domain action of `-y`, giving the class of
`x ↦ u (-y + x)`. -/
def correspondenceWeightedLebesgueL2Translate (y : E)
    (u : Lp V 2 (volume : Measure (E))) : Lp V 2 (volume : Measure (E)) :=
  l2Translate y u

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem correspondenceWeighted_continuous_lebesgueL2Translate (u : Lp V 2 (volume : Measure (E))) :
    Continuous (fun y => correspondenceWeightedLebesgueL2Translate y u) :=
  continuous_l2Translate u

omit [NormedSpace ℝ V] [CompleteSpace V] in
@[simp] theorem correspondenceWeighted_lebesgueL2Translate_zero
    (u : Lp V 2 (volume : Measure (E))) : correspondenceWeightedLebesgueL2Translate 0 u = u :=
  l2Translate_zero u

omit [NormedSpace ℝ V] [CompleteSpace V] in
@[simp] theorem correspondenceWeighted_norm_lebesgueL2Translate (y : E)
    (u : Lp V 2 (volume : Measure (E))) :
    ‖correspondenceWeightedLebesgueL2Translate y u‖ = ‖u‖ :=
  norm_l2Translate y u

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem correspondenceWeighted_lebesgueL2Translate_ae (y : E)
    (u : Lp V 2 (volume : Measure (E))) :
    (correspondenceWeightedLebesgueL2Translate y u : E → V) =ᵐ[volume] fun x => u (x - y) :=
  l2Translate_ae y u

/-- The average `∫ y, φ.normed volume y • correspondenceWeightedLebesgueL2Translate y u` of the
translates of `u` against the normalized bump `φ`. -/
def correspondenceWeightedLebesgueL2BumpAverage (φ : ContDiffBump (0 : E))
    (u : Lp V 2 (volume : Measure (E))) : Lp V 2 (volume : Measure (E)) :=
  l2BumpAverage φ u

omit [CompleteSpace V] in
theorem correspondenceWeighted_integrable_lebesgueL2BumpIntegrand (φ : ContDiffBump (0 : E))
    (u : Lp V 2 (volume : Measure (E))) :
    Integrable (fun y => φ.normed volume y • correspondenceWeightedLebesgueL2Translate y u) :=
  integrable_l2BumpIntegrand φ u

omit [CompleteSpace V] in
/-- A normalized bump average is a contraction on the actual Lebesgue L² space. -/
theorem correspondenceWeighted_norm_lebesgueL2BumpAverage_le (φ : ContDiffBump (0 : E))
    (u : Lp V 2 (volume : Measure (E))) :
    ‖correspondenceWeightedLebesgueL2BumpAverage φ u‖ ≤ ‖u‖ :=
  norm_l2BumpAverage_le φ u

/-- Continuous linear test pairings commute with the actual L² bump average. -/
theorem correspondenceWeighted_lebesgueL2BumpAverage_pairing (φ : ContDiffBump (0 : E))
    (u : Lp V 2 (volume : Measure (E)))
    (L : Lp V 2 (volume : Measure (E)) →L[ℝ] ℝ) :
    L (correspondenceWeightedLebesgueL2BumpAverage φ u) =
      ∫ y, φ.normed volume y * L (correspondenceWeightedLebesgueL2Translate y u) :=
  l2BumpAverage_pairing φ u L

/-- The Bochner L² average has the expected translated representative pairing
against every actual scalar L² test. -/
theorem correspondenceWeighted_lebesgueL2BumpAverage_test_pairing (φ : ContDiffBump (0 : E))
    (u : Lp ℝ 2 (volume : Measure (E)))
    (w : E → ℝ) (hw : MemLp w 2 volume) :
    (∫ x, correspondenceWeightedLebesgueL2BumpAverage φ u x * w x) =
      ∫ y, φ.normed volume y * (∫ x, u (x - y) * w x) :=
  l2BumpAverage_test_pairing φ u w hw

/-- A local translation error bound controls the actual averaged L² error. -/
theorem correspondenceWeighted_lebesgueL2BumpAverage_error_le (φ : ContDiffBump (0 : E))
    (u : Lp V 2 (volume : Measure (E))) (ε : ℝ) (_hε : 0 ≤ ε)
    (he : ∀ y ∈ Function.support (φ.normed volume),
      ‖correspondenceWeightedLebesgueL2Translate y u - u‖ ≤ ε) :
    ‖correspondenceWeightedLebesgueL2BumpAverage φ u - u‖ ≤ ε :=
  l2BumpAverage_error_le φ u ε he

/-- Normalized bump averages converge strongly in actual Lebesgue L². -/
theorem correspondenceWeighted_lebesgueL2BumpAverage_tendsto
    (φ : ℕ → ContDiffBump (0 : E))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (u : Lp V 2 (volume : Measure (E))) :
    Tendsto (fun m => correspondenceWeightedLebesgueL2BumpAverage (φ m) u) atTop (𝓝 u) :=
  l2BumpAverage_tendsto φ hφ u

end
end GinibrePoincare
