/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOneParticleRadius.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOneParticleMarkov

/-! # Actual squared-radius laws of the one-particle driven Ginibre solution

These laws are pushforwards of the proved planar Gaussian transition. The
initial planar state is retained explicitly; autonomy as a function of its
radius requires a separate rotation-invariance argument.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The squared radius `|z 0|²` of the unique particle. -/
def ginibreOneParticleRadius (z : Configuration 1) : ℝ := Complex.normSq (z 0)

theorem ginibreOneParticleRadius_continuous : Continuous ginibreOneParticleRadius := by
  unfold ginibreOneParticleRadius
  fun_prop

/-- The law of the squared radius under the one-particle Ornstein–Uhlenbeck transition at time
`t` started at `z`. -/
def ginibreOneParticleRadiusTransition (α t : ℝ≥0) (z : Configuration 1) : Measure ℝ :=
  (ginibreOneParticleOUTransition α t z).map ginibreOneParticleRadius

theorem ginibreOneParticleBrownianPath_radius_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P)
    (α t : ℝ≥0) (z : Configuration 1) :
    HasLaw (fun ω => ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z t ω))
      (ginibreOneParticleRadiusTransition α t z) P := by
  have hr : HasLaw ginibreOneParticleRadius
      ((ginibreOneParticleOUTransition α t z).map ginibreOneParticleRadius)
      (ginibreOneParticleOUTransition α t z) :=
    ⟨ginibreOneParticleRadius_continuous.measurable.aemeasurable, rfl⟩
  exact hr.comp (ginibreOneParticleBrownianPath_hasLaw Br Bi P hBr hBi hind α t z)

theorem ginibreOneParticleBrownianPath_radius_conditional_law {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P)
    (α s t : ℝ≥0) (z : Configuration 1)
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hbound : ∀ y, ‖f y‖ ≤ C) :
    P[(fun ω => f (ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z (s+t) ω))) |
      ginibrePlanarBrownianPastMeasurableSpace Br Bi s] =ᵐ[P]
      (fun ω => ∫ r, f r ∂ginibreOneParticleRadiusTransition α t
        (ginibreOneParticleBrownianPath Br Bi α z s ω)) := by
  have h := ginibreOneParticleBrownianPath_whole_past_markov Br Bi P hBr hBi hind α s t z
    (f ∘ ginibreOneParticleRadius) (hf.comp ginibreOneParticleRadius_continuous.measurable)
    C (fun y => hbound _)
  apply h.trans
  apply Filter.Eventually.of_forall
  intro ω
  dsimp only
  unfold ginibreOneParticleRadiusTransition
  rw [integral_map ginibreOneParticleRadius_continuous.measurable.aemeasurable
    hf.stronglyMeasurable.aestronglyMeasurable]
  rfl

end
end GinibrePoincare
