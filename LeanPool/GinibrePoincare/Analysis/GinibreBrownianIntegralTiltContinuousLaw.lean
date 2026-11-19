/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltContinuousLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltCanonicalMap

/-!
# Ginibre Brownian integral tilt continuous law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreFiniteContinuousNoiseNormalize_law`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance normalizedFiniteNoiseMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance normalizedFiniteNoiseBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- Bundles the path `N ω` on `[0, T]` as a continuous map, falling back to the zero path when
`N ω` is not continuous. -/
def ginibreFiniteContinuousNoiseNormalize {Ω : Type*} (n : ℕ) (T : ℝ≥0)
    (N : Ω → Icc (0 : ℝ) (T : ℝ) → Configuration n) (ω : Ω) :
    C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ContinuousMap.mkD (N ω) 0

/-- Normalization of actual almost surely continuous finite-noise paths
preserves their law across the original and tilted probability spaces.
This is a reusable measurable-mapping lemma. -/
theorem ginibreFiniteContinuousNoiseNormalize_law {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T : ℝ≥0) (P Q : Measure Ω) [P.IsComplete]
    (N M : Ω → Icc (0 : ℝ) (T : ℝ) → Configuration n)
    (hN : Measurable N) (hM : Measurable M)
    (hcN : ∀ᵐ ω ∂P, Continuous (N ω)) (hcM : ∀ᵐ ω ∂P, Continuous (M ω))
    (hQP : Q ≪ P) (hLaw : Q.map N = P.map M) :
    Measurable (ginibreFiniteContinuousNoiseNormalize n T N) ∧
      Measurable (ginibreFiniteContinuousNoiseNormalize n T M) ∧
      Q.map (ginibreFiniteContinuousNoiseNormalize n T N)=
        P.map (ginibreFiniteContinuousNoiseNormalize n T M) := by
  let : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩
  let X := ginibreFiniteContinuousNoiseNormalize n T N
  let Y := ginibreFiniteContinuousNoiseNormalize n T M
  have hXN : ∀ᵐ ω ∂P, ∀ t, X ω t=N ω t := by
    filter_upwards [hcN] with ω hω
    intro t
    simp [X, ginibreFiniteContinuousNoiseNormalize, ContinuousMap.mkD, hω]
  have hYM : ∀ᵐ ω ∂P, ∀ t, Y ω t=M ω t := by
    filter_upwards [hcM] with ω hω
    intro t
    simp [Y, ginibreFiniteContinuousNoiseNormalize, ContinuousMap.mkD, hω]
  have hXm : Measurable X := by
    apply ginibre_measurable_continuousMap_of_evaluations
    intro t
    apply (aemeasurable_iff_measurable (μ := P)).mp
    exact ((measurable_pi_apply t).comp hN).aemeasurable.congr
      (hXN.mono (fun ω hω => (hω t).symm))
  have hYm : Measurable Y := by
    apply ginibre_measurable_continuousMap_of_evaluations
    intro t
    apply (aemeasurable_iff_measurable (μ := P)).mp
    exact ((measurable_pi_apply t).comp hM).aemeasurable.congr
      (hYM.mono (fun ω hω => (hω t).symm))
  refine ⟨hXm, hYm,?_⟩
  apply actualContinuousMap_law_eq_of_raw_path_law Q P X Y hXm hYm
  have hXNQ : ∀ᵐ ω ∂Q, ∀ t, X ω t=N ω t := hQP.ae_le hXN
  have hXQ : (fun ω t => X ω t)=ᵐ[Q] N :=
    hXNQ.mono (fun ω hω => funext hω)
  have hYP : (fun ω t => Y ω t)=ᵐ[P] M := hYM.mono (fun ω hω => funext hω)
  exact (Measure.map_congr hXQ).trans (hLaw.trans (Measure.map_congr hYP).symm)

end
end GinibrePoincare
