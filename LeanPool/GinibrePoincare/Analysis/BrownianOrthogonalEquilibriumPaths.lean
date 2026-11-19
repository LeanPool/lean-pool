/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalEquilibriumPaths.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalGlobalPathFactorization
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Brownian orthogonal equilibrium paths

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreEquilibriumPath_measurable`, `ginibreRelativeEquilibriumPath_measurable`,
`ginibre_equilibrium_OU_relative_functionals_independent`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance (n : ℕ) : MeasurableSpace C(ℝ, Configuration n) := borel _
local instance (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
/-- The Borel σ-algebra on continuous complex paths `C(ℝ, ℂ)`. -/
local instance instBorelBrownianOrthogonalEquilibriumPaths59 : MeasurableSpace C(ℝ, ℂ) := borel _
local instance : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩

/-- The actual canonical path initialized from a configuration sampled at equilibrium. -/
def ginibreEquilibriumPath {Ω : Type*} {n : ℕ} (α : ℝ)
    (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (p : Configuration n × Ω) : C(ℝ, Configuration n) :=
  ginibreDrivenGlobalPathElement α (ginibreFreeInitialVersion z₀ hz₀ p.1,
    ginibreBrownianFullContinuousNoise n B α p.2)

theorem ginibreEquilibriumPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) : Measurable (ginibreEquilibriumPath α z₀ hz₀ B) :=
  (ginibreDrivenGlobalPathElement_measurable hn α).comp
    (((ginibreFreeInitialVersion_measurable z₀ hz₀).comp measurable_fst).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd))

/-- The true relative canonical path uses only the relative initial value and noise. -/
def ginibreRelativeEquilibriumPath {Ω : Type*} {n : ℕ} (α : ℝ)
    (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (p : Configuration n × Ω) : C(ℝ, Configuration n) :=
  ginibreDrivenGlobalPathElement α
    (ginibreFreeInitialVersion (recenteredConfiguration n z₀) (collisionFree_recentered hz₀)
      (recenteredConfiguration n p.1),
      ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α p.2))

theorem ginibreRelativeEquilibriumPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) : Measurable (ginibreRelativeEquilibriumPath α z₀ hz₀ B) :=
        by
  have hW : Measurable (recenteredConfiguration n) := by
    convert (recenteredCLM n).continuous.measurable using 1
    funext z
    exact (recenteredCLM_apply n z).symm
  exact (ginibreDrivenGlobalPathElement_measurable hn α).comp
    ((((ginibreFreeInitialVersion_measurable _ _).comp hW).comp measurable_fst).prodMk
      (((ginibreContinuousNoiseRecenter_continuous n).measurable.comp
        (ginibreBrownianFullContinuousNoise_measurable n B P hB α)).comp measurable_snd))

/-- The equilibrium-initialized center and relative canonical functionals are independent. -/
theorem ginibre_equilibrium_OU_relative_functionals_independent {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IndepFun (fun p : Configuration n × Ω => ginibreOUPathElement n α
      (coordinateSum p.1, ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α
          p.2)))
      (ginibreRelativeEquilibriumPath α z₀ hz₀ B) ((ginibreMeasure n).prod P) := by
  have hrel : Measurable (fun p : Configuration n × GinibreContinuousNoise n =>
      ginibreDrivenGlobalPathElement α
        (ginibreFreeInitialVersion (recenteredConfiguration n z₀) (collisionFree_recentered hz₀)
            p.1, p.2)) :=
    (ginibreDrivenGlobalPathElement_measurable hn α).comp
      (((ginibreFreeInitialVersion_measurable _ _).comp measurable_fst).prodMk measurable_snd)
  exact (ginibre_equilibrium_center_relative_inputs_independent hn B P hB hind α).comp
    (ginibreOUPathElement_measurable n α) hrel

end
end GinibrePoincare
