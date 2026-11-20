/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsReversalInitialPaths.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalPathFactory
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinCorrectedDriver
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianActualStationaryOUReversal
/-!
# Alternative Bakry Emery Gibbs reversal initial paths

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryGibbsGaussianInitialPath_measurable`,
`bakryEmeryGibbsGaussianInitialOUPath_measurable`, `bakryEmeryGibbsGaussianInitialPath_initial`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(Icc 0 T, Configuration n)`. -/
local instance bakryGibbsInitialPathsPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance bakryGibbsInitialPaths_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- Actual gradient diffusion driven by the original Brownian coordinates,
with its initial state supplied by the concrete Gaussian coordinate assembly. -/
def bakryEmeryGibbsGaussianInitialPath {Ω : Type*} {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (T : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (x : ((Fin n × Fin 2) → ℝ) × Ω) : C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  bakryEmeryGibbsPath W hW κ hκ hc T
    (ginibreHamiltonianOUCoordinateAssembly n x.1, bakryEmeryOriginalCompactDriver n B T x.2)

/-- The Ornstein–Uhlenbeck path on `[0, T]` (with `α = n²`) started from the configuration
assembled from the Gaussian coordinates `x.1` and driven by the Brownian noise of `B` at `x.2`. -/
def bakryEmeryGibbsGaussianInitialOUPath {Ω : Type*} (n : ℕ) (T : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (x : ((Fin n × Fin 2) → ℝ) × Ω) : C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  ginibreHamiltonianOUJointHorizonPath n ((n : ℝ)^2) T
    (ginibreHamiltonianOUCoordinateAssembly n x.1,
      ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) x.2)

theorem bakryEmeryGibbsGaussianInitialPath_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (T : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (bakryEmeryGibbsGaussianInitialPath W hW κ hκ hc T B) :=
  (bakryEmeryGibbsPath_measurable W hW κ hκ hc T).comp
    (((ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable.comp measurable_fst).prodMk
      ((bakryEmeryOriginalCompactDriver_measurable n B P hB T).comp measurable_snd))

theorem bakryEmeryGibbsGaussianInitialOUPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (bakryEmeryGibbsGaussianInitialOUPath n T B) :=
  (ginibreHamiltonianOUJointHorizonPath_measurable n ((n : ℝ)^2) T).comp
    (((ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable.comp measurable_fst).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB ((n : ℝ)^2)).comp measurable_snd))

@[simp] theorem bakryEmeryGibbsGaussianInitialPath_initial {Ω : Type*} {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (T : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (x : ((Fin n × Fin 2) → ℝ) × Ω) :
    bakryEmeryGibbsGaussianInitialPath W hW κ hκ hc T B x ⟨0, le_rfl, T.property⟩ =
      ginibreHamiltonianOUCoordinateAssembly n x.1 := by
  unfold bakryEmeryGibbsGaussianInitialPath
  rw [bakryEmeryGibbsPath_initial]
  have hzero := (ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) x.2).property
  change _ + (configurationEuclideanEquiv n).symm
    ((configurationEuclideanEquiv n) ((ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) x.2).val
        0)) = _
  rw [hzero]
  simp

end
end GinibrePoincare
