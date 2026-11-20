/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsLSIDriverIdentification.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsStationaryLaw
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsLSICoupling
/-!
# Alternative Bakry Emery Gibbs LSI driver identification

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryGibbsActualEndpoint_eq_BrownianEndpoint`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

theorem bakryEmeryOriginalCompactDriver_eq_BrownianNoisePath
    (n : ℕ) (hn : 0 < n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0) :
    bakryEmeryOriginalCompactDriver n B T =ᵐ[P]
      (fun ω => Real.sqrt 2 • bakryEmeryBrownianNoisePath (T : ℝ) B ω) := by
  have hn0 : (n : ℝ)^2 ≠ 0 := by positivity
  have hscale : 2*(n : ℝ)^2/(n : ℝ)^2 = 2 := by field_simp
  filter_upwards [bakryEmeryOriginalCompactDriver_ae_eq n B P hB T,
    bakryEmeryBrownianNoisePath_actual (T : ℝ) B P hB] with ω hω hpath
  apply ContinuousMap.ext
  intro t
  rw [hω t]
  change configurationEuclideanEquiv n (ginibreConfigurationBrownianNoise n B ((n : ℝ)^2) ω t) =
    Real.sqrt 2 • bakryEmeryBrownianNoisePath (T : ℝ) B ω t
  rw [hpath t]
  apply PiLp.ext
  intro i
  rcases i with ⟨j, k⟩
  fin_cases k <;>
    simp [ginibreConfigurationBrownianNoise, bakryEmeryBrownianNoiseReal,
      configurationEuclideanEquiv_apply_zero, configurationEuclideanEquiv_apply_one, hscale]

theorem bakryEmeryGibbsActualEndpoint_eq_BrownianEndpoint
    (n : ℕ) (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n×Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (B : (Fin n×Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ z : Configuration n,
      configurationEuclideanEquiv n (bakryEmeryGibbsActualEndpoint W hW κ hκ hc T B (z, ω)) =
        bakryEmeryBrownianEndpoint (W ∘ (configurationEuclideanEquiv n).symm) κ hκ
          (hW.comp (configurationEuclideanEquiv n).symm.contDiff) hc
          (configurationEuclideanEquiv n z) T T.coe_nonneg B ω := by
  filter_upwards [bakryEmeryOriginalCompactDriver_eq_BrownianNoisePath n hn B P hB T] with ω hω
  intro z
  simp only [bakryEmeryGibbsActualEndpoint, bakryEmeryGibbsPath, ContinuousMap.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply, bakryEmeryBrownianEndpoint,
    bakryEmeryLangevinPath, bakryEmeryLangevinEndpoint, hω]

end
end GinibrePoincare
