/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionCompactResolvent.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionCoreResolvent

/-!
# Ginibre stochastic transition compact resolvent

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreOriginalStochasticL2Resolvent_compact_adjoint_integral`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreCompactTestValue_pairing {n : ℕ} (hn : 0 < n)
    (f : Lp ℝ 2 (ginibreMeasure n)) (φ : Configuration n → ℝ)
    (hφ : IsGinibreCollisionFreeCompactTest φ) :
    inner ℝ f (ginibreCompactTestValue hn φ hφ)=∫ z, f z*φ z ∂ginibreMeasure n := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ginibreCompactTestValue_ae hn φ hφ] with z hz
  simp [hz, mul_comm]

theorem ginibreCompactTestPregenerator_pairing {n : ℕ} (hn : 0 < n)
    (f : Lp ℝ 2 (ginibreMeasure n)) (φ : Configuration n → ℝ)
    (hφ : IsGinibreCollisionFreeCompactTest φ) :
    inner ℝ f (ginibreCompactTestPregenerator hn φ hφ)=
      ∫ z, f z*ginibrePregenerator n φ z ∂ginibreMeasure n := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ginibreCompactTestPregenerator_ae hn φ hφ] with z hz
  simp [hz, mul_comm]

theorem ginibreOriginalStochasticL2Resolvent_compact_adjoint_integral {Ω : Type*} [MeasurableSpace
    Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 0 < (α : ℝ)) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (f : Lp ℝ 2 (ginibreMeasure n))
    (φ : Configuration n → ℝ) (hφ : IsGinibreCollisionFreeCompactTest φ) :
    let u := ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) f
    (∫ z, u z*φ z ∂ginibreMeasure n)-(∫ z, u z*ginibrePregenerator n φ z ∂ginibreMeasure n)=
      ∫ z, f z*φ z ∂ginibreMeasure n := by
  have h := ginibreOriginalStochasticL2Resolvent_compact_adjoint_equation hn α hα P B hB hiB f φ hφ
  simpa only [ginibreCompactTestValue_pairing, ginibreCompactTestPregenerator_pairing] using h

end
end GinibrePoincare
