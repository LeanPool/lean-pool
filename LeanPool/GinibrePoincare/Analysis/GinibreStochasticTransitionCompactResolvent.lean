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
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactTestLaplace

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

/-- A smooth compactly supported collision-free test function, as an element of
`Lp ℝ 2 (ginibreMeasure n)`. -/
def ginibreCompactTestValue {n : ℕ} (hn : 0 < n) (φ : Configuration n → ℝ)
    (hφ : IsGinibreCollisionFreeCompactTest φ) : Lp ℝ 2 (ginibreMeasure n) := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  exact (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).toLp φ

/-- The Ginibre pregenerator applied to a compact collision-free test function, as an element
of `Lp ℝ 2 (ginibreMeasure n)`. -/
def ginibreCompactTestPregenerator {n : ℕ} (hn : 0 < n) (φ : Configuration n → ℝ)
    (hφ : IsGinibreCollisionFreeCompactTest φ) : Lp ℝ 2 (ginibreMeasure n) := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  exact ((continuous_ginibrePregenerator_of_compact_test hφ).memLp_of_hasCompactSupport
    (hasCompactSupport_ginibrePregenerator hφ.2.1)).toLp (ginibrePregenerator n φ)

theorem ginibreCompactTestValue_ae {n : ℕ} (hn : 0 < n) (φ : Configuration n → ℝ)
    (hφ : IsGinibreCollisionFreeCompactTest φ) :
    (ginibreCompactTestValue hn φ hφ : Configuration n → ℝ)=ᵐ[ginibreMeasure n] φ := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).coeFn_toLp

theorem ginibreCompactTestPregenerator_ae {n : ℕ} (hn : 0 < n) (φ : Configuration n → ℝ)
    (hφ : IsGinibreCollisionFreeCompactTest φ) :
    (ginibreCompactTestPregenerator hn φ hφ : Configuration n → ℝ)=ᵐ[ginibreMeasure n]
        ginibrePregenerator n φ := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact ((continuous_ginibrePregenerator_of_compact_test hφ).memLp_of_hasCompactSupport
    (hasCompactSupport_ginibrePregenerator hφ.2.1)).coeFn_toLp

/-- Genuine unit resolvent identity on the concrete smooth collision-free core,
derived from the actual stochastic Dynkin formula. -/
theorem ginibreOriginalStochasticL2Resolvent_compact_test {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 0 < (α : ℝ)) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P)
    (φ : Configuration n → ℝ) (hφ : IsGinibreCollisionFreeCompactTest φ) :
    ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ))
      (ginibreCompactTestValue hn φ hφ-ginibreCompactTestPregenerator hn φ hφ)=
        ginibreCompactTestValue hn φ hφ := by
  let c : ℝ := (α : ℝ)/(n : ℝ)
  have hc : 0<c := div_pos hα (by exact_mod_cast hn)
  have hpc := continuous_ginibrePregenerator_of_compact_test hφ
  obtain ⟨C, hC⟩ := hφ.2.1.exists_bound_of_continuous hφ.1.continuous
  obtain ⟨D, hD⟩ := (hasCompactSupport_ginibrePregenerator hφ.2.1).exists_bound_of_continuous hpc
  refine ginibreOriginalStochasticL2Resolvent_of_bounded_point_identity hn α P B hB hiB hc
    _ _ (fun z => φ z-ginibrePregenerator n φ z) ?_ ?_ (C+D) ?_ ?_
  · filter_upwards [Lp.coeFn_sub (ginibreCompactTestValue hn φ hφ) (ginibreCompactTestPregenerator
      hn φ hφ),
      ginibreCompactTestValue_ae hn φ hφ, ginibreCompactTestPregenerator_ae hn φ hφ] with z hsub hv
          hp
    rw [hsub]
    change (ginibreCompactTestValue hn φ hφ) z-(ginibreCompactTestPregenerator hn φ hφ) z=_
    rw [hv, hp]
  · exact (hφ.1.continuous.sub hpc).measurable
  · intro z
    exact (norm_sub_le _ _).trans (add_le_add (hC z) (hD z))
  · filter_upwards [ginibre_ae_collisionFree n hn,
      ginibreCompactTestValue_ae hn φ hφ,
      ginibreStationaryContinuousTransitionMean_eq_original_ae hn α P B hB hiB φ,
      ginibreStationaryContinuousTransitionMean_eq_original_ae hn α P B hB hiB (ginibrePregenerator
          n φ)]
        with z hz hv ha hb
    rw [hv]
    have he := ginibreBrownian_compact_test_transition_weighted_laplace_identity hn α c hc z hz B P
        hB hiB φ hφ
    refine Eq.trans ?_ he
    apply integral_congr_ae
    exact ae_of_all _ fun t => by
      dsimp only
      rw [ginibreStationaryContinuousTransitionMean_sub hn α P B hB φ (ginibrePregenerator n φ)
        hφ.1.continuous.measurable hpc.measurable C D hC hD t z, ha t, hb t]
      simp only [ginibreRealPaperSpeedGenerator]
      rw [integral_const_mul]
      dsimp [c]
      ring

theorem ginibreOriginalStochasticL2Resolvent_compact_adjoint_equation {Ω : Type*} [MeasurableSpace
    Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 0 < (α : ℝ)) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (f : Lp ℝ 2 (ginibreMeasure n))
    (φ : Configuration n → ℝ) (hφ : IsGinibreCollisionFreeCompactTest φ) :
    let u := ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) f
    inner ℝ u (ginibreCompactTestValue hn φ hφ)-inner ℝ u (ginibreCompactTestPregenerator hn φ hφ)=
      inner ℝ f (ginibreCompactTestValue hn φ hφ) := by
  have hc : 0<(α : ℝ)/(n : ℝ) := div_pos hα (by exact_mod_cast hn)
  have he := ginibreOriginalStochasticL2Resolvent_symmetric hn α P B hB hiB hc
    (ginibreCompactTestValue hn φ hφ-ginibreCompactTestPregenerator hn φ hφ) f
  rw [ginibreOriginalStochasticL2Resolvent_compact_test hn α hα P B hB hiB φ hφ] at he
  simpa only [inner_sub_left, real_inner_comm] using he

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
