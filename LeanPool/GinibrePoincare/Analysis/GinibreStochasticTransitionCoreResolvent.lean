/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionCoreResolvent.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionL2Resolvent
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionContinuousMean
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionLaplaceFubini
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreCompatibility
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactTestLaplace
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorSpectrum
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Ginibre stochastic transition core resolvent

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreOriginalStochasticL2Resolvent_core_adjoint_equation`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Generic integration reduction, with its pointwise Laplace premise explicit.
The operator and Bochner resolvent are the actual constructed stochastic ones. -/
theorem ginibreOriginalStochasticL2Resolvent_of_bounded_point_identity {Ω : Type*} [MeasurableSpace
    Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) {c : ℝ} (hc : 0 < c)
    (g w : Lp ℝ 2 (ginibreMeasure n)) (v : Configuration n → ℝ)
    (hg : (g : Configuration n → ℝ) =ᵐ[ginibreMeasure n] v)
    (hv : Measurable v) (C : ℝ) (hC : ∀ z, ‖v z‖ ≤ C)
    (hp : ∀ᵐ z ∂ginibreMeasure n,
      (∫ t in Ioi (0 : ℝ), c * Real.exp (-c * t) * ginibreStationaryContinuousTransitionMean α B P v
          t
          z) = w z) :
    ginibreOriginalStochasticL2Resolvent hn α P B hB hiB c g=w := by
  let := ginibreMeasure_isProbabilityMeasure hn
  apply ext_inner_left ℝ
  intro f
  rw [ginibreOriginalStochasticL2Resolvent_pairing hn α P B hB hiB hc]
  let m := fun p : ℝ × Configuration n => ginibreStationaryContinuousTransitionMean α B P v p.1 p.2
  have hm : Measurable m := ginibreStationaryContinuousTransitionMean_joint_measurable hn α P B hB v
      hv
  have hfi : Integrable (f : Configuration n → ℝ) (ginibreMeasure n) := (Lp.memLp f).integrable (by
      norm_num)
  have hs := boundedTransitionMean_laplace_fubini (ginibreMeasure n) (fun z => c*f z)
    (hfi.const_mul c) m hm C (fun p => ginibreStationaryContinuousTransitionMean_bound α P B v C hC
        p.1 p.2) hc
  have he : (∫ t in Ioi (0 : ℝ), c*Real.exp (-c*t)*
      inner ℝ f (ginibreOriginalStochasticL2Operator hn α P B hB hiB t.toNNReal g))=
      ∫ t in Ioi (0 : ℝ), ∫ z, (c*f z)*(Real.exp (-c*t)*m (t, z)) ∂ginibreMeasure n := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [ginibreOriginalStochasticL2Operator_measurable_mean_pairing hn α P B hB hiB t.toNNReal f g v
        hg hv C hC,
      Real.coe_toNNReal t ht.le,← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by dsimp [m]; ring
  rw [he, hs]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hp] with z hz
  have hz' : c*(∫ t in Ioi (0 : ℝ), Real.exp (-c*t)*m (t, z))=w z := by
    rw [← integral_const_mul]
    simpa only [m, mul_assoc] using hz
  change c*f z*(∫ t in Ioi (0 : ℝ), Real.exp (-c*t)*m (t, z))=w z*f z
  rw [mul_comm c (f z), mul_assoc, hz', mul_comm]

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

private theorem coreCompactRepresentatives_eq {n : ℕ} (hn : 0 < n)
    (φ : Configuration n → ℝ) (hφ : IsTheoremOneNineCore φ)
    (htest : IsGinibreCollisionFreeCompactTest φ) :
    ginibreFullCoreValue hn φ hφ = ginibreCompactTestValue hn φ htest ∧
      ginibreFullCorePregenerator hn φ hφ = ginibreCompactTestPregenerator hn φ htest := by
  exact ⟨Lp.ext ((ginibreFullCoreValue_ae hn φ hφ).trans
    (ginibreCompactTestValue_ae hn φ htest).symm),
    Lp.ext ((ginibreFullCorePregenerator_ae hn φ hφ).trans
      (ginibreCompactTestPregenerator_ae hn φ htest).symm)⟩

/-- Genuine unit resolvent identity on the concrete smooth collision-free core,
derived from the actual stochastic Dynkin formula. -/
theorem ginibreOriginalStochasticL2Resolvent_core {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 0 < (α : ℝ)) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P)
    (φ : Configuration n → ℝ) (hφ : IsTheoremOneNineCore φ) :
    ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ))
      (ginibreFullCoreValue hn φ hφ-ginibreFullCorePregenerator hn φ hφ)=
        ginibreFullCoreValue hn φ hφ := by
  have htest : IsGinibreCollisionFreeCompactTest φ := hφ.isCollisionFreeCompactTest
  obtain ⟨hvalue, hpregenerator⟩ := coreCompactRepresentatives_eq hn φ hφ htest
  simpa only [hvalue, hpregenerator] using
    ginibreOriginalStochasticL2Resolvent_compact_test hn α hα P B hB hiB φ htest

theorem ginibreOriginalStochasticL2Resolvent_core_adjoint_equation {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 0 < (α : ℝ)) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (f : Lp ℝ 2 (ginibreMeasure n))
    (φ : Configuration n → ℝ) (hφ : IsTheoremOneNineCore φ) :
    let u := ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) f
    inner ℝ u (ginibreFullCoreValue hn φ hφ)-inner ℝ u (ginibreFullCorePregenerator hn φ hφ)=
      inner ℝ f (ginibreFullCoreValue hn φ hφ) := by
  have htest : IsGinibreCollisionFreeCompactTest φ := hφ.isCollisionFreeCompactTest
  obtain ⟨hvalue, hpregenerator⟩ := coreCompactRepresentatives_eq hn φ hφ htest
  simpa only [hvalue, hpregenerator] using
    ginibreOriginalStochasticL2Resolvent_compact_adjoint_equation hn α hα P B hB hiB f φ htest

end
end GinibrePoincare
