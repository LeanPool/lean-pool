/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsStationaryLaw.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsInitialLaw
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsEquilibriumReversal
/-!
# Alternative Bakry Emery Gibbs stationary law

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryGibbsActualEndpoint_hilbert_stationary`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(Icc 0 T, Configuration n)`. -/
local instance bakryStationaryLawConfigMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance bakryStationaryLaw_configBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩
/-- The Borel σ-algebra on continuous Euclidean paths
`C(Icc 0 T, EuclideanSpace ℝ (Fin n × Fin 2))`. -/
local instance bakryStationaryLawEuclideanMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), EuclideanSpace ℝ (Fin n × Fin 2)) := borel _
local instance bakryStationaryLaw_euclideanBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), EuclideanSpace ℝ (Fin n × Fin 2)) := ⟨rfl⟩

/-- The time-`T` endpoint of the Gibbs gradient path of `W` started at `p.1` and driven by the
original compact Brownian driver of `B` at `p.2`. -/
def bakryEmeryGibbsActualEndpoint {Ω : Type*} {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (T : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (p : Configuration n × Ω) :
    Configuration n :=
  bakryEmeryGibbsPath W hW κ hκ hc T (p.1, bakryEmeryOriginalCompactDriver n B T p.2)
    ⟨T, T.coe_nonneg, le_rfl⟩

theorem bakryEmeryGibbsActualEndpoint_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (T : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (bakryEmeryGibbsActualEndpoint W hW κ hκ hc T B) := by
  let pth := bakryEmeryGibbsPath W hW κ hκ hc T
  have hm : Measurable pth := bakryEmeryGibbsPath_measurable W hW κ hκ hc T
  have hn := bakryEmeryOriginalCompactDriver_measurable n B P hB T
  have hi : Measurable (fun p : Configuration n × Ω =>
      (p.1, bakryEmeryOriginalCompactDriver n B T p.2)) :=
    measurable_fst.prodMk (hn.comp measurable_snd)
  have he : Measurable (fun q : C(Icc (0 : ℝ) (T : ℝ), Configuration n) =>
      q ⟨(T : ℝ), T.coe_nonneg, le_rfl⟩) := ContinuousMap.measurable_eval _
  change Measurable (fun p : Configuration n × Ω =>
    pth (p.1, bakryEmeryOriginalCompactDriver n B T p.2) ⟨(T : ℝ), T.coe_nonneg, le_rfl⟩)
  exact he.comp (hm.comp hi)

/-- The literal Gibbs law is invariant for the actual unit-diffusion gradient
endpoint, with both the solution factory and Gibbs mass discharged internally. -/
theorem bakryEmeryGibbsActualEndpoint_stationary {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (hT : 0 < T) :
    ((bakryEmeryNormalizedGibbs volume W).prod P).map
      (bakryEmeryGibbsActualEndpoint W hW κ hκ hc T B) = bakryEmeryNormalizedGibbs volume W := by
  let A := ginibreHamiltonianOUCoordinateAssembly n
  let σ := bakryEmeryGibbsCoordinateRawMeasure n W
  let σN := bakryEmeryGibbsCoordinateInitialMeasure n W
  let F := bakryEmeryGibbsGaussianInitialPath W hW κ hκ hc T B
  let E := bakryEmeryGibbsActualEndpoint W hW κ hκ hc T B
  have hA : Measurable A := A.continuous.measurable
  have hF := bakryEmeryGibbsGaussianInitialPath_measurable W hW κ hκ hc T B P hB
  have hE := bakryEmeryGibbsActualEndpoint_measurable W hW κ hκ hc T B P hB
  have hw : Measurable (bakryEmeryGibbsCoordinateWeight n W) := by
    have hS : Continuous (bakryEmeryGibbsRelativePotential W) :=
      hW.continuous.sub (continuous_const.mul contDiff_configurationNormSq.continuous)
    exact (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hS.neg).measurable).comp hA
  have hraw : bakryEmeryGibbsEquilibriumWeightedPathLaw W hW κ hκ hc T P B = (σ.prod P).map F := by
    unfold bakryEmeryGibbsEquilibriumWeightedPathLaw
    change (((Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))).prod P).withDensity
      (fun x => bakryEmeryGibbsCoordinateWeight n W x.1)).map F = _
    rw [← prod_withDensity_left hw]
    rfl
  have hEnd := bakryEmeryGibbsEquilibriumWeightedPathLaw_endpoint hn W hW κ hκ hc P B hB hiB T hT
  rw [hraw, Measure.map_map (ContinuousMap.measurable_eval _) hF,
    Measure.map_map (ContinuousMap.measurable_eval _) hF] at hEnd
  have hinit : (fun x => F x ⟨0, le_rfl, T.coe_nonneg⟩) = A ∘ Prod.fst := by
    funext x
    exact bakryEmeryGibbsGaussianInitialPath_initial W hW κ hκ hc T B x
  have hterm : (fun x => F x ⟨T, T.coe_nonneg, le_rfl⟩) = E ∘ Prod.map A id := by rfl
  change (σ.prod P).map (fun x => F x ⟨T, T.coe_nonneg, le_rfl⟩) =
    (σ.prod P).map (fun x => F x ⟨0, le_rfl, T.coe_nonneg⟩) at hEnd
  rw [hinit,← Measure.map_map hA measurable_fst, Measure.map_fst_prod, measure_univ,
      one_smul] at hEnd
  have hσN : IsProbabilityMeasure σN := bakryEmeryGibbsCoordinateInitialMeasure_probability hn W hW
      κ hκ hc
  let := hσN
  have hassembly : σN.map A = bakryEmeryNormalizedGibbs volume W :=
    bakryEmeryGibbsCoordinateInitialMeasure_assembly hn W hW κ hκ hc
  have hprod : (σN.map A).prod P = (σN.prod P).map (Prod.map A id) := by
    simpa using Measure.map_prod_map σN P hA measurable_id
  rw [← hassembly, hprod, Measure.map_map hE (hA.prodMap measurable_id)]
  change (σN.prod P).map (E ∘ Prod.map A id) = σN.map A
  rw [← hterm]
  unfold σN bakryEmeryGibbsCoordinateInitialMeasure
  have hTerm : Measurable (fun x : ((Fin n × Fin 2) → ℝ) × Ω => F x
      (⟨(T : ℝ), T.coe_nonneg, le_rfl⟩ : Icc (0 : ℝ) (T : ℝ))) :=
    (ContinuousMap.measurable_eval (⟨(T : ℝ), T.coe_nonneg, le_rfl⟩ : Icc (0 : ℝ) (T : ℝ))).comp hF
  rw [Measure.prod_smul_left, Measure.map_smul _ hTerm.aemeasurable,
    Measure.map_smul _ hA.aemeasurable]
  exact congrArg (fun μ => (bakryEmeryGibbsCoordinateRawMeasure n W univ)⁻¹ • μ) hEnd

/-- The same concrete stationary endpoint law in the real Hilbert coordinates
used for the Bakry–Émery contraction and entropy proof. -/
theorem bakryEmeryGibbsActualEndpoint_hilbert_stationary {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (hT : 0 < T) :
    ((bakryEmeryNormalizedGibbs volume W).prod P).map
      (fun p => configurationEuclideanEquiv n (bakryEmeryGibbsActualEndpoint W hW κ hκ hc T B p)) =
      bakryEmeryNormalizedGibbs volume (W ∘ (configurationEuclideanEquiv n).symm) := by
  have hh := congrArg (Measure.map (configurationEuclideanEquiv n))
    (bakryEmeryGibbsActualEndpoint_stationary hn W hW κ hκ hc P B hB hiB T hT)
  rw [Measure.map_map (configurationEuclideanEquiv n).continuous.measurable
    (bakryEmeryGibbsActualEndpoint_measurable W hW κ hκ hc T B P hB),
    bakryEmeryConfiguration_normalizedGibbs_map n W hW.continuous] at hh
  exact hh

end
end GinibrePoincare
