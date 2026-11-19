/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalContinuousNoise.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalConfigurationProcess
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianCenterFunctional

/-!
# Brownian orthogonal continuous noise

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianFamily_actual_continuous_center_recenter_noise_independent`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Independence can be recovered through actual measurable embeddings. -/
theorem indepFun_of_measurable_embeddings {Ω A B C D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (P : Measure Ω) (X : Ω → A) (Y : Ω → B) (f : A → C) (g : B → D)
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (hi : IndepFun (f ∘ X) (g ∘ Y) P) : IndepFun X Y P := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hi ⊢
  intro S T hS hT
  have hh := hi (f '' S) (g '' T) (hf.measurableSet_image.mpr hS) (hg.measurableSet_image.mpr hT)
  simpa only [Set.preimage_comp, Set.preimage_image_eq _ hf.injective,
    Set.preimage_image_eq _ hg.injective] using hh

/-- Whole-path independence in the evaluation sigma algebra gives independence
of the actual continuous-path random elements with their Borel sigma algebras. -/
theorem indepFun_continuousMap_of_path_independence {Ω E F : Type*}
    [MeasurableSpace Ω] [TopologicalSpace E] [SecondCountableTopology E] [T2Space E]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace F] [SecondCountableTopology F] [T2Space F]
    [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace C(ℝ, E)] [BorelSpace C(ℝ, E)] [PolishSpace C(ℝ, E)]
    [MeasurableSpace C(ℝ, F)] [BorelSpace C(ℝ, F)] [PolishSpace C(ℝ, F)]
    (P : Measure Ω) (X : Ω → C(ℝ, E)) (Y : Ω → C(ℝ, F))
    (hi : IndepFun (fun ω t => X ω t) (fun ω t => Y ω t) P) : IndepFun X Y P := by
  let d := TopologicalSpace.denseSeq ℝ
  let f : C(ℝ, E) → ℕ → E := fun x k => x (d k)
  let g : C(ℝ, F) → ℕ → F := fun y k => y (d k)
  have hf : MeasurableEmbedding f :=
    (continuous_pi (fun k => continuous_eval_const (d k))).measurableEmbedding (by
      intro x y h
      apply DFunLike.coe_injective
      exact (TopologicalSpace.denseRange_denseSeq ℝ).equalizer x.continuous y.continuous h)
  have hg : MeasurableEmbedding g :=
    (continuous_pi (fun k => continuous_eval_const (d k))).measurableEmbedding (by
      intro x y h
      apply DFunLike.coe_injective
      exact (TopologicalSpace.denseRange_denseSeq ℝ).equalizer x.continuous y.continuous h)
  have hE : Measurable (fun x : ℝ → E => fun k : ℕ => x (d k)) := by
    apply Measurable.of_eval
    intro k
    exact measurable_pi_apply (d k)
  have hF : Measurable (fun x : ℝ → F => fun k : ℕ => x (d k)) := by
    apply Measurable.of_eval
    intro k
    exact measurable_pi_apply (d k)
  exact indepFun_of_measurable_embeddings P X Y f g hf hg (hi.comp hE hF)

/-- The actual normalized continuous center and recentered noise random elements
are independent under the original independent coordinate Brownian motions. -/
theorem brownianFamily_actual_continuous_center_recenter_noise_independent {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (α : ℝ) :
    @IndepFun Ω C(ℝ, ℂ) (GinibreContinuousNoise n) _ (borel _) _
      (fun ω => ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω))
      (fun ω => ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α ω)) P :=
          by
  let : MeasurableSpace C(ℝ, ℂ) := borel _
  let : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩
  let : MeasurableSpace C(ℝ, Configuration n) := borel _
  let : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
  let X := fun ω => ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω)
  let Y := fun ω => ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α ω)
  have hsum : Measurable (fun f : ℝ → Configuration n => fun t => coordinateSum (f t)) := by
    apply Measurable.of_eval
    intro t
    simpa only [Function.comp_def, coordinateSumCLM_apply] using
      (coordinateSumCLM n).continuous.measurable.comp (measurable_pi_apply (X := fun _ : ℝ =>
          Configuration n) t)
  have hraw := (brownianFamily_actual_center_recenter_noise_independent n B P hB hind α).comp
    hsum measurable_id
  have hx : (fun ω t => coordinateSum (projectToCenterLine n
      (ginibreConfigurationBrownianNoise n B α ω t))) =ᵐ[P] (fun ω t => X ω t) := by
    filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hω
    funext t
    change coordinateSum (projectToCenterLine n _) = coordinateSumCLM n _
    rw [coordinateSum_projectToCenterLine n hn, coordinateSumCLM_apply, hω t]
  have hy : (fun ω t => recenteredConfiguration n
      (ginibreConfigurationBrownianNoise n B α ω t)) =ᵐ[P] (fun ω t => (Y ω).val t) := by
    filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hω
    funext t
    change recenteredConfiguration n _ = recenteredCLM n _
    rw [recenteredCLM_apply, hω t]
  have hc : IndepFun X (fun ω => (Y ω).val) P :=
    indepFun_continuousMap_of_path_independence P X (fun ω => (Y ω).val) (hraw.congr hx hy)
  have hclosed : IsClosed {N : C(ℝ, Configuration n) | N 0 = 0} :=
    isClosed_eq (continuous_eval_const 0) continuous_const
  have hec : Topology.IsClosedEmbedding (fun N : GinibreContinuousNoise n => N.val) :=
    hclosed.isClosedEmbedding_subtypeVal
  have he : MeasurableEmbedding (fun N : GinibreContinuousNoise n => N.val) :=
      hec.measurableEmbedding
  exact indepFun_of_measurable_embeddings P X Y id (fun N => N.val) .id he hc

end
end GinibrePoincare
