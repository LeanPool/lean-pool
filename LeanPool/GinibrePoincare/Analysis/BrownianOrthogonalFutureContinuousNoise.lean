/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalFutureContinuousNoise.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalFuturePath
public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalContinuousNoise

/-!
# Brownian orthogonal future continuous noise

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianFamily_future_continuous_noise_independent_augmented_variable`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem indepFun_continuousMap_left_of_path_independence {Ω E A : Type*}
    [MeasurableSpace Ω] [TopologicalSpace E] [SecondCountableTopology E] [T2Space E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace A]
    [MeasurableSpace C(ℝ, E)] [BorelSpace C(ℝ, E)] [PolishSpace C(ℝ, E)]
    (P : Measure Ω) (X : Ω → C(ℝ, E)) (Y : Ω → A)
    (hi : IndepFun (fun ω t => X ω t) Y P) : IndepFun X Y P := by
  let d := TopologicalSpace.denseSeq ℝ
  let f : C(ℝ, E) → ℕ → E := fun x k => x (d k)
  have hf : MeasurableEmbedding f :=
    (continuous_pi (fun k => continuous_eval_const (d k))).measurableEmbedding (by
      intro x y h
      apply DFunLike.coe_injective
      exact (TopologicalSpace.denseRange_denseSeq ℝ).equalizer x.continuous y.continuous h)
  have hE : Measurable (fun x : ℝ → E => fun k : ℕ => x (d k)) := by
    apply Measurable.of_eval
    intro k
    exact measurable_pi_apply (d k)
  exact indepFun_of_measurable_embeddings P X Y f id hf .id (hi.comp hE measurable_id)

/-- The actual shifted normalized continuous configuration Brownian noise is
independent of every actual completed-past measurable state. -/
theorem brownianFamily_future_continuous_noise_independent_augmented_variable
    {Ω A : Type*} [mAmbient : MeasurableSpace Ω] [MeasurableSpace A]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (α : ℝ) (s : ℝ≥0) (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal) s) _ Y) :
    IndepFun (ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α) Y P := by
  let : MeasurableSpace C(ℝ, Configuration n) := borel _
  let : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
  let N := ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α
  let H : ((Fin n × Fin 2) → ℝ≥0 → ℝ) → ℝ → Configuration n :=
    fun p t j => Real.sqrt (2*α/(n : ℝ)^2) •
      ((p (j, 0) t.toNNReal : ℂ)+Complex.I*(p (j, 1) t.toNNReal : ℂ))
  have hH : Measurable H := by
    apply Measurable.of_eval
    intro t
    apply Measurable.of_eval
    intro j
    exact ((((measurable_pi_apply t.toNNReal).comp (measurable_pi_apply (j, 0))).complex_ofReal).add
      (measurable_const.mul (((measurable_pi_apply t.toNNReal).comp
        (measurable_pi_apply (j, 1))).complex_ofReal))).const_smul (Real.sqrt (2*α/(n : ℝ)^2))
  have hfresh := brownianFamily_future_independent_augmented_variable B P
    (fun i => (hB i).toIsPreBrownianReal) hind s Y hY
  have hraw := hfresh.comp hH measurable_id
  have hshift := (brownianFamilyShift_isBrownian_independent B P hB hind s).1
  have heq : (fun ω => H (fun i t => brownianFamilyShift B s i t ω)) =ᵐ[P]
      (fun ω t => (N ω).val t) := by
    filter_upwards [ginibreBrownianFullContinuousNoise_ae n (brownianFamilyShift B s) P hshift α]
        with ω hω
    funext t
    exact (hω t).symm
  have hCM : IndepFun (fun ω => (N ω).val) Y P :=
    indepFun_continuousMap_left_of_path_independence P (fun ω => (N ω).val) Y
      (hraw.congr heq Filter.EventuallyEq.rfl)
  have hclosed : IsClosed {f : C(ℝ, Configuration n) | f 0 = 0} :=
    isClosed_eq (continuous_eval_const 0) continuous_const
  have hec : Topology.IsClosedEmbedding (fun f : GinibreContinuousNoise n => f.val) :=
    hclosed.isClosedEmbedding_subtypeVal
  exact indepFun_of_measurable_embeddings P N Y (fun f => f.val) id
    hec.measurableEmbedding .id hCM

end
end GinibrePoincare
