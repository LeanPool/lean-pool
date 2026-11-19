/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalContinuousPathLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalPathLaw
public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalFutureContinuousNoise

/-!
# Brownian orthogonal continuous path law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianFamily_shift_continuous_noise_law_eq`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem continuousMap_law_eq_of_whole_path_law_eq {Ω E : Type*}
    [MeasurableSpace Ω] [TopologicalSpace E] [SecondCountableTopology E] [T2Space E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace C(ℝ, E)] [BorelSpace C(ℝ, E)] [PolishSpace C(ℝ, E)]
    (P : Measure Ω) (X Y : Ω → C(ℝ, E)) (hX : Measurable X) (hY : Measurable Y)
    (hlaw : P.map (fun ω t => X ω t) = P.map (fun ω t => Y ω t)) :
    P.map X = P.map Y := by
  let d := TopologicalSpace.denseSeq ℝ
  let f : C(ℝ, E) → ℕ → E := fun x k => x (d k)
  have hf : MeasurableEmbedding f :=
    (continuous_pi (fun k => continuous_eval_const (d k))).measurableEmbedding (by
      intro x y h
      apply DFunLike.coe_injective
      exact (TopologicalSpace.denseRange_denseSeq ℝ).equalizer x.continuous y.continuous h)
  have hXm : Measurable (fun ω t => X ω t) := by
    apply Measurable.of_eval
    intro t
    exact (continuous_eval_const t).measurable.comp hX
  have hYm : Measurable (fun ω t => Y ω t) := by
    apply Measurable.of_eval
    intro t
    exact (continuous_eval_const t).measurable.comp hY
  let R : (ℝ → E) → ℕ → E := fun x k => x (d k)
  have hR : Measurable R := by
    apply Measurable.of_eval
    intro k
    exact measurable_pi_apply (d k)
  apply hf.map_injective
  rw [Measure.map_map hf.measurable hX, Measure.map_map hf.measurable hY]
  have hh := congrArg (Measure.map R) hlaw
  rw [Measure.map_map hR hXm, Measure.map_map hR hYm] at hh
  exact hh

/-- Assembles real coordinate paths into the configuration noise path whose coordinate `j` at
time `t` is `√(2α/n²) • (p (j, 0) t + I * p (j, 1) t)`, with `t` read as `t.toNNReal`. -/
def brownianConfigurationNoisePathMap (n : ℕ) (α : ℝ) :
    ((Fin n × Fin 2) → ℝ≥0 → ℝ) → ℝ → Configuration n :=
  fun p t j => Real.sqrt (2*α/(n : ℝ)^2) •
    ((p (j, 0) t.toNNReal : ℂ)+Complex.I*(p (j, 1) t.toNNReal : ℂ))

theorem brownianConfigurationNoisePathMap_measurable (n : ℕ) (α : ℝ) :
    Measurable (brownianConfigurationNoisePathMap n α) := by
  apply Measurable.of_eval
  intro t
  apply Measurable.of_eval
  intro j
  exact ((((measurable_pi_apply t.toNNReal).comp (measurable_pi_apply (j, 0))).complex_ofReal).add
    (measurable_const.mul (((measurable_pi_apply t.toNNReal).comp
      (measurable_pi_apply (j, 1))).complex_ofReal))).const_smul (Real.sqrt (2*α/(n : ℝ)^2))

/-- The actual normalized continuous shifted configuration noise has exactly
 the same whole-path law as the original actual noise. -/
theorem brownianFamily_shift_continuous_noise_law_eq {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (α : ℝ) (s : ℝ≥0) :
    P.map (ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α) =
      P.map (ginibreBrownianFullContinuousNoise n B α) := by
  let : MeasurableSpace C(ℝ, Configuration n) := borel _
  let : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
  let X := ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α
  let Y := ginibreBrownianFullContinuousNoise n B α
  have hshift := (brownianFamilyShift_isBrownian_independent B P hB hind s).1
  have hX : Measurable X := ginibreBrownianFullContinuousNoise_measurable n _ P hshift α
  have hY : Measurable Y := ginibreBrownianFullContinuousNoise_measurable n _ P hB α
  have hXm : Measurable (fun ω i t => brownianFamilyShift B s i t ω) := by
    apply Measurable.of_eval
    intro i
    exact brownianScalar_whole_path_measurable P _ (hshift i).toIsPreBrownianReal
  have hYm : Measurable (fun ω i t => B i t ω) := by
    apply Measurable.of_eval
    intro i
    exact brownianScalar_whole_path_measurable P _ (hB i).toIsPreBrownianReal
  have hraw : P.map (fun ω => ginibreConfigurationBrownianNoise n (brownianFamilyShift B s) α ω) =
      P.map (fun ω => ginibreConfigurationBrownianNoise n B α ω) := by
    have hh := congrArg (Measure.map (brownianConfigurationNoisePathMap n α))
      (brownianFamily_shift_whole_path_law_eq P B hB hind s)
    rw [Measure.map_map (brownianConfigurationNoisePathMap_measurable n α) hXm,
      Measure.map_map (brownianConfigurationNoisePathMap_measurable n α) hYm] at hh
    exact hh
  have hXL : (fun ω => ginibreConfigurationBrownianNoise n (brownianFamilyShift B s) α ω) =ᵐ[P]
      (fun ω t => (X ω).val t) :=
    (ginibreBrownianFullContinuousNoise_ae n _ P hshift α).mono fun ω hω => (funext hω).symm
  have hYL : (fun ω => ginibreConfigurationBrownianNoise n B α ω) =ᵐ[P]
      (fun ω t => (Y ω).val t) :=
    (ginibreBrownianFullContinuousNoise_ae n _ P hB α).mono fun ω hω => (funext hω).symm
  have hval : Continuous (fun f : GinibreContinuousNoise n => f.val) := continuous_subtype_val
  have hCM : P.map (fun ω => (X ω).val) = P.map (fun ω => (Y ω).val) := by
    apply continuousMap_law_eq_of_whole_path_law_eq P (fun ω => (X ω).val) (fun ω => (Y ω).val)
      (hval.measurable.comp hX) (hval.measurable.comp hY)
    exact (Measure.map_congr hXL).symm.trans (hraw.trans (Measure.map_congr hYL))
  have hclosed : IsClosed {f : C(ℝ, Configuration n) | f 0 = 0} :=
    isClosed_eq (continuous_eval_const 0) continuous_const
  have hec : Topology.IsClosedEmbedding (fun f : GinibreContinuousNoise n => f.val) :=
    hclosed.isClosedEmbedding_subtypeVal
  apply hec.measurableEmbedding.map_injective
  rw [Measure.map_map hec.measurableEmbedding.measurable hX,
    Measure.map_map hec.measurableEmbedding.measurable hY]
  exact hCM

end
end GinibrePoincare
