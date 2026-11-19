/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionPermutationNoise.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionPermutationMaximal
public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalContinuousPathLaw

/-!
# Ginibre stochastic transition permutation noise

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreContinuousNoisePermute_continuous`,
`ginibreBrownian_continuous_noise_permute_law`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_continuous_noise_family_law_eq {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B C : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hC : ∀ i, IsBrownianReal (C i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (hindC : iIndepFun (fun i ω t => C i t ω) P) (α : ℝ) :
    P.map (ginibreBrownianFullContinuousNoise n C α) =
      P.map (ginibreBrownianFullContinuousNoise n B α) := by
  let : MeasurableSpace C(ℝ, Configuration n) := borel _
  let : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
  let X := ginibreBrownianFullContinuousNoise n C α
  let Y := ginibreBrownianFullContinuousNoise n B α
  have hshift := hC
  have hX : Measurable X := ginibreBrownianFullContinuousNoise_measurable n _ P hshift α
  have hY : Measurable Y := ginibreBrownianFullContinuousNoise_measurable n _ P hB α
  have hXm : Measurable (fun ω i t => C i t ω) := by
    apply Measurable.of_eval
    intro i
    exact brownianScalar_whole_path_measurable P _ (hshift i).toIsPreBrownianReal
  have hYm : Measurable (fun ω i t => B i t ω) := by
    apply Measurable.of_eval
    intro i
    exact brownianScalar_whole_path_measurable P _ (hB i).toIsPreBrownianReal
  have hraw : P.map (fun ω => ginibreConfigurationBrownianNoise n C α ω) =
      P.map (fun ω => ginibreConfigurationBrownianNoise n B α ω) := by
    have hh := congrArg (Measure.map (brownianConfigurationNoisePathMap n α))
      (brownianFamily_whole_path_law_eq P C B (fun i => (hC i).toIsPreBrownianReal)
        (fun i => (hB i).toIsPreBrownianReal) hindC hind)
    rw [Measure.map_map (brownianConfigurationNoisePathMap_measurable n α) hXm,
      Measure.map_map (brownianConfigurationNoisePathMap_measurable n α) hYm] at hh
    exact hh
  have hXL : (fun ω => ginibreConfigurationBrownianNoise n C α ω) =ᵐ[P]
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

/-- The Brownian family with particle indices relabeled by `σ`: `(j, b) ↦ B (σ j, b)`. -/
def ginibreParticleBrownianRelabel {Ω : Type*} {n : ℕ} (σ : ParticlePermutation n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ :=
  fun i => B (σ i.1, i.2)

/-- The noise path with particles permuted by `ginibreParticlePermutationCLM σ` at every
time. -/
def ginibreContinuousNoisePermute {n : ℕ} (σ : ParticlePermutation n)
    (N : GinibreContinuousNoise n) : GinibreContinuousNoise n :=
  ⟨(⟨ginibreParticlePermutationCLM σ, (ginibreParticlePermutationCLM σ).continuous⟩ :
    C(Configuration n, Configuration n)).comp N.val, by
      change ginibreParticlePermutationCLM σ (N.val 0)=0
      rw [N.property, map_zero]⟩

theorem ginibreContinuousNoisePermute_continuous {n : ℕ} (σ : ParticlePermutation n) :
    Continuous (ginibreContinuousNoisePermute σ) := by
  apply Continuous.subtype_mk
  exact ((⟨ginibreParticlePermutationCLM σ, (ginibreParticlePermutationCLM σ).continuous⟩ :
    C(Configuration n, Configuration n)).continuous_postcomp).comp continuous_subtype_val

theorem ginibreBrownian_relabel_independent {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : ParticlePermutation n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hi : iIndepFun (fun i ω t => B i t ω) P) :
    iIndepFun (fun i ω t => ginibreParticleBrownianRelabel σ B i t ω) P := by
  exact hi.precomp (Equiv.prodCongr σ (Equiv.refl (Fin 2))).injective

theorem ginibreBrownian_relabel_continuous_noise_ae {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : ParticlePermutation n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    ginibreBrownianFullContinuousNoise n (ginibreParticleBrownianRelabel σ B) α =ᵐ[P]
      (fun ω => ginibreContinuousNoisePermute σ (ginibreBrownianFullContinuousNoise n B α ω)) := by
  have hC : ∀ i, IsBrownianReal (ginibreParticleBrownianRelabel σ B i) P := fun i => hB (σ i.1, i.2)
  filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB α,
    ginibreBrownianFullContinuousNoise_ae n _ P hC α] with ω hω hω'
  apply Subtype.ext
  ext t j
  change (ginibreBrownianFullContinuousNoise n _ α ω).val t j=
    (ginibreParticlePermutationCLM σ ((ginibreBrownianFullContinuousNoise n B α ω).val t)) j
  rw [ginibreParticlePermutationCLM_apply, hω, hω']
  rfl

theorem ginibreBrownian_continuous_noise_permute_law {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : ParticlePermutation n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hi : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) :
    P.map (fun ω => ginibreContinuousNoisePermute σ (ginibreBrownianFullContinuousNoise n B α ω))=
      P.map (ginibreBrownianFullContinuousNoise n B α) := by
  rw [← Measure.map_congr (ginibreBrownian_relabel_continuous_noise_ae σ B P hB α)]
  exact ginibreBrownian_continuous_noise_family_law_eq n B (ginibreParticleBrownianRelabel σ B) P hB
    (fun i => hB (σ i.1, i.2)) hi (ginibreBrownian_relabel_independent σ B P hi) α

end
end GinibrePoincare
