/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltConfigurationLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltContinuousLaw

/-!
# Ginibre Brownian integral tilt configuration law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreFiniteVectorNoiseLift_configurationNoise`,
`ginibreInteraction_actual_configuration_continuous_noise_law`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Literal linear coordinate lift and real-time reindex of a finite vector
Brownian driving path. -/
def ginibreFiniteVectorNoiseLift (n : ℕ) (α : ℝ) (T : ℝ≥0)
    (f : Icc (0 : ℝ≥0) T → (Fin n × Fin 2) → ℝ)
    (t : Icc (0 : ℝ) (T : ℝ)) : Configuration n :=
  ginibreBrownianEmbeddingCLM n α (f ⟨t.val.toNNReal,
    ⟨bot_le, Real.toNNReal_le_iff_le_coe.mpr t.property.2⟩⟩)

theorem ginibreFiniteVectorNoiseLift_measurable (n : ℕ) (α : ℝ) (T : ℝ≥0) :
    Measurable (ginibreFiniteVectorNoiseLift n α T) := by
  apply Measurable.of_eval
  intro t
  exact (ginibreBrownianEmbeddingCLM n α).measurable.comp (measurable_pi_apply _)

/-- The literal configuration lift preserves actual whole finite vector
noise laws. This is a measurable mapping step for the Girsanov whole-path
law, with no stochastic conclusion asserted independently of that law. -/
theorem ginibreFiniteVectorNoiseLift_law {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (α : ℝ) (T : ℝ≥0) (P Q : Measure Ω)
    (X Y : Ω → Icc (0 : ℝ≥0) T → (Fin n × Fin 2) → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hLaw : Q.map X = P.map Y) :
    Measurable (fun ω => ginibreFiniteVectorNoiseLift n α T (X ω)) ∧
    Measurable (fun ω => ginibreFiniteVectorNoiseLift n α T (Y ω)) ∧
    Q.map (fun ω => ginibreFiniteVectorNoiseLift n α T (X ω))=
      P.map (fun ω => ginibreFiniteVectorNoiseLift n α T (Y ω)) := by
  have hm := ginibreFiniteVectorNoiseLift_measurable n α T
  exact ⟨hm.comp hX, hm.comp hY,
    ((show IdentDistrib X Y Q P from ⟨hX.aemeasurable, hY.aemeasurable, hLaw⟩).comp hm).map_eq⟩

@[simp] theorem ginibreFiniteVectorNoiseLift_configurationNoise {Ω : Type*}
    (n : ℕ) (α : ℝ) (T : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (ω : Ω) (t : Icc (0 : ℝ) (T : ℝ)) :
    ginibreFiniteVectorNoiseLift n α T (fun s i => B i s.val ω) t=
      ginibreConfigurationBrownianNoise n B α ω t.val := by
  rfl

/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance configLawFiniteMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance configLawFiniteBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- Genuine continuous configuration-driver law for the actual bounded
Hamiltonian interaction tilt. The likelihood is built from limits of the
literal Brownian left sums; the conclusion supplies the continuous random
noise paths required by the measurable canonical original solver. -/
theorem ginibreInteraction_actual_configuration_continuous_noise_law {Ω : Type*}
    [MeasurableSpace Ω] (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n)
    (hYC : ∀ ω, Continuous (fun t => Y t ω)) (hCF : ∀ t ω, CollisionFree (Y t ω))
    (hF : ∀ i t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal) t) _
      (fun ω => ginibreInteractionBrownianTilt n α (Y t ω) i))
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t ω, (∑ i, (ginibreInteractionBrownianTilt n α (Y t ω) i) ^ 2) ≤ C ^ 2)
    (T : ℝ≥0) (hT : 0 < T)
    (hs : ∀ i k, AEStronglyMeasurable (brownianUniformLeftSum (B i)
      (fun t ω => ginibreInteractionBrownianTilt n α (Y t ω) i) T (k + 1)) P)
    (I : (Fin n × Fin 2) → Ω → ℝ)
    (hI : ∀ i, TendstoInMeasure P (fun k => brownianUniformLeftSum (B i)
      (fun t ω => ginibreInteractionBrownianTilt n α (Y t ω) i) T (k + 1)) atTop (I i)) :
    let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity
      (fun i t ω => ginibreInteractionBrownianTilt n α (Y t ω) i) T I ω))
    let N := fun ω (t : Icc (0 : ℝ) (T : ℝ)) =>
      ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω t.val
    let M := fun ω (t : Icc (0 : ℝ) (T : ℝ)) =>
      ginibreConfigurationBrownianNoise n (fun i r ω => B i r ω-B i 0 ω) α ω t.val
    Measurable (ginibreFiniteContinuousNoiseNormalize n T N) ∧
      Measurable (ginibreFiniteContinuousNoiseNormalize n T M) ∧
      Q.map (ginibreFiniteContinuousNoiseNormalize n T N)=
        P.map (ginibreFiniteContinuousNoiseNormalize n T M) := by
  classical
  dsimp only
  let F := fun i t ω => ginibreInteractionBrownianTilt n α (Y t ω) i
  let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity F T I
      ω))
  have hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Icc 0 T) := by
    intro i
    exact ae_of_all P (fun ω => ((ginibreInteractionBrownianTilt_continuousOn n α i).comp_continuous
      (hYC ω) (fun t => hCF t ω)).continuousOn)
  obtain ⟨hXm, hYm, hLaw, hcont⟩ := brownianVectorExponentialIntegralDensity_whole_path_law
    B P hB hind F hF C hC hb T hT hc hs I hI
  obtain ⟨hNm, hMm, hConfig⟩ := ginibreFiniteVectorNoiseLift_law n α T P Q _ _ hXm hYm hLaw
  have hBc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => B i t ω) :=
    ae_all_iff.mpr (fun i => (hB i).cont)
  have hNc : ∀ᵐ ω ∂P, Continuous (fun t : Icc (0 : ℝ) (T : ℝ) =>
      ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω t.val)
          := by
    filter_upwards [hBc] with ω hω
    exact (ginibreInteractionCorrectedBrownian_noise_continuous n α B Y ω hω
      (hYC ω) (fun t => hCF t ω)).1.comp continuous_subtype_val
  have hMc : ∀ᵐ ω ∂P, Continuous (fun t : Icc (0 : ℝ) (T : ℝ) =>
      ginibreConfigurationBrownianNoise n (fun i r ω => B i r ω-B i 0 ω) α ω t.val) := by
    filter_upwards [hBc] with ω hω
    change Continuous (fun t : Icc (0 : ℝ) (T : ℝ) =>
      ginibreBrownianEmbeddingCLM n α (fun i => B i t.val.toNNReal ω-B i 0 ω))
    apply (ginibreBrownianEmbeddingCLM n α).continuous.comp
    apply continuous_pi
    intro i
    exact ((hω i).comp (continuous_real_toNNReal.comp continuous_subtype_val)).sub continuous_const
  exact ginibreFiniteContinuousNoiseNormalize_law n T P Q _ _ hNm hMm hNc hMc
    (withDensity_absolutelyContinuous P _) hConfig

end
end GinibrePoincare
