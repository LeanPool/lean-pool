/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltOUSublevelCanonicalLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltActualCanonicalLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUSublevelInteractionDensity
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltOUSurvival

/-!
# Ginibre Brownian integral tilt OU sublevel canonical law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreActualOU_sublevel_canonical_whole_path_law_exists`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance canonicalSublevelFiniteMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance canonicalSublevelFiniteBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- Canonical original path driven by the continuous normalization of a
literal finite configuration noise path. -/
def ginibreCanonicalFiniteNoisePath {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (T : ℝ≥0) (N : Ω → Icc (0 : ℝ) (T : ℝ) → Configuration n)
    (ω : Ω) (t : Icc (0 : ℝ≥0) T) : Configuration n :=
  ginibreDrivenMaximalValue n α
    (ginibreFiniteNoiseExtension n T (ginibreFiniteContinuousNoiseNormalize n T N ω)).val z t.val

/-- Unconditional identification of the complete canonical original finite
path law under the actual sublevel OU interaction likelihood. The ordinary
Brownian and corrected drivers are literal continuous configuration paths;
the likelihood is formed from the genuine stochastic integral limits. -/
theorem ginibreActualOU_sublevel_canonical_whole_path_law_exists {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ)
    (hR : ginibreHamiltonian n z < R) (T : ℝ≥0) (hT : 0 < T) :
    ∃ Y : ℝ≥0 → Ω → Configuration n,
      ∃ M : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ,
      (∀ i, TendstoInMeasure P (fun k => brownianUniformLeftSum (B i)
        (fun r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (k+1)) atTop (M i T)) ∧
      Integrable (brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T)) P ∧
      (∫ ω, brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω ∂P)=1 ∧
      let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω))
      ((∀ᵐ ω ∂Q, (T : ℝ≥0∞)<ginibreDrivenMaximalLifetime n α
        (ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω) z) ∧
      IdentDistrib
        (fun ω (t : Icc (0 : ℝ≥0) T) => ginibreDrivenMaximalValue n α
          (ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω) z
              t.val)
        (fun ω (t : Icc (0 : ℝ≥0) T) => ginibreBrownianMaximalProcess n α z B t.val ω) Q P) ∧
      ∀ᵐ ω ∂Q,
        let N := ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α
            ω
        ((∀ t≤T, ginibreDrivenMaximalValue n α N z t ∈ ginibreHamiltonianOUSublevelDomain n R) ↔
          (∀ t≤T, ginibreHamiltonianOUReferenceProcess n α z B t ω ∈
              ginibreHamiltonianOUSublevelDomain n R)) ∧
        ((∀ t≤T, ginibreHamiltonianOUReferenceProcess n α z B t ω ∈
            ginibreHamiltonianOUSublevelDomain n R) →
          (∀ t≤T, ginibreDrivenMaximalValue n α N z t=ginibreHamiltonianOUReferenceProcess n α z B t
              ω) ∧
          (∀ t≤T, Y t ω=ginibreHamiltonianOUReferenceProcess n α z B t ω) ∧
          brownianVectorExponentialIntegralDensity
            (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω =
            Real.exp (ginibreInteractionPotential n z)*
              (ginibreHamiltonianGradientPathWeight n α T (fun s => Y s.toNNReal ω)/
                ginibreQuadraticGradientPathWeight n α T (fun s => Y s.toNNReal ω))) := by
  classical
  obtain ⟨K, hK, hCF, Y, hYC, hYR, hY0, hY, θ, hStop, hθ, hStopped, hθActual, hEq, M, hM, hDi, hD1,
      hAction⟩ :=
    ginibreHamiltonianOU_sublevel_interaction_action_density_exists hn B P hB hind α z hz R hR T hT
  let F := fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i
  obtain ⟨C, hC, hb⟩ := ginibreInteractionBrownianTilt_compact_bound n α K hK hCF
  have hF (i : Fin n × Fin 2) (r : ℝ≥0) : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) r) _ (F i r) :=
    (ginibreInteractionBrownianTilt_measurable n α i).comp (hY r).measurable
  have hFi (i : Fin n × Fin 2) (r : ℝ≥0) : MemLp (F i r) 2 P := by
    apply MemLp.of_bound ((hF i r).mono ((ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)).le r) le_rfl).aestronglyMeasurable C
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    apply abs_le_of_sq_le_sq _ hC
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (F j r ω)) (Finset.mem_univ i)).trans (hb _
        (hYR r ω))
  obtain ⟨hNm, hMm, hLaw⟩ := ginibreInteraction_actual_configuration_continuous_noise_law n B P hB
      hind α
    Y hYC (fun r ω => hCF _ (hYR r ω)) hF C hC (fun r ω => hb _ (hYR r ω)) T hT
    (fun i k => (brownianUniformLeftSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal)
      hind i (F i) (hF i) (hFi i) T (k+1)).aestronglyMeasurable)
    (fun i => M i T) (fun i => (hM i).2.2.2.2 T le_rfl)
  refine ⟨Y, M, fun i => (hM i).2.2.2.2 T le_rfl, hDi, hD1,?_⟩
  constructor
  · let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity F T
      (fun i => M i T) ω))
    let N := fun ω => ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B
        Y) α ω
    let L := fun ω => ginibreConfigurationBrownianNoise n (fun i r ω => B i r ω-B i 0 ω) α ω
    have hQP : Q ≪ P := withDensity_absolutelyContinuous P _
    have hBc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => B i t ω) := ae_all_iff.mpr (fun i => (hB i).cont)
    have hNcP : ∀ᵐ ω ∂P, Continuous (N ω) ∧ N ω 0=0 := by
      filter_upwards [hBc] with ω hω
      exact ginibreInteractionCorrectedBrownian_noise_continuous n α B Y ω hω (hYC ω) (fun t => hCF
          _ (hYR t ω))
    have hNc : ∀ᵐ ω ∂Q, Continuous (N ω) ∧ N ω 0=0 := hQP.ae_le hNcP
    have hBz : ∀ᵐ ω ∂P, ∀ i, B i 0 ω=0 := ae_all_iff.mpr (fun i => (hB i).eval_zero_ae_eq_zero)
    have hBaseEq : ∀ᵐ ω ∂P, L ω=fun s => (ginibreBrownianFullContinuousNoise n B α ω).val s := by
      filter_upwards [hBz, ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hz hn
      funext s
      rw [hn s]
      funext j
      simp [L, ginibreConfigurationBrownianNoise, hz]
    have hLc : ∀ᵐ ω ∂P, Continuous (L ω) ∧ L ω 0=0 := by
      filter_upwards [hBaseEq] with ω hω
      rw [hω]
      exact ⟨(ginibreBrownianFullContinuousNoise n B α ω).val.continuous,
        (ginibreBrownianFullContinuousNoise n B α ω).property⟩
    have hAliveL : ∀ᵐ ω ∂P, (T : ℝ≥0∞)<ginibreDrivenMaximalLifetime n α (L ω) z := by
      filter_upwards [hBaseEq, ginibreBrownianMaximalLifetime_top_ae hn α z hz B P hB hind] with ω
          hω htop
      rw [hω]
      change (T : ℝ≥0∞)<ginibreBrownianMaximalLifetime n α z B ω
      rw [htop]
      exact ENNReal.coe_lt_top
    have hTransfer := ginibreActualFiniteNoise_canonical_whole_path_law hn α z hz T P Q N L
      hNc hLc hAliveL hNm hMm hLaw
    have hIdent := hTransfer.2
    have heR : (fun ω (t : Icc (0 : ℝ≥0) T) => ginibreDrivenMaximalValue n α (L ω) z t.val)=ᵐ[P]
        (fun ω (t : Icc (0 : ℝ≥0) T) => ginibreBrownianMaximalProcess n α z B t.val ω) := by
      filter_upwards [hBaseEq] with ω hω
      funext t
      rw [hω]
      rfl
    exact ⟨hTransfer.1, hIdent.aemeasurable_fst, hIdent.aemeasurable_snd.congr heR,
      hIdent.map_eq.trans (Measure.map_congr heR)⟩
  · let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity F T
      (fun i => M i T) ω))
    have hQP : Q ≪ P := withDensity_absolutelyContinuous P _
    have hCan : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t≤θ ω → ginibreDrivenMaximalValue n α
        (ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω) z
            t=Y t ω :=
      ginibreOUPath_correctedBrownian_canonical_prefix_ae n α B P hB Y z θ hYC
        (fun t ω => hCF _ (hYR t ω)) hY0 hEq
    have hCanQ : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t≤θ ω → ginibreDrivenMaximalValue n α
        (ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω) z
            t=Y t ω := hQP.ae_le hCan
    have hActionQ := hQP.ae_le hAction
    filter_upwards [hCanQ, hActionQ] with ω hC hA
    refine ⟨ginibreOU_canonical_survival_iff_reference_survival n α z B R T Y θ
      hStopped hθActual _ ω (hθ ω).2 hC,?_⟩
    intro hStay
    have hEq := ginibreOU_canonical_prefix_eq_reference_on_survival n α z B R T Y θ
      hStopped hθActual _ ω hC hStay
    have hθT : θ ω=T := (hθActual ω).trans
      (ginibreHamiltonianOUSublevelStop_eq_horizon_of_stays n α z B R T ω hStay)
    exact ⟨hEq, (ginibreHamiltonianOUSublevelStopped_eq_reference_of_stays
      n α z B R T Y θ hStopped hθActual ω hStay).2, hA T (hθT ▸ le_rfl)⟩

end
end GinibrePoincare
