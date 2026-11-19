/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltOUSublevel.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUSublevelInteractionDensity
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltVolterra

/-!
# Ginibre Brownian integral tilt OU sublevel

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreActualOU_sublevel_tilted_canonical_prefix_exists`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The actual selected OU interaction likelihood simultaneously normalizes,
turns the entire corrected driver into Brownian noise, and identifies its
reference path with the genuine canonical original Ginibre solution before
the actual positive stopping time. -/
theorem ginibreActualOU_sublevel_tilted_canonical_prefix_exists {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ)
    (hR : ginibreHamiltonian n z < R) (T : ℝ≥0) (hT : 0 < T) :
    ∃ Y : ℝ≥0 → Ω → Configuration n,
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ t ω, CollisionFree (Y t ω)) ∧
      (∀ ω, Y 0 ω=z) ∧ ∃ θ : Ω → ℝ≥0,
      IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun ω => (θ ω : WithTop ℝ≥0)) ∧ (∀ ω, 0<θ ω ∧ θ ω≤T) ∧
      (∀ t ω, Y t ω=ginibreHamiltonianOUReferenceProcess n α z B (min t (θ ω)) ω) ∧
      (∀ ω, θ ω=ginibreHamiltonianOUSublevelStop n α z B R T ω) ∧
      ∃ M : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ,
      (∀ i t, t≤T → TendstoInMeasure P (fun k => brownianUniformLeftSum (B i)
        (fun r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) t (k+1)) atTop (M i t)) ∧
      Integrable (brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T)) P ∧
      (∫ ω, brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω ∂P)=1 ∧
      let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω))
      Q.map (fun ω (t : Icc (0 : ℝ≥0) T) i => ginibreInteractionCorrectedBrownian n α B Y i t.val
          ω)=
        P.map (fun ω (t : Icc (0 : ℝ≥0) T) i => B i t.val ω-B i 0 ω) ∧
      (∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t≤θ ω → ginibreDrivenMaximalValue n α
        (ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω) z
            t=Y t ω) ∧
      ∀ᵐ ω ∂Q, ∀ t≤θ ω, brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) t (fun i => M i t) ω =
        Real.exp (ginibreInteractionPotential n z)*
          (ginibreHamiltonianGradientPathWeight n α t (fun s => Y s.toNNReal ω)/
            ginibreQuadraticGradientPathWeight n α t (fun s => Y s.toNNReal ω)) := by
  classical
  obtain ⟨K, hK, hCF, Y, hYC, hYR, hY0, hY, θ, hStop, hθ, hStopped, hθActual, hEq, M, hM, hDi, hD1,
      hAction⟩ :=
    ginibreHamiltonianOU_sublevel_interaction_action_density_exists hn B P hB hind α z hz R hR T hT
  let F := fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i
  let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity F T (fun
      i => M i T) ω))
  have hQP : Q ≪ P := withDensity_absolutelyContinuous P _
  obtain ⟨C, hC, hb⟩ := ginibreInteractionBrownianTilt_compact_bound n α K hK hCF
  have hF (i : Fin n × Fin 2) (r : ℝ≥0) : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) r) _ (F i r) :=
    (ginibreInteractionBrownianTilt_measurable n α i).comp (hY r).measurable
  have hFc (i : Fin n × Fin 2) : ∀ᵐ ω ∂P, ContinuousOn (fun r => F i r ω) (Icc 0 T) :=
    ae_of_all P (fun ω => ((ginibreInteractionBrownianTilt_continuousOn n α i).comp_continuous
      (hYC ω) (fun r => hCF _ (hYR r ω))).continuousOn)
  have hFi (i : Fin n × Fin 2) (r : ℝ≥0) : MemLp (F i r) 2 P := by
    apply MemLp.of_bound ((hF i r).mono ((ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)).le r) le_rfl).aestronglyMeasurable C
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    apply abs_le_of_sq_le_sq _ hC
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (F j r ω)) (Finset.mem_univ i)).trans (hb _
        (hYR r ω))
  have hLaw := brownianVectorExponentialIntegralDensity_whole_path_law B P hB hind F hF C hC
    (fun r ω => hb _ (hYR r ω)) T hT hFc
    (fun i k => (brownianUniformLeftSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal)
      hind i (F i) (hF i) (hFi i) T (k+1)).aestronglyMeasurable)
    (fun i => M i T) (fun i => (hM i).2.2.2.2 T le_rfl)
  refine ⟨Y, hYC, fun r ω => hCF _ (hYR r ω), hY0, θ, hStop, hθ, hStopped, hθActual, M,
    fun i t ht => (hM i).2.2.2.2 t ht, hDi, hD1, hLaw.2.2.1,
    hQP.ae_le (ginibreOUPath_correctedBrownian_canonical_prefix_ae n α B P hB Y z θ hYC
      (fun t ω => hCF _ (hYR t ω)) hY0 hEq), hQP.ae_le hAction⟩

end
end GinibrePoincare
