/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianOUSublevelInteractionDensity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUSublevelInteractionIto
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInteractionTilt
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUActionExpansion

/-! The actual normalized Brownian interaction likelihood equals the literal
OU-relative Hamiltonian action through a genuine positive stopping time. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreHamiltonianOU_sublevel_interaction_action_density_exists {Ω : Type*} [MeasurableSpace
    Ω]
    {n : ℕ} (hn : 0 < n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ) (hRlevel : ginibreHamiltonian n z < R) (T :
        ℝ≥0) (hT : 0 < T) :
    ∃ K : Set (Configuration n), IsCompact K ∧
      (∀ x ∈ K, CollisionFree x) ∧ ∃ Y : ℝ≥0 → Ω → Configuration n,
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ t ω, Y t ω ∈ K) ∧
      (∀ ω, Y 0 ω = z) ∧
      StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
          Y ∧
      ∃ θ : Ω → ℝ≥0,
      IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun ω => (θ ω : WithTop ℝ≥0)) ∧ (∀ ω, 0 < θ ω ∧ θ ω ≤ T) ∧
      (∀ t ω, Y t ω = ginibreHamiltonianOUReferenceProcess n α z B (min t (θ ω)) ω) ∧
      (∀ ω, θ ω = ginibreHamiltonianOUSublevelStop n α z B R T ω) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ θ ω, Y t ω = z+ginibreConfigurationBrownianNoise n B α ω t+
        ∫ s in (0 : ℝ)..t, (-2*(α : ℝ)/(n : ℝ)) • Y s.toNNReal ω) ∧
      ∃ M : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ,
      (∀ i, Martingale (M i) (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P ∧
        (∀ ω, Continuous (fun t => M i t ω)) ∧ (∀ t, MemLp (M i t) 2 P) ∧
        M i 0 =ᵐ[P] (fun _ => 0) ∧
        ∀ t ≤ T, TendstoInMeasure P
          (fun k => brownianUniformLeftSum (B i)
            (fun r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) t (k+1)) atTop (M i t)) ∧
      Integrable (brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T)) P ∧
      (∫ ω, brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω ∂P)=1 ∧
      ∀ᵐ ω ∂P, ∀ t ≤ θ ω,
        brownianVectorExponentialIntegralDensity
          (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) t (fun i => M i t) ω =
        Real.exp (ginibreInteractionPotential n z) *
          (ginibreHamiltonianGradientPathWeight n α (t : ℝ) (fun s => Y s.toNNReal ω) /
            ginibreQuadraticGradientPathWeight n α (t : ℝ) (fun s => Y s.toNNReal ω)) := by
  obtain ⟨K, hK, hCF, Y, hYC, hYR, hY0, hY, θ, hStop, hθ, hStopped, hθActual, hEq, J, hJM, hJC, hJL,
      hJ0, hLimit, hIto⟩ :=
    ginibreHamiltonianOU_sublevel_interaction_ito_exists hn B P hB hind α z hz R hRlevel T hT
  obtain ⟨M, hM, hDi, hD1⟩ := ginibreInteractionBrownianTilt_exponential_exists
    n B P hB hind α Y hY hYC K hK hCF hYR T
  have hSum := ginibreInteractionBrownianTilt_integrals_eq_gradient n B P hB hind α Y hY
    K hK hCF hYR T J hJC hLimit M (fun i => (hM i).2.1) (fun i => (hM i).2.2.2.2)
  refine ⟨K, hK, hCF, Y, hYC, hYR, hY0, hY, θ, hStop, hθ, hStopped, hθActual, hEq, M, hM, hDi,
      hD1,?_⟩
  filter_upwards [hSum, hIto] with ω hSumω hItoω
  intro t ht
  have hMt := hSumω t (ht.trans (hθ ω).2)
  have hIt := hItoω t ht
  have hEnergy : brownianVectorTimeEnergy
      (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) t ω =
      (α/(2*(n : ℝ)^2)) * ∫ s in (0 : ℝ)..t, ginibreInteractionGradientNormSq n (Y s.toNNReal ω) :=
          by
    unfold brownianVectorTimeEnergy
    simp_rw [ginibreInteractionBrownianTilt_energy n α α.property]
    rw [intervalIntegral.integral_const_mul]
  have hx : ContinuousOn (fun s : ℝ => Y s.toNNReal ω) (Icc 0 (t : ℝ)) :=
    ((hYC ω).comp continuous_real_toNNReal).continuousOn
  have hex := ginibreHamiltonianOUPathQuotient_expansion hn α (t : ℝ) t.property
    (fun s : ℝ => Y s.toNNReal ω) hx (fun s hs => hCF _ (hYR _ _))
  rw [hex]
  unfold brownianVectorExponentialIntegralDensity
  rw [hMt, hEnergy,← Real.exp_add]
  rw [Real.toNNReal_zero, hY0, Real.toNNReal_coe]
  apply congrArg Real.exp
  rw [← hIt]
  ring

end
end GinibrePoincare
