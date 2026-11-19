/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianOUSublevelInteractionIto.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInteractionPotential
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUReferenceSublevelStopped
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactItoIntegral

/-! A genuine original-Brownian compact stopped reference OU process and its
interaction-potential Itô martingale, with all local analytic facts derived. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreHamiltonianOU_sublevel_interaction_ito_exists {Ω : Type*} [MeasurableSpace Ω]
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
      ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧
      J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t ≤ T, TendstoInMeasure P
        (ginibreConfigurationBrownianGradientSum n B α Y (ginibreInteractionPotential n) t) atTop (J
            t)) ∧
      ∀ᵐ ω ∂P, ∀ t ≤ θ ω,
        ginibreInteractionPotential n (Y t ω)-ginibreInteractionPotential n z-
          ((2*(α : ℝ)/(n : ℝ))*(2*vandermondeDegree n : ℕ))*(t : ℝ) = J t ω := by
  let K := ginibreHamiltonianSublevel n R
  have hK : IsCompact K := ginibreHamiltonianSublevel_isCompact hn R
  have hKCF : ∀ x ∈ K, CollisionFree x := fun x hx => hx.1
  obtain ⟨Y, hYC, hYR, hY0, hAdapt, θ, hStop, hθ, hStopped, hθActual, hEq⟩ :=
    ginibreHamiltonianOU_reference_sublevel_stopped_exists hn B P hB α z hz R hRlevel T hT
  have hθT (ω : Ω) : θ ω ≤ T := (hθ ω).2
  let b : ℝ → Ω → Configuration n := fun s ω => (-2*(α : ℝ)/(n : ℝ)) • Y s.toNNReal ω
  have hb (ω : Ω) : Continuous (fun s => b s ω) := by
    exact ((hYC ω).comp continuous_real_toNNReal).const_smul (-2*(α : ℝ)/(n : ℝ))
  obtain ⟨R, hR, hRB⟩ := hK.isBounded.exists_pos_norm_le
  let M := |(-2*(α : ℝ)/(n : ℝ))| * R
  have hM : 0 ≤ M := mul_nonneg (abs_nonneg _) hR.le
  have hbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ ω, ‖b s ω‖ ≤ M := by
    intro s hs ω
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hRB _ (hYR _ _)) (abs_nonneg _)
  have hV : ContDiffOn ℝ 2 (ginibreInteractionPotential n) {x | CollisionFree x} :=
    fun x hx => ((ginibreInteractionPotential_contDiffAt n x hx).of_le
      (by exact WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffWithinAt
  have hθm : Measurable θ := by
    have hm : Measurable (fun ω => (θ ω : WithTop ℝ≥0))  := hStop.measurable.mono
        hStop.measurableSpace_le le_rfl
    have hh := ENNReal.measurable_toNNReal.comp hm
    simpa [Function.comp_def] using hh
  have hVEq : ∀ᵐ ω ∂P, ∀ t ≤ θ ω, Y t ω = z+ginibreConfigurationBrownianNoise n B α ω t+
      ∫ s in (0 : ℝ)..t, b s ω := hEq
  have hVol : ∀ᵐ ω ∂P, ∀ t ≤ θ ω, Y t ω = Y 0 ω+
      (ginibreConfigurationBrownianNoise n B α ω t-ginibreConfigurationBrownianNoise n B α ω 0)+
      ∫ s in (0 : ℝ)..t, b s ω := by
    filter_upwards [hVEq, ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hω hNoise
    intro t ht
    rw [hY0, hNoise.2, sub_zero]
    exact hω t ht
  obtain ⟨J, hJM, hJC, hJL, hJ0, hLimit, hIto⟩ :=
    ginibreCompactVolterra_continuous_ito_integral_exists n B P hB hind α Y hAdapt hYC
      (ginibreInteractionPotential n) {x | CollisionFree x} K (isOpen_collisionFree n) hV hK hKCF
          hYR
      T b hb M hM hbound θ hθm hθT hVol
  refine ⟨K, hK, hKCF, Y, hYC, hYR, hY0, hAdapt, θ, hStop,
    fun ω => ⟨(hθ ω).1, hθT ω⟩, hStopped, hθActual, hVEq, J, hJM, hJC, hJL, hJ0, hLimit,?_⟩
  filter_upwards [hIto] with ω hω
  intro t ht
  have h := hω t ht
  unfold ginibreConfigurationTestCompensator at h
  have hL : (∫ s in (0 : ℝ)..t, configurationLaplacian (ginibreInteractionPotential n) (Y s.toNNReal
      ω)) = 0 := by
    simp_rw [ginibreInteractionPotential_laplacian _ (hKCF _ (hYR _ _))]
    simp
  have hD : (∫ s in (0 : ℝ)..t, fderiv ℝ (ginibreInteractionPotential n) (Y s.toNNReal ω) (b s ω)) =
      ((2*(α : ℝ)/(n : ℝ))*(2*vandermondeDegree n : ℕ))*(t : ℝ) := by
    have he (s : ℝ) : fderiv ℝ (ginibreInteractionPotential n) (Y s.toNNReal ω) (b s ω) =
        ((2*(α : ℝ)/(n : ℝ))*(2*vandermondeDegree n : ℕ)) := by
      have hg := ginibreInteractionPotential_ou_generator (α : ℝ) (Y s.toNNReal ω) (hKCF _ (hYR _
          _))
      rw [ginibreInteractionPotential_laplacian _ (hKCF _ (hYR _ _)), mul_zero, add_zero] at hg
      exact hg
    simp_rw [he]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  simpa [hY0, hL, hD] using h

end
end GinibrePoincare
