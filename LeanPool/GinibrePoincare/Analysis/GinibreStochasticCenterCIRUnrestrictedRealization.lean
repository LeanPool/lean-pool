/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterCIRUnrestrictedRealization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterSquaredDrivenLocal
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroCIRDrivenLocal
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalizationExhaustion
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRadialPath

/-! Genuine stochastic CIR realization of the original Ginibre radius.
The Brownian driver, stochastic integrals and exhausting stopping times are
all constructed from the original independent Brownian family. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_center_unrestricted_CIR_realization
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
    let τ := fun k : ℕ => ginibreBrownianHamiltonianBoundedStop n α z B (ginibreHamiltonian n z+k) k
    ∃ β : ℝ≥0 → Ω → ℝ,
      IsBrownianReal β P ∧ Martingale β F P ∧ (∀ t, MemLp (β t) 2 P) ∧
      (∀ s t (Y : Ω → ℝ), @Measurable Ω ℝ (F s) _ Y →
        IndepFun Y (fun ω => β (s+t) ω-β s ω) P) ∧
      (∀ k, IsStoppingTime F (fun ω => (τ k ω : WithTop ℝ≥0))) ∧
      (∀ ω, Monotone (fun k => τ k ω)) ∧
      (∀ᵐ ω ∂P, ∀ b : ℝ≥0, ∀ᶠ k : ℕ in atTop, b ≤ τ k ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => (ginibreCenterSquared n) (ginibreBrownianMaximalProcess n
          α z B t ω)) ∧
        ∀ t, 0 < t → 0 < (ginibreCenterSquared n) (ginibreBrownianMaximalProcess n α z B t ω)) ∧
      ∀ (R : ℝ), ginibreHamiltonian n z ≤ R → ∀ (T : ℝ≥0),
        let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
        let a := fun t ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*(ginibreCenterSquared n) (X t ω))
        ∃ J : ℝ≥0 → Ω → ℝ,
          Martingale J F P ∧ (∀ ω, Continuous (fun t => J t ω)) ∧
          (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
          (∀ t ≤ T, Tendsto (fun k => ∫ ω,
            (brownianUniformLeftSum β a t (k+1) ω-J t ω)^2 ∂P) atTop (𝓝 0)) ∧
          (∀ t ≤ T, TendstoInMeasure P (fun k => brownianUniformLeftSum β a t (k+1)) atTop (J t)) ∧
          (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
            (ginibreCenterSquared n) (X t ω)-(ginibreCenterSquared n) z = J t ω+
              ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
                ((1 : ℝ)-(ginibreCenterSquared n) (X s.toNNReal ω))) := by
  classical
  let i₀ : Fin n × Fin 2 := (⟨0, by omega⟩, 0)
  let e : EuclideanSpace ℝ (Fin n × Fin 2) := EuclideanSpace.single i₀ 1
  have he : ‖e‖=1 := by simp [e, PiLp.norm_single]
  obtain ⟨β, hβ, hβM, hβL, hβ0, hβLim, hβShift, hβFresh⟩ :=
    ginibreBrownianMaximalProcess_center_unrestricted_Brownian_exists hn α hα z hz B P hB hind
  refine ⟨β, hβ, hβM, hβL, hβFresh,?_,?_,?_,?_,?_⟩
  · intro k
    exact ginibreBrownianHamiltonianBoundedStop_isStoppingTime (by omega) α z hz B P hB
      _ (le_add_of_nonneg_right (Nat.cast_nonneg k)) k
  · intro ω
    exact ginibreBrownianHamiltonianBoundedStop_natural_monotone n α z B ω
  · exact ginibreBrownianHamiltonianBoundedStop_exhausts_ae (by omega) α z hz B P hB hind
  · filter_upwards [ginibreBrownian_center_all_positive_times_nonzero hn α hα z hz B P hB hind,
      (ginibreBrownianMaximalProcess_global_original_solution (by omega) α z hz B P hB hind).2]
      with ω hnonzero hsolution
    have hc : Continuous (fun t : ℝ≥0 => ginibreBrownianMaximalProcess n α z B t ω) := by
      simpa only [Function.comp_def, Real.toNNReal_coe] using hsolution.1.comp NNReal.continuous_coe
    refine ⟨(contDiff_ginibreCenterSquared n).continuous.comp hc, fun t ht => ?_⟩
    exact lt_of_le_of_ne (ginibreCenterSquared_nonneg n _) (Ne.symm (hnonzero t ht))
  · intro R hR T
    by_cases hcenter : ginibreCenterSquared n z=0
    · exact ginibreBrownianMaximalProcess_zero_center_CIR_Brownian_integral hn α hα z hz hcenter
        B P hB hind e he β hβM hβL hβLim R hR T
    · exact ginibreBrownianMaximalProcess_local_center_CIR_Brownian_integral hn α z hz
        (lt_of_le_of_ne (ginibreCenterSquared_nonneg n z) (Ne.symm hcenter)) B P hB hind
        e he β hβL hβLim R hR T
end
end GinibrePoincare
