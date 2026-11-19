/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterSquaredDrivenLocal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterSquaredFullNoiseSums
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterBrownian
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousFieldIntegral
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticIntegralUntilIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticWeightedSumMemLp
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionNatural
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCIRDrivenLocal

/-! Actual localized CIR stochastic integration against the constructed radial
Brownian driver. The substitution is derived from genuine Brownian sums. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_local_center_CIR_Brownian_integral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (hcenter : 0 < ginibreCenterSquared n z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (he : ‖e‖ = 1)
    (β : ℝ≥0 → Ω → ℝ) (hβL : ∀ t, MemLp (β t) 2 P)
    (hβLim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω =>
        ginibreCenterRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k + 1) ω) atTop (β t))
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0) :
    let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
    let a := fun t ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*(ginibreCenterSquared n) (X t ω))
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t ≤ T, Tendsto (fun k => ∫ ω,
        (brownianUniformLeftSum β a t (k+1) ω-J t ω)^2 ∂P) atTop (𝓝 0)) ∧
      (∀ t ≤ T, TendstoInMeasure P (fun k => brownianUniformLeftSum β a t (k+1)) atTop (J t)) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
        (ginibreCenterSquared n) (X t ω)-(ginibreCenterSquared n) z = J t ω+
          ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
            ((1 : ℝ)-(ginibreCenterSquared n) (X s.toNNReal ω))) := by
  classical
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  let a := fun t ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*(ginibreCenterSquared n) (X t ω))
  let u := fun t ω => ginibreCenterRadialDirection n e (ginibreBrownianMaximalProcess n α z B t ω)
  obtain ⟨hu, hunit, huc⟩ := ginibreBrownianMaximalProcess_centerDirection_properties hn α z hz
      hcenter B P hB hind e he
  obtain ⟨ha, hac, C, hC, hbound⟩ :=
      ginibreBrownianHamiltonianStoppedProcess_center_CIR_amplitude_properties
    (by omega) α z hz B P hB R hR T
  obtain ⟨N, hNM, hNC, hNL, hN0, hNS, hNIto⟩ :=
      ginibreBrownianMaximalProcess_local_center_CIR_integral_exists
    hn α z hz B P hB hind R hR T e
  have hCF (s : ℝ≥0) (ω : Ω) : CollisionFree (X s ω) :=
    (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B R hR T s ω).1
  exact ginibreBoundedField_substitution_integral_until B P hB hind a u ha hu hunit C hC.le
    hbound T (fun i => by
      filter_upwards [huc] with ω hω
      exact ((hac ω).mul ((PiLp.continuous_apply 2 (fun _ : Fin n × Fin 2 => ℝ) i).comp
        hω)).continuousOn)
    β hβL (fun J _ t _ hJS => brownianUnitIntegral_bounded_substitution_of_horizon_limits B P hB
      hind u hu hunit huc a (fun r => (ha r).measurable) C hC.le hbound t
      (Eventually.of_forall (fun ω => (hac ω).continuousOn)) β hβL hβLim (J t) hJS)
    (ginibreBrownianHamiltonianBoundedStop n α z B R T)
    (fun ω => ginibreDrivenHamiltonianBoundedStop_le n α _ z R T)
    (fun t k ω => ∑ i, brownianUniformLeftSum (B i)
      (fun s ω => a s ω * ginibreCenterRadialDirection n e (X s ω) i) t (k + 1) ω)
    N hNC hNS (fun t _ k ω hts => by
      rw [← ginibreConfigurationBrownianGradientSum_centerSquared hn B α α.coe_nonneg X hCF e t k
        ω]
      exact (ginibreConfigurationBrownianGradientSum_centerSquared_full_direction hn α
        α.coe_nonneg z hz B R hR T e t k ω hts).symm)
    (fun t ω r => (ginibreCenterSquared n) (X t ω) - (ginibreCenterSquared n) z = r +
      ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
        ((1 : ℝ) - (ginibreCenterSquared n) (X s.toNNReal ω))) hNIto
end
end GinibrePoincare
