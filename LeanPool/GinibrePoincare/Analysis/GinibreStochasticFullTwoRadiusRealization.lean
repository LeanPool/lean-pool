/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticFullTwoRadiusRealization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroDriverIndependence
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroSpeed
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroCIRDrivenLocal
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterSquaredDrivenLocal
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCIRDrivenLocal

/-! # Independent CIR drivers for the two radii

The two observables are `ginibreCenterSquared` and `pairwiseRadius`. Their
CIR drift shapes are respectively `1` and `recenteredGammaShape n`; both use
the same speed factor `4 * α / n`. Independence in the conclusion concerns
the entire scalar Brownian driver processes.

The proof first separates zero speed, where the observables are constant.
For positive speed it constructs the unrestricted center driver and the
relative radial driver, proves their independence, and realizes each local
integral. The center integral has separate branches for zero and positive
initial center, since normalization of its radial direction at zero requires
a different argument. Intersecting the two full-measure Itô events yields
both equations with the same Hamiltonian stopping time and time cap.
The sum-convergence clauses specify the integrals by mean-square limits. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_full_two_radius_independent_CIR_realization
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
    ∃ βS βR : ℝ≥0 → Ω → ℝ,
      IsBrownianReal βS P ∧ IsBrownianReal βR P ∧
      IndepFun (fun ω t => βS t ω) (fun ω t => βR t ω) P ∧
      ∀ (R : ℝ), ginibreHamiltonian n z ≤ R → ∀ (T : ℝ≥0),
        let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
        let aS := fun t ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*ginibreCenterSquared n (X t ω))
        let aR := fun t ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*pairwiseRadius (X t ω))
        ∃ JS JR : ℝ≥0 → Ω → ℝ,
          Martingale JS F P ∧ Martingale JR F P ∧
          (∀ ω, Continuous (fun t => JS t ω)) ∧ (∀ ω, Continuous (fun t => JR t ω)) ∧
          (∀ t ≤ T, Tendsto (fun k => ∫ ω,
            (brownianUniformLeftSum βS aS t (k+1) ω-JS t ω)^2 ∂P) atTop (𝓝 0)) ∧
          (∀ t ≤ T, Tendsto (fun k => ∫ ω,
            (brownianUniformLeftSum βR aR t (k+1) ω-JR t ω)^2 ∂P) atTop (𝓝 0)) ∧
          ∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
            (ginibreCenterSquared n (X t ω)-ginibreCenterSquared n z = JS t ω+
              ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*(1-ginibreCenterSquared n (X s.toNNReal ω))) ∧
            (pairwiseRadius (X t ω)-pairwiseRadius z = JR t ω+
              ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
                ((recenteredGammaShape n : ℝ)-pairwiseRadius (X s.toNNReal ω))) := by
  classical
  -- At zero speed the two observables are constant, so treat this case directly.
  by_cases hα0 : α=0
  · subst α
    simpa only [NNReal.coe_zero] using ginibreBrownian_zero_speed_two_radius_CIR_realization
      (by omega) z hz B P hB hind
  have hα : 0 < α := lt_of_le_of_ne bot_le (Ne.symm hα0)
  let i₀ : Fin n × Fin 2 := (⟨0, by omega⟩, 0)
  let e : EuclideanSpace ℝ (Fin n × Fin 2) := EuclideanSpace.single i₀ 1
  have he : ‖e‖=1 := by simp [e, PiLp.norm_single]
  obtain ⟨βS, hβS, hβSM, hβSL, hβS0, hβSLim, hβSShift, hβSFresh⟩ :=
    ginibreBrownianMaximalProcess_center_unrestricted_Brownian_exists hn α hα z hz B P hB hind
  obtain ⟨βR, hβR, hβRM, hβRL, hβR0, hβRLim, hβRShift, hβRFresh⟩ :=
    ginibreBrownianMaximalProcess_radial_Brownian_exists hn α z hz B P hB hind
  refine ⟨βS, βR, hβS, hβR, ?_, ?_⟩
  · exact ginibreBrownian_unrestricted_center_radial_drivers_independent hn α hα z hz
      B P hB hind e e βS βR hβS.cont hβS0 hβSShift hβR.cont hβRLim
  · intro R hR T
    -- The zero-center branch requires the unrestricted center construction.
    have hcenterIntegral := if hcenter : ginibreCenterSquared n z=0 then
      ginibreBrownianMaximalProcess_zero_center_CIR_Brownian_integral hn α hα z hz hcenter
        B P hB hind e he βS hβSM hβSL hβSLim R hR T else
      ginibreBrownianMaximalProcess_local_center_CIR_Brownian_integral hn α z hz
        (lt_of_le_of_ne (ginibreCenterSquared_nonneg n z) (Ne.symm hcenter))
        B P hB hind e he βS hβSL hβSLim R hR T
    obtain ⟨JS, hJSM, hJSC, hJSL, hJS0, hJSMS, hJSLim, hSIto⟩ := hcenterIntegral
    obtain ⟨JR, hJRM, hJRC, hJRL, hJR0, hJRMS, hJRLim, hRIto⟩ :=
      ginibreBrownianMaximalProcess_local_CIR_Brownian_integral hn α z hz B P hB hind
        e he βR hβRL hβRLim R hR T
    refine ⟨JS, JR, hJSM, hJRM, hJSC, hJRC, hJSMS, hJRMS, ?_⟩
    filter_upwards [hSIto, hRIto] with ω hs hr
    exact fun t ht => ⟨hs t ht, hr t ht⟩

end
end GinibrePoincare
