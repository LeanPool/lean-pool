/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexRadialCDF.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexRadialDensity
public import LeanPool.GinibrePoincare.Analysis.StrongConvexCDF

/-!
# Strong convex radial CDF

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `radialConfinementProbabilityDensity_CDF_image`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem radialConfinementProbabilityDensity_CDF_zero (n k : ℕ) (Q : ℝ → ℝ) :
    densityCDF (radialConfinementProbabilityDensity n k Q) 0 = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Iic] with r hr
  exact div_eq_zero_iff.mpr (Or.inl (radialConfinementDensity_zero n k Q hr))

theorem radialConfinementProbabilityDensity_CDF_strictMono (n k : ℕ)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hi : Integrable (radialConfinementDensity n k Q) volume) :
    StrictMonoOn (densityCDF (radialConfinementProbabilityDensity n k Q)) (Ici 0) := by
  have hp := radialConfinementProbabilityDensity_continuous n k hQ
  have hpi : Integrable (radialConfinementProbabilityDensity n k Q) volume := hi.div_const _
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (densityCDF_continuous _ hp hpi).continuousOn
  intro x hx
  have hxpos : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  rw [(densityCDF_hasDerivAt _ hp hpi x).deriv]
  exact radialConfinementProbabilityDensity_pos n k Q hi hxpos

theorem radialConfinementProbabilityDensity_CDF_image (n k : ℕ)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hi : Integrable (radialConfinementDensity n k Q) volume) :
    densityCDF (radialConfinementProbabilityDensity n k Q) '' Ioi 0 = Ioo 0 1 := by
  let p := radialConfinementProbabilityDensity n k Q
  let μ := (volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal (p r))
  let : IsProbabilityMeasure μ := radialConfinementProbabilityDensity_isProbability n k Q hQ hi
  have hp : Continuous p := radialConfinementProbabilityDensity_continuous n k hQ
  have hpi : Integrable p volume := hi.div_const _
  have he : cdf μ = densityCDF p := funext fun x =>
    cdf_withDensity_eq_densityCDF p hp.measurable
      (radialConfinementProbabilityDensity_nonneg n k Q hi) x
  apply strictly_increasing_CDF_image_Ioi _ 0
    (densityCDF_continuous p hp hpi).continuousOn
    (radialConfinementProbabilityDensity_CDF_strictMono n k Q hQ hi)
    (radialConfinementProbabilityDensity_CDF_zero n k Q)
  · intro x
    rw [← he]
    exact cdf_le_one μ x
  · rw [← he]
    exact tendsto_cdf_atTop μ

end
end GinibrePoincare
