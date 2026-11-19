/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexRadialProfile.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexQuantileEndpoints
public import LeanPool.GinibrePoincare.Analysis.StrongConvexQuantileCalculus
public import LeanPool.GinibrePoincare.Analysis.StrongConvexRadialCDF
public import Mathlib.Topology.ExtendFrom

/-!
# Strong convex radial profile

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `radialConfinementProbabilityDensity_profile_continuousOn`.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Actual quantile density profiles extend continuously by zero at both
probability endpoints when the density vanishes at its support endpoints. -/
theorem positive_densityQuantileProfile_continuousOn (F p : ℝ → ℝ)
    (hm : StrictMonoOn F (Ici 0)) (hF0 : F 0 = 0)
    (hr : F '' Ioi 0 = Ioo 0 1) (hp : Continuous p) (hp0 : p 0 = 0)
    (htop : Tendsto p atTop (𝓝 0)) :
    ContinuousOn (densityQuantileProfile F p (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr)
      (Icc 0 1) := by
  let q := increasingCDFQuantileOn F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr
  let f := p ∘ q
  have hleft : Tendsto f (𝓝[Ioo 0 1] 0) (𝓝 0) := by
    simpa only [hp0] using hp.continuousAt.tendsto.comp
      (increasingCDFQuantileOn_tendsto_zero F hm hF0 hr)
  have hright : Tendsto f (𝓝[Ioo 0 1] 1) (𝓝 0) :=
    htop.comp (increasingCDFQuantileOn_tendsto_atTop F hm hr)
  have hcont : ContinuousOn f (Ioo 0 1) :=
    hp.comp_continuousOn (increasingCDFQuantileOn_continuousOn F (Ioi 0)
      (hm.mono Ioi_subset_Ici_self) hr)
  have hclosure : Icc (0 : ℝ) 1 ⊆ closure (Ioo 0 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hc : ContinuousOn (extendFrom (Ioo 0 1) f) (Icc 0 1) := by
    apply continuousOn_extendFrom hclosure
    intro x hx
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hx with (rfl | rfl | hx)
    · exact ⟨0, hleft⟩
    · exact ⟨0, hright⟩
    · exact ⟨f x, hcont x hx⟩
  apply hc.congr
  intro x hx
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hx with (rfl | rfl | hx)
  · rw [extendFrom_eq (hclosure (left_mem_Icc.mpr (by norm_num))) hleft]
    simp [densityQuantileProfile]
  · rw [extendFrom_eq (hclosure (right_mem_Icc.mpr (by norm_num))) hright]
    simp [densityQuantileProfile]
  · rw [extendFrom_extends hcont x hx]
    simp [densityQuantileProfile, hx, f, q]

theorem radialConfinementProbabilityDensity_profile_continuousOn
    (n k : ℕ) (hn : 0 < n) (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hi : MeasureTheory.Integrable (radialConfinementDensity n k Q) MeasureTheory.volume)
    (c C : ℝ) (hc : 0 < c) (hbound : ∀ r, 0 < r → c * r ^ 2 + C ≤ Q r) :
    ContinuousOn (densityQuantileProfile
      (densityCDF (radialConfinementProbabilityDensity n k Q))
      (radialConfinementProbabilityDensity n k Q) (Ioi 0)
      ((radialConfinementProbabilityDensity_CDF_strictMono n k Q hQ hi).mono Ioi_subset_Ici_self)
      (radialConfinementProbabilityDensity_CDF_image n k Q hQ hi)) (Icc 0 1) := by
  apply positive_densityQuantileProfile_continuousOn
    (densityCDF (radialConfinementProbabilityDensity n k Q))
    (radialConfinementProbabilityDensity n k Q)
    (radialConfinementProbabilityDensity_CDF_strictMono n k Q hQ hi)
    (radialConfinementProbabilityDensity_CDF_zero n k Q)
    (radialConfinementProbabilityDensity_CDF_image n k Q hQ hi)
    (radialConfinementProbabilityDensity_continuous n k hQ)
  · simp [radialConfinementProbabilityDensity, radialConfinementDensity]
  · change Tendsto (fun r => radialConfinementDensity n k Q r /
      ∫ t, radialConfinementDensity n k Q t) atTop (𝓝 0)
    simpa only [zero_div] using
      (radialConfinementDensity_tendsto_zero n k hn Q c C hc hbound).div_const
        (∫ t, radialConfinementDensity n k Q t)

end
end GinibrePoincare
