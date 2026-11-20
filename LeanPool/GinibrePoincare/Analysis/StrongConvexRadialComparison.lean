/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexRadialComparison.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexGaussianComparison
public import LeanPool.GinibrePoincare.Analysis.StrongConvexRadialProfile
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticRadialBochner

/-!
# Strong convex radial comparison

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `rhoConvex_radial_profile_dominates_gaussian`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem rhoConvex_radial_profile_dominates_gaussian (n k : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    let Q := fun r : ℝ => V (r : ℂ)
    let hi := rhoConvexPotential_radial_density_integrable n k hn ρ hρ hV hrot hc
    let p := radialConfinementProbabilityDensity n k Q
    let hQ := hV.continuous.comp Complex.continuous_ofReal
    let hm := (radialConfinementProbabilityDensity_CDF_strictMono n k Q hQ hi).mono
        Ioi_subset_Ici_self
    let hr := radialConfinementProbabilityDensity_CDF_image n k Q hQ hi
    ∀ u ∈ Icc 0 1, Real.sqrt ((n : ℝ) * ρ) * standardGaussianDensityProfile u ≤
      densityQuantileProfile (densityCDF p) p (Ioi 0) hm hr u := by
  dsimp only
  let Q := fun r : ℝ => V (r : ℂ)
  have hQ : ContDiff ℝ 2 Q := hV.comp Complex.ofRealCLM.contDiff
  have hi := rhoConvexPotential_radial_density_integrable n k hn ρ hρ hV hrot hc
  let p := radialConfinementProbabilityDensity n k Q
  let F := densityCDF p
  let hm := (radialConfinementProbabilityDensity_CDF_strictMono n k Q hQ.continuous hi).mono
      Ioi_subset_Ici_self
  let hr := radialConfinementProbabilityDensity_CDF_image n k Q hQ.continuous hi
  let H := densityQuantileProfile F p (Ioi 0) hm hr
  have hp : ∀ r ∈ Ioi (0 : ℝ), 0 < p r := fun r hr =>
    radialConfinementProbabilityDensity_pos n k Q hi hr
  have hF : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt F (p r) r := fun r _ =>
    densityCDF_hasDerivAt p (radialConfinementProbabilityDensity_continuous n k hQ.continuous)
      (hi.div_const _) r
  have hHpos (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : 0 < H u := by
    simp only [H, densityQuantileProfile, ite_eq_left hu]
    exact hp _ (increasingCDFQuantileOn_mem F (Ioi 0) hm hr u hu)
  apply density_profile_dominates_gaussian H ((n : ℝ) * ρ) (mul_pos (by exact_mod_cast hn) hρ)
  · apply radialConfinementProbabilityDensity_profile_continuousOn n k hn Q hQ.continuous hi
      (ρ / 2) (V 0) (by positivity)
    intro r hr
    simpa only [Q, Complex.normSq_ofReal, pow_two] using
      rhoConvexPotential_quadratic_lower_bound ρ hrot hc (r : ℂ)
  · simp [H, densityQuantileProfile]
  · simp [H, densityQuantileProfile]
  · intro u hu
    apply densityQuantileProfile_contDiffAt_two F p (Ioi 0) hm hr hF
      (fun r hr => (hp r hr).ne') _ u hu
    intro r hr
    exact (radialConfinementProbabilityDensity_contDiffAt n k hQ hr).contDiffWithinAt
  · exact hHpos
  · intro u hu
    let q := increasingCDFQuantileOn F (Ioi 0) hm hr
    have hq : 0 < q u := increasingCDFQuantileOn_mem F (Ioi 0) hm hr u hu
    have he := densityQuantileProfile_second_derivative F p
      (radialEffectivePotential n (k + 1) Q) (Ioi 0) hm hr hF
      (fun r hr => (hp r hr).ne')
      (fun r hr => radialConfinementProbabilityDensity_hasDerivAt n k Q
        (hQ.differentiable (by norm_num)) hr)
      (fun r hr => contDiffAt_radialEffectivePotential n (k + 1) hV r hr) u hu
    change deriv (deriv H) u = _ at he
    rw [he]
    have hb := rhoConvexPotential_radial_curvature n (k + 1) (by omega) ρ hV hc (q u) hq
    exact div_le_div_of_nonneg_right (neg_le_neg hb) (hHpos u hu).le

end
end GinibrePoincare
