/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexGaussianComparison.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexGaussianProfile
public import LeanPool.GinibrePoincare.Analysis.StrongConvexDensityComparison

/-!
# Strong convex Gaussian comparison

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `density_profile_dominates_gaussian`.
-/

@[expose] public section

open Set
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem density_profile_dominates_gaussian (h : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hc : ContinuousOn h (Icc 0 1)) (h0 : 0 ≤ h 0) (h1 : 0 ≤ h 1)
    (hd : ∀ u ∈ Ioo 0 1, ContDiffAt ℝ 2 h u)
    (hp : ∀ u ∈ Ioo 0 1, 0 < h u)
    (hdd : ∀ u ∈ Ioo 0 1, deriv (deriv h) u ≤ -κ / h u) :
    ∀ u ∈ Icc 0 1, Real.sqrt κ * standardGaussianDensityProfile u ≤ h u := by
  let j := fun u => Real.sqrt κ * standardGaussianDensityProfile u
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  apply positive_density_profile_comparison h j 0 1 κ (by norm_num) hκ hc
    (standardGaussianDensityProfile_continuousOn.const_mul _)
  · simpa [j, standardGaussianDensityProfile, densityQuantileProfile] using h0
  · simpa [j, standardGaussianDensityProfile, densityQuantileProfile] using h1
  · exact hd
  · intro u hu
    exact contDiffAt_const.mul (standardGaussianDensityProfile_contDiffAt u hu)
  · exact hp
  · intro u hu
    exact mul_pos hs (standardGaussianDensityProfile_pos u hu)
  · exact hdd
  · intro u hu
    have he : deriv (deriv j) u = Real.sqrt κ *
        deriv (deriv standardGaussianDensityProfile) u := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        (iteratedDeriv_const_mul (n := 2) (Real.sqrt κ)
          (standardGaussianDensityProfile_contDiffAt u hu))
    rw [he, standardGaussianDensityProfile_second_derivative u hu]
    have hi := (standardGaussianDensityProfile_pos u hu).ne'
    have hs2 := Real.sq_sqrt hκ.le
    dsimp [j]
    field_simp
    nlinarith

end
end GinibrePoincare
