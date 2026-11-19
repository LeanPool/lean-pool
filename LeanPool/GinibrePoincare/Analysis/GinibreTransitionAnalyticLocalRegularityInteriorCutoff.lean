/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityInteriorCutoff.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCompactTests
public import LeanPool.GinibrePoincare.Analysis.GinibreInteriorWeakGradient
public import LeanPool.GinibrePoincare.Analysis.GaussianFourierCoordinates
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalClosure
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Ginibre transition analytic local regularity interior cutoff

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_exists_compact_interior_cutoff`.
-/

@[expose] public section
open Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Every genuine compact collision-free domain admits a compact smooth cutoff
which is identically one on a neighborhood of that domain. -/
theorem ginibreLocalRegularity_exists_compact_interior_cutoff
    (n : ℕ) (hn : 0 < n) (K : Set (Configuration n)) (hK : IsCompact K)
    (hs : K ⊆ {z | CollisionFree z}) :
    ∃ η : Configuration n → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ {z | CollisionFree z} ∧ ∀ z ∈ K, η =ᶠ[𝓝 z] 1 := by
  let e := configurationEuclideanEquiv n
  obtain ⟨χ₀, hχ₀, hχ₀c, hχ₀one⟩ := ginibreLocalRegularity_exists_compact_cutoff (e '' K) (hK.image
      e.continuous)
  let χ := χ₀ ∘ e
  have hχ : ContDiff ℝ ∞ χ := hχ₀.comp e.contDiff
  have hχc : HasCompactSupport χ := hχ₀c.comp_homeomorph e.toHomeomorph
  have hχone (z) (hz : z ∈ K) : χ =ᶠ[𝓝 z] 1 :=
    (hχ₀one (e z) ⟨z, hz, rfl⟩).comp_tendsto e.continuous.continuousAt
  obtain ⟨ψ, hψ, hψs, hψone⟩ := exists_ginibreInteriorCutoff n hn K hK hs
  refine ⟨χ*ψ, hχ.mul hψ, hχc.mul_right, tsupport_mul_subset_right.trans hψs,?_⟩
  intro z hz
  filter_upwards [hχone z hz, hψone z hz] with x hx hy
  simp [hx, hy]

end
end GinibrePoincare
