/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticWeakSymmetry.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticWeakCore

/-!
# Ginibre transition analytic weak symmetry

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreTransitionAnalytic_resolvent_from_core_distributional`.
-/

@[expose] public section

namespace GinibrePoincare
noncomputable section

/-- The genuine unique distributional gradient inherits symmetry from the
actual symmetric L² value. No gradient symmetry assumption is needed. -/
theorem ginibreFullSymmetricValue_distributional_pair_symmetric {n : ℕ} (hn : 0 < n)
    (u : ginibreFullSymmetricValues n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u.val g) :
    IsGinibreSymmetricWeakPair (u.val, g) := by
  intro σ
  refine ⟨u.property σ,?_⟩
  have hp := ginibreDistributionalGradient_permute hn σ u.val g hu
  rw [u.property σ] at hp
  exact ginibre_distributional_gradient_unique n hn u.val _ g hp hu

/-- A genuine full distributional resolvent with the literal compact-core
equation is the analytic resolvent; its weak-pair symmetry is derived. -/
theorem ginibreTransitionAnalytic_resolvent_from_core_distributional {n : ℕ} (hn : 0 < n)
    (f u : ginibreFullSymmetricValues n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u.val g)
    (heq : ∀ (φ : Configuration n → ℝ) (hφ : IsTheoremOneNineCore φ),
      inner ℝ u.val (ginibreFullCoreValue hn φ hφ) +
        (1 / (n : ℝ)) * inner ℝ g (ginibreFullCoreGradient hn φ hφ) =
          inner ℝ f.val (ginibreFullCoreValue hn φ hφ)) :
    ginibreFullSymmetricResolvent n hn f=u :=
  ginibreTransitionAnalyticWeakCore_resolvent hn f u g hu
    (ginibreFullSymmetricValue_distributional_pair_symmetric hn u g hu) heq

end
end GinibrePoincare
