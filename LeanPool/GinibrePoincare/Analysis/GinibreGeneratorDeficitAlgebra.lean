/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreGeneratorDeficitAlgebra.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorVariational
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakVariational
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorHermiteLowering
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreIdentification
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConstants
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroup
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-! # Generator deficit algebra independent of the Hermite deficit

The Γ₂ deficit reduces to twice the Poincaré deficit plus the squared shifted
generator. This identity uses only the actual weak generator pairing.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The generator identity used in the second part of Section 6, before choosing
any proof of the first deficit. The gradient is obtained from actual graph membership. -/
theorem ginibreGenerator_second_deficit_algebra {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val, g) ∧
      ‖v.val‖^2 - 2*ginibreWeakEnergy n g =
        ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖^2 +
          2*(ginibreWeakEnergy n g - 2*ginibreL2Variance n hn u.val) := by
  obtain ⟨g, hu, hs, hpair⟩ := (ginibreFullGenerator_real_graph_iff_exists_gradient hn u v).mp
      hgraph
  obtain ⟨huc, hsc⟩ := ginibreFullCenter_weak_pair hn u.val g hu hs
  have he : ginibreWeakEnergy n g = -inner ℝ v.val (ginibreFullCenter n hn u.val) := by
    simpa only [ginibreWeakEnergy, real_inner_self_eq_norm_sq] using
      hpair (ginibreFullCenter n hn u.val) g huc hsc
  refine ⟨g, hu, hs,?_⟩
  rw [norm_add_sq_real, norm_smul, real_inner_smul_right]
  norm_num
  rw [mul_pow, ginibreFullCenter_variance]
  nlinarith [he]

end
end GinibrePoincare
