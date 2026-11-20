/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorFriedrichsSquareRootCalculus.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorFriedrichsSquareRootRange
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
/-!
# Correspondence operator Friedrichs square root calculus

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceFriedrichsComplementSqrt_selfAdjoint`,
`correspondenceFriedrichsSquareRoots_commute`, `correspondenceFriedrichsSquareRoots_sum_squares`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section

theorem correspondenceFriedrichs_one_sub_resolvent_nonneg (n : ℕ) (hn : 0 < n) :
    0 ≤ 1 - correspondenceOperatorComplexResolvent n hn := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    ((IsSelfAdjoint.one (GinibreFullComplexL2 n→L[ℂ]GinibreFullComplexL2 n)).sub
        (correspondenceOperatorComplexResolvent_isSelfAdjoint n hn)), ?_⟩
  intro x
  have h1 := RCLike.re_le_norm (inner ℂ (correspondenceOperatorComplexResolvent n hn x) x)
  have h2 := norm_inner_le_norm (𝕜:=ℂ) (correspondenceOperatorComplexResolvent n hn x) x
  have h3 := correspondenceOperatorComplexResolvent_norm_le n hn x
  change 0 ≤ RCLike.re (inner ℂ ((1 - correspondenceOperatorComplexResolvent n hn) x) x)
  rw [sub_apply, one_apply_eq_self, inner_sub_left, map_sub, inner_self_eq_norm_sq]
  nlinarith [norm_nonneg x, norm_nonneg (correspondenceOperatorComplexResolvent n hn x)]

/-- The square root `CFC.sqrt (1 - correspondenceOperatorComplexResolvent n hn)`. -/
def correspondenceFriedrichsComplementSqrt (n : ℕ) (hn : 0 < n) :
    GinibreFullComplexL2 n →L[ℂ] GinibreFullComplexL2 n :=
  CFC.sqrt (1 - correspondenceOperatorComplexResolvent n hn)

theorem correspondenceFriedrichsComplementSqrt_square (n : ℕ) (hn : 0 < n) :
    correspondenceFriedrichsComplementSqrt n hn * correspondenceFriedrichsComplementSqrt n hn =
      1 - correspondenceOperatorComplexResolvent n hn :=
  CFC.sqrt_mul_sqrt_self _ (correspondenceFriedrichs_one_sub_resolvent_nonneg n hn)

theorem correspondenceFriedrichsComplementSqrt_selfAdjoint (n : ℕ) (hn : 0 < n) :
    IsSelfAdjoint (correspondenceFriedrichsComplementSqrt n hn) :=
  (CFC.sqrt_nonneg (1 - correspondenceOperatorComplexResolvent n hn)).isSelfAdjoint

theorem correspondenceFriedrichsSquareRoots_commute (n : ℕ) (hn : 0 < n) :
    Commute (correspondenceFriedrichsResolventSqrt n hn)
      (correspondenceFriedrichsComplementSqrt n hn) := by
  have h : Commute (correspondenceOperatorComplexResolvent n hn)
      (1 - correspondenceOperatorComplexResolvent n hn) :=
    (Commute.one_right _).sub_right (Commute.refl _)
  have h1 := h.cfcₙ_nnreal NNReal.sqrt
  have h2 := h1.symm.cfcₙ_nnreal NNReal.sqrt
  exact h2.symm

theorem correspondenceFriedrichsSquareRoots_sum_squares (n : ℕ) (hn : 0 < n)
    (x : GinibreFullComplexL2 n) :
    correspondenceFriedrichsResolventSqrt n hn (correspondenceFriedrichsResolventSqrt n hn x)+
      correspondenceFriedrichsComplementSqrt n hn (correspondenceFriedrichsComplementSqrt n hn x)=x
          := by
  rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, correspondenceFriedrichsResolventSqrt_square,
    correspondenceFriedrichsComplementSqrt_square]
  simp

end
end GinibrePoincare
