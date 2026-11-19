/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorFriedrichsSquareRootRange.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorComplex
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
/-!
# Correspondence operator Friedrichs square root range

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceSquareRoot_adjoint_range`,
`correspondenceFriedrichsResolventSqrt_selfAdjoint`,
`correspondenceFriedrichsResolventSqrt_injective`,
`correspondenceFriedrichsResolventSqrt_denseRange`.
-/

@[expose] public section
open Set
namespace GinibrePoincare
noncomputable section

/-- The range theorem needed for the closed-form square-root representation.
It follows from extending the literal norm-preserving map on a dense range. -/
theorem correspondenceSquareRoot_adjoint_range
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (A : H →L[ℝ] K) (B : H →L[ℝ] H) (hB : B.adjoint = B)
    (hd : DenseRange B) (hn : ∀ x, ‖A x‖ = ‖B x‖) :
    range A.adjoint=range B := by
  let U := A.toLinearMap.extendOfIsometry (e:=B.toLinearMap) hd hn
  have he : A=U.toContinuousLinearMap.comp B := by
    ext x
    exact (LinearMap.extendOfIsometry_eq A.toLinearMap hd hn x).symm
  have hadj : A.adjoint=B.comp U.toContinuousLinearMap.adjoint := by
    rw [he, ContinuousLinearMap.adjoint_comp, hB]
  rw [hadj]
  apply Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨U.toContinuousLinearMap.adjoint x, rfl⟩
  · rintro y ⟨x, rfl⟩
    refine ⟨U x,?_⟩
    have h:=congrArg (fun L : H→L[ℝ]H=>L x) U.adjoint_comp_self
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, one_apply_eq_self,
        LinearIsometry.coe_toContinuousLinearMap] using congrArg B h

/-- The real continuous functional calculus on bounded operators of the full complex `L²`
space. The `ℝ`-module structure of `Lp` agrees with the restriction of scalars from `ℂ` only
after unfolding, so the generic C⋆-algebra instance is stated here at the concrete type. -/
instance ginibreFullComplexL2_realContinuousFunctionalCalculus (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ
      (GinibreFullComplexL2 n →L[ℂ] GinibreFullComplexL2 n) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

/-- The bounded functional-calculus square root of the actual resolvent. -/
def correspondenceFriedrichsResolventSqrt (n : ℕ) (hn : 0 < n) :
    GinibreFullComplexL2 n →L[ℂ] GinibreFullComplexL2 n :=
  CFC.sqrt (correspondenceOperatorComplexResolvent n hn)

theorem correspondenceFriedrichsResolventSqrt_square (n : ℕ) (hn : 0 < n) :
    correspondenceFriedrichsResolventSqrt n hn * correspondenceFriedrichsResolventSqrt n hn =
      correspondenceOperatorComplexResolvent n hn :=
  CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (correspondenceOperatorComplexResolvent_isPositive n hn))

theorem correspondenceFriedrichsResolventSqrt_selfAdjoint (n : ℕ) (hn : 0 < n) :
    IsSelfAdjoint (correspondenceFriedrichsResolventSqrt n hn) :=
  (CFC.sqrt_nonneg (correspondenceOperatorComplexResolvent n hn)).isSelfAdjoint

theorem correspondenceFriedrichsResolventSqrt_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (correspondenceFriedrichsResolventSqrt n hn) := by
  intro x y h
  apply correspondenceOperatorComplexResolvent_injective n hn
  have he := congrArg (correspondenceFriedrichsResolventSqrt n hn) h
  simpa only [← mul_apply_eq_comp, correspondenceFriedrichsResolventSqrt_square] using he

theorem correspondenceFriedrichsResolventSqrt_denseRange (n : ℕ) (hn : 0 < n) :
    DenseRange (correspondenceFriedrichsResolventSqrt n hn) := by
  apply (correspondenceOperatorComplexResolvent_denseRange n hn).mono
  rintro y ⟨x, rfl⟩
  refine ⟨correspondenceFriedrichsResolventSqrt n hn x, ?_⟩
  exact congrArg (fun L : GinibreFullComplexL2 n →L[ℂ] GinibreFullComplexL2 n => L x)
    (correspondenceFriedrichsResolventSqrt_square n hn)

end
end GinibrePoincare
