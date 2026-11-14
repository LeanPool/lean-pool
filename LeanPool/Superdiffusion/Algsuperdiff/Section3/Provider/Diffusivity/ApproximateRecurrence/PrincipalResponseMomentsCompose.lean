/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseMomentsFourth
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseLegsBudget

/-!
# PrincipalResponseMomentsCompose

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: sub-step (iv) of the principal response, composing the two moments

This module supplies the interface between the two moment displays and the
Hoelder/budget chain of `PrincipalResponseLegsHolder` and
`PrincipalResponseLegsBudget`.  Nothing new is estimated: what is supplied is
the **pointwise domination** `X <= B . V^2` in the exact shape the chain
consumes, with `B` the operator norm and `V` the normalized load length.

## Main results

* `sq_sqrt_annealedSqrtNormSq` -- the square undoes the square root of the
  Hoelder split.
* `blockVecDot_coarseBlockMatrix_le_operatorEnvelope` -- the pointwise
  domination itself.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Observable
open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-! ## The load length -/

/-- `| bfAhom^{1/2} P |` squared is `| bfAhom^{1/2} P |^2`: the square root taken
is undone by the square of the Hoelder split. -/
theorem sq_sqrt_annealedSqrtNormSq (sigma : PositiveScalar) (Y : BlockVec d) :
    Real.sqrt (annealedSqrtNormSq sigma Y) ^ (2 : ℕ) =
      annealedSqrtNormSq sigma Y :=
  Real.sq_sqrt (annealedSqrtNormSq_nonneg sigma Y)

/-- **The pointwise domination, in the shape the Hoelder split consumes.**  With

* `V := | bfAhom^{1/2} Y |`, the normalized load length,

the energy `Y . bfA(R; a) Y` obeys `X <= B . V^2`. -/
theorem blockVecDot_coarseBlockMatrix_le_operatorEnvelope [NeZero d]
    (sigma : PositiveScalar) (R : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) {s : ℝ} {q : Ch02.MultiscaleExponent}
    (hs : 0 < s) (hq : q.IsAdmissible) (Y : BlockVec d) :
    blockVecDot Y
        (blockMatVecMul
          (Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (a.coeffOn R)) Y) ≤
      2 * ((sigma : ℝ)⁻¹ * Ch02.LambdaSq R s q a +
          (sigma : ℝ) * (Ch02.lambdaSq R s q a)⁻¹) *
        Real.sqrt (annealedSqrtNormSq sigma Y) ^ (2 : ℕ) := by
  rw [sq_sqrt_annealedSqrtNormSq, annealedSqrtNormSq]
  exact blockVecDot_coarseBlockMatrix_le_weightedMultiscaleEllipticity sigma R a
    hs hq Y

section Compose

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}

end Compose

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
