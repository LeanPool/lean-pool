/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Bounded operators are determined by original test pairings -/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open UniformSpace
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem completionOperator_eq_of_test_pairings
    (A B : Completion E →L[𝕜] Completion E)
    (h : ∀ x y : E, inner 𝕜 (x : Completion E) (A (y : Completion E)) =
      inner 𝕜 (x : Completion E) (B (y : Completion E))) : A = B := by
  have he (x y : Completion E) : inner 𝕜 x (A y) = inner 𝕜 x (B y) := by
    refine Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro u
    refine Completion.induction_on y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro v
    exact h u v
  apply ContinuousLinearMap.ext
  intro y
  exact ext_inner_left 𝕜 (fun x => he x y)

theorem completionOperator_isSelfAdjoint_of_test_pairings
    (A : Completion E →L[𝕜] Completion E)
    (h : ∀ x y : E, inner 𝕜 (A (x : Completion E)) (y : Completion E) =
      inner 𝕜 (x : Completion E) (A (y : Completion E))) : IsSelfAdjoint A := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  refine Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  refine Completion.induction_on y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro v
  exact h u v

end VacuumBellSeparation.Gaussian
