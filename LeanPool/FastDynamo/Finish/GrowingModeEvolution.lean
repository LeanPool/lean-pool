/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Finish.RealSolution

/-!
# The norm law of an explicit eigen-trajectory

An eigenpair `(λ, b)` of a bundled-domain operator gives the explicit strong solution
`t ↦ e^{tλ} b` (`DomainOperator.eigenTrajectory`, `Operator/Evolution.lean`),
independently of semigroup generation.  This file records that it starts at its eigenvector
(`eigenTrajectory_zero`) and the exact ambient norm law `‖e^{tλ} b‖ = e^{t Re λ} ‖b‖`
(`norm_embedding_eigenTrajectory`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter

namespace DomainOperator

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- The explicit eigen-trajectory starts at its eigenvector. -/
@[simp] theorem eigenTrajectory_zero
    (A : DomainOperator X D) (eigenvalue : ℂ) (B : D) :
    A.eigenTrajectory eigenvalue B 0 = B := by
  simp [eigenTrajectory]

/-- Exact exponential norm law for the ambient state of a complex
eigen-trajectory. -/
theorem norm_embedding_eigenTrajectory
    (A : DomainOperator X D) (eigenvalue : ℂ) (B : D) (t : ℝ) :
    ‖A.embedding (A.eigenTrajectory eigenvalue B t)‖ =
      Real.exp (t * eigenvalue.re) * ‖A.embedding B‖ := by
  rw [eigenTrajectory, map_smul, norm_smul, Complex.norm_exp]
  congr 2
  simp

end DomainOperator

end

end FastDynamo
