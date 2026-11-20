/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Bounded operator-valued multipliers on `L²`

This module constructs quotient-level pointwise multiplication by an
operator-valued `L∞` symbol (`operatorMulL2`), with its almost-everywhere
representative formula and the sharp norm bound.

The construction is generic in the measure space and in the complex normed
source and target spaces.  It is used for the matrix-valued multipliers on the
transverse torus and on the three-torus.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

section Generic

variable {X E F G : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [BorelSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [SecondCountableTopologyEither X (E →L[ℂ] F)]
  [SecondCountableTopologyEither X (F →L[ℂ] G)]
  [SecondCountableTopologyEither X (E →L[ℂ] G)]

/-! ## Arbitrary essentially bounded operator-valued symbols -/

/-- Pointwise application of an `L∞` operator-valued symbol to an `L²` field. -/
def operatorMulL2 (mu : Measure X) :
    Lp (E →L[ℂ] F) ∞ mu →L[ℂ] Lp E 2 mu →L[ℂ] Lp F 2 mu :=
  (ContinuousLinearMap.apply ℂ F).flip.holderL mu ∞ 2 2

omit [TopologicalSpace X] [BorelSpace X]
  [SecondCountableTopologyEither X (E →L[ℂ] F)] in
/-- Almost-everywhere representative of pointwise operator application. -/
theorem operatorMulL2_coe_ae (mu : Measure X)
    (A : Lp (E →L[ℂ] F) ∞ mu) (f : Lp E 2 mu) :
    (operatorMulL2 mu A f : X → F) =ᵐ[mu] fun x ↦ A x (f x) := by
  exact ContinuousLinearMap.coeFn_holder _ _ _

/-- The flipped evaluation pairing `e ↦ (A ↦ A e)`, from `E` into `(E →L[ℂ] F) →L[ℂ] F`, has
operator norm at most one.  This is the constant appearing in the Hölder bound for
`operatorMulL2`, and is what makes pointwise application of an `L∞` symbol a contraction. -/
private theorem norm_operatorApply_flip_le :
    ‖((ContinuousLinearMap.apply ℂ F :
      E →L[ℂ] (E →L[ℂ] F) →L[ℂ] F).flip)‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_flip]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro e
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg e)
  intro A
  simpa [mul_comm] using A.le_opNorm e

omit [TopologicalSpace X] [BorelSpace X]
  [SecondCountableTopologyEither X (E →L[ℂ] F)] in
/-- Hölder's sharp pointwise-application estimate. -/
theorem norm_operatorMulL2_apply_apply_le (mu : Measure X)
    (A : Lp (E →L[ℂ] F) ∞ mu) (f : Lp E 2 mu) :
    ‖operatorMulL2 mu A f‖ ≤ ‖A‖ * ‖f‖ := by
  calc
    ‖operatorMulL2 mu A f‖ ≤
        ‖(ContinuousLinearMap.apply ℂ F : E →L[ℂ] (E →L[ℂ] F) →L[ℂ] F).flip‖ * ‖A‖ * ‖f‖ :=
      ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
    _ ≤ 1 * ‖A‖ * ‖f‖ := by
      gcongr
      exact norm_operatorApply_flip_le
    _ = ‖A‖ * ‖f‖ := by simp

end Generic

end

end FastDynamo
