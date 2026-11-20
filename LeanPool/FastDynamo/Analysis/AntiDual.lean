/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The complex anti-dual of a Hilbert space

For a complex Hilbert space `E`, the anti-dual used in the paper is the
space `E →L⋆[ℂ] ℂ` of continuous conjugate-linear functionals.  Mathlib's
Fréchet--Riesz equivalence is stated for the linear dual.  This file supplies
the conjugate-linear counterpart and proves its norm and evaluation formulas
without adding an axiom.

With Mathlib's convention (the inner product is conjugate-linear in its first
argument), the representing functional associated to `x` is
`y ↦ inner ℂ y x`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Conjugating the value of a continuous conjugate-linear functional gives a
continuous linear functional. -/
def complexAntiDualConj (f : E →L⋆[ℂ] ℂ) : E →L[ℂ] ℂ :=
  ({
    toFun := fun x => starRingEnd ℂ (f x)
    map_add' := by
      intro x y
      simp
    map_smul' := by
      intro c x
      simp
  } : E →ₗ[ℂ] ℂ).mkContinuous ‖f‖ (fun x => by
    simpa using f.le_opNorm x)

/-- Evaluation formula for the conjugation map on the anti-dual: `complexAntiDualConj f`
sends `x` to the complex conjugate of `f x`. -/
@[simp] theorem complexAntiDualConj_apply (f : E →L⋆[ℂ] ℂ) (x : E) :
    complexAntiDualConj f x = starRingEnd ℂ (f x) :=
  rfl

/-- Conjugating the values preserves the operator norm. -/
theorem norm_complexAntiDualConj (f : E →L⋆[ℂ] ℂ) :
    ‖complexAntiDualConj f‖ = ‖f‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
    intro x
    simpa using f.le_opNorm x
  · apply ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (complexAntiDualConj f))
    intro x
    simpa using (complexAntiDualConj f).le_opNorm x

/-- Conjugating the flipped inner-product functional recovers Mathlib's
ordinary inner-product functional. -/
theorem complexAntiDualConj_innerSLFlip (x : E) :
    complexAntiDualConj ((innerSLFlip ℂ) x) = (innerSL ℂ) x := by
  ext y
  simp [complexAntiDualConj_apply, innerSLFlip_apply_apply,
    innerSL_apply_apply]

/-- The flipped inner-product map is an isometry into the complex anti-dual. -/
theorem norm_innerSLFlip_apply (x : E) :
    ‖(innerSLFlip ℂ) x‖ = ‖x‖ := by
  rw [← norm_complexAntiDualConj]
  rw [complexAntiDualConj_innerSLFlip]
  exact innerSL_apply_norm ℂ x

/-- Complex Fréchet--Riesz representation for anti-linear functionals: every
continuous conjugate-linear functional is `y ↦ inner ℂ y x`. -/
theorem innerSLFlip_surjective [CompleteSpace E] :
    Function.Surjective (innerSLFlip ℂ : E → E →L⋆[ℂ] ℂ) := by
  intro f
  obtain ⟨x, hx⟩ := (InnerProductSpace.toDual ℂ E).surjective
    (complexAntiDualConj f)
  refine ⟨x, ?_⟩
  ext y
  have hy := congrArg (fun g : E →L[ℂ] ℂ => g y) hx
  simpa [complexAntiDualConj_apply] using congrArg (starRingEnd ℂ) hy

/-- The complex Fréchet--Riesz linear isometric equivalence with the
anti-dual. -/
def complexToAntiDual [CompleteSpace E] :
    E ≃ₗᵢ[ℂ] (E →L⋆[ℂ] ℂ) :=
  LinearIsometryEquiv.ofSurjective
    ({
      toLinearMap := (innerSLFlip ℂ).toLinearMap
      norm_map' := norm_innerSLFlip_apply
    } : E →ₗᵢ[ℂ] (E →L⋆[ℂ] ℂ))
    innerSLFlip_surjective

/-- Exact evaluation formula for the anti-dual Riesz equivalence. -/
@[simp] theorem complexToAntiDual_apply_apply [CompleteSpace E] (x y : E) :
    (complexToAntiDual x) y = inner ℂ y x := by
  change ((innerSLFlip ℂ) x) y = inner ℂ y x
  exact innerSLFlip_apply_apply ℂ x y

end

end FastDynamo
