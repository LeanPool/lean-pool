/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.NormNum

/-!
# Liouville's inequality for algebraic integers

For a nonzero algebraic integer `β` of a number field `K` and any embedding `σ : K →+* ℂ`,

  `1 ≤ ‖σ β‖ * house β ^ ([K : ℚ] - 1)`.

This is the arithmetic lower bound used in every transcendence proof: a nonzero algebraic
integer cannot be too small at one place if it is not too large at all the others.
-/

@[expose] public section

namespace LeanPool

open NumberField

namespace StrongSix

variable {K : Type*} [Field K] [NumberField K]

theorem one_le_norm_algebraNorm_of_integral {β : K} (hβ : IsIntegral ℤ β) (hβ0 : β ≠ 0) :
    1 ≤ ‖Algebra.norm ℚ β‖ := by
  let b : 𝓞 K := ⟨β, hβ⟩
  have hb0 : b ≠ 0 := fun h => hβ0 (congrArg Subtype.val h)
  have hn : Algebra.norm ℤ b ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb0
  have hcast : ((Algebra.norm ℤ b : ℤ) : ℚ) = Algebra.norm ℚ β := Algebra.coe_norm_int b
  rw [← hcast, Int.norm_cast_rat, Int.norm_eq_abs]
  exact_mod_cast Int.one_le_abs hn

/-- **Liouville's inequality.** -/
theorem one_le_norm_mul_house_pow {β : K} (hβ : IsIntegral ℤ β) (hβ0 : β ≠ 0) (σ : K →+* ℂ) :
    1 ≤ ‖σ β‖ * house β ^ (Module.finrank ℚ K - 1) :=
  (one_le_norm_algebraNorm_of_integral hβ hβ0).trans (norm_norm_le_norm_mul_house_pow β σ)

end StrongSix

end LeanPool
