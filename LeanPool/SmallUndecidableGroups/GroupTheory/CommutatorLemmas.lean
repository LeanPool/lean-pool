/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Commute.Basic

/-! Shared inverse-commutator criteria for the Borisov and host constructions. -/

@[expose] public section

namespace Undecidability.CommutatorLemmas

variable {G : Type*} [Group G]

/-- The inverse-convention commutator is trivial exactly when its entries commute. -/
theorem inverse_commutator_eq_one_iff_commute (a b : G) :
    a⁻¹ * b⁻¹ * a * b = 1 ↔ Commute a b := by
  simpa only [commutatorElement_def, inv_inv, Commute.inv_inv_iff] using
    (commutatorElement_eq_one_iff_commute (g₁ := a⁻¹) (g₂ := b⁻¹))

/-- The inverse-convention commutator criterion expressed as equality of products. -/
theorem inverse_commutator_eq_one_iff_mul_eq_mul (a b : G) :
    a⁻¹ * b⁻¹ * a * b = 1 ↔ a * b = b * a := by
  rw [inverse_commutator_eq_one_iff_commute, commute_iff_eq]

end Undecidability.CommutatorLemmas
