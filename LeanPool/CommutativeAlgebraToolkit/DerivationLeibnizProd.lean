/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.Ring

/-!
# The Leibniz rule for finite products and integer powers of units

## Main statements

* `Derivation.leibniz_prod`: `D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) • D (f i)`.
* `Derivation.leibniz_zpow_units`: `D (u ^ n) = n • u ^ (n - 1) • D u` for a unit `u` and
  `n : ℤ`.
-/

public section

namespace Derivation

section

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [AddCommMonoid M]
variable [Algebra R A] [Module A M] [Module R M]
variable (D : Derivation R A M)

/-- The Leibniz rule for a finite product. -/
theorem leibniz_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) • D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, leibniz, ih, Finset.erase_insert ha,
      Finset.smul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [smul_smul, Finset.erase_insert_of_ne (by grind), Finset.prod_insert (by grind)]

end

section

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M] [Module R M]
variable (D : Derivation R A M)

/-- The Leibniz rule for integer powers of a unit. See `Derivation.leibniz_zpow` for fields. -/
theorem leibniz_zpow_units (u : Aˣ) (n : ℤ) :
    D ↑(u ^ n) = n • ((u ^ (n - 1) : Aˣ) : A) • D ↑u := by
  rcases n with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, leibniz_pow,
      ← natCast_zsmul]
    rcases k with _ | k <;> simp
  · simp only [Int.negSucc_sub_one, zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    rw [leibniz_pow, D.leibniz_of_mul_eq_one (Units.inv_mul u), ← Nat.cast_smul_eq_nsmul A,
      ← Int.cast_smul_eq_zsmul A, Nat.add_sub_cancel]
    simp only [smul_smul]
    congr 1
    push_cast
    ring

end

end Derivation
