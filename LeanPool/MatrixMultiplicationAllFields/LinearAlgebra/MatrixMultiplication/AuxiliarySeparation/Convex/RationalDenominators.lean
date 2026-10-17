/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Clearing denominators in nonnegative rational families
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

/-- Every natural multiple of a denominator clears its nonnegative rational. -/
theorem exists_nat_eq_mul_rat_of_den_dvd {q : ℚ} (hq : 0 ≤ q)
    {D : ℕ} (hD : q.den ∣ D) :
    ∃ c : ℕ, (D : ℚ) * q = (c : ℚ) := by
  obtain ⟨k, rfl⟩ := hD
  refine ⟨k * q.num.toNat, ?_⟩
  have hnum : (q.num.toNat : ℚ) = (q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  push_cast
  rw [hnum]
  calc
    (q.den : ℚ) * k * q = k * ((q.den : ℚ) * q) := by ring
    _ = k * (q.num : ℚ) := by rw [Rat.den_mul_eq_num]

/-- A finite nonnegative rational family has a common positive denominator
which turns every coefficient into a natural number. -/
theorem exists_nat_mul_eq_nat {I : Type*} [Finite I]
    (q : I → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ, ∀ i, (D : ℚ) * q i = (c i : ℚ) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let D : ℕ := ∏ i, (q i).den
  have hD : 0 < D := Finset.prod_pos fun i _ ↦ (q i).den_pos
  have hc : ∀ i, ∃ c : ℕ, (D : ℚ) * q i = (c : ℚ) := by
    intro i
    exact exists_nat_eq_mul_rat_of_den_dvd (hq i)
      (Finset.dvd_prod_of_mem (fun j ↦ (q j).den) (Finset.mem_univ i))
  choose c hc using hc
  exact ⟨D, hD, c, hc⟩

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
