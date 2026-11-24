/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Multinomial bounds and zero multiplicities

A multinomial coefficient is bounded by the factorial of its total degree.
Prepending a zero multiplicity leaves it unchanged.
-/

@[expose] public section

namespace TrotterError

open Finset

/-- Every multinomial coefficient is at most the factorial of the total degree: the multinomial
`Nat.multinomial s f` divides `(∑ f)!` (via `Nat.multinomial_spec`), and the complementary product
of factorials is `≥ 1`. -/
lemma multinomial_le_factorial {α : Type*} (s : Finset α) (f : α → ℕ) :
    Nat.multinomial s f ≤ Nat.factorial (∑ i ∈ s, f i) := by
  have hspec := Nat.multinomial_spec s f
  have hprod : 1 ≤ ∏ i ∈ s, (f i).factorial := one_le_prod (fun i _ => Nat.factorial_pos _)
  calc
    Nat.multinomial s f = Nat.multinomial s f * 1 := by rw [mul_one]
    _ ≤ Nat.multinomial s f * (∏ i ∈ s, (f i).factorial) := Nat.mul_le_mul_left _ hprod
    _ = (∏ i ∈ s, (f i).factorial) * Nat.multinomial s f := by rw [mul_comm]
    _ = (∑ i ∈ s, f i).factorial := hspec

/-- `Nat.multinomial (Fin.cons 0 q) = Nat.multinomial q`: prepending a zero multiplicity does not
change the multinomial coefficient. -/
lemma multinomial_cons_zero {s : ℕ} (q : Fin s → ℕ) :
    Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.cons 0 q) =
      Nat.multinomial (univ : Finset (Fin s)) q := by
  unfold Nat.multinomial
  rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
  simp [Nat.factorial_zero]

end TrotterError
