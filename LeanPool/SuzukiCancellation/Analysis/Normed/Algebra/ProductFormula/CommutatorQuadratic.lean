/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.Commutator
public import LeanPool.SuzukiCancellation.Algebra.BigOperators.FinAntidiagonal

/-!
# Quadratic ordered commutator constants

At order two the multinomial conjugation constant consists of the diagonal
double commutators and twice the strictly ordered mixed commutators.

## Main results

* `αCommConj_cons`: the recursion splitting off the innermost generator.
* `αCommConj_two_eq_sum`: the explicit quadratic formula.
-/

@[expose] public noncomputable section

open Finset

namespace TrotterError

variable {A : Type*} [NormedRing A] [Algebra ℝ A]

/-- The multinomial commutator constant splits by the innermost multiplicity. -/
lemma αCommConj_cons {s : ℕ} (Z : Fin (s + 1) → A) (B : A) (p : ℕ) :
    αCommConj Z B p = ∑ k ∈ range (p + 1), (p.choose k : ℝ) *
      αCommConj (fun i ↦ Z i.succ) (adPow (Z 0) k B) (p - k) := by
  rw [αCommConj, sum_finAntidiagonal_succ]
  apply sum_congr rfl
  intro k hk
  rw [αCommConj, mul_sum]
  apply sum_congr rfl
  intro q hq
  rw [multinomial_fin_succ, adSequence_cons,
    mem_finAntidiagonal.mp hq, Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hk)),
    Nat.cast_mul]
  ring

/-- The zeroth-order commutator constant is the norm of its target. -/
@[simp] lemma αCommConj_zero {s : ℕ} (Z : Fin s → A) (B : A) :
    αCommConj Z B 0 = ‖B‖ := by
  induction s with
  | zero => simp [αCommConj, finAntidiagonal_zero, adSequence]
  | succ s ih =>
      rw [αCommConj_cons]
      simpa only [sum_range_succ, sum_range_zero, zero_add, Nat.choose_zero_right,
        Nat.cast_one, one_mul, Nat.sub_zero, pow_zero, one_apply_eq_self] using
        ih (fun i ↦ Z i.succ)

/-- The first-order commutator constant is the sum of the individual bracket norms. -/
lemma αCommConj_one {s : ℕ} (Z : Fin s → A) (B : A) :
    αCommConj Z B 1 = ∑ i, ‖⁅Z i, B⁆‖ := by
  induction s with
  | zero => simp [αCommConj, finAntidiagonal_zero]
  | succ s ih =>
      rw [αCommConj_cons]
      simp only [sum_range_succ, sum_range_zero, zero_add, Nat.choose_zero_right,
        Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self,
        pow_zero, pow_one, one_apply_eq_self, LieAlgebra.ad_apply,
        αCommConj_zero, ih, Fin.sum_univ_succ]
      rw [add_comm]

/-- **Quadratic commutator constant.** Diagonal terms have weight one and
strictly ordered mixed terms have weight two. The lower index acts first. -/
theorem αCommConj_two_eq_sum {s : ℕ} (Z : Fin s → A) (B : A) :
    αCommConj Z B 2 = (∑ i, ‖⁅Z i, ⁅Z i, B⁆⁆‖) +
      2 * ∑ i, ∑ j ∈ univ.filter (fun j ↦ i < j), ‖⁅Z j, ⁅Z i, B⁆⁆‖ := by
  induction s with
  | zero => simp [αCommConj, finAntidiagonal_zero]
  | succ s ih =>
      rw [αCommConj_cons]
      simp only [sum_range_succ, sum_range_zero, zero_add]
      norm_num only [Nat.choose, Nat.sub_self, Nat.reduceSub, Nat.sub_zero,
        Nat.cast_ofNat, Nat.cast_one, one_mul, pow_zero, one_apply_eq_self,
        ad_pow_succ, LieAlgebra.ad_apply]
      rw [ih, αCommConj_one, αCommConj_zero]
      simp only [sum_filter, Fin.sum_univ_succ, Fin.succ_pos, Fin.not_lt_zero,
        Fin.succ_lt_succ_iff, ite_true, ite_false, zero_add]
      ring

end TrotterError
