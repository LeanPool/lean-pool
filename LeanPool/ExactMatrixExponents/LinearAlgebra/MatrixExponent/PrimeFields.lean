/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.FieldExtension
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod

/-!
# Reduction to prime fields

It suffices to rule out one finite system of coefficient equations at
a time. The threshold can be tested with integer arithmetic alone.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent

theorem prime_specialization {F : Type*} [Field F] {s : ℝ} (h : omega F < s) :
    ∃ (p : ℕ) (_ : Fact p.Prime), omega (ZMod p) < s := by
  obtain ⟨k, _, _, hk⟩ := finite_specialization h
  let p := ringChar k
  have : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let : Algebra (ZMod p) k := ZMod.algebra k p
  exact ⟨p, inferInstance, (omega_extension (ZMod p) k) ▸ hk⟩

/-- Lifting the upper bound from small fields to all universes. -/
theorem upper_of_small {s : ℝ} (h : ∀ (k : Type) [Field k], omega k ≤ s)
    (F : Type*) [Field F] : omega F ≤ s := by
  obtain ⟨p, hp⟩ := CharP.exists F
  rcases CharP.char_is_prime_or_zero F p with hprime | rfl
  · have : Fact p.Prime := ⟨hprime⟩
    let : Algebra (ZMod p) F := ZMod.algebra F p
    rw [omega_extension (ZMod p) F]
    exact h _
  · let : CharZero F := CharP.charP_to_charZero F
    rw [omega_extension ℚ F]
    exact h _

theorem rank_threshold (n r : ℕ) :
    (r : ℝ) < (n : ℝ) ^ (9 / 4 : ℝ) ↔ r ^ 4 < n ^ 9 := by
  have he : ((n : ℝ) ^ (9 / 4 : ℝ)) ^ (4 : ℕ) = (n : ℝ) ^ (9 : ℕ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    norm_num
  rw [← pow_lt_pow_iff_left₀ (Nat.cast_nonneg (α := ℝ) r)
    (Real.rpow_nonneg (Nat.cast_nonneg n) (9 / 4)) (by decide : (4 : ℕ) ≠ 0), he]
  norm_cast

end MatrixMultiplicationAllFields.MatrixExponent
