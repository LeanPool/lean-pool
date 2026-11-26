/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.FieldExtension
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Degree
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Folding.Swap
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod

/-!
# The upper bound over every field

First bound the exponent at shapes `(AB, AC, BC)` for positive integers
`A, B, C`. All three integers equal to one gives the square.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle

theorem small_field (F : Type*) [Field F] : ∃ (K : Type) (_ : Field K), Nonempty (Algebra K F) := by
  obtain ⟨p, hp⟩ := CharP.exists F
  rcases CharP.char_is_prime_or_zero F p with hprime | rfl
  · have : Fact p.Prime := ⟨hprime⟩
    exact ⟨ZMod p, inferInstance, ⟨ZMod.algebra F p⟩⟩
  · let : CharZero F := CharP.charP_to_charZero F
    exact ⟨ℚ, inferInstance, ⟨inferInstance⟩⟩

theorem closed_fulfills (K : Type) [Field K] [IsAlgClosed K] : Fulfills K :=
  closed_laws {
    discrete := coeff_discrete character_bound
    density := coeff_density
    cells := coeff_cells
    binary := Profile.coeff_binary
    degrees := Sparse.coeff_degrees
  } K

theorem discrete_bound (F : Type*) [Field F] : DiscreteBound F := by
  obtain ⟨K, _, ⟨alg⟩⟩ := small_field F
  intro A B C hA hB hC
  have h₁ : 0 ≤ (A : ℝ) * B := by positivity
  have h₂ : 0 ≤ (A : ℝ) * C := by positivity
  have h₃ : 0 ≤ (B : ℝ) * C := by positivity
  rw [exponent_extension K F h₁ h₂ h₃, ← exponent_extension K (AlgebraicClosure K) h₁ h₂ h₃]
  exact (closed_fulfills _).discrete A B C hA hB hC

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle

namespace MatrixMultiplicationAllFields.MatrixExponent

theorem upper_bound (F : Type*) [Field F] : omega F ≤ 9 / 4 := by
  have h := Rectangle.discrete_bound F 1 1 1 (by decide) (by decide) (by decide)
  norm_num [Rectangle.square] at h
  exact h

theorem arithmetic_bound (F : Type*) [Field F] : Admissible F (9 / 4) := by
  intro ε hε
  have h : omega F < 9 / 4 + ε := lt_add_of_le_of_pos (upper_bound F) hε
  obtain ⟨s, hs, hlt⟩ := exists_lt_of_csInf_lt ⟨3, admissible_three F⟩ h
  obtain ⟨C, hC, hprog⟩ := hs (9 / 4 + ε - s) (sub_pos.mpr hlt)
  refine ⟨C, hC, ?_⟩
  simpa only [show s + (9 / 4 + ε - s) = 9 / 4 + ε by ring] using hprog

end MatrixMultiplicationAllFields.MatrixExponent
