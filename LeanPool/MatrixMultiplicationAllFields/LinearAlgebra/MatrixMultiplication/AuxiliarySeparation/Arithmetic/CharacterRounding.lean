/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Arithmetic/CharacterRounding.lean`,
by Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K`
algebraically closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.ExponentComparison
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Integer rounding in the detecting-character argument

The character used at a matrix size may depend on that size. A uniform bound
on all those characters is enough: the loss of one in rounding their target
values cannot change a positive power exponent. The character-existence and
character-growth assumptions remain explicit in the final implications.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- Rounding strictly down works at integers too: use `ceil x - 1`. -/
theorem exists_nat_sub_one_le_lt {x : ℝ} (hx : 0 < x) :
    ∃ k : ℕ, x - 1 ≤ (k : ℝ) ∧ (k : ℝ) < x := by
  have hc : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx
  refine ⟨⌈x⌉₊ - 1, ?_, ?_⟩
  · rw [Nat.cast_sub hc]
    norm_num only [Nat.cast_one]
    linarith [Nat.le_ceil x]
  · exact ((Nat.ceil_eq_iff (by omega : ⌈x⌉₊ ≠ 0)).1 rfl).1

/-- An additive loss of one does not affect a comparison to a nonnegative
power exponent. No sign assumption on the exponent on the left is needed. -/
theorem rpow_exponent_le_of_nat_sub_one_bound {ν τ : ℝ} (hτ : 0 ≤ τ)
    (hbound : ∀ d : ℕ, 2 ≤ d → (d : ℝ) ^ ν - 1 ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply rpow_exponent_le_of_nat_bound (C := 2)
  intro d hd
  by_cases hd2 : 2 ≤ d
  · have h := hbound d hd2
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hpow : 1 ≤ (d : ℝ) ^ τ := Real.one_le_rpow hdreal hτ
    linarith
  · have hd1 : d = 1 := by omega
    simp [hd1]

/-- The integer witnesses in the final rounding argument can vary with `d`. -/
theorem exponent_le_of_integer_rounding {ν τ : ℝ} (hτ : 0 ≤ τ)
    (hround : ∀ d : ℕ, 2 ≤ d →
      ∃ k : ℕ, (d : ℝ) ^ ν - 1 ≤ k ∧ (k : ℝ) ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply rpow_exponent_le_of_nat_sub_one_bound hτ
  intro d hd
  obtain ⟨k, hk, hk'⟩ := hround d hd
  exact hk.trans hk'

/-- A positive exponent on the left makes the target exponent nonnegative
automatically, so it is an alternative to that hypothesis above. -/
theorem exponent_le_of_integer_rounding_of_pos {ν τ : ℝ} (hν : 0 < ν)
    (hround : ∀ d : ℕ, 2 ≤ d →
      ∃ k : ℕ, (d : ℝ) ^ ν - 1 ≤ k ∧ (k : ℝ) ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  have hτ : 0 ≤ τ := by
    by_contra hneg
    obtain ⟨k, hk, hk'⟩ := hround 2 le_rfl
    norm_num only [Nat.cast_ofNat] at hk hk'
    have hpτ : (2 : ℝ) ^ τ < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (lt_of_not_ge hneg)
    have hklt : (k : ℝ) < 1 := hk'.trans_lt hpτ
    have hk0 : k = 0 := by
      have : k < 1 := by exact_mod_cast hklt
      omega
    rw [hk0, Nat.cast_zero] at hk
    have hpν : 1 < (2 : ℝ) ^ ν := Real.one_lt_rpow (by norm_num) hν
    linarith
  exact exponent_le_of_integer_rounding hτ hround

/-- Explicitly conditional passage from detecting characters to the exponent
bound. The detecting character is allowed to depend on both `d` and `k`. -/
theorem exponent_le_of_detecting_characters {ν τ : ℝ} (hτ : 0 ≤ τ)
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ, (k : ℝ) < (d : ℝ) ^ ν →
      ∃ χ : Character K, (k : ℝ) ≤ χ.value (Tensor.matMul K d d d))
    (bound : ∀ χ : Character K, ∀ d : ℕ, 2 ≤ d →
      χ.value (Tensor.matMul K d d d) ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply exponent_le_of_integer_rounding hτ
  intro d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨k, hk, hk'⟩ :=
    exists_nat_sub_one_le_lt (Real.rpow_pos_of_pos hdpos ν)
  obtain ⟨χ, hχ⟩ := detect d hd k hk'
  exact ⟨k, hk, hχ.trans (bound χ d hd)⟩

/-- The character growth bound can be supplied as a uniform bound on its
exponent sum, together with the matrix-value identity. -/
theorem exponent_le_of_detecting_character_exponents {ν τ : ℝ} (hτ : 0 ≤ τ)
    (exponentSum : Character K → ℝ)
    (value : ∀ χ : Character K, ∀ d : ℕ, 2 ≤ d →
      χ.value (Tensor.matMul K d d d) = (d : ℝ) ^ exponentSum χ)
    (upper : ∀ χ : Character K, exponentSum χ ≤ τ)
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ, (k : ℝ) < (d : ℝ) ^ ν →
      ∃ χ : Character K, (k : ℝ) ≤ χ.value (Tensor.matMul K d d d)) :
    ν ≤ τ := by
  apply exponent_le_of_detecting_characters hτ detect
  intro χ d hd
  rw [value χ d hd]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ d by omega))
    (upper χ)

/-- The paper's final `ν ≤ 9/4` implication, with its two substantive character
inputs visible rather than incorporated into the definition of `ν`. -/
theorem exactRankExponent_le_nine_quarters_of_characters
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ,
      (k : ℝ) < (d : ℝ) ^ exactRankExponent K →
      ∃ χ : Character K, (k : ℝ) ≤ χ.value (Tensor.matMul K d d d))
    (bound : ∀ χ : Character K, ∀ d : ℕ, 2 ≤ d →
      χ.value (Tensor.matMul K d d d) ≤ (d : ℝ) ^ (9 / 4 : ℝ)) :
    exactRankExponent K ≤ 9 / 4 :=
  exponent_le_of_detecting_characters (by norm_num) detect bound

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
