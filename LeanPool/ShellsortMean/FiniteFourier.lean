/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: extracted the Fourier identities shared by two modules. -/

module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Tactic.Ring

/-! Transposition and conjugation for the finite Fourier transform on `ZMod`. -/

public section

namespace Shellsort.FiniteFourier

open Finset ZMod
open scoped ComplexConjugate

variable {N : ℕ} [NeZero N]

/-- Transpose the finite Fourier transform under the bilinear sum pairing. -/
theorem dft_transpose (f g : ZMod N → ℂ) :
    (∑ k, dft f k * g k) = ∑ j, f j * dft g j := by
  simp only [dft_apply, smul_eq_mul, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  rw [mul_comm k j]
  ring

/-- Conjugate the standard character at a negative residue. -/
theorem stdAddChar_conj_neg (j : ZMod N) : conj (stdAddChar (-j)) = stdAddChar j := by
  rw [stdAddChar_apply, stdAddChar_apply, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  simp

/-- Conjugating the input and negating the frequency conjugates the Fourier coefficient. -/
theorem dft_conj_neg (f : ZMod N → ℂ) (k : ZMod N) :
    dft (fun j ↦ conj (f j)) (-k) = conj (dft f k) := by
  simp only [dft_apply, smul_eq_mul, map_sum, map_mul, mul_neg, neg_neg, stdAddChar_conj_neg]

end Shellsort.FiniteFourier
