/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/BinarySeries.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.Cuts
public import Mathlib.Analysis.Real.OfDigits

/-!
# Binary Series
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BinarySeries

def bit (B : Oracle) (n : ℕ) : ℕ := if B n then 1 else 0

def digits (B : Oracle) (n : ℕ) : Fin 2 := ⟨bit B n, by unfold bit; split <;> omega⟩

noncomputable def value (B : Oracle) : ℝ := Real.ofDigits (digits B)

def numeral (B : Oracle) : ℕ → ℕ
  | 0 => 0
  | n+1 => 2 * numeral B n + bit B n

theorem numeral_sum (B : Oracle) (n : ℕ) :
    (∑ i ∈ Finset.range n, Real.ofDigitsTerm (digits B) i) =
      (numeral B n : ℝ) / 2^n := by
  induction n with
  | zero => simp [numeral]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [numeral, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Real.ofDigitsTerm, digits, pow_succ]
    field_simp

theorem split_value (B : Oracle) (n : ℕ) :
    value B = (numeral B n : ℝ)/2^n + (2^n : ℝ)⁻¹ * value (fun i => B (i+n)) := by
  exact (Real.ofDigits_eq_sum_add_ofDigits (digits B) n).trans (by rw [numeral_sum]; rfl)

theorem nonneg (B : Oracle) : 0 ≤ value B := Real.ofDigits_nonneg _
theorem le_one (B : Oracle) : value B ≤ 1 := Real.ofDigits_le_one _

theorem positive (B : Oracle) (h : ∃ n, B n = true) : 0 < value B := by
  obtain ⟨n, hn⟩ := h
  have ht : 0 < Real.ofDigitsTerm (digits B) n := by
    simp [Real.ofDigitsTerm, digits, bit, hn]
  exact lt_of_lt_of_le ht (Summable.le_tsum Real.summable_ofDigitsTerm n
    (fun _ _ => Real.ofDigitsTerm_nonneg))

theorem complement (B : Oracle) : value B + value (fun n => !(B n)) = 1 := by
  rw [value, value, Real.ofDigits, Real.ofDigits, ← Summable.tsum_add
    Real.summable_ofDigitsTerm Real.summable_ofDigitsTerm]
  have he : (fun n => Real.ofDigitsTerm (digits B) n +
      Real.ofDigitsTerm (digits (fun n => !(B n))) n) =
      Real.ofDigitsTerm (fun _ => (⟨1, by omega⟩ : Fin 2)) := by
    funext n
    cases h : B n <;> simp [Real.ofDigitsTerm, digits, bit, h]
  rw [he]
  exact Real.ofDigits_const_last_eq_one' (by omega : 1 < 2)

theorem lt_one (B : Oracle) (h : ∃ n, B n = false) : value B < 1 := by
  have hp := positive (fun n => !(B n)) (by obtain ⟨n, hn⟩ := h; exact ⟨n, by simp [hn]⟩)
  have hc := complement B
  linarith

def Mixed (B : Oracle) : Prop := ∀ N, (∃ n, N ≤ n ∧ B n = true) ∧ (∃ n, N ≤ n ∧ B n = false)

theorem strict_bracket (B : Oracle) (h : Mixed B) (n : ℕ) :
    (numeral B n : ℝ)/2^n < value B ∧ value B < (numeral B n + 1 : ℝ)/2^n := by
  have hp : 0 < value (fun i => B (i+n)) := by
    apply positive
    obtain ⟨k,hk,hb⟩ := (h n).1
    exact ⟨k-n, by simpa [Nat.sub_add_cancel hk] using hb⟩
  have hu : value (fun i => B (i+n)) < 1 := by
    apply lt_one
    obtain ⟨k,hk,hb⟩ := (h n).2
    exact ⟨k-n, by simpa [Nat.sub_add_cancel hk] using hb⟩
  rw [split_value B n]
  have hd : (0 : ℝ) < (2^n : ℝ)⁻¹ := by positivity
  constructor
  · nlinarith
  · rw [add_div]
    simp only [one_div]
    nlinarith

theorem bracket (B : Oracle) (n : ℕ) :
    (numeral B n : ℝ)/2^n ≤ value B ∧ value B ≤ (numeral B n + 1 : ℝ)/2^n := by
  rw [split_value B n]
  have hp := nonneg (fun i => B (i+n))
  have hu := le_one (fun i => B (i+n))
  have hd : (0 : ℝ) < (2^n : ℝ)⁻¹ := by positivity
  constructor
  · nlinarith
  · rw [add_div]; simp only [one_div]; nlinarith

end TuringRigidity.BinarySeries

end OAI
