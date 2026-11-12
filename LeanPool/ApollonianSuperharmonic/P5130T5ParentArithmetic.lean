/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordFareyParameter
public import Mathlib.Tactic.Linarith

-- [TABLET NODE: P5130T5ParentArithmetic]

/-!
# P5130T5ParentArithmetic

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5130T5ParentArithmetic (P : FordFareyParameter) (hq : 1 < P.q) :
    0 < P.q₁ ∧ P.q₁ < P.q ∧ 0 < P.q₂ ∧ P.q₂ < P.q ∧
    Nat.Coprime P.q₁ P.p₁.natAbs ∧ Nat.Coprime P.q₂ P.p₂.natAbs ∧
    P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int) = 1 := by
-- BODY
  have hs : (P.q : Int) = P.q₁ + P.q₂ := by exact_mod_cast P.sum_q
  have hd := P.det₁
  have hp := P.sum_p
  have hcross : P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int) = 1 := by
    rw [hs, hp] at hd
    nlinarith [hd]
  have hpos : 0 < P.q₁ := by
    by_contra hn
    have hz : P.q₁ = 0 := by omega
    rw [hz] at hd
    simp only [Nat.cast_zero, zero_mul, sub_zero] at hd
    have hqi : (1 : Int) < P.q := by exact_mod_cast hq
    have : (P.q : Int) ∣ 1 := ⟨P.p₁, by nlinarith [hd]⟩
    have := Int.le_of_dvd (by norm_num : (0 : Int) < 1) this
    omega
  have hcop₁ : Int.gcd (P.q₁ : Int) P.p₁ = 1 := by
    have hdiv : (Int.gcd (P.q₁ : Int) P.p₁ : Int) ∣ 1 := by
      rw [← hcross]
      exact dvd_sub (dvd_mul_of_dvd_left (Int.gcd_dvd_right _ _) _)
        (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) _)
    have hn : Int.natAbs (Int.gcd (P.q₁ : Int) P.p₁ : Int) = 1 :=
      Int.isUnit_iff_natAbs_eq.mp (isUnit_of_dvd_one hdiv)
    simpa using hn
  have hcop₂ : Int.gcd (P.q₂ : Int) P.p₂ = 1 := by
    have hdiv : (Int.gcd (P.q₂ : Int) P.p₂ : Int) ∣ 1 := by
      rw [← hcross]
      exact dvd_sub (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) _)
        (dvd_mul_of_dvd_left (Int.gcd_dvd_right _ _) _)
    have hn : Int.natAbs (Int.gcd (P.q₂ : Int) P.p₂ : Int) = 1 :=
      Int.isUnit_iff_natAbs_eq.mp (isUnit_of_dvd_one hdiv)
    simpa using hn
  refine ⟨hpos, P.q₁_lt, P.q₂_pos, by have := P.sum_q; omega, ?_, ?_, hcross⟩
  · simpa [Int.gcd] using hcop₁
  · simpa [Int.gcd] using hcop₂

end ApollonianSuperharmonic

end
