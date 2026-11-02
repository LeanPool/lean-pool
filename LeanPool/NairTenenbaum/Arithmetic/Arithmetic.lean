/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Arithmetic functions in Nair–Tenenbaum

Equation (1) and the basic consequences used in §2 of *Short sums of certain
arithmetic functions*, Acta Math. 180 (1998), 119–144.
Tuples take values in `ℕ+`, so zero is never silently admitted into the domain.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- A tuple of positive integers with a fixed number of coordinates. -/
abbrev Tuple (k : ℕ) := Fin k → ℕ+
/-- A real-valued arithmetic function on positive integer tuples. -/
abbrev ArithmeticMap (k : ℕ) := Tuple k → ℝ

/-- Total number of prime factors, with multiplicity. -/
def bigOmega (n : ℕ) : ℕ := n.primeFactorsList.length

@[simp] theorem bigOmega_one : bigOmega 1 = 0 := by simp [bigOmega]

theorem bigOmega_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    bigOmega (m * n) = bigOmega m + bigOmega n := by
  simpa [bigOmega] using (Nat.perm_primeFactorsList_mul hm hn).length_eq

/-- Product of the coordinates of a positive tuple. -/
def mass {k : ℕ} (n : Tuple k) : ℕ := ∏ j, (n j : ℕ)

theorem mass_pos {k : ℕ} (n : Tuple k) : 0 < mass n :=
  Finset.prod_pos fun j _ => (n j).pos

@[simp] theorem mass_mul {k : ℕ} (m n : Tuple k) :
    mass (m * n) = mass m * mass n := by simp [mass, Finset.prod_mul_distrib]

/-- Coprimality is coordinatewise, as in (1), not between the two total products. -/
def Coprime {k : ℕ} (m n : Tuple k) : Prop := ∀ j, Nat.Coprime (m j) (n j)

theorem Coprime.symm {k : ℕ} {m n : Tuple k} (h : Coprime m n) : Coprime n m :=
  fun j => (h j).symm

@[simp] theorem coprime_one_right {k : ℕ} (m : Tuple k) : Coprime m 1 :=
  fun _ => Nat.coprime_one_right _

@[simp] theorem coprime_one_left {k : ℕ} (m : Tuple k) : Coprime 1 m :=
  (coprime_one_right m).symm

theorem coprime_mul_right {k : ℕ} (a b c : Tuple k) :
    Coprime a (b * c) ↔ Coprime a b ∧ Coprime a c := by
  simp only [Coprime, Pi.mul_apply, PNat.mul_coe, Nat.coprime_mul_iff_right,
    forall_and]

theorem coprime_mul_left {k : ℕ} (a b c : Tuple k) :
    Coprime (a * b) c ↔ Coprime a c ∧ Coprime b c := by
  simp only [Coprime, Pi.mul_apply, PNat.mul_coe, Nat.coprime_mul_iff_left,
    forall_and]

/-- The majorant in equation (1). -/
noncomputable def growthBound {k : ℕ} (A B ε : ℝ) (m : Tuple k) : ℝ :=
  min (A ^ bigOmega (mass m)) (B * (mass m : ℝ) ^ ε)

/-- Membership of `𝓜ₖ(A,B,ε)`. Parameter ranges are supplied by individual theorems. -/
structure Admissible {k : ℕ} (A B ε : ℝ) (F : ArithmeticMap k) : Prop where
  nonneg : ∀ n, 0 ≤ F n
  growth : ∀ m n, Coprime m n → F (m * n) ≤ growthBound A B ε m * F n

theorem growthBound_nonneg {k : ℕ} {A B ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (m : Tuple k) : 0 ≤ growthBound A B ε m := by
  exact le_min (pow_nonneg hA _) (mul_nonneg hB (Real.rpow_nonneg (by positivity) _))

theorem growthBound_mono {k : ℕ} {A B ε A' B' ε' : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAA : A ≤ A') (hBB : B ≤ B') (hε : ε ≤ ε')
    (m : Tuple k) : growthBound A B ε m ≤ growthBound A' B' ε' m := by
  apply min_le_min
  · exact pow_le_pow_left₀ hA hAA _
  · exact mul_le_mul hBB (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast mass_pos m) hε) (Real.rpow_nonneg (by positivity) _) (hB.trans hBB)

theorem Admissible.mono {k : ℕ} {A B ε A' B' ε' : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAA : A ≤ A') (hBB : B ≤ B') (hε : ε ≤ ε') : Admissible A' B' ε' F := by
  refine ⟨hF.nonneg, fun m n h => (hF.growth m n h).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (growthBound_mono hA hB hAA hBB hε m) (hF.nonneg n)

theorem Admissible.le_at_one {k : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (n : Tuple k) :
    F n ≤ growthBound A B ε n * F 1 := by
  simpa using hF.growth n 1 (coprime_one_right n)

theorem Admissible.eq_zero_of_one {k : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (h : F 1 = 0) : F = 0 := by
  funext n
  exact le_antisymm (by simpa [h] using hF.le_at_one n) (hF.nonneg n)

theorem Admissible.add {k : ℕ} {A B ε : ℝ} {F H : ArithmeticMap k}
    (hF : Admissible A B ε F) (hH : Admissible A B ε H) :
    Admissible A B ε (F + H) := by
  refine ⟨fun n => add_nonneg (hF.nonneg n) (hH.nonneg n), fun m n h => ?_⟩
  simpa [mul_add] using add_le_add (hF.growth m n h) (hH.growth m n h)

theorem Admissible.smul {k : ℕ} {A B ε c : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hc : 0 ≤ c) :
    Admissible A B ε (fun n => c * F n) := by
  refine ⟨fun n => mul_nonneg hc (hF.nonneg n), fun m n h => ?_⟩
  simpa [mul_left_comm] using mul_le_mul_of_nonneg_left (hF.growth m n h) hc

/-- Taking a nonnegative power preserves the arithmetic class with the expected
change in its three parameters. -/
theorem Admissible.rpow {k : ℕ} {A B ε t : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t) :
    Admissible (A ^ t) (B ^ t) (ε * t) (fun n => F n ^ t) := by
  refine ⟨fun n => Real.rpow_nonneg (hF.nonneg n) _, fun m n hmn => ?_⟩
  calc
    F (m * n) ^ t ≤ (growthBound A B ε m * F n) ^ t :=
      Real.rpow_le_rpow (hF.nonneg _) (hF.growth m n hmn) ht
    _ = growthBound A B ε m ^ t * F n ^ t :=
      Real.mul_rpow (growthBound_nonneg hA hB _) (hF.nonneg n)
    _ ≤ growthBound (A ^ t) (B ^ t) (ε * t) m * F n ^ t := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hF.nonneg n) _)
      apply le_min
      · calc
          growthBound A B ε m ^ t ≤ (A ^ bigOmega (mass m)) ^ t :=
            Real.rpow_le_rpow (growthBound_nonneg hA hB _) (min_le_left _ _) ht
          _ = (A ^ t) ^ bigOmega (mass m) := (Real.rpow_pow_comm hA _ _).symm
      · calc
          growthBound A B ε m ^ t ≤ (B * (mass m : ℝ) ^ ε) ^ t :=
            Real.rpow_le_rpow (growthBound_nonneg hA hB _) (min_le_right _ _) ht
          _ = B ^ t * (mass m : ℝ) ^ (ε * t) := by
            rw [Real.mul_rpow hB (by positivity), ← Real.rpow_mul (by positivity)]

end NairTenenbaum
