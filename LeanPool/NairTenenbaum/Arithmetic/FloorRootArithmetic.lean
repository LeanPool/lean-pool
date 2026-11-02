/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.ProductArithmetic
public import Mathlib.Data.Nat.Factorization.Root

/-! # Lifting arithmetic weights through prime-factor roots

The flooring root divides each prime multiplicity by `d`. It is multiplicative
on coprime arguments and recovers `n` from `n^d`. Thus a scalar admissible
weight can be lifted to an additional coordinate without assuming that the
weight itself is multiplicative.
-/

@[expose] public section

namespace NairTenenbaum

/-- The prime-factor flooring root on positive integers. -/
def positiveFloorRoot (d : ℕ+) (n : ℕ+) : ℕ+ :=
  ⟨Nat.floorRoot d n, Nat.pos_of_ne_zero (Nat.floorRoot_ne_zero.mpr ⟨d.ne_zero, n.ne_zero⟩)⟩

@[simp] theorem positiveFloorRoot_pow (d : ℕ+) (n : ℕ+) :
    positiveFloorRoot d (n ^ (d : ℕ)) = n := by
  apply PNat.coe_injective
  exact Nat.floorRoot_pow_self d.ne_zero n

theorem positiveFloorRoot_dvd (d : ℕ+) (n : ℕ+) :
    (positiveFloorRoot d n : ℕ) ∣ (n : ℕ) := by
  exact (dvd_pow_self _ d.ne_zero).trans Nat.floorRoot_pow_dvd

theorem positiveFloorRoot_coprime (d : ℕ+) {m n : ℕ+}
    (h : Nat.Coprime (m : ℕ) (n : ℕ)) :
    Nat.Coprime (positiveFloorRoot d m) (positiveFloorRoot d n) :=
  h.of_dvd (positiveFloorRoot_dvd d m) (positiveFloorRoot_dvd d n)

theorem positiveFloorRoot_mul (d : ℕ+) {m n : ℕ+}
    (h : Nat.Coprime (m : ℕ) (n : ℕ)) :
    positiveFloorRoot d (m * n) = positiveFloorRoot d m * positiveFloorRoot d n := by
  apply PNat.coe_injective
  apply Nat.eq_of_factorization_eq (PNat.ne_zero _) (PNat.ne_zero _)
  intro p
  change (Nat.floorRoot d ((m : ℕ) * n)).factorization p =
    (Nat.floorRoot d m * Nat.floorRoot d n).factorization p
  simp only [Nat.factorization_floorRoot,
    Nat.factorization_mul m.ne_zero n.ne_zero,
    Nat.factorization_mul (Nat.floorRoot_ne_zero.mpr ⟨d.ne_zero, m.ne_zero⟩)
      (Nat.floorRoot_ne_zero.mpr ⟨d.ne_zero, n.ne_zero⟩),
    Finsupp.floorDiv_apply, Finsupp.add_apply]
  by_cases hp : (m : ℕ).factorization p = 0
  · simp [hp]
  · have hn : (n : ℕ).factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpn
      exact (Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hp),
          Nat.dvd_of_factorization_pos hp, hpn⟩) h
    simp [hn]

theorem bigOmega_le_of_dvd {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) :
    bigOmega m ≤ bigOmega n := by
  obtain ⟨a, rfl⟩ := h
  rw [bigOmega_mul (left_ne_zero_of_mul hn) (right_ne_zero_of_mul hn)]
  omega

/-- Lifting a scalar weight along the flooring root preserves its admissibility
parameters. The bound deliberately uses the ambient argument rather than its root. -/
theorem admissible_floorRoot {A B ε : ℝ} {F : ArithmeticMap 1}
    (hF : Admissible A B ε F) (hA : 1 ≤ A) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (d : ℕ+) :
    Admissible A B ε (fun n : Tuple 1 => F (fun _ => positiveFloorRoot d (n 0))) := by
  refine ⟨fun n => hF.nonneg _, fun m n hmn => ?_⟩
  have H := hF.growth (fun _ => positiveFloorRoot d (m 0))
    (fun _ => positiveFloorRoot d (n 0))
    (fun _ => positiveFloorRoot_coprime d (hmn 0))
  have hmul : (fun _ : Fin 1 => positiveFloorRoot d ((m * n) 0)) =
      (fun _ : Fin 1 => positiveFloorRoot d (m 0)) *
        (fun _ : Fin 1 => positiveFloorRoot d (n 0)) := by
    ext i
    exact positiveFloorRoot_mul d (hmn 0)
  rw [hmul]
  refine H.trans (mul_le_mul_of_nonneg_right ?_ (hF.nonneg _))
  simp only [growthBound, mass, Fin.prod_univ_one]
  apply min_le_min
  · exact pow_le_pow_right₀ hA (bigOmega_le_of_dvd (m 0).ne_zero (positiveFloorRoot_dvd d _))
  · apply mul_le_mul_of_nonneg_left _ hB
    exact Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.le_of_dvd (m 0).pos (positiveFloorRoot_dvd d (m 0))) hε

end NairTenenbaum
