/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.DivisorSums.RoughCofactorBounds

/-! # Smooth and rough parts at a real cutoff -/

@[expose] public section

namespace NairTenenbaum

/-- The factor supported on primes up to the smoothness cutoff. -/
noncomputable def smoothPart (n : ℕ+) (z : ℝ) : ℕ+ :=
  primeSelect (fun _ : Fin 1 => n) (Finset.range (⌊z⌋₊ + 1)) 0

/-- The complementary factor supported on primes above the smoothness cutoff. -/
noncomputable def roughPart (n : ℕ+) (z : ℝ) : ℕ+ :=
  primeReject (fun _ : Fin 1 => n) (Finset.range (⌊z⌋₊ + 1)) 0

theorem smoothPart_mul_roughPart (n : ℕ+) (z : ℝ) : smoothPart n z * roughPart n z = n := by
  exact congrFun (primeSelect_mul_primeReject (fun _ : Fin 1 => n) (Finset.range (⌊z⌋₊ + 1))) 0

theorem cutoff_lt_of_mem_roughPart (n : ℕ+) (z : ℝ) {p : ℕ}
    (hp : p ∈ (roughPart n z : ℕ).primeFactors) : z < (p : ℝ) := by
  have H := primeReject_range_prime_ge (fun _ : Fin 1 => n) (⌊z⌋₊ + 1) 0 hp
  exact Nat.lt_of_floor_lt (by omega)

theorem log_roughPart (n : ℕ+) (z : ℝ) :
    Real.log (roughPart n z : ℕ) = Real.log (n : ℕ) - Real.log (smoothPart n z : ℕ) := by
  have H : (smoothPart n z : ℝ) * (roughPart n z : ℝ) = (n : ℝ) := by
    exact_mod_cast smoothPart_mul_roughPart n z
  have HL := congrArg Real.log H
  rw [Real.log_mul (by positivity) (by positivity)] at HL
  linarith

end NairTenenbaum
