/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeLogSums
public import LeanPool.NairTenenbaum.Arithmetic.RootAuxiliary

/-! # Exponentially tilted auxiliary series

Multiplication by `n^(γ β)` is the exponential moment in the Rankin argument
for Lemma 2. Its convergence is proved with the shifted exponent `ε+β`.
The prime increment estimates retain the dependence on the cutoff explicitly.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- The root auxiliary weight after exponential tilting. -/
noncomputable def tiltedRootAuxiliary (A B ε β : ℝ) (γ : ℕ) (Q : ℤ[X]) (n : ℕ) : ℝ :=
  rootAuxiliary A B ε γ Q n * (n : ℝ) ^ ((γ : ℝ) * β)

@[simp] theorem tiltedRootAuxiliary_one (A B ε β : ℝ) (γ : ℕ) (Q : ℤ[X]) :
    tiltedRootAuxiliary A B ε β γ Q 1 = 1 := by simp [tiltedRootAuxiliary]

theorem tiltedRootAuxiliary_nonneg {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (γ : ℕ) (Q : ℤ[X]) (n : ℕ) : 0 ≤ tiltedRootAuxiliary A B ε β γ Q n :=
  mul_nonneg (rootAuxiliary_nonneg hA hB γ Q n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem tiltedRootAuxiliary_mul (A B ε β : ℝ) (γ : ℕ) (Q : ℤ[X]) {m n : ℕ}
    (hmn : m.Coprime n) : tiltedRootAuxiliary A B ε β γ Q (m * n) =
      tiltedRootAuxiliary A B ε β γ Q m * tiltedRootAuxiliary A B ε β γ Q n := by
  rw [tiltedRootAuxiliary, rootAuxiliary_mul A B ε γ Q hmn, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  simp only [tiltedRootAuxiliary]
  ring

/-- Tilting shifts the local geometric ratio from `ε` to `ε+β`. -/
theorem tiltedRootAuxiliary_prime_pow_le {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) (Q : ℤ[X]) {p : ℕ} (hp : p.Prime)
    (C ν : ℕ) (hρ : rootCount Q (p ^ ν) ≤ C) :
    tiltedRootAuxiliary A B ε β γ Q (p ^ ν) ≤
      (C : ℝ) * B * auxiliaryRatio (ε + β) γ p ^ ν := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h := mul_le_mul_of_nonneg_right (rootAuxiliary_prime_pow_le hA hB hε γ Q hp C ν hρ)
    (Real.rpow_nonneg (Nat.cast_nonneg (p ^ ν)) ((γ : ℝ) * β))
  refine h.trans_eq ?_
  rw [Nat.cast_pow, ← Real.rpow_pow_comm hp₀.le, mul_assoc, ← mul_pow,
    auxiliaryRatio, ← Real.rpow_add hp₀, auxiliaryRatio]
  congr 2
  congr 1
  ring

theorem tiltedRootAuxiliary_prime_pow_summable {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) (hγ : (γ : ℝ) * (ε + β) < 1) (Q : ℤ[X])
    {p : ℕ} (hp : p.Prime) (C : ℕ) (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    Summable (fun ν : ℕ => tiltedRootAuxiliary A B ε β γ Q (p ^ ν)) :=
  Summable.of_nonneg_of_le
    (fun _ => tiltedRootAuxiliary_nonneg hA (zero_le_one.trans hB) γ Q _)
    (fun ν => tiltedRootAuxiliary_prime_pow_le hA hB hε γ Q hp C ν (hρ ν))
    ((summable_geometric_of_lt_one (auxiliaryRatio_nonneg (ε + β) γ p)
      (auxiliaryRatio_lt_one hp hγ)).mul_left ((C : ℝ) * B))

/-- The local increment of the exponential moment, beginning at exponent one. -/
noncomputable def localMomentTerm (A B ε β : ℝ) (γ : ℕ) (Q : ℤ[X]) (p ν : ℕ) : ℝ :=
  rootAuxiliary A B ε γ Q (p ^ (ν + 1)) *
    (((p : ℝ) ^ (ν + 1)) ^ ((γ : ℝ) * β) - 1)

/-- The local higher-order error in the tilted Euler factor. -/
noncomputable def localMomentError (A B ε β : ℝ) (γ : ℕ) (Q : ℤ[X]) (p : ℕ) : ℝ :=
  ∑' ν : ℕ, localMomentTerm A B ε β γ Q p ν

theorem localMomentTerm_nonneg {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (γ : ℕ) (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    0 ≤ localMomentTerm A B ε β γ Q p ν := by
  apply mul_nonneg (rootAuxiliary_nonneg hA hB _ _ _)
  exact sub_nonneg.mpr (Real.one_le_rpow (one_le_pow₀ (by exact_mod_cast hp.one_le))
    (mul_nonneg (Nat.cast_nonneg γ) hβ))

theorem localMomentTerm_le_tilted {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (γ : ℕ) (Q : ℤ[X]) (p ν : ℕ) :
    localMomentTerm A B ε β γ Q p ν ≤ tiltedRootAuxiliary A B ε β γ Q (p ^ (ν + 1)) := by
  unfold localMomentTerm tiltedRootAuxiliary
  rw [Nat.cast_pow]
  exact mul_le_mul_of_nonneg_left (by linarith) (rootAuxiliary_nonneg hA hB _ _ _)

theorem localMomentTerm_summable {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hβ : 0 ≤ β) (γ : ℕ) (hγ : (γ : ℝ) * (ε + β) < 1) (Q : ℤ[X])
    {p : ℕ} (hp : p.Prime) (C : ℕ) (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    Summable (localMomentTerm A B ε β γ Q p) :=
  Summable.of_nonneg_of_le
    (fun ν => localMomentTerm_nonneg hA (zero_le_one.trans hB) hβ γ Q hp ν)
    (fun ν => localMomentTerm_le_tilted hA (zero_le_one.trans hB) γ Q p ν)
    ((summable_nat_add_iff
      (f := fun ν : ℕ => tiltedRootAuxiliary A B ε β γ Q (p ^ ν)) 1).mpr
      (tiltedRootAuxiliary_prime_pow_summable hA hB hε γ hγ Q hp C hρ))

/-- The alternative geometric bound uses `A^γ/p`, which is sharper at large primes. -/
theorem rootAuxiliary_prime_pow_le_A {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) (Q : ℤ[X]) {p : ℕ} (hp : p.Prime)
    (C ν : ℕ) (hρ : rootCount Q (p ^ ν) ≤ C) :
    rootAuxiliary A B ε γ Q (p ^ ν) ≤ (C : ℝ) * B * (A ^ γ / p) ^ ν := by
  have ha : auxiliaryLocal A B ε γ p ν ≤ B * A ^ (γ * ν) :=
    (auxiliaryLocal_le_geometric hA hB hε γ p ν).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_min hA (by positivity)) (min_le_left _ _) _) (zero_le_one.trans hB))
  rw [rootAuxiliary, auxiliary_prime_pow A B ε γ hp, Nat.cast_pow]
  calc
    _ ≤ ((B * A ^ (γ * ν)) * (C : ℝ)) / (p : ℝ) ^ ν := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul ha (by exact_mod_cast hρ) (Nat.cast_nonneg _)
        (mul_nonneg (zero_le_one.trans hB) (pow_nonneg hA _))
    _ = _ := by rw [pow_mul, div_pow]; ring

/-- A large-prime bound for the tilted series. -/
theorem tiltedRootAuxiliary_prime_pow_le_A {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) (Q : ℤ[X]) {p : ℕ} (hp : p.Prime)
    (C ν : ℕ) (hρ : rootCount Q (p ^ ν) ≤ C) :
    tiltedRootAuxiliary A B ε β γ Q (p ^ ν) ≤
      (C : ℝ) * B * (A ^ γ * (p : ℝ) ^ ((γ : ℝ) * β) / p) ^ ν := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have H := mul_le_mul_of_nonneg_right (rootAuxiliary_prime_pow_le_A hA hB hε γ Q hp C ν hρ)
    (Real.rpow_nonneg (Nat.cast_nonneg (p ^ ν)) ((γ : ℝ) * β))
  refine H.trans_eq ?_
  rw [Nat.cast_pow, ← Real.rpow_pow_comm hp₀.le, mul_assoc, ← mul_pow]
  congr 2
  ring

/-- First-prime-power contribution to the moment error. -/
theorem localMomentTerm_zero_le {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hβ : 0 ≤ β) (γ : ℕ) (Q : ℤ[X]) {p : ℕ} (hp : p.Prime)
    (C : ℕ) (hρ : rootCount Q p ≤ C) :
    localMomentTerm A B ε β γ Q p 0 ≤
      ((C : ℝ) * B * A ^ γ) * (((p : ℝ) ^ ((γ : ℝ) * β) - 1) / p) := by
  have hgap : 0 ≤ (p : ℝ) ^ ((γ : ℝ) * β) - 1 := sub_nonneg.mpr
    (Real.one_le_rpow (by exact_mod_cast hp.one_le) (mul_nonneg (Nat.cast_nonneg γ) hβ))
  have H := mul_le_mul_of_nonneg_right
    (rootAuxiliary_prime_pow_le_A hA hB hε γ Q hp C 1 (by simpa using hρ)) hgap
  simp only [localMomentTerm, zero_add, pow_one]
  calc
    _ ≤ ((C : ℝ) * B * (A ^ γ / p)) * ((p : ℝ) ^ ((γ : ℝ) * β) - 1) := by
      simpa only [pow_one] using H
    _ = _ := by ring

/-- The first-power part of the exponential moment is uniform in `z`. -/
theorem localMomentTerm_zero_sum_uniform {A B ε κ z : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z) (γ : ℕ) (Q : ℤ[X])
    (C : ℕ) (hρ : ∀ p, p.Prime → rootCount Q p ≤ C) :
    (∑ p ∈ (Finset.Icc 0 ⌊z⌋₊).filter Nat.Prime,
      localMomentTerm A B ε (κ / Real.log z) γ Q p 0) ≤
      ((C : ℝ) * B * A ^ γ) *
        (((γ : ℝ) * κ) * Real.exp ((γ : ℝ) * κ) * Real.log 4 * (1 + (Real.log 2)⁻¹)) := by
  have hlog : 0 < Real.log z := Real.log_pos (by linarith)
  calc
    _ ≤ ∑ p ∈ (Finset.Icc 0 ⌊z⌋₊).filter Nat.Prime,
        ((C : ℝ) * B * A ^ γ) * (((p : ℝ) ^ (((γ : ℝ) * κ) / Real.log z) - 1) / p) := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [mul_div_assoc] using localMomentTerm_zero_le hA hB hε
        (div_nonneg hκ hlog.le) γ Q (Finset.mem_filter.mp hp).2 C (hρ p (Finset.mem_filter.mp hp).2)
    _ = ((C : ℝ) * B * A ^ γ) *
        ∑ p ∈ (Finset.Icc 0 ⌊z⌋₊).filter Nat.Prime,
          ((p : ℝ) ^ (((γ : ℝ) * κ) / Real.log z) - 1) / p := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (prime_rpow_gap_sum_uniform hz (mul_nonneg (Nat.cast_nonneg γ) hκ)) (by positivity)

end NairTenenbaum
