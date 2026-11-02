/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyIntegratedBound

/-! # An elementary pole bound for the logarithmically weighted prime series

Logarithmic intervals and Chebyshev's bound give `P(σ)≪deg(Q)/(σ−1)`.
The leading constant is not asserted to be one. The exact integrating factor
allows this elementary bound to be used separately from sharp bounds on `R`.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

theorem log_div_rpow_le_log_bin {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1 < σ) :
    Real.log p / (p : ℝ) ^ σ ≤ (Real.log p / p) * Real.exp (-(σ - 1)) ^ ⌊Real.log p⌋₊ := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  calc
    _ = (Real.log p / p) * Real.exp (Real.log p * (-(σ - 1))) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hp₀.le,
        show -σ = -1 + (-(σ - 1)) by ring, Real.rpow_add hp₀,
        Real.rpow_neg_one, Real.rpow_def_of_pos hp₀]
      ring
    _ ≤ (Real.log p / p) * Real.exp ((⌊Real.log p⌋₊ : ℝ) * (-(σ - 1))) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (div_nonneg hl hp₀.le)
      exact mul_le_mul_of_nonpos_right (Nat.floor_le hl) (by linarith)
    _ = _ := by rw [Real.exp_nat_mul]

theorem prime_log_power_sum_le_geometric (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {σ : ℝ} (hσ : 1 < σ) :
    (∑ p ∈ S, Real.log p / (p : ℝ) ^ σ) ≤
      (Real.log 4 * Real.exp 2) / (1 - Real.exp (-(σ - 1))) := by
  let r := Real.exp (-(σ - 1))
  let k : ℕ → ℕ := fun p => ⌊Real.log p⌋₊
  have hr₀ : 0 ≤ r := Real.exp_nonneg _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hbin (j : ℕ) : (∑ p ∈ S.filter (fun p => k p = j), Real.log p / p) ≤
      Real.log 4 * Real.exp 2 := by
    apply le_trans _ (prime_log_mass_log_interval S hS (j : ℝ))
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpS, hpj⟩ := mem_filter.mp hp
      have hfloor := Nat.floor_le (Real.log_natCast_nonneg p)
      have hceil := Nat.lt_floor_add_one (Real.log p)
      change ⌊Real.log p⌋₊ = j at hpj
      rw [hpj] at hfloor hceil
      exact mem_filter.mpr ⟨hpS, hfloor, by linarith⟩
    · intro p hp _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  calc
    _ ≤ ∑ p ∈ S, (Real.log p / p) * r ^ k p :=
      sum_le_sum (fun p hp => log_div_rpow_le_log_bin (hS p hp) hσ)
    _ = ∑ j ∈ S.image k, ∑ p ∈ S.filter (fun p => k p = j), (Real.log p / p) * r ^ k p :=
      (sum_fiberwise_of_maps_to (fun p hp => mem_image_of_mem k hp) _).symm
    _ = ∑ j ∈ S.image k, (∑ p ∈ S.filter (fun p => k p = j), Real.log p / p) * r ^ j := by
      apply sum_congr rfl
      intro j _
      rw [sum_mul]
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ ≤ ∑ j ∈ S.image k, (Real.log 4 * Real.exp 2) * r ^ j :=
      sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hbin j) (pow_nonneg hr₀ _))
    _ = (Real.log 4 * Real.exp 2) * ∑ j ∈ S.image k, r ^ j := (mul_sum _ _ _).symm
    _ ≤ (Real.log 4 * Real.exp 2) * ∑' j : ℕ, r ^ j :=
      mul_le_mul_of_nonneg_left ((summable_geometric_of_lt_one hr₀ hr₁).sum_le_tsum _
        (fun j _ => pow_nonneg hr₀ j)) (by positivity)
    _ = _ := by rw [tsum_geometric_of_lt_one hr₀ hr₁]; rfl

theorem geometric_exp_inv_le_two_div {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    (1 - Real.exp (-u))⁻¹ ≤ 2 / u := by
  have hr₀ := Real.exp_pos (-u)
  have hr₁ : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have H := mul_le_mul_of_nonneg_right (Real.add_one_le_exp u) hr₀.le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at H
  have huR : u ≤ 2 * (1 - Real.exp (-u)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu₁) (sub_pos.mpr hr₁).le]
  rw [inv_eq_one_div]
  exact (div_le_div_iff₀ (sub_pos.mpr hr₁) hu).mpr (by linarith)

theorem rootPrimeDirichletSum_le_pole {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {σ : ℝ} (hσ : 1 < σ) (hσ₂ : σ ≤ 2) :
    rootPrimeDirichletSum Q σ ≤
      (2 * (Q.natDegree : ℝ) * (Real.log 4 * Real.exp 2)) / (σ - 1) := by
  apply Real.tsum_le_of_sum_le (fun p => rootPrimeLogWeight_nonneg Q σ p.2)
  intro S
  have hinj : Set.InjOn (fun p : Nat.Primes => p.1) (↑S : Set Nat.Primes) :=
    fun _ _ _ _ h => Subtype.ext h
  have H := prime_log_power_sum_le_geometric (S.image (fun p => p.1))
    (by intro p hp; obtain ⟨r, _, rfl⟩ := mem_image.mp hp; exact r.2) hσ
  rw [sum_image hinj] at H
  calc
    _ ≤ ∑ p ∈ S, (Q.natDegree : ℝ) * (Real.log p.1 / (p.1 : ℝ) ^ σ) := by
      apply sum_le_sum
      intro p _
      unfold rootPrimeLogWeight
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast rootCount_le_degree hQ p.2)
        (div_nonneg (Real.log_natCast_nonneg p.1) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    _ = (Q.natDegree : ℝ) * ∑ p ∈ S, Real.log p.1 / (p.1 : ℝ) ^ σ := (mul_sum _ _ _).symm
    _ ≤ (Q.natDegree : ℝ) * ((Real.log 4 * Real.exp 2) / (1 - Real.exp (-(σ - 1)))) :=
      mul_le_mul_of_nonneg_left H (Nat.cast_nonneg _)
    _ ≤ (Q.natDegree : ℝ) * ((Real.log 4 * Real.exp 2) * (2 / (σ - 1))) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (geometric_exp_inv_le_two_div (by
        linarith) (by linarith)) (by positivity)
    _ = _ := by ring

/-- With the exact integrating factor, an elementary pole bound suffices
for the logarithmically weighted prime series. Only `R(σ)` remains in the
exponential factor. -/
theorem hooleyReducedMomentMajorant_le_pole {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} {q : ℕ} (hq : 2 < q) (htq : t ≤ q) (hσ : 1 < σ) (hσ₂ : σ ≤ 2) :
    hooleyReducedMomentMajorant Q t q σ ≤
      (hooleyPrimeErrorConstant Q q ^ (t / q) / ((q : ℝ) - 1)) *
        (2 * (Q.natDegree : ℝ) * (Real.log 4 * Real.exp 2)) ^ (1 - t / q) *
        (σ - 1) ^ (t / q - 1) *
        Real.exp (((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1) * rootPrimePowerSum Q σ) := by
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have hθ : 0 ≤ 1 - t / q := sub_nonneg.mpr ((div_le_one (by linarith : (0 : ℝ) < q)).mpr htq)
  have hP := Real.rpow_le_rpow (rootPrimeDirichletSum_nonneg Q σ)
    (rootPrimeDirichletSum_le_pole hQ hσ hσ₂) hθ
  have hpow :
      ((2 * (Q.natDegree : ℝ) * (Real.log 4 * Real.exp 2)) / (σ - 1)) ^ (1 - t / q) =
        (2 * (Q.natDegree : ℝ) * (Real.log 4 * Real.exp 2)) ^ (1 - t / q) *
          (σ - 1) ^ (t / q - 1) := by
    rw [Real.div_rpow (by positivity) (by linarith : 0 ≤ σ - 1), div_eq_mul_inv,
      ← Real.rpow_neg (by linarith : 0 ≤ σ - 1)]
    congr 2
    ring
  rw [hpow] at hP
  unfold hooleyReducedMomentMajorant
  calc
    _ ≤ (hooleyPrimeErrorConstant Q q ^ (t / q) / ((q : ℝ) - 1)) *
        ((2 * (Q.natDegree : ℝ) * (Real.log 4 * Real.exp 2)) ^ (1 - t / q) *
          (σ - 1) ^ (t / q - 1)) *
        Real.exp (((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1) * rootPrimePowerSum Q σ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul_of_nonneg_left hP (div_nonneg
        (Real.rpow_nonneg (hooleyPrimeErrorConstant_nonneg Q q) _) (by linarith))
    _ = _ := by ring

end NairTenenbaum
