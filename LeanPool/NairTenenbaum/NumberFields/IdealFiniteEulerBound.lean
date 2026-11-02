/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.FiniteGeometricProduct
public import LeanPool.NairTenenbaum.NumberFields.IdealNormDirichlet

/-! # Finite ideal sums bounded by geometric Euler products -/

@[expose] public section

namespace NairTenenbaum

open Finset Real NumberField Ideal UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

/-- The multiplicative weight obtained by raising ideal norms to a real power. -/
noncomputable def idealNormWeightHom (σ : ℝ) : Ideal (𝓞 K) →* ℝ where
  toFun I := (Ideal.absNorm I : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' I J := by
    simp only [map_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

theorem ideal_eq_prod_factor_counts {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (S : Finset (Ideal (𝓞 K))) (hS : (normalizedFactors I).toFinset ⊆ S) :
    I = ∏ P ∈ S, P ^ (normalizedFactors I).count P := by
  classical
  have H := prod_normalizedFactors_eq hI
  rw [normalize_eq] at H
  exact H.symm.trans (prod_multiset_count_of_subset _ _ hS)

theorem idealNorm_prime_gt_one {P : Ideal (𝓞 K)} (hP : Prime P) :
    1 < Ideal.absNorm P := by
  have h₀ : Ideal.absNorm P ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]
    exact hP.ne_zero
  have h₁ : Ideal.absNorm P ≠ 1 := by
    rw [ne_eq, Ideal.absNorm_eq_one_iff]
    exact fun h => hP.not_isUnit (Ideal.isUnit_iff.mpr h)
  omega

theorem finite_idealNorm_sum_le_prod (T S : Finset (Ideal (𝓞 K)))
    (hT : ∀ I ∈ T, I ≠ ⊥) (hS : ∀ P ∈ S, Prime P)
    (hsupport : ∀ I ∈ T, (normalizedFactors I).toFinset ⊆ S) {σ : ℝ} (hσ : 0 < σ) :
    (∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-σ)) ≤
      ∏ P ∈ S, (1 - (Ideal.absNorm P : ℝ) ^ (-σ))⁻¹ := by
  classical
  let e (I : Ideal (𝓞 K)) (P : S) := (normalizedFactors I).count P.1
  have he : Set.InjOn e T := by
    intro I hI J hJ h
    rw [ideal_eq_prod_factor_counts (hT I hI) S (hsupport I hI),
      ideal_eq_prod_factor_counts (hT J hJ) S (hsupport J hJ)]
    apply prod_congr rfl
    intro P hP
    rw [show (normalizedFactors I).count P = (normalizedFactors J).count P from congrFun h ⟨P, hP⟩]
  have hw (P : S) : (Ideal.absNorm P.1 : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by
      exact_mod_cast idealNorm_prime_gt_one (hS P.1 P.2)) (by linarith)
  have H := finite_sum_geometric_product_le T e he
    (fun P : S => (Ideal.absNorm P.1 : ℝ) ^ (-σ))
    (fun P => Real.rpow_nonneg (Nat.cast_nonneg _) _) hw
  have HE (I : Ideal (𝓞 K)) (hI : I ∈ T) :
      (∏ P : S, ((Ideal.absNorm P.1 : ℝ) ^ (-σ)) ^ e I P) = (Ideal.absNorm I : ℝ) ^ (-σ) := by
    change (∏ P : S, idealNormWeightHom σ P.1 ^ (normalizedFactors I).count P.1) =
        idealNormWeightHom σ I
    simp only [← map_pow]
    rw [← map_prod]
    congr 1
    rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I).count P)]
    rw [← ideal_eq_prod_factor_counts (hT I hI) S (hsupport I hI)]
  rw [sum_congr rfl HE] at H
  simpa only [Finset.prod_coe_sort S (fun P => (1 - (Ideal.absNorm P : ℝ) ^ (-σ))⁻¹)] using H

theorem idealNorm_prime_weight_le_half {P : Ideal (𝓞 K)} (hP : Prime P)
    {σ : ℝ} (hσ : 1 ≤ σ) : (Ideal.absNorm P : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have hn : (2 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast idealNorm_prime_gt_one hP
  calc
    _ ≤ (Ideal.absNorm P : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ _ := by rw [Real.rpow_neg_one, ← one_div]; exact one_div_le_one_div_of_le (by norm_num) hn

theorem finite_idealNorm_sum_le_exp (T S : Finset (Ideal (𝓞 K)))
    (hT : ∀ I ∈ T, I ≠ ⊥) (hS : ∀ P ∈ S, Prime P)
    (hsupport : ∀ I ∈ T, (normalizedFactors I).toFinset ⊆ S) {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-σ)) ≤ Real.exp
      (∑ P ∈ S, ((Ideal.absNorm P : ℝ) ^ (-σ) + 2 * ((Ideal.absNorm P : ℝ) ^ (-σ)) ^ 2)) := by
  apply (finite_idealNorm_sum_le_prod T S hT hS hsupport (by linarith : 0 < σ)).trans
  rw [Real.exp_sum]
  apply prod_le_prod₀
  · intro P hP
    exact inv_nonneg.mpr (by linarith [idealNorm_prime_weight_le_half (hS P hP) hσ])
  · intro P hP
    exact one_sub_inv_le_exp_quadratic
      (idealNorm_prime_weight_le_half (hS P hP) hσ)

end NairTenenbaum
