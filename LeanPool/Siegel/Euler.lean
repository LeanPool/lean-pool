/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Siegel.Coeff
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Characters inducing the same character

`∏_{p ∣ n} (1 - 1/p) ≥ c(η) n^{-η}`, and if `χ₁ χ = 1` at level `N₁ N` then
`‖L(1,χ)‖ ≥ ‖L(1,χ₁)‖ (∏_{p ∣ N₁N} (1 - 1/p))²`.
-/

@[expose] public section

open Complex DirichletCharacter Finset

namespace SiegelThmLib

lemma one_sub_inv_nonneg {p : ℕ} (hp : p.Prime) : (0 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  rw [sub_nonneg]; exact inv_le_one_of_one_le₀ this

lemma half_le_one_sub_inv {p : ℕ} (hp : p.Prime) : (1 : ℝ) / 2 ≤ 1 - (p : ℝ)⁻¹ := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) this
  linarith

/-- `∏_{p ∣ n} (1 - 1/p) ≥ c n^{-η}`. -/
lemma prod_one_sub_inv_ge {η : ℝ} (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, n ≠ 0 →
      c * (n : ℝ) ^ (-η) ≤ ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = ⌈(2 : ℝ) ^ (1 / η)⌉₊ := ⟨_, rfl⟩
  refine ⟨(1 / 2) ^ P, by positivity, fun n hn => ?_⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ,
      g = fun p => (if p < P then (1 / 2 : ℝ) else 1) * (p : ℝ) ^ (-η) := ⟨_, rfl⟩
  have hle : ∀ p ∈ n.primeFactors, g p ≤ 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpr.one_lt.le
    have hrp : (p : ℝ) ^ (-η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
    have hhalf := half_le_one_sub_inv hpr
    simp only [hg]
    split_ifs with h
    · linarith
    · push Not at h
      have hPp : (2 : ℝ) ^ (1 / η) ≤ p :=
        (Nat.le_ceil _).trans (by rw [← hP]; exact_mod_cast h)
      have h2 : (2 : ℝ) ≤ (p : ℝ) ^ η := by
        have := Real.rpow_le_rpow (by positivity) hPp hη.le
        rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hη.ne', Real.rpow_one]
          at this
      have h3 : (p : ℝ) ^ (-η) ≤ 1 / 2 := by
        rw [Real.rpow_neg (by linarith), one_div]
        exact inv_anti₀ (by norm_num) h2
      linarith
  have hg0 : ∀ p ∈ n.primeFactors, 0 ≤ g p := by
    intro p hp
    simp only [hg]
    have : (0 : ℝ) ≤ (p : ℝ) ^ (-η) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    split_ifs <;> positivity
  have h1 := Finset.prod_le_prod₀ hg0 hle
  have h2 : ∏ p ∈ n.primeFactors, g p =
      (∏ p ∈ n.primeFactors, (if p < P then (1 / 2 : ℝ) else 1)) *
        (∏ p ∈ n.primeFactors, (p : ℝ)) ^ (-η) := by
    simp only [hg]
    rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
  have h3 : (1 / 2 : ℝ) ^ P ≤ ∏ p ∈ n.primeFactors, (if p < P then (1 / 2 : ℝ) else 1) := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    calc (n.primeFactors.filter (· < P)).card ≤ (range P).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter] at hp
          exact mem_range.mpr hp.2
      _ = P := card_range P
  have h4 : (n : ℝ) ^ (-η) ≤ (∏ p ∈ n.primeFactors, (p : ℝ)) ^ (-η) := by
    have hpos : (0 : ℝ) < ∏ p ∈ n.primeFactors, (p : ℝ) := by
      refine Finset.prod_pos fun p hp => ?_
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have hdvd : (∏ p ∈ n.primeFactors, p) ≤ n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
    have hdvd' : (∏ p ∈ n.primeFactors, (p : ℝ)) ≤ n := by
      have := (Nat.cast_le (α := ℝ)).mpr hdvd
      simpa [Nat.cast_prod] using this
    exact Real.rpow_le_rpow_of_nonpos hpos hdvd' (by linarith)
  have h5 : 0 ≤ (n : ℝ) ^ (-η) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc (1 / 2 : ℝ) ^ P * (n : ℝ) ^ (-η)
      ≤ (∏ p ∈ n.primeFactors, (if p < P then (1 / 2 : ℝ) else 1)) *
          (∏ p ∈ n.primeFactors, (p : ℝ)) ^ (-η) :=
        mul_le_mul h3 h4 h5 (Finset.prod_nonneg fun p _ => by split_ifs <;> norm_num)
    _ = ∏ p ∈ n.primeFactors, g p := h2.symm
    _ ≤ _ := h1

/-- Lower bound for a local Euler factor at `s = 1`. -/
lemma norm_euler_factor_ge {M : ℕ} (χ : DirichletCharacter ℂ M) (p : ℕ) :
    1 - (p : ℝ)⁻¹ ≤ ‖1 - χ p * (p : ℂ) ^ (-(1 : ℂ))‖ := by
  rw [cpow_neg_one]
  have h1 : ‖χ p * (p : ℂ)⁻¹‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, norm_inv, norm_natCast]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (Nat.cast_nonneg p)) (norm_le_one χ _)
  have h2 := norm_sub_norm_le (1 : ℂ) (χ p * (p : ℂ)⁻¹)
  rw [norm_one] at h2
  linarith

/-- Upper bound for a local Euler factor at `s = 1`. -/
lemma norm_euler_factor_le {M : ℕ} (χ : DirichletCharacter ℂ M) (p : ℕ) :
    ‖1 - χ p * (p : ℂ) ^ (-(1 : ℂ))‖ ≤ 1 + (p : ℝ)⁻¹ := by
  rw [cpow_neg_one]
  have h1 : ‖χ p * (p : ℂ)⁻¹‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, norm_inv, norm_natCast]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (Nat.cast_nonneg p)) (norm_le_one χ _)
  calc ‖1 - χ p * (p : ℂ)⁻¹‖ ≤ ‖(1 : ℂ)‖ + ‖χ p * (p : ℂ)⁻¹‖ := norm_sub_le _ _
    _ ≤ 1 + (p : ℝ)⁻¹ := by rw [norm_one]; linarith

lemma key_ineq {A B X Y E : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hn : A * X = B * Y)
    (hlow : E ≤ X) (hup : Y * E ≤ 1) : A * E ^ 2 ≤ B := by
  calc A * E ^ 2 = A * E * E := by ring
    _ ≤ A * X * E := by gcongr
    _ = B * (Y * E) := by rw [hn]; ring
    _ ≤ B * 1 := by gcongr
    _ = B := mul_one B

/-- The equivalent case: `χ₁ χ` principal at level `N₁ N`. -/
lemma equiv_case {N₁ N : ℕ} [NeZero N₁] [NeZero N] {χ₁ : DirichletCharacter ℂ N₁}
    {χ : DirichletCharacter ℂ N} (hχ₁ : χ₁ ≠ 1) (hχ : χ ≠ 1) (h : χ ^ 2 = 1)
    (hψ : prodChar χ₁ χ = 1) :
    ‖LFunction χ₁ 1‖ * (∏ p ∈ (N₁ * N).primeFactors, (1 - (p : ℝ)⁻¹)) ^ 2 ≤
      ‖LFunction χ 1‖ := by
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = changeLevel (dvd_mul_right N₁ N) χ₁ := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c, c = changeLevel (dvd_mul_left N N₁) χ := ⟨_, rfl⟩
  have hc2sq : c₂ * c₂ = 1 := by rw [← pow_two, hc₂, ← map_pow, h, map_one]
  have hprod : c₁ * c₂ = 1 := by rw [hc₁, hc₂, ← hψ]; rfl
  have hc : c₁ = c₂ := by
    calc c₁ = c₁ * (c₂ * c₂) := by rw [hc2sq, mul_one]
      _ = (c₁ * c₂) * c₂ := (mul_assoc _ _ _).symm
      _ = c₂ := by rw [hprod, one_mul]
  have hL := congrArg (fun c => LFunction c 1) hc
  simp only [hc₁, hc₂] at hL
  rw [LFunction_changeLevel _ _ (Or.inl hχ₁), LFunction_changeLevel _ _ (Or.inl hχ)] at hL
  have hn := congrArg norm hL
  simp only [norm_mul, norm_prod] at hn
  have hE0 : 0 ≤ ∏ p ∈ (N₁ * N).primeFactors, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_nonneg fun p hp => one_sub_inv_nonneg (Nat.prime_of_mem_primeFactors hp)
  have hlow : ∏ p ∈ (N₁ * N).primeFactors, (1 - (p : ℝ)⁻¹) ≤
      ∏ p ∈ (N₁ * N).primeFactors, ‖1 - χ₁ p * (p : ℂ) ^ (-(1 : ℂ))‖ :=
    Finset.prod_le_prod₀ (fun p hp => one_sub_inv_nonneg (Nat.prime_of_mem_primeFactors hp))
      (fun p _ => norm_euler_factor_ge χ₁ p)
  have hup : (∏ p ∈ (N₁ * N).primeFactors, ‖1 - χ p * (p : ℂ) ^ (-(1 : ℂ))‖) *
      ∏ p ∈ (N₁ * N).primeFactors, (1 - (p : ℝ)⁻¹) ≤ 1 := by
    have h1 : (∏ p ∈ (N₁ * N).primeFactors, ‖1 - χ p * (p : ℂ) ^ (-(1 : ℂ))‖) ≤
        ∏ p ∈ (N₁ * N).primeFactors, (1 + (p : ℝ)⁻¹) :=
      Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
        (fun p _ => norm_euler_factor_le χ p)
    have h2 : (∏ p ∈ (N₁ * N).primeFactors, (1 + (p : ℝ)⁻¹)) *
        ∏ p ∈ (N₁ * N).primeFactors, (1 - (p : ℝ)⁻¹) ≤ 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
      · have := one_sub_inv_nonneg (Nat.prime_of_mem_primeFactors hp)
        have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
        positivity
      · nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
    calc _ ≤ (∏ p ∈ (N₁ * N).primeFactors, (1 + (p : ℝ)⁻¹)) *
          ∏ p ∈ (N₁ * N).primeFactors, (1 - (p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right h1 hE0
      _ ≤ 1 := h2
  exact key_ineq (norm_nonneg _) (norm_nonneg _) hE0 hn hlow hup

end SiegelThmLib
