/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.Positivity
public import LeanPool.Siegel.CharSum

/-!
# Non-negative coefficients of `ζ(s) L(s,χ₁) L(s,χ₂) L(s,χ₁χ₂)`

For real characters `χ₁` (mod `N₁`) and `χ₂` (mod `N₂`), `ψ = χ₁χ₂` (mod `N₁N₂`), the Dirichlet
coefficients `a = ζ * χ₁ * χ₂ * ψ` are non-negative reals with `a 1 = 1`.
-/

@[expose] public section

open ArithmeticFunction DirichletCharacter LSeries Finset

open scoped ComplexOrder LSeries.notation ArithmeticFunction.zeta

namespace SiegelThmLib

/-- Value of a character of lower level after `changeLevel`, at a natural number. -/
lemma changeLevel_natCast {M K : ℕ} (h : M ∣ K) (χ : DirichletCharacter ℂ M) (n : ℕ) :
    changeLevel h χ (n : ZMod K) = if n.Coprime K then χ n else 0 := by
  split_ifs with hc
  · have hu : IsUnit (n : ZMod K) := (ZMod.isUnit_iff_coprime n K).mpr hc
    have := changeLevel_eq_cast_of_dvd χ h hu.unit
    simp only [IsUnit.unit_spec] at this
    rw [this, ZMod.cast_natCast h]
  · exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])

lemma eq_zero_of_not_coprime {M : ℕ} (χ : DirichletCharacter ℂ M) {n : ℕ}
    (h : ¬ n.Coprime M) : χ n = 0 :=
  MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])

variable {N₁ N₂ : ℕ}

/-- The product character `χ₁ χ₂` at level `N₁ N₂`. -/
noncomputable def prodChar (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    DirichletCharacter ℂ (N₁ * N₂) :=
  changeLevel (dvd_mul_right N₁ N₂) χ₁ * changeLevel (dvd_mul_left N₂ N₁) χ₂

lemma prodChar_apply (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) (n : ℕ) :
    prodChar χ₁ χ₂ n = χ₁ n * χ₂ n := by
  rw [prodChar, MulChar.coeToFun_mul, Pi.mul_apply, changeLevel_natCast, changeLevel_natCast]
  by_cases hc : n.Coprime (N₁ * N₂)
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc, zero_mul]
    rw [Nat.coprime_mul_iff_right, not_and_or] at hc
    rcases hc with hc | hc
    · rw [eq_zero_of_not_coprime χ₁ hc, zero_mul]
    · rw [eq_zero_of_not_coprime χ₂ hc, mul_zero]

lemma prodChar_sq {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) : prodChar χ₁ χ₂ ^ 2 = 1 := by
  rw [prodChar, mul_pow, ← map_pow, ← map_pow, h₁, h₂, map_one, map_one, one_mul]

/-! ### Values at prime powers -/

lemma mul_apply_prime_pow (f g : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ i ∈ range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => f x * g y),
    Nat.sum_divisors_prime_pow hp]
  refine sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (by have := mem_range.mp hi; omega) hp.pos]

lemma toArith_prime_pow {M : ℕ} (χ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    toArithmeticFunction (χ ·) (p ^ k) = χ p ^ k := by
  rw [← apply_eq_toArithmeticFunction_apply χ (pow_ne_zero k hp.ne_zero), Nat.cast_pow,
    map_pow]

lemma geom_nonneg {z : ℂ} (hz : z = 0 ∨ z = 1 ∨ z = -1) (j : ℕ) :
    0 ≤ ∑ t ∈ range (j + 1), z ^ t := by
  rcases hz with rfl | rfl | rfl
  · exact sum_nonneg fun t _ => pow_nonneg le_rfl t
  · exact sum_nonneg fun t _ => by simp
  · rw [neg_one_geom_sum]; split_ifs <;> simp

/-- The local factor `∑_{t ≤ j} u^t (uv)^{j-t}` is non-negative when `u ∈ {0, 1}`
or `u = v = -1` (with `v ∈ {0, ±1}`). -/
lemma local_nonneg {u v : ℂ} (hv : v = 0 ∨ v = 1 ∨ v = -1)
    (hu : u = 0 ∨ u = 1 ∨ (u = -1 ∧ v = -1)) (j : ℕ) :
    0 ≤ ∑ t ∈ range (j + 1), u ^ t * (u * v) ^ (j - t) := by
  rcases hu with rfl | rfl | ⟨rfl, rfl⟩
  · exact sum_nonneg fun t _ => mul_nonneg (pow_nonneg le_rfl t) (pow_nonneg (by simp) _)
  · simp only [one_pow, one_mul]
    have := sum_range_reflect (fun t => v ^ t) (j + 1)
    simp only [add_tsub_cancel_right] at this
    rw [this]
    exact geom_nonneg hv j
  · simp only [mul_neg, mul_one, neg_neg, one_pow, mul_one]
    exact geom_nonneg (Or.inr (Or.inr rfl)) j

/-! ### The coefficient sequence -/


/-- The arithmetic function `χ ↦ (n ↦ χ n)`. -/
noncomputable abbrev X {M : ℕ} (χ : DirichletCharacter ℂ M) : ArithmeticFunction ℂ :=
  toArithmeticFunction (χ ·)

/-- `a = ζ * χ₁ * χ₂ * χ₁χ₂`. -/
noncomputable def coeff (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    ArithmeticFunction ℂ :=
  zetaMul χ₁ * (X χ₂ * X (prodChar χ₁ χ₂))

lemma coeff_eq' (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    coeff χ₁ χ₂ = zetaMul χ₂ * (X χ₁ * X (prodChar χ₁ χ₂)) := by
  simp only [coeff, zetaMul]; ring

lemma isMultiplicative_coeff (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    (coeff χ₁ χ₂).IsMultiplicative :=
  (isMultiplicative_zetaMul χ₁).mul ((isMultiplicative_toArithmeticFunction χ₂).mul
    (isMultiplicative_toArithmeticFunction _))

lemma coeff_one (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    coeff χ₁ χ₂ 1 = 1 :=
  (isMultiplicative_coeff χ₁ χ₂).map_one

/-- `(χ_b * ψ)(p^j) = ∑ χ_b(p)^t ψ(p)^{j-t}` with `ψ(p) = χ_b(p) χ_c(p)`. -/
lemma XX_prime_pow {M K : ℕ} (χb : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ K)
    {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (X χb * X ψ) (p ^ j) = ∑ t ∈ range (j + 1), χb p ^ t * ψ p ^ (j - t) := by
  rw [mul_apply_prime_pow _ _ hp]
  refine sum_congr rfl fun t _ => ?_
  rw [toArith_prime_pow _ hp, toArith_prime_pow _ hp]

lemma coeff_prime_pow_nonneg {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ coeff χ₁ χ₂ (p ^ k) := by
  have hx := val_cases h₁ (p : ZMod N₁)
  have hy := val_cases h₂ (p : ZMod N₂)
  have hψ : prodChar χ₁ χ₂ p = χ₁ p * χ₂ p := prodChar_apply χ₁ χ₂ p
  by_cases hcase : χ₂ p = 0 ∨ χ₂ p = 1 ∨ (χ₂ p = -1 ∧ χ₁ p = -1)
  · rw [coeff, mul_apply_prime_pow _ _ hp]
    refine sum_nonneg fun i _ => mul_nonneg (zetaMul_nonneg h₁ _) ?_
    rw [XX_prime_pow _ _ hp, hψ]
    have := local_nonneg hx hcase (k - i)
    simpa only [mul_comm (χ₂ p) (χ₁ p)] using this
  · have hx' : χ₁ p = 0 ∨ χ₁ p = 1 ∨ (χ₁ p = -1 ∧ χ₂ p = -1) := by
      rcases hx with h | h | h <;> rcases hy with h' | h' | h' <;>
        (try norm_num [h, h'] at hcase) <;> (try norm_num [h, h'])
    rw [coeff_eq', mul_apply_prime_pow _ _ hp]
    refine sum_nonneg fun i _ => mul_nonneg (zetaMul_nonneg h₂ _) ?_
    rw [XX_prime_pow _ _ hp, hψ]
    exact local_nonneg hy hx' (k - i)

/-- The coefficients are non-negative reals. -/
lemma coeff_nonneg {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) (n : ℕ) : 0 ≤ coeff χ₁ χ₂ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [(isMultiplicative_coeff χ₁ χ₂).multiplicative_factorization _ hn] using!
      Finset.prod_nonneg
        fun p hp => coeff_prime_pow_nonneg h₁ h₂ (Nat.prime_of_mem_primeFactors hp) _

/-! ### The L-series -/

variable [NeZero N₁] [NeZero N₂]

lemma LSeriesSummable_X {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable ↗(X χ) s :=
  (LSeriesSummable_congr _ fun h => (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
    ZMod.LSeriesSummable_of_one_lt_re χ hs

lemma LSeries_X {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(X χ) s = LFunction χ s := by
  rw [LFunction_eq_LSeries χ hs]
  exact (LSeries_congr (fun h => χ.apply_eq_toArithmeticFunction_apply h) s).symm

lemma LSeriesSummable_coeff (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable ↗(coeff χ₁ χ₂) s :=
  LSeriesSummable_mul (LSeriesSummable_zetaMul χ₁ hs)
    (LSeriesSummable_mul (LSeriesSummable_X χ₂ hs) (LSeriesSummable_X _ hs))

lemma abscissa_coeff_le (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    abscissaOfAbsConv ↗(coeff χ₁ χ₂) ≤ ((1 : ℝ) : EReal) :=
  abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_coeff χ₁ χ₂ (by simpa using hy)

/-- `∑ aₙ n^{-s} = ζ(s) · L(s,χ₁) L(s,χ₂) L(s,χ₁χ₂)` for `Re s > 1`. -/
lemma LSeries_coeff (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries ↗(coeff χ₁ χ₂) s = LSeries 1 s *
      (LFunction χ₁ s * LFunction χ₂ s * LFunction (prodChar χ₁ χ₂) s) := by
  have hzs : LSeriesSummable ↗((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) s :=
    LSeriesSummable_zeta_iff.mpr hs
  have hz : LSeries ↗((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) s = LSeries 1 s :=
    congrFun LSeries_zeta_eq s
  rw [coeff, zetaMul, LSeries_mul' (LSeriesSummable_mul hzs (LSeriesSummable_X χ₁ hs))
    (LSeriesSummable_mul (LSeriesSummable_X χ₂ hs) (LSeriesSummable_X _ hs)),
    LSeries_mul' hzs (LSeriesSummable_X χ₁ hs),
    LSeries_mul' (LSeriesSummable_X χ₂ hs) (LSeriesSummable_X _ hs), hz, LSeries_X χ₁ hs,
    LSeries_X χ₂ hs, LSeries_X _ hs]
  ring

end SiegelThmLib
