/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Rectangular.Recursion
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Rectangular.Growth
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.RecursiveBlockPrograms
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.FieldCoefficientExtraction
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Rectangular.ComplexASI

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Rectangular matrix multiplication algorithms and their asymptotic exponents. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

namespace Arithmetic

variable {F : Type*} [Field F]

theorem rectangularAdmissibleExponent_of_rankAtMost
    {a b R : ℕ} (ha : 2 ≤ a) {k τ : ℝ} (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hRank : MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.matrixCoefficients
        (K := F) (Fin a) (Fin b) (Fin a)) R)
    (hτ : 0 ≤ τ) (hR : (R : ℝ) ≤ (a : ℝ) ^ τ)
    (hin : (a * b : ℕ) ≤ (a : ℝ) ^ τ)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) ^ τ) :
    RectangularAdmissibleExponent F k τ := by
  apply rectangularAdmissibleExponent_of_block_step
    (K := 2 * R * (2 * (a * b) + a ^ 2)) ha hk hab hτ hR hin hout
  · exact ⟨scalarAlgorithm F, scalarAlgorithm_correct F, (scalarAlgorithm_cost F).le⟩
  · intro m p P hP
    obtain ⟨Q, hQ, hcost⟩ := RecursiveBlock.rank_block_step hRank P hP
    refine ⟨Q, hQ, ?_⟩
    rw [hcost]
    nlinarith [Nat.zero_le (2 * R * (2 * (a * b) * m ^ 2 + a ^ 2 * (m * p)))]

theorem rectangular_rpow_omega_le_of_rankAtMost
    {a b R : ℕ} {B k : ℝ} (ha : 2 ≤ a) (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hRank : MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.matrixCoefficients
        (K := F) (Fin a) (Fin b) (Fin a)) R)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ B) (hin : (a * b : ℕ) ≤ B)
    (hR : (R : ℝ) ≤ B) :
    (a : ℝ) ^ rectangularOmega F k ≤ B := by
  have ha1 : 1 < (a : ℝ) := by exact_mod_cast (by omega : 1 < a)
  have ha0 : 0 < (a : ℝ) := lt_trans zero_lt_one ha1
  have hB : 0 < B := (sq_pos_of_pos ha0).trans_le hout
  have hpow : (a : ℝ) ^ Real.logb a B = B :=
    Real.rpow_logb ha0 (ne_of_gt ha1) hB
  have hτ : 2 ≤ Real.logb (a : ℝ) B := by
    apply (Real.le_logb_iff_rpow_le ha1 hB).mpr
    simpa only [Real.rpow_two] using hout
  have hadm := rectangularAdmissibleExponent_of_rankAtMost ha hk hab hRank
    (by linarith : 0 ≤ Real.logb (a : ℝ) B)
    (hR.trans_eq hpow.symm) (hin.trans_eq hpow.symm) (hout.trans_eq hpow.symm)
  exact (Real.rpow_le_rpow_of_exponent_le ha1.le
    (rectangularOmega_le_of_admissibleExponent hadm)).trans_eq hpow

theorem rectangular_rpow_omega_le_of_rank_growth
    {a b : ℕ} {q C k : ℝ} (ha : 2 ≤ a) (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ q) (hin : (a * b : ℕ) ≤ q)
    (R : ℕ → ℕ)
    (hRank : ∀ t, MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
        (Fin (a ^ t)) (Fin (b ^ t)) (Fin (a ^ t))) (R t))
    (hcost : ∀ t, (R t : ℝ) ≤ C * q ^ t) :
    (a : ℝ) ^ rectangularOmega F k ≤ q := by
  have ha0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have hq0 : 0 ≤ q := (sq_nonneg (a : ℝ)).trans hout
  apply power_le_of_forall_pow_le_mul_pow hq0 (C := max 1 C)
  intro t ht
  have hat : 2 ≤ a ^ t := ha.trans (le_self_pow (by omega) (Nat.ne_of_gt ht))
  have habt : ((a ^ t : ℕ) : ℝ) ^ k ≤ ((b ^ t : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow, ← Real.rpow_pow_comm ha0]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
  have hbase : ((a ^ t : ℕ) : ℝ) ^ (2 : ℕ) ≤ max 1 C * q ^ t := by
    calc
      ((a ^ t : ℕ) : ℝ) ^ (2 : ℕ) = ((a : ℝ) ^ (2 : ℕ)) ^ t := by
        rw [Nat.cast_pow, ← pow_mul, ← pow_mul, Nat.mul_comm t 2]
      _ ≤ q ^ t := by gcongr
      _ ≤ max 1 C * q ^ t := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C) (pow_nonneg hq0 t)
  have hinput : ((a ^ t * b ^ t : ℕ) : ℝ) ≤ max 1 C * q ^ t := by
    calc
      ((a ^ t * b ^ t : ℕ) : ℝ) = (((a * b : ℕ) : ℝ)) ^ t := by
        simp only [Nat.cast_mul, Nat.cast_pow, mul_pow]
      _ ≤ q ^ t := pow_le_pow_left₀ (Nat.cast_nonneg _) hin t
      _ ≤ max 1 C * q ^ t := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C) (pow_nonneg hq0 t)
  have hcost' : (R t : ℝ) ≤ max 1 C * q ^ t :=
    (hcost t).trans (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C)
      (pow_nonneg hq0 t))
  have h := rectangular_rpow_omega_le_of_rankAtMost hat hk habt
    (hRank t) hbase hinput hcost'
  simpa only [Nat.cast_pow, ← Real.rpow_pow_comm ha0] using h

theorem equalRectangular_inequality {a b L r : ℕ} {k : ℝ}
    (ha : 2 ≤ a) (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hbatch : MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin a))) r) :
    (L : ℝ) * (a : ℝ) ^ rectangularOmega F k ≤ (r : ℝ) := by
  by_cases hL0 : L = 0
  · subst L
    simp
  have hL : 0 < L := Nat.pos_of_ne_zero hL0
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by
    have hbR : (0 : ℝ) < (b : ℝ) :=
      (Real.rpow_pos_of_pos (by exact_mod_cast ha0) k).trans_le hab
    exact_mod_cast hbR
  have hlower := Tensor.rectangular_directSum_rank_lower ha0 hb0 hbatch
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hout : (a : ℝ) ^ (2 : ℕ) ≤ (r : ℝ) / (L : ℝ) := by
    apply (le_div_iff₀ hLR).mpr
    have hh : (L : ℝ) * (a : ℝ) ^ (2 : ℕ) ≤ (r : ℝ) := by exact_mod_cast hlower.1
    simpa only [mul_comm] using hh
  have hin : ((a * b : ℕ) : ℝ) ≤ (r : ℝ) / (L : ℝ) := by
    apply (le_div_iff₀ hLR).mpr
    have hh : (L : ℝ) * ((a * b : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hlower.2
    simpa only [mul_comm] using hh
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hq : 1 < (r : ℝ) / (L : ℝ) := by nlinarith
  have hcost := affine_recurrence_bound (fun t => (batchRank L r t : ℝ))
    ((r : ℝ) / (L : ℝ)) (r : ℝ) hq (Nat.cast_nonneg r)
    (fun t => batchRank_succ_le_affine hL r t)
  have hbound : (a : ℝ) ^ rectangularOmega F k ≤ (r : ℝ) / (L : ℝ) := by
    apply rectangular_rpow_omega_le_of_rank_growth
      (C := (batchRank L r 0 : ℝ) + (r : ℝ) / ((r : ℝ) / (L : ℝ) - 1))
      ha hk hab hout hin (batchRank L r)
    · exact Tensor.rectangular_pow_batchRank hL hbatch
    · intro t
      exact (hcost t).trans_eq (mul_comm _ _)
  simpa only [mul_comm] using (le_div_iff₀ hLR).mp hbound

theorem power_le_of_forall_pow_le_square_linear_mul_pow (d : ℕ) {x r : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ n : ℕ, 0 < n → x ^ n ≤ ((d * n + 1 : ℕ) : ℝ) ^ 2 * r ^ n) :
    x ≤ r := by
  apply power_le_of_forall_pow_le_linear_mul_pow (2 * d) hr
  intro n hn
  apply le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0)
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr n))
  have he := h (n * 2) (Nat.mul_pos hn (by decide))
  have hcount : d * (n * 2) + 1 = 2 * d * n + 1 := by ring
  simpa only [pow_mul, hcount, mul_pow] using he

theorem equalRectangular_inequality_of_polynomialApproximation
    {a b L r d D : ℕ} {k : ℝ}
    (ha : 2 ≤ a) (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (P : MatrixMultiplication.Foundation.Tensor.PolynomialApproximation
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin a))) r d D) :
    (L : ℝ) * (a : ℝ) ^ rectangularOmega F k ≤ (r : ℝ) := by
  apply power_le_of_forall_pow_le_square_linear_mul_pow d (Nat.cast_nonneg r)
  intro t ht
  have hat : 2 ≤ a ^ t := ha.trans (le_self_pow (by omega) (Nat.ne_of_gt ht))
  have habt : ((a ^ t : ℕ) : ℝ) ^ k ≤ ((b ^ t : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg a)]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
  have h := equalRectangular_inequality hat hk habt
    (Tensor.rectangular_directSum_power_rank (FieldCoefficientExtraction.rank_power P t))
  simpa only [Nat.cast_pow, Nat.cast_mul, mul_pow,
    ← Real.rpow_pow_comm (Nat.cast_nonneg a)] using h

theorem equalRectangular_log_inequality_of_polynomialApproximation
    {a b L r d D : ℕ} {k : ℝ}
    (ha : 2 ≤ a) (hL : 0 < L) (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (P : MatrixMultiplication.Foundation.Tensor.PolynomialApproximation
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin a))) r d D) :
    rectangularOmega F k * Real.log (a : ℝ) ≤ Real.log (r : ℝ) - Real.log (L : ℝ) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hpow := Real.rpow_pos_of_pos ha0 (rectangularOmega F k)
  have hbound := equalRectangular_inequality_of_polynomialApproximation ha hk hab P
  have hlog := Real.log_le_log (mul_pos hL0 hpow) hbound
  rw [Real.log_mul (ne_of_gt hL0) (ne_of_gt hpow), Real.log_rpow ha0] at hlog
  linarith

theorem equalSquare_inequality_of_polynomialApproximation
    {n L r d D : ℕ} (hn : 1 ≤ n)
    (P : MatrixMultiplication.Foundation.Tensor.PolynomialApproximation
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin n) (Fin n) (Fin n))) r d D) :
    (L : ℝ) * (n : ℝ) ^ omega F ≤ (r : ℝ) := by
  by_cases hn1 : n = 1
  · subst n
    simp only [Nat.cast_one, Real.one_rpow, mul_one]
    apply power_le_of_forall_pow_le_square_linear_mul_pow d (Nat.cast_nonneg r)
    intro t ht
    have hrank := Tensor.rectangular_directSum_power_rank
      (FieldCoefficientExtraction.rank_power P t)
    have hlower := MatrixMultiplication.Foundation.Tensor.directSum_square_rank_lower
      (L ^ t) (1 ^ t) ((d * t + 1) ^ 2 * r ^ t) (by simp) hrank
    have hcast := (Nat.cast_le (α := ℝ)).mpr hlower
    simpa only [one_pow, mul_one, Nat.cast_mul, Nat.cast_pow] using hcast
  · have h := equalRectangular_inequality_of_polynomialApproximation
      (by omega : 2 ≤ n) (by norm_num : (0 : ℝ) ≤ 1)
      (by simp : (n : ℝ) ^ (1 : ℝ) ≤ (n : ℝ)) P
    simpa only [rectangularOmega_one] using h

theorem equalVolume_inequality_of_polynomialApproximation
    {a b c L r d D : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (P : MatrixMultiplication.Foundation.Tensor.PolynomialApproximation
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin c))) r d D) :
    (L : ℝ) * ((a * b * c : ℕ) : ℝ) ^ (omega F / 3) ≤ (r : ℝ) := by
  let tags : Fin (L ^ 3) ≃ (Fin L × Fin L) × Fin L :=
    Fintype.equivOfCardEq (by simp [pow_succ])
  let indices : Fin (a * b * c) ≃ Fin a × Fin b × Fin c :=
    Fintype.equivOfCardEq (by simp [mul_assoc])
  have Q := P.matrixCoefficientsDirectSumSymmetrized.matrixCoefficientsDirectSumOfInjective
    tags tags.injective indices indices.injective
  have h := equalSquare_inequality_of_polynomialApproximation
    (Nat.mul_pos (Nat.mul_pos ha hb) hc) Q
  apply mul_rpow_third_le_of_cube (Nat.cast_nonneg (a * b * c)) (Nat.cast_nonneg r)
  simpa only [Nat.cast_pow] using h

end Arithmetic
end MatrixMultiplication

end

end MatrixMultiplicationAllFields
