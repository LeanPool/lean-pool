/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Growth
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Exponent
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexAsymptoticRecurrence
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexBatchCeiling
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialPowerGrowth
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorFlattening
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.GCongr

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite coefficient tensors and their algebraic transformations. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.Foundation

namespace Tensor

theorem matrixCoefficients_rank_of_injective {K A B : Type*} [CommSemiring K]
    [DecidableEq A] [DecidableEq B] {R : ℕ}
    (h : RankAtMost (matrixCoefficients (K := K) A A A) R)
    (f : B → A) (hf : Function.Injective f) :
    RankAtMost (matrixCoefficients (K := K) B B B) R := by
  have hp := h.pullback (fun x : B × B => (f x.1, f x.2))
    (fun y : B × B => (f y.1, f y.2))
    (fun z : B × B => (f z.1, f z.2))
  convert hp using 1
  funext x y z
  simp only [pullback, matrixCoefficients, hf.eq_iff]

theorem matrixCoefficients_directSum_rank_of_injective
    {K ι κ A B : Type*} [CommSemiring K]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq A] [DecidableEq B] {R : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A A A)) R)
    (f : κ → ι) (hf : Function.Injective f) (g : B → A) (hg : Function.Injective g) :
    RankAtMost (directSum (fun _ : κ => matrixCoefficients (K := K) B B B)) R := by
  have hp := h.pullback
    (fun x : κ × (B × B) => (f x.1, (g x.2.1, g x.2.2)))
    (fun y : κ × (B × B) => (f y.1, (g y.2.1, g y.2.2)))
    (fun z : κ × (B × B) => (f z.1, (g z.2.1, g z.2.2)))
  convert hp using 1
  funext x y z
  simp only [pullback, directSum, matrixCoefficients, hf.eq_iff, hg.eq_iff]

theorem matrixCoefficients_directSum_power_rank {K : Type*} [CommSemiring K]
    {n k R t : ℕ}
    (h : RankAtMost (power (directSum
      (fun _ : Fin k => matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n))) t) R) :
    RankAtMost (directSum (fun _ : Fin (k ^ t) =>
      matrixCoefficients (K := K) (Fin (n ^ t)) (Fin (n ^ t)) (Fin (n ^ t)))) R := by
  have hmatrix := matrixCoefficients_directSum_rank_of_power h
  let tags : Fin (k ^ t) ≃ (Fin t → Fin k) := Fintype.equivOfCardEq (by simp)
  let indices : Fin (n ^ t) ≃ (Fin t → Fin n) := Fintype.equivOfCardEq (by simp)
  exact matrixCoefficients_directSum_rank_of_injective hmatrix
    tags tags.injective indices indices.injective

theorem PolynomialApproximation.square_directSum_power_rank
    {n k r d D : ℕ}
    (A : PolynomialApproximation
      (directSum (fun _ : Fin k => matrixMultiplication n n n)) r d D) (t : ℕ) :
    RankAtMost (directSum (fun _ : Fin (k ^ t) =>
      matrixMultiplication (n ^ t) (n ^ t) (n ^ t))) ((D * t + 1) * r ^ t) :=
  matrixCoefficients_directSum_power_rank (A.rank_power t)

theorem matrixCoefficients_fin_one_rank {K : Type*} [CommSemiring K] :
    RankAtMost (matrixCoefficients (K := K) (Fin 1) (Fin 1) (Fin 1)) 1 := by
  have heq : matrixCoefficients (K := K) (Fin 1) (Fin 1) (Fin 1) =
      rankOne (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
    funext x y z
    have hxy : x.2 = y.1 := Subsingleton.elim _ _
    have hyz : y.2 = z.1 := Subsingleton.elim _ _
    have hzx : z.2 = x.1 := Subsingleton.elim _ _
    simp [matrixCoefficients, rankOne, hxy, hyz, hzx]
  rw [heq]
  exact rankOne_rankAtMost _ _ _

theorem matrixCoefficients_pow_batchRank {K : Type*} [CommSemiring K]
    {n k r : ℕ} (hk : 0 < k)
    (hbatch : RankAtMost
      (directSum (fun _ : Fin k => matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n))) r) :
    ∀ t : ℕ, RankAtMost
      (matrixCoefficients (K := K) (Fin (n ^ t)) (Fin (n ^ t)) (Fin (n ^ t)))
      (batchRank k r t) := by
  intro t
  induction t with
  | zero => exact matrixCoefficients_fin_one_rank (K := K)
  | succ t ih =>
    let e : Fin (n ^ (t + 1)) ≃ Fin (n ^ t) × Fin n :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    have hp := matrixCoefficients_batch_rank_ceiling ih hbatch hk
    have hr := matrixCoefficients_rank_of_injective hp e e.injective
    simpa only [batchRank_succ] using hr

end Tensor

namespace Arithmetic

theorem rpow_omega_le_of_rankAtMost {n R : ℕ} {B : ℝ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R)
    (hquad : (n : ℝ) ^ 2 ≤ B) (hR : (R : ℝ) ≤ B) :
    (n : ℝ) ^ omega ≤ B := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn0 : 0 < (n : ℝ) := lt_trans zero_lt_one hn1
  have hB : 0 < B := (sq_pos_of_pos hn0).trans_le hquad
  have hpow : (n : ℝ) ^ Real.logb n B = B :=
    Real.rpow_logb hn0 (ne_of_gt hn1) hB
  have hτ : 2 ≤ Real.logb (n : ℝ) B := by
    apply (Real.le_logb_iff_rpow_le hn1 hB).mpr
    simpa only [Real.rpow_two] using hquad
  have hadmissible := admissibleExponent_of_rankAtMost hn hRank hτ (hR.trans_eq hpow.symm)
  exact (Real.rpow_le_rpow_of_exponent_le hn1.le
    (omega_le_of_admissibleExponent hadmissible)).trans_eq hpow

theorem rpow_omega_le_of_rank_growth {n : ℕ} {q C : ℝ} (hn : 2 ≤ n)
    (hquad : (n : ℝ) ^ 2 ≤ q) (R : ℕ → ℕ)
    (hRank : ∀ t : ℕ, Tensor.RankAtMost
      (Tensor.matrixMultiplication (n ^ t) (n ^ t) (n ^ t)) (R t))
    (hcost : ∀ t : ℕ, (R t : ℝ) ≤ C * q ^ t) :
    (n : ℝ) ^ omega ≤ q := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hq0 : 0 ≤ q := (sq_nonneg (n : ℝ)).trans hquad
  apply power_le_of_forall_pow_le_mul_pow hq0 (C := max 1 C)
  intro t ht
  have hnt : 2 ≤ n ^ t := hn.trans (le_self_pow (by omega) (Nat.ne_of_gt ht))
  have hbase : ((n ^ t : ℕ) : ℝ) ^ 2 ≤ max 1 C * q ^ t := by
    calc
      ((n ^ t : ℕ) : ℝ) ^ 2 = ((n : ℝ) ^ 2) ^ t := by
        rw [Nat.cast_pow, ← pow_mul, ← pow_mul, Nat.mul_comm t 2]
      _ ≤ q ^ t := by gcongr
      _ ≤ max 1 C * q ^ t := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C) (pow_nonneg hq0 t)
  have hcost' : (R t : ℝ) ≤ max 1 C * q ^ t :=
    (hcost t).trans (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C)
      (pow_nonneg hq0 t))
  have h := rpow_omega_le_of_rankAtMost hnt (hRank t) hbase hcost'
  simpa only [Nat.cast_pow, ← Real.rpow_pow_comm hn0] using h

theorem equalSummand_inequality_of_quadratic_bound {n k r : ℕ}
    (hn : 2 ≤ n) (hk : 0 < k)
    (hbatch : Tensor.RankAtMost
      (Tensor.directSum (fun _ : Fin k => Tensor.matrixMultiplication n n n)) r)
    (hquad : (n : ℝ) ^ 2 ≤ (r : ℝ) / (k : ℝ)) :
    (k : ℝ) * (n : ℝ) ^ omega ≤ (r : ℝ) := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 1 < (r : ℝ) / (k : ℝ) := by nlinarith
  have hRank := Tensor.matrixCoefficients_pow_batchRank hk hbatch
  have hcost := affine_recurrence_bound (fun t => (batchRank k r t : ℝ))
    ((r : ℝ) / (k : ℝ)) (r : ℝ) hq (Nat.cast_nonneg r)
    (fun t => batchRank_succ_le_affine hk r t)
  have hbound : (n : ℝ) ^ omega ≤ (r : ℝ) / (k : ℝ) := by
    apply rpow_omega_le_of_rank_growth
      (C := (batchRank k r 0 : ℝ) + (r : ℝ) / ((r : ℝ) / (k : ℝ) - 1))
      hn hquad (batchRank k r)
    · exact hRank
    · intro t
      exact (hcost t).trans_eq (mul_comm _ _)
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  simpa only [mul_comm] using (le_div_iff₀ hkreal).mp hbound

theorem equalSummand_inequality {n k r : ℕ} (hn : 1 ≤ n)
    (hbatch : Tensor.RankAtMost
      (Tensor.directSum (fun _ : Fin k => Tensor.matrixMultiplication n n n)) r) :
    (k : ℝ) * (n : ℝ) ^ omega ≤ (r : ℝ) := by
  have hlower := Tensor.directSum_square_rank_lower k n r (by omega) hbatch
  by_cases hn1 : n = 1
  · subst n
    simpa only [Nat.cast_one, Real.one_rpow, mul_one, one_pow] using
      (show (k : ℝ) ≤ (r : ℝ) by exact_mod_cast (by simpa using hlower : k ≤ r))
  by_cases hk0 : k = 0
  · subst k
    simp
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  apply equalSummand_inequality_of_quadratic_bound (by omega) hk hbatch
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  apply (le_div_iff₀ hkreal).mpr
  have hlower_real : (k : ℝ) * (n : ℝ) ^ 2 ≤ (r : ℝ) := by exact_mod_cast hlower
  simpa only [mul_comm] using hlower_real

theorem equalSummand_inequality_of_polynomialApproximation {n k r d D : ℕ}
    (hn : 1 ≤ n)
    (A : Tensor.PolynomialApproximation
      (Tensor.directSum (fun _ : Fin k => Tensor.matrixMultiplication n n n)) r d D) :
    (k : ℝ) * (n : ℝ) ^ omega ≤ (r : ℝ) := by
  apply power_le_of_forall_pow_le_linear_mul_pow D (Nat.cast_nonneg r)
  intro t ht
  have hnt : 1 ≤ n ^ t := pow_pos (by omega : 0 < n) t
  have h := equalSummand_inequality hnt (A.square_directSum_power_rank t)
  simpa only [Nat.cast_pow, Nat.cast_mul, mul_pow,
    ← Real.rpow_pow_comm (Nat.cast_nonneg n)] using h

end Arithmetic

end MatrixMultiplication.Foundation

end

end MatrixMultiplicationAllFields
