/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.Padding
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Growth
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Rectangular matrix multiplication algorithms and their asymptotic exponents. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

theorem rectangular_power_cost_padding_bound
    {a b : ℕ} (ha : 2 ≤ a) {k s C : ℝ} (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ)) (hs : 0 ≤ s) (hC : 0 < C)
    (hpower : ∀ t : ℕ, ∃ P : MatrixAlgorithm F (a ^ t) (b ^ t) (a ^ t),
      P.Correct ∧ (P.cost : ℝ) ≤ C * ((a : ℝ) ^ s) ^ t) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : MatrixAlgorithm F n (innerSize n k) n,
        P.Correct ∧ (P.cost : ℝ) ≤ D * (n : ℝ) ^ s := by
  have hapos : 0 < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  refine ⟨C * (a : ℝ) ^ s, mul_pos hC (Real.rpow_pos_of_pos hapos s), ?_⟩
  intro n hn
  obtain ⟨t, hnt, htn⟩ := MatrixMultiplication.Foundation.Arithmetic.exists_power_cover ha hn
  obtain ⟨P, hP, hcost⟩ := hpower t
  obtain ⟨Q, hQ, hQP⟩ := MatrixAlgorithm.exists_restrict
    hnt (innerSize_le_pow hk hnt hab) hnt P hP
  refine ⟨Q, hQ, ?_⟩
  calc
    (Q.cost : ℝ) ≤ (P.cost : ℝ) := by exact_mod_cast hQP
    _ ≤ C * ((a : ℝ) ^ s) ^ t := hcost
    _ = C * ((a ^ t : ℕ) : ℝ) ^ s := by
      rw [Real.rpow_pow_comm hapos.le, Nat.cast_pow]
    _ ≤ C * ((a : ℝ) * (n : ℝ)) ^ s :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast htn) hs) hC.le
    _ = (C * (a : ℝ) ^ s) * (n : ℝ) ^ s := by
      rw [Real.mul_rpow hapos.le (Nat.cast_nonneg n)]
      ring

theorem rectangularAdmissibleExponent_of_power_costs
    {a b : ℕ} (ha : 2 ≤ a) {k τ : ℝ} (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ)) (hτ : 0 ≤ τ)
    (hpower : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ t : ℕ, ∃ P : MatrixAlgorithm F (a ^ t) (b ^ t) (a ^ t),
        P.Correct ∧ (P.cost : ℝ) ≤ C * ((a : ℝ) ^ (τ + ε)) ^ t) :
    RectangularAdmissibleExponent F k τ := by
  intro ε hε
  obtain ⟨C, hC, hcost⟩ := hpower ε hε
  exact rectangular_power_cost_padding_bound ha hk hab (by linarith) hC hcost

/-- The recursive cost of rectangular block multiplication with explicit linear overhead. -/
def rectangularBlockCost (a b R K : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => R * rectangularBlockCost a b R K t + K * ((a * b) ^ t + (a ^ 2) ^ t)

@[simp] theorem rectangularBlockCost_zero (a b R K : ℕ) :
    rectangularBlockCost a b R K 0 = 1 := rfl

@[simp] theorem rectangularBlockCost_succ (a b R K t : ℕ) :
    rectangularBlockCost a b R K (t + 1) =
      R * rectangularBlockCost a b R K t + K * ((a * b) ^ t + (a ^ 2) ^ t) := rfl

theorem rectangularBlockCost_bound {a b R K : ℕ} (ha : 2 ≤ a)
    {τ ε : ℝ} (hε : 0 < ε)
    (hR : (R : ℝ) ≤ (a : ℝ) ^ τ)
    (hin : (a * b : ℕ) ≤ (a : ℝ) ^ τ)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) ^ τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t,
      (rectangularBlockCost a b R K t : ℝ) ≤ C * ((a : ℝ) ^ (τ + ε)) ^ t := by
  have haone : 1 < (a : ℝ) := by exact_mod_cast (by omega : 1 < a)
  have hrate : (R : ℝ) < (a : ℝ) ^ (τ + ε) :=
    hR.trans_lt (Real.rpow_lt_rpow_of_exponent_lt haone (by linarith))
  have hlarge : (a : ℝ) ^ τ ≤ (a : ℝ) ^ (τ + ε) :=
    Real.rpow_le_rpow_of_exponent_le haone.le (by linarith)
  have hin0 : (0 : ℝ) ≤ (a * b : ℕ) := Nat.cast_nonneg _
  have hd : 0 ≤ max ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ)) :=
    hin0.trans (le_max_left _ _)
  apply MatrixMultiplication.Foundation.Arithmetic.geometric_cost_recurrence_bound
    (fun t => (rectangularBlockCost a b R K t : ℝ))
    (R : ℝ) (2 * K) (max ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ)))
    ((a : ℝ) ^ (τ + ε)) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by positivity) hd hrate (max_le (hin.trans hlarge) (hout.trans hlarge))
  intro t
  simp only [rectangularBlockCost_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  have h1 : ((a : ℝ) * (b : ℝ)) ^ t ≤
      max ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ)) ^ t := by
    apply pow_le_pow_left₀ (by positivity)
    simpa only [Nat.cast_mul] using le_max_left ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ))
  have h2 : ((a : ℝ) ^ (2 : ℕ)) ^ t ≤
      max ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ)) ^ t :=
    pow_le_pow_left₀ (sq_nonneg _) (le_max_right _ _) t
  simp only [Nat.cast_mul] at h1 h2
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Nat.cast_nonneg K)]

theorem rectangular_power_programs_of_block_step {a b R K : ℕ}
    (hscalar : ∃ P : MatrixAlgorithm F 1 1 1, P.Correct ∧ P.cost ≤ 1)
    (hstep : ∀ m p : ℕ, ∀ P : MatrixAlgorithm F m p m, P.Correct →
      ∃ Q : MatrixAlgorithm F (a * m) (b * p) (a * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * (m * p + m ^ 2)) :
    ∀ t : ℕ, ∃ P : MatrixAlgorithm F (a ^ t) (b ^ t) (a ^ t),
      P.Correct ∧ P.cost ≤ rectangularBlockCost a b R K t := by
  intro t
  induction t with
  | zero => simpa using hscalar
  | succ t ih =>
    obtain ⟨P, hP, hcost⟩ := ih
    obtain ⟨Q, hQ, hQcost⟩ := hstep (a ^ t) (b ^ t) P hP
    have hbound : Q.cost ≤ rectangularBlockCost a b R K (t + 1) := by
      apply hQcost.trans
      simp only [rectangularBlockCost_succ, mul_pow, ← pow_mul, Nat.mul_comm t 2]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left R hcost) _
    have hresult : ∃ Q : MatrixAlgorithm F (a * a ^ t) (b * b ^ t) (a * a ^ t),
        Q.Correct ∧ Q.cost ≤ rectangularBlockCost a b R K (t + 1) := ⟨Q, hQ, hbound⟩
    exact (pow_succ' a t).symm ▸ ((pow_succ' b t).symm ▸ hresult)

theorem rectangularAdmissibleExponent_of_block_step
    {a b R K : ℕ} (ha : 2 ≤ a) {k τ : ℝ} (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ)) (hτ : 0 ≤ τ)
    (hR : (R : ℝ) ≤ (a : ℝ) ^ τ)
    (hin : (a * b : ℕ) ≤ (a : ℝ) ^ τ)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) ^ τ)
    (hscalar : ∃ P : MatrixAlgorithm F 1 1 1, P.Correct ∧ P.cost ≤ 1)
    (hstep : ∀ m p : ℕ, ∀ P : MatrixAlgorithm F m p m, P.Correct →
      ∃ Q : MatrixAlgorithm F (a * m) (b * p) (a * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * (m * p + m ^ 2)) :
    RectangularAdmissibleExponent F k τ := by
  apply rectangularAdmissibleExponent_of_power_costs ha hk hab hτ
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := rectangularBlockCost_bound (K := K) ha hε hR hin hout
  refine ⟨C, hC, ?_⟩
  intro t
  obtain ⟨P, hP, hcost⟩ := rectangular_power_programs_of_block_step hscalar hstep t
  exact ⟨P, hP, (by exact_mod_cast hcost : (P.cost : ℝ) ≤
    (rectangularBlockCost a b R K t : ℝ)).trans (hbound t)⟩

end MatrixMultiplication.Arithmetic

end

end MatrixMultiplicationAllFields
