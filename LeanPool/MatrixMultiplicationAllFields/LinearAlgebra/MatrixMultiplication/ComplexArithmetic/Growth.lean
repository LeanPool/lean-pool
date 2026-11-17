/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Complexity
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.MatrixPadding
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.RecursiveBlockPrograms
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

theorem exists_power_cover {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    ∃ k : ℕ, n ≤ b ^ k ∧ b ^ k ≤ b * n := by
  refine ⟨Nat.log b n + 1, (Nat.lt_pow_succ_log_self (by omega) n).le, ?_⟩
  rw [pow_succ']
  exact Nat.mul_le_mul_left b (Nat.pow_log_le_self b (by omega))

theorem geometric_cost_recurrence_bound (x : ℕ → ℝ) (a b d q : ℝ)
    (hx : 0 ≤ x 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (haq : a < q) (hdq : d ≤ q)
    (hstep : ∀ k, x (k + 1) ≤ a * x k + b * d ^ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, x k ≤ C * q ^ k := by
  let C := x 0 + b / (q - a) + 1
  have hgap : 0 < q - a := sub_pos.mpr haq
  have hfrac : 0 ≤ b / (q - a) := div_nonneg hb hgap.le
  have hC : 0 < C := by dsimp [C]; linarith
  have hcancel : (q - a) * (b / (q - a)) = b := by
    field_simp [ne_of_gt hgap]
  have hCfrac : b / (q - a) ≤ C := by dsimp [C]; linarith
  have hcoeff : a * C + b ≤ C * q := by
    have hmul := mul_le_mul_of_nonneg_left hCfrac hgap.le
    rw [hcancel] at hmul
    calc
      a * C + b ≤ a * C + (q - a) * C := add_le_add_right hmul _
      _ = C * q := by ring
  refine ⟨C, hC, ?_⟩
  intro k
  induction k with
  | zero => simp only [pow_zero, mul_one]; dsimp [C]; linarith
  | succ k ih =>
    calc
      x (k + 1) ≤ a * x k + b * d ^ k := hstep k
      _ ≤ a * (C * q ^ k) + b * q ^ k :=
        add_le_add (mul_le_mul_of_nonneg_left ih ha)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd hdq k) hb)
      _ = (a * C + b) * q ^ k := by ring
      _ ≤ (C * q) * q ^ k :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (hd.trans hdq) k)
      _ = C * q ^ (k + 1) := by rw [pow_succ]; ring

theorem power_cost_padding_bound
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 < C)
    (hpower : ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k),
      P.Correct ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ s) ^ k) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm n,
      P.Correct ∧ (P.cost : ℝ) ≤ D * (n : ℝ) ^ s := by
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  refine ⟨C * (b : ℝ) ^ s, mul_pos hC (Real.rpow_pos_of_pos hbpos s), ?_⟩
  intro n hn
  obtain ⟨k, hnk, hkn⟩ := exists_power_cover hb hn
  obtain ⟨P, hP, hcost⟩ := hpower k
  obtain ⟨Q, hQ, hQP⟩ := hpad hnk P hP
  refine ⟨Q, hQ, ?_⟩
  calc
    (Q.cost : ℝ) ≤ (P.cost : ℝ) := by exact_mod_cast hQP
    _ ≤ C * ((b : ℝ) ^ s) ^ k := hcost
    _ = C * ((b ^ k : ℕ) : ℝ) ^ s := by
      rw [Real.rpow_pow_comm hbpos.le, Nat.cast_pow]
    _ ≤ C * ((b : ℝ) * (n : ℝ)) ^ s :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkn) hs) hC.le
    _ = (C * (b : ℝ) ^ s) * (n : ℝ) ^ s := by
      rw [Real.mul_rpow hbpos.le (Nat.cast_nonneg n)]
      ring

theorem admissibleExponent_of_uniform_power_costs
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {τ C : ℝ} (hτ : 0 ≤ τ) (hC : 0 < C)
    (hpower : ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k),
      P.Correct ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ τ) ^ k) :
    AdmissibleExponent τ := by
  obtain ⟨D, hD, hall⟩ := power_cost_padding_bound hpad hb hτ hC hpower
  intro ε hε
  refine ⟨D, hD, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hall n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)) hD.le

theorem admissibleExponent_of_power_costs
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 0 ≤ τ)
    (hpower : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k),
        P.Correct ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ (τ + ε)) ^ k) :
    AdmissibleExponent τ := by
  intro ε hε
  obtain ⟨C, hC, hcost⟩ := hpower ε hε
  exact power_cost_padding_bound hpad hb (by linarith) hC hcost

theorem admissibleExponent_of_recursive_costs
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (P : ∀ k : ℕ, MatrixAlgorithm (b ^ k))
    (hP : ∀ k, (P k).Correct)
    (hstep : ∀ k, (P (k + 1)).cost ≤ R * (P k).cost + K * (b ^ k) ^ 2) :
    AdmissibleExponent τ := by
  apply admissibleExponent_of_power_costs hpad hb (by linarith)
  intro ε hε
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hbone : 1 < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hrate : (R : ℝ) < (b : ℝ) ^ (τ + ε) :=
    hR.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hbone (by linarith))
  have hquad : (b : ℝ) ^ (2 : ℕ) ≤ (b : ℝ) ^ (τ + ε) := by
    rw [← Real.rpow_natCast]
    change (b : ℝ) ^ (2 : ℝ) ≤ (b : ℝ) ^ (τ + ε)
    exact Real.rpow_le_rpow_of_exponent_le hbone.le (by linarith)
  obtain ⟨C, hC, hbound⟩ := geometric_cost_recurrence_bound
    (fun k => ((P k).cost : ℝ)) (R : ℝ) (K : ℝ) ((b : ℝ) ^ (2 : ℕ))
    ((b : ℝ) ^ (τ + ε)) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (sq_nonneg _) hrate hquad (fun k => by
      have h := hstep k
      have hcast : ((P (k + 1)).cost : ℝ) ≤
          (R : ℝ) * ((P k).cost : ℝ) + (K : ℝ) * ((b : ℝ) ^ k) ^ 2 := by
        exact_mod_cast h
      simpa only [← pow_mul, Nat.mul_comm k 2] using hcast)
  exact ⟨C, hC, fun k => ⟨P k, hP k, hbound k⟩⟩

/-- The recursive arithmetic cost for a fixed block size, rank bound and linear overhead. -/
def blockRecurrenceCost (b R K : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => R * blockRecurrenceCost b R K k + K * (b ^ k) ^ 2

@[simp] theorem blockRecurrenceCost_zero (b R K : ℕ) :
    blockRecurrenceCost b R K 0 = 1 := rfl

@[simp] theorem blockRecurrenceCost_succ (b R K k : ℕ) :
    blockRecurrenceCost b R K (k + 1) =
      R * blockRecurrenceCost b R K k + K * (b ^ k) ^ 2 := rfl

theorem power_programs_of_block_step {b R K : ℕ}
    (hstep : ∀ m : ℕ, ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k), P.Correct ∧
      P.cost ≤ blockRecurrenceCost b R K k := by
  intro k
  induction k with
  | zero =>
    exact ⟨scalarAlgorithm, scalarAlgorithm_correct, by simp⟩
  | succ k ih =>
    obtain ⟨P, hP, hcost⟩ := ih
    obtain ⟨Q, hQ, hQcost⟩ := hstep (b ^ k) P hP
    have hbound : Q.cost ≤ blockRecurrenceCost b R K (k + 1) := by
      exact hQcost.trans (Nat.add_le_add_right (Nat.mul_le_mul_left R hcost) _)
    have hresult : ∃ Q : MatrixAlgorithm (b * b ^ k), Q.Correct ∧
        Q.cost ≤ blockRecurrenceCost b R K (k + 1) := ⟨Q, hQ, hbound⟩
    exact (pow_succ' b k).symm ▸ hresult

theorem admissibleExponent_of_block_step_of_padding
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (hstep : ∀ m : ℕ, ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    AdmissibleExponent τ := by
  apply admissibleExponent_of_power_costs hpad hb (by linarith)
  intro ε hε
  have hbone : 1 < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hrate : (R : ℝ) < (b : ℝ) ^ (τ + ε) :=
    hR.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hbone (by linarith))
  have hquad : (b : ℝ) ^ (2 : ℕ) ≤ (b : ℝ) ^ (τ + ε) := by
    rw [← Real.rpow_natCast]
    change (b : ℝ) ^ (2 : ℝ) ≤ (b : ℝ) ^ (τ + ε)
    exact Real.rpow_le_rpow_of_exponent_le hbone.le (by linarith)
  obtain ⟨C, hC, hbound⟩ := geometric_cost_recurrence_bound
    (fun k => (blockRecurrenceCost b R K k : ℝ))
    (R : ℝ) (K : ℝ) ((b : ℝ) ^ (2 : ℕ)) ((b : ℝ) ^ (τ + ε))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (sq_nonneg _) hrate hquad (fun k => by
      simp only [blockRecurrenceCost_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2])
  refine ⟨C, hC, ?_⟩
  intro k
  obtain ⟨P, hP, hcost⟩ := power_programs_of_block_step hstep k
  exact ⟨P, hP, (by exact_mod_cast hcost : (P.cost : ℝ) ≤
    (blockRecurrenceCost b R K k : ℝ)).trans (hbound k)⟩

theorem admissibleExponent_of_block_step
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (hstep : ∀ m : ℕ, ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    AdmissibleExponent τ :=
  admissibleExponent_of_block_step_of_padding
    (fun h P hP => MatrixAlgorithm.exists_restrict h P hP) hb hτ hR hstep

theorem admissibleExponent_of_rankAtMost {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R)
    {τ : ℝ} (hτ : 2 ≤ τ) (hR : (R : ℝ) ≤ (n : ℝ) ^ τ) :
    AdmissibleExponent τ := by
  apply admissibleExponent_of_block_step (K := 6 * R * n ^ 2) hn hτ hR
  intro m P hP
  obtain ⟨Q, hQ, hcost⟩ := RecursiveBlock.rank_block_step hRank P hP
  exact ⟨Q, hQ, hcost.le⟩

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixMultiplicationAllFields
