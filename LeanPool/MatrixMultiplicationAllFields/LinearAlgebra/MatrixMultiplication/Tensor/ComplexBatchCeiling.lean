/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
public import Lean.Elab.Tactic.Omega

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite coefficient tensors and their algebraic transformations. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation

def batchCount (R k : ℕ) : ℕ := (R + k - 1) / k

@[simp] theorem batchCount_zero (k : ℕ) : batchCount 0 k = 0 := by
  unfold batchCount
  by_cases hk : k = 0
  · simp [hk]
  · apply Nat.div_eq_of_lt
    omega

theorem le_batchCount_mul (R : ℕ) {k : ℕ} (hk : 0 < k) :
    R ≤ batchCount R k * k := by
  have hdiv := Nat.div_add_mod (R + k - 1) k
  have hmod := Nat.mod_lt (R + k - 1) hk
  rw [Nat.mul_comm k ((R + k - 1) / k)] at hdiv
  unfold batchCount
  omega

theorem batchCount_le_iff {R k B : ℕ} (hk : 0 < k) :
    batchCount R k ≤ B ↔ R ≤ B * k := by
  unfold batchCount
  rw [Nat.div_le_iff_le_mul hk]
  omega

theorem batchCount_mul_lt (R : ℕ) {k : ℕ} (hk : 0 < k) :
    batchCount R k * k < R + k := by
  have hmul := Nat.div_mul_le_self (R + k - 1) k
  unfold batchCount
  omega

theorem batchCount_pos_iff {R k : ℕ} (hk : 0 < k) :
    0 < batchCount R k ↔ 0 < R := by
  have hzero := batchCount_le_iff (R := R) (B := 0) hk
  simp only [Nat.zero_mul] at hzero
  omega

theorem batchCount_cast_lt (R : ℕ) {k : ℕ} (hk : 0 < k) :
    (batchCount R k : ℝ) < (R : ℝ) / (k : ℝ) + 1 := by
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hmul : (batchCount R k : ℝ) * (k : ℝ) < (R : ℝ) + (k : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using
      (Nat.cast_lt (α := ℝ)).mpr (batchCount_mul_lt R hk)
  calc
    (batchCount R k : ℝ) < ((R : ℝ) + (k : ℝ)) / (k : ℝ) :=
      (lt_div_iff₀ hkR).mpr hmul
    _ = (R : ℝ) / (k : ℝ) + 1 := by rw [add_div, div_self (ne_of_gt hkR)]

theorem batchCount_cast_le (R : ℕ) {k : ℕ} (hk : 0 < k) :
    (batchCount R k : ℝ) ≤ (R : ℝ) / (k : ℝ) + 1 :=
  (batchCount_cast_lt R hk).le

theorem batchCount_mul_cast_le (R r : ℕ) {k : ℕ} (hk : 0 < k) :
    ((batchCount R k * r : ℕ) : ℝ) ≤
      (r : ℝ) / (k : ℝ) * (R : ℝ) + (r : ℝ) := by
  calc
    ((batchCount R k * r : ℕ) : ℝ) = (batchCount R k : ℝ) * (r : ℝ) := by
      rw [Nat.cast_mul]
    _ ≤ ((R : ℝ) / (k : ℝ) + 1) * (r : ℝ) :=
      mul_le_mul_of_nonneg_right (batchCount_cast_le R hk) (Nat.cast_nonneg r)
    _ = (r : ℝ) / (k : ℝ) * (R : ℝ) + (r : ℝ) := by
      simp only [div_eq_mul_inv]
      ring

def batchRank (k r : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => batchCount (batchRank k r t) k * r

@[simp] theorem batchRank_zero (k r : ℕ) : batchRank k r 0 = 1 := rfl

@[simp] theorem batchRank_succ (k r t : ℕ) :
    batchRank k r (t + 1) = batchCount (batchRank k r t) k * r := rfl

theorem batchRank_succ_le_affine {k : ℕ} (hk : 0 < k) (r t : ℕ) :
    (batchRank k r (t + 1) : ℝ) ≤
      (r : ℝ) / (k : ℝ) * (batchRank k r t : ℝ) + (r : ℝ) := by
  rw [batchRank_succ]
  exact batchCount_mul_cast_le (batchRank k r t) r hk

theorem batchRank_pos {k r : ℕ} (hk : 0 < k) (hr : 0 < r) :
    ∀ t, 0 < batchRank k r t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [batchRank_succ]
    exact Nat.mul_pos ((batchCount_pos_iff hk).mpr ih) hr

namespace Tensor

variable {K X Y Z U V W A B : Type*} [CommSemiring K]

theorem RankAtMost.repeat_batch_ceiling {S : Tensor K U V W} {k r R : ℕ}
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r) (hk : 0 < k) :
    RankAtMost (directSum (fun _ : Fin R => S)) (batchCount R k * r) :=
  hbatch.repeat_batch (le_batchCount_mul R hk)

theorem RankAtMost.batch_product_ceiling [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {R k r : ℕ}
    (hT : RankAtMost T R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r) (hk : 0 < k) :
    RankAtMost (Tensor.product T S) (batchCount R k * r) :=
  hT.batch_product hbatch (le_batchCount_mul R hk)

theorem matrixCoefficients_batch_rank_ceiling [DecidableEq A] [DecidableEq B] [Fintype B]
    {R k r : ℕ}
    (houter : RankAtMost (matrixCoefficients (K := K) A A A) R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => matrixCoefficients (K := K) B B B)) r)
    (hk : 0 < k) :
    RankAtMost (matrixCoefficients (K := K) (A × B) (A × B) (A × B))
      (batchCount R k * r) :=
  matrixCoefficients_batch_rank houter hbatch (le_batchCount_mul R hk)

end Tensor
end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
