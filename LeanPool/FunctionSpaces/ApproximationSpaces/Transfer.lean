/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Embedding
public import Mathlib.Analysis.Normed.Operator.NNNorm

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Functoriality of approximation spaces

Let `A` and `B` be approximation schemes in `X` and `Y`, and `T : X → Y` a bounded linear map
that sends approximants to approximants, `T (A n) ⊆ B n`.  Then `E^B_n(T f) ≤ ‖T‖ E^A_n(f)`
for all `n` (`approxError_map_le`), and therefore `T` maps `A^s_q(X)` into `B^s_q(Y)` with

`‖T f‖_{B^s_q} ≤ ‖T‖ ‖f‖_{A^s_q}`

for both quasi-norms (`approxNorm_map_le`, `approxNormDyadic_map_le`).  Approximation spaces
are functorial in the pair (space, scheme); the image scheme `A.map T` satisfies the
hypothesis automatically.
-/

@[expose] public section

open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable {A : ApproximationScheme X} {B : ApproximationScheme Y} {s : ℝ} {q : ℝ≥0∞}

/-- **Functoriality**, Pietsch's quasi-norm: `‖T f‖_{B^s_q} ≤ ‖T‖ ‖f‖_{A^s_q}`. -/
theorem approxNorm_map_le (T : X →L[ℝ] Y) (hT : ∀ n, ∀ a ∈ A n, T a ∈ B n) (f : X) :
    B.approxNorm s q (T f) ≤ ‖T‖ₑ * A.approxNorm s q f := by
  rw [approxNorm, approxNorm, ← ENNReal.lqNorm_const_mul]
  refine ENNReal.lqNorm_mono fun n => ?_
  rw [mul_left_comm]
  gcongr
  exact approxError_map_le T hT f n

/-- **Functoriality**, dyadic quasi-norm: `‖T f‖^dyadic ≤ ‖T‖ ‖f‖^dyadic`. -/
theorem approxNormDyadic_map_le (T : X →L[ℝ] Y) (hT : ∀ n, ∀ a ∈ A n, T a ∈ B n) (f : X) :
    B.approxNormDyadic s q (T f) ≤ ‖T‖ₑ * A.approxNormDyadic s q f := by
  rw [approxNormDyadic, approxNormDyadic, mul_add, ← ENNReal.lqNorm_const_mul]
  refine add_le_add (T.le_opENorm f) (ENNReal.lqNorm_mono fun k => ?_)
  rw [approxSeqDyadic, approxSeqDyadic, mul_left_comm]
  gcongr
  exact approxError_map_le T hT f _

/-- A bounded linear map with `T(A_n) ⊆ B_n` maps `A^s_q` into `B^s_q`. -/
theorem MemApprox.map (T : X →L[ℝ] Y) (hT : ∀ n, ∀ a ∈ A n, T a ∈ B n) {f : X}
    (hf : A.MemApprox s q f) : B.MemApprox s q (T f) :=
  (approxNorm_map_le T hT f).trans_lt (ENNReal.mul_lt_top eNorm_lt_top hf)

/-- The image of `A^s_q(X)` under `T` lies in `B^s_q(Y)`. -/
theorem approxSpace_map_le (hs : 0 ≤ s) (hq : 1 ≤ q) (T : X →L[ℝ] Y)
    (hT : ∀ n, ∀ a ∈ A n, T a ∈ B n) :
    (A.approxSpace s q hs hq).map T.toLinearMap ≤ B.approxSpace s q hs hq := by
  rintro _ ⟨f, hf, rfl⟩
  exact MemApprox.map T hT hf

/-- A bounded linear map is functorial for the image scheme `A.map T`. -/
theorem mem_map_of_mem' (T : X →L[ℝ] Y) : ∀ n, ∀ a ∈ A n, T a ∈ A.map T.toLinearMap n :=
  fun _ _ ha => A.mem_map_of_mem T.toLinearMap ha

end ApproximationScheme
