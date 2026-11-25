/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Calculus.TaylorAsymptotics
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiTaylor

/-!
# The sharp local coefficient of the Suzuki product

The actual product and the exact exponential have identical derivatives below
degree five. Taylor's theorem therefore identifies the leading local error with
the quintic Lie polynomial, and gives its norm as the sharp local coefficient.

## Main results

* `isLittleO_fiveStageStrangProduct_sub_exp_sub_quintic`: the actual leading local error.
* `tendsto_inv_pow_mul_norm_fiveStageStrangProduct_sub_exp`: the sharp norm limit.
-/

@[expose] public noncomputable section

open NormedSpace Asymptotics Filter
open scoped RealScalar ContDiff Topology

namespace FQFP.BCH

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The actual local-error derivatives through degree five: only the quintic
derivative can be nonzero, and it is the factorial-scaled quintic Lie term. -/
theorem iteratedDeriv_fiveStageStrangProduct_sub_exp_zero (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (n : ℕ) (hn : n ≤ 5) :
    iteratedDeriv n (fun t ↦ fiveStageStrangProduct a b p t - exp (t • (a + b))) 0 =
      if n = 5 then (Nat.factorial 5 : ℝ) • suzukiQuinticTerm a b p else 0 := by
  rw [iteratedDeriv_fun_sub
    ((contDiff_fiveStageStrangProduct a b p).contDiffAt.of_le (by exact_mod_cast le_top))
    ((TrotterError.contDiff_exp_smul_const (a + b)).contDiffAt.of_le
      (by exact_mod_cast le_top)),
    iteratedDeriv_fiveStageStrangProduct_zero, TrotterError.iteratedDeriv_exp_smul_const]
  simp only [zero_smul, exp_zero, mul_one]
  have hj := expListTerm_fiveStageStrang_through_six a b p hp ⟨n, by lia⟩
  norm_num only [Fin.ext_iff] at hj
  rw [hj]
  have hn6 : n ≠ 6 := by lia
  simp only [← Rat.cast_smul_eq_qsmul ℝ, Rat.cast_inv,
    Rat.cast_natCast, smul_add, smul_smul]
  have hfact : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  by_cases hn5 : n = 5
  · subst n
    simp [hfact]
  · simp [hn5, hn6, hfact]

/-- The actual local error equals the quintic Lie term to leading order,
without any norm-control or small-step hypothesis on the generators. -/
theorem isLittleO_fiveStageStrangProduct_sub_exp_sub_quintic
    (a b : A) (p : ℝ) (hp : IsSuzukiCubic p) :
    (fun t ↦ fiveStageStrangProduct a b p t - exp (t • (a + b)) -
      t ^ 5 • suzukiQuinticTerm a b p) =o[𝓝 (0 : ℝ)] (fun t ↦ t ^ 5) := by
  apply TrotterError.isLittleO_sub_pow_smul_of_iteratedDeriv
  · exact ((contDiff_fiveStageStrangProduct a b p).sub
      (TrotterError.contDiff_exp_smul_const (a + b))).of_le (by simp)
  · intro k hk
    rw [iteratedDeriv_fiveStageStrangProduct_sub_exp_zero a b p hp k (by lia)]
    simp [show k ≠ 5 by lia]
  · simpa using iteratedDeriv_fiveStageStrangProduct_sub_exp_zero a b p hp 5 le_rfl

/-- **Sharp local coefficient.** As positive steps tend to zero, the local
error norm divided by the fifth power tends to the norm of the quintic Lie term. -/
theorem tendsto_inv_pow_mul_norm_fiveStageStrangProduct_sub_exp
    (a b : A) (p : ℝ) (hp : IsSuzukiCubic p) :
    Tendsto (fun t ↦ (t ^ 5)⁻¹ * ‖fiveStageStrangProduct a b p t - exp (t • (a + b))‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖suzukiQuinticTerm a b p‖) :=
  TrotterError.tendsto_inv_pow_mul_norm_of_isLittleO
    (isLittleO_fiveStageStrangProduct_sub_exp_sub_quintic a b p hp)

end FQFP.BCH
