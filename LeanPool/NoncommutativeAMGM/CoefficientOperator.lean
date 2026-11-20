/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.Basic

/-!
# The triangular operator in Lemma 3.10

In shifted coordinates `t = X - 1`, let `A = t d/dt`. The operator below is
`A(A+1) - t(A+1)(L-1-A)`. Its action is exactly equation (38).
Self-adjointness for the coefficient inner product and the norm bound are separate tasks.
-/

@[expose] public section

namespace NoncommutativeAMGM

open Polynomial

/-- Multiplication by `X-1`, as a real linear map. -/
noncomputable def multiplyShift : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ where
  toFun p := (X - 1) * p
  map_add' p q := mul_add _ _ _
  map_smul' r p := by simp

/-- Euler operator in shifted coordinates. -/
noncomputable def shiftedEuler : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ where
  toFun p := (X - 1) * p.derivative
  map_add' p q := by simp [derivative_add, mul_add]
  map_smul' r p := by simp

/-- The finite-degree coefficient operator used in equation (38). -/
noncomputable def coefficientOperator (L : ℕ) : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ :=
  shiftedEuler * shiftedEuler + shiftedEuler -
    multiplyShift.comp (((L : ℝ) - 1) • LinearMap.id +
      ((L : ℝ) - 2) • shiftedEuler - shiftedEuler * shiftedEuler)

theorem shiftedEuler_power (l : ℕ) :
    shiftedEuler ((X - 1 : Polynomial ℝ) ^ l) = (l : ℝ) • (X - 1 : Polynomial ℝ) ^ l := by
  cases l with
  | zero => simp [shiftedEuler]
  | succ l =>
    simp only [shiftedEuler, LinearMap.coe_mk, AddHom.coe_mk, derivative_pow,
      derivative_sub, derivative_X, derivative_one, sub_zero, mul_one]
    rw [pow_succ]
    simp [Algebra.smul_def]
    ring

/-- Equation (38), with the degree and scalar factors made explicit. -/
theorem coefficientOperator_power (L l : ℕ) :
    coefficientOperator L ((X - 1 : Polynomial ℝ) ^ l) =
      ((l : ℝ) * ((l : ℝ) + 1)) • (X - 1 : Polynomial ℝ) ^ l -
        (((l : ℝ) + 1) * ((L : ℝ) - l - 1)) • (X - 1 : Polynomial ℝ) ^ (l + 1) := by
  simp only [coefficientOperator, LinearMap.sub_apply, LinearMap.add_apply,
    Module.End.mul_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    shiftedEuler_power, map_smul, multiplyShift, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [mul_sub, mul_add, mul_smul_comm, ← pow_succ', smul_smul]
  module

/-- The subspace spanned by `(X-1)ʲ, …, (X-1)ᴸ⁻¹`. -/
noncomputable def powerTail (L j : ℕ) : Submodule ℝ (Polynomial ℝ) :=
  Submodule.span ℝ {p | ∃ l : ℕ, j ≤ l ∧ l < L ∧ p = (X - 1) ^ l}

theorem power_mem_powerTail {L j l : ℕ} (hjl : j ≤ l) (hlL : l < L) :
    (X - 1 : Polynomial ℝ) ^ l ∈ powerTail L j :=
  Submodule.subset_span ⟨l, hjl, hlL, rfl⟩

/-- The operator preserves the high-order vanishing subspace in Lemma 3.10. -/
theorem coefficientOperator_preserves_powerTail (L j : ℕ) (p : Polynomial ℝ)
    (hp : p ∈ powerTail L j) : coefficientOperator L p ∈ powerTail L j := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨l, hjl, hlL, rfl⟩ := hp
    rw [coefficientOperator_power]
    apply Submodule.sub_mem
    · exact Submodule.smul_mem _ _ (power_mem_powerTail hjl hlL)
    · by_cases htop : l + 1 = L
      · have hzero : (L : ℝ) - l - 1 = 0 := by
          have hL : (L : ℝ) = l + 1 := by exact_mod_cast htop.symm
          linarith
        simp [hzero]
      · exact Submodule.smul_mem _ _ (power_mem_powerTail (by omega) (by omega))
  | zero => simp
  | add p q _ _ hp hq => simpa using (powerTail L j).add_mem hp hq
  | smul r p _ hp => simpa using (powerTail L j).smul_mem r hp

end NoncommutativeAMGM
