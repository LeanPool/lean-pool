/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation.Separation

theorem grid_modular_collision (Q c t u v : ℤ)
    (hc : 0 ≤ c ∧ c < Q) (ht : 0 ≤ t ∧ t < Q)
    (hu : 0 ≤ u ∧ u < Q) (hv : 0 ≤ v ∧ v < Q)
    (hmod : Int.ModEq (4 * Q) c (t + u - v)) : c = t + u - v := by
  have hdvd : 4 * Q ∣ t + u - v - c := hmod.dvd
  have hz : t + u - v - c = 0 := by
    rcases le_total 0 (t + u - v - c) with h | h
    · exact Int.eq_zero_of_dvd_of_nonneg_of_lt h (by omega) hdvd
    · have hn : -(t + u - v - c) = 0 :=
        Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) (Int.dvd_neg.mpr hdvd)
      omega
  omega

variable {ι : Type*} [Fintype ι]

/-- Squared Euclidean norm of a finitely indexed real vector. -/
def squaredNorm (t : ι → ℝ) : ℝ := ∑ i, (t i) ^ 2

/-- Euclidean dot product of two finitely indexed real vectors. -/
def dot (t u : ι → ℝ) : ℝ := ∑ i, t i * u i

theorem squaredNorm_displacement (t u v : ι → ℝ) :
    squaredNorm (fun i => t i + u i - v i) =
      squaredNorm t + 2 * (dot t u - dot t v) +
        squaredNorm (fun i => u i - v i) := by
  calc
    squaredNorm (fun i => t i + u i - v i) =
        ∑ i, ((t i) ^ 2 + 2 * (t i * u i - t i * v i) +
          (u i - v i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      simp only [squaredNorm, dot, Finset.sum_add_distrib,
        mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]

theorem sphere_slice_collision (t c u v : ι → ℝ)
    (hsphere : squaredNorm c = squaredNorm t)
    (hslice : dot t u = dot t v)
    (hcollision : ∀ i, c i = t i + u i - v i) : u = v ∧ c = t := by
  have hc : c = fun i => t i + u i - v i := funext hcollision
  have hzero : squaredNorm (fun i => u i - v i) = 0 := by
    have hid := squaredNorm_displacement t u v
    rw [← hc, hsphere, hslice] at hid
    linarith
  have huv : u = v := by
    funext i
    have hle : (u i - v i) ^ 2 ≤ squaredNorm (fun j => u j - v j) :=
      Finset.single_le_sum (fun j _ => sq_nonneg (u j - v j)) (Finset.mem_univ i)
    rw [hzero] at hle
    nlinarith [sq_nonneg (u i - v i)]
  refine ⟨huv, ?_⟩
  funext i
  rw [hcollision, huv]
  ring

end MatrixMultiplication.Foundation.Separation

end MatrixMultiplicationAllFields
