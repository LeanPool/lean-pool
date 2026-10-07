/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Comparing the sup norm with the Euclidean quantity on `Fin m → ℝ`

Mathlib equips the product type `Fin m → ℝ` with the sup norm
(`‖x‖ = ⨆ i, |x i|`, realized as a finite maximum here), not the Euclidean
(`ℓ²`) norm. Whenever a field that is Lipschitz or bounded in this sup norm
feeds into an estimate phrased in Euclidean terms, the two norms have to be
compared explicitly. This file collects the elementary inequalities that make
that comparison, in either direction and with the intermediate `ℓ¹` quantity,
as used around `lem:aniso:comparison`.
-/

public section

open Finset


namespace CIV



/-- The squared sup norm is bounded by the sum of squares of the coordinates:
`‖x‖² ≤ ∑ᵢ xᵢ²`. -/
theorem sq_norm_le_sum_sq {m : ℕ} (x : Fin m → ℝ) : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · have hx : x = 0 := funext (fun i => (hm.false i).elim)
    simp [hx]
  · obtain ⟨i, hi⟩ := (IsGreatest.pi_norm x).1
    dsimp only at hi
    rw [← hi, Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

/-- The sum of squares of the coordinates is bounded by `m` times the squared
sup norm: `∑ᵢ xᵢ² ≤ m · ‖x‖²`. -/
theorem sum_sq_le_card_mul_sq_norm {m : ℕ} (x : Fin m → ℝ) : ∑ i, x i ^ 2 ≤ m * ‖x‖ ^ 2 := by
  have h_bound : ∀ i ∈ (Finset.univ : Finset (Fin m)), x i ^ 2 ≤ ‖x‖ ^ 2 := by
    intro i _
    have h := norm_le_pi_norm (f := x) (i := i)
    rw [Real.norm_eq_abs] at h
    calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
      _ ≤ ‖x‖ ^ 2 := by
        have h_abs_nonneg : 0 ≤ |x i| := abs_nonneg _
        nlinarith only [h, h_abs_nonneg, norm_nonneg x]
  calc
    ∑ i, x i ^ 2 ≤ (Finset.univ : Finset (Fin m)).card • ‖x‖ ^ 2 :=
      Finset.sum_le_card_nsmul _ _ _ h_bound
    _ = m * ‖x‖ ^ 2 := by rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The sup norm is bounded by the Euclidean norm: `‖x‖ ≤ √(∑ᵢ xᵢ²)`. -/
theorem norm_le_sqrt_sum_sq {m : ℕ} (x : Fin m → ℝ) : ‖x‖ ≤ Real.sqrt (∑ i, x i ^ 2) :=
  Real.le_sqrt_of_sq_le (sq_norm_le_sum_sq x)

/-- The Euclidean norm is bounded by `√m` times the sup norm:
`√(∑ᵢ xᵢ²) ≤ √m · ‖x‖`. -/
theorem sqrt_sum_sq_le_sqrt_card_mul_norm {m : ℕ} (x : Fin m → ℝ) :
    Real.sqrt (∑ i, x i ^ 2) ≤ Real.sqrt m * ‖x‖ := by
  have h1 : ∑ i, x i ^ 2 ≤ (m : ℝ) * ‖x‖ ^ 2 := sum_sq_le_card_mul_sq_norm x
  have h2 : Real.sqrt (∑ i, x i ^ 2) ≤ Real.sqrt ((m : ℝ) * ‖x‖ ^ 2) := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq (norm_nonneg x)] at h2

/-- Each coordinate is bounded by the sup norm: `|xᵢ| ≤ ‖x‖`. -/
theorem abs_apply_le_norm {m : ℕ} (x : Fin m → ℝ) (i : Fin m) : |x i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using norm_le_pi_norm (f := x) (i := i)

/-- Hölder's inequality with the sup norm on `x` and the `ℓ¹` norm on `y`:
`|∑ᵢ xᵢ yᵢ| ≤ ‖x‖ · ∑ᵢ |yᵢ|`. -/
theorem abs_sum_mul_le_norm_mul_sqrt {m : ℕ} (x y : Fin m → ℝ) :
    |∑ i, x i * y i| ≤ ‖x‖ * ∑ i, |y i| := by
  calc
    |∑ i, x i * y i| ≤ ∑ i, |x i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |x i| * |y i| := by simp [abs_mul]
    _ ≤ ∑ i, ‖x‖ * |y i| := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      have h := norm_le_pi_norm (f := x) (i := i)
      rw [Real.norm_eq_abs] at h
      exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
    _ = ‖x‖ * ∑ i, |y i| := by rw [Finset.mul_sum]

/-- Discrete Cauchy–Schwarz: the `ℓ¹` norm is bounded by `√m` times the
Euclidean norm, `∑ᵢ |yᵢ| ≤ √m · √(∑ᵢ yᵢ²)`. -/
theorem sum_abs_le_sqrt_card_mul_sqrt_sum_sq {m : ℕ} (y : Fin m → ℝ) :
    ∑ i, |y i| ≤ Real.sqrt m * Real.sqrt (∑ i, y i ^ 2) := by
  have h_sq : (∑ i, |y i|) ^ 2 ≤ (m : ℝ) * ∑ i, y i ^ 2 := by
    calc
      (∑ i, |y i|) ^ 2 = (∑ i, (1 : ℝ) * |y i|) ^ 2 := by simp
      _ ≤ (∑ _i : Fin m, (1 : ℝ) ^ 2) * ∑ i, (|y i|) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => |y i|)
      _ = (m : ℝ) * ∑ i, y i ^ 2 := by simp [sq_abs, Finset.card_univ]
  have h_eq : Real.sqrt m * Real.sqrt (∑ i, y i ^ 2) = Real.sqrt ((m : ℝ) * ∑ i, y i ^ 2) :=
    (Real.sqrt_mul (Nat.cast_nonneg m) _).symm
  rw [h_eq]
  exact Real.le_sqrt_of_sq_le h_sq

end CIV
