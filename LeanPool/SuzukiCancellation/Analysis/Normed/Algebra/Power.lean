/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Tactic.NoncommRing

/-!
# Noncommutative power differences and polynomial remainders

Separate bounds on the two inputs retain the asymmetric geometric constant. Homogeneous
corrections give bounds for the second, third, and fourth powers of a perturbed input.

## Main results

* `FQFP.norm_pow_sub_pow_le_of_le`.
* `FQFP.norm_sq_sub_sq_le`.
* `FQFP.norm_sub_le_succ_pow_div`.
* `FQFP.norm_sq_sub_corrections_le`.
* `FQFP.norm_cube_sub_corrections_le`.
* `FQFP.norm_fourth_sub_linear_le`.
-/

@[expose] public section
open Finset
namespace FQFP

variable {A : Type*} [NormedRing A]

/-- A power difference with separate bounds for its two inputs. -/
lemma norm_pow_sub_pow_le_of_le (x y : A) {X Y d : ℝ}
    (hx : ‖x‖ ≤ X) (hy : ‖y‖ ≤ Y) (hd : ‖x - y‖ ≤ d) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ d * ∑ i ∈ range (n + 1), X ^ i * Y ^ (n - i) := by
  induction n with
  | zero => simpa using hd
  | succ n ih =>
    have hgeom : (∑ i ∈ range (n + 2), X ^ i * Y ^ (n + 1 - i)) =
        X * (∑ i ∈ range (n + 1), X ^ i * Y ^ (n - i)) + Y ^ (n + 1) := by
      rw [sum_range_succ']
      simp only [Nat.add_sub_add_right, pow_zero, one_mul]
      rw [mul_sum]
      congr 1
      apply sum_congr rfl
      intro i hi
      rw [pow_succ]
      ring
    have heq : x ^ (n + 2) - y ^ (n + 2) =
        x * (x ^ (n + 1) - y ^ (n + 1)) + (x - y) * y ^ (n + 1) := by
      simp only [pow_succ', mul_sub, sub_mul]
      noncomm_ring
    rw [heq]
    calc
      _ ≤ X * (d * ∑ i ∈ range (n + 1), X ^ i * Y ^ (n - i)) + d * Y ^ (n + 1) :=
        norm_add_le_of_le (norm_mul_le_of_le hx ih)
          (norm_mul_le_of_le hd ((norm_pow_le' y (Nat.succ_pos n)).trans
            (pow_le_pow_left₀ (norm_nonneg y) hy (n + 1))))
      _ = _ := by
        rw [hgeom]
        ring

/-- With a common norm bound, every term of the telescoping sum has the same majorant. -/
lemma norm_pow_sub_pow_le_of_common_bound (x y : A) {M : ℝ}
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ n * M ^ (n - 1) * ‖x - y‖ := by
  cases n with
  | zero => simp
  | succ k =>
    have hsum : ∑ i ∈ range (k + 1), M ^ i * M ^ (k - i) = (k + 1 : ℕ) * M ^ k := by
      calc
        _ = ∑ _i ∈ range (k + 1), M ^ k := by
          apply sum_congr rfl
          intro i hi
          rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hi))]
        _ = _ := by simp
    simpa only [hsum, Nat.add_one_sub_one, mul_comm ‖x - y‖] using
      norm_pow_sub_pow_le_of_le x y hx hy le_rfl k

/-- A noncommutative square difference is controlled by the difference of its inputs. -/
lemma norm_sq_sub_sq_le {𝔸 : Type*} [NormedRing 𝔸] (x y : 𝔸) :
    ‖x ^ 2 - y ^ 2‖ ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  simpa [sum_range_succ, add_comm, mul_comm] using
    norm_pow_sub_pow_le_of_le x y le_rfl le_rfl le_rfl 1

/-! ### Homogeneous polynomial corrections -/

/-- A lower-order remainder and one homogeneous term give the next-order large-input bound. -/
lemma norm_sub_le_succ_pow_div {E : Type*} [SeminormedAddCommGroup E]
    (x y : E) (n : ℕ) {K L s d : ℝ} (hs : 0 ≤ s) (hd : 0 < d) (hd1 : d ≤ 1)
    (hx : ‖x‖ ≤ K * s ^ n / d) (hy : ‖y‖ ≤ s ^ n) (hKL : K + 1 ≤ L * s) :
    ‖x - y‖ ≤ L * s ^ (n + 1) / d := by
  calc
    _ ≤ K * s ^ n / d + s ^ n := (norm_sub_le x y).trans (add_le_add hx hy)
    _ = (K * s ^ n + s ^ n * d) / d := by field_simp
    _ ≤ ((K + 1) * s ^ n) / d := by
      apply div_le_div_of_nonneg_right _ hd.le
      nlinarith only [mul_le_mul_of_nonneg_left hd1 (pow_nonneg hs n)]
    _ ≤ L * s ^ (n + 1) / d := by
      apply div_le_div_of_nonneg_right _ hd.le
      calc
        _ ≤ (L * s) * s ^ n := mul_le_mul_of_nonneg_right hKL (pow_nonneg hs n)
        _ = _ := by ring

/-- A square after corrections of degrees two, three, and four. -/
lemma norm_sq_sub_corrections_le (z P T₂ T₃ T₄ : A) {s : ℝ}
    (hz : ‖z‖ ≤ s) (hT₂ : ‖T₂‖ ≤ s ^ 2)
    (hR₃ : ‖P - T₂‖ ≤ s ^ 3) (hR₄ : ‖P - T₂ - T₃‖ ≤ s ^ 4)
    (hR₅ : ‖P - T₂ - T₃ - T₄‖ ≤ s ^ 5) :
    ‖(z + P) ^ 2 - z ^ 2 - (z * T₂ + T₂ * z) -
      (z * T₃ + T₂ ^ 2 + T₃ * z) -
      (z * T₄ + T₂ * T₃ + T₃ * T₂ + T₄ * z)‖ ≤ 5 * s ^ 6 := by
  have heq : (z + P) ^ 2 - z ^ 2 - (z * T₂ + T₂ * z) -
      (z * T₃ + T₂ ^ 2 + T₃ * z) - (z * T₄ + T₂ * T₃ + T₃ * T₂ + T₄ * z) =
      z * (P - T₂ - T₃ - T₄) + (P - T₂ - T₃ - T₄) * z +
        T₂ * (P - T₂ - T₃) + (P - T₂ - T₃) * T₂ + (P - T₂) ^ 2 := by
    noncomm_ring
  rw [heq]
  have hsq : ‖(P - T₂) ^ 2‖ ≤ (s ^ 3) ^ 2 :=
    (norm_pow_le' _ (by norm_num)).trans (pow_le_pow_left₀ (norm_nonneg _) hR₃ 2)
  exact (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
    (norm_add_le_of_le (norm_mul_le_of_le hz hR₅) (norm_mul_le_of_le hR₅ hz))
      (norm_mul_le_of_le hT₂ hR₄)) (norm_mul_le_of_le hR₄ hT₂)) hsq).trans_eq (by ring)

/-- A cube after its degree-four and degree-five homogeneous corrections. -/
lemma norm_cube_sub_corrections_le (z P T₂ T₃ : A) {s : ℝ}
    (hz : ‖z‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2) (hT₂ : ‖T₂‖ ≤ s ^ 2)
    (hR₃ : ‖P - T₂‖ ≤ s ^ 3) (hR₄ : ‖P - T₂ - T₃‖ ≤ s ^ 4) :
    ‖(z + P) ^ 3 - z ^ 3 - (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
      (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z)‖ ≤ 10 * s ^ 6 := by
  have hz2 : ‖z ^ 2‖ ≤ s ^ 2 :=
    (norm_pow_le' z (by norm_num)).trans (pow_le_pow_left₀ (norm_nonneg z) hz 2)
  have hsquare : ‖P ^ 2 - T₂ ^ 2‖ ≤ 2 * s ^ 5 :=
    ((norm_sq_sub_sq_le P T₂).trans
      (mul_le_mul (add_le_add hP hT₂) hR₃ (norm_nonneg _)
        (add_nonneg (sq_nonneg s) (sq_nonneg s)))).trans_eq (by ring)
  have hmiddle : ‖P * z * P - T₂ * z * T₂‖ ≤ 2 * s ^ 6 := by
    rw [show P * z * P - T₂ * z * T₂ =
      (P - T₂) * z * P + T₂ * z * (P - T₂) by noncomm_ring]
    exact (norm_add_le_of_le (norm_mul_le_of_le (norm_mul_le_of_le hR₃ hz) hP)
      (norm_mul_le_of_le (norm_mul_le_of_le hT₂ hz) hR₃)).trans_eq (by ring)
  have hcube : ‖P ^ 3‖ ≤ (s ^ 2) ^ 3 :=
    (norm_pow_le' P (by norm_num)).trans (pow_le_pow_left₀ (norm_nonneg P) hP 3)
  have heq : (z + P) ^ 3 - z ^ 3 - (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
      (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) =
      z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z + (P - T₂ - T₃) * z ^ 2 +
        z * (P ^ 2 - T₂ ^ 2) + (P * z * P - T₂ * z * T₂) +
          (P ^ 2 - T₂ ^ 2) * z + P ^ 3 := by noncomm_ring
  rw [heq]
  exact (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
    (norm_add_le_of_le (norm_add_le_of_le (norm_mul_le_of_le hz2 hR₄)
      (norm_mul_le_of_le (norm_mul_le_of_le hz hR₄) hz)) (norm_mul_le_of_le hR₄ hz2))
        (norm_mul_le_of_le hz hsquare)) hmiddle) (norm_mul_le_of_le hsquare hz))
          hcube).trans_eq (by ring)

/-- A fourth power after a first-order correction of degree two. -/
lemma norm_fourth_sub_linear_le (y z T₂ : A) {s : ℝ}
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖z‖ ≤ s) (hP : ‖y - z‖ ≤ s ^ 2)
    (hR₃ : ‖y - z - T₂‖ ≤ s ^ 3) :
    ‖y ^ 4 - z ^ 4 -
      (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3)‖ ≤ 15 * s ^ 6 := by
  let U := y ^ 2 - z ^ 2
  let D := U - (z * T₂ + T₂ * z)
  have hU : ‖U‖ ≤ 3 * s ^ 3 :=
    ((norm_sq_sub_sq_le y z).trans
      (mul_le_mul (add_le_add hy hz) hP (norm_nonneg _)
        (by
          have := (norm_nonneg z).trans hz
          positivity))).trans_eq (by ring)
  have hP2 : ‖(y - z) ^ 2‖ ≤ (s ^ 2) ^ 2 :=
    (norm_pow_le' _ (by norm_num)).trans (pow_le_pow_left₀ (norm_nonneg _) hP 2)
  have hD : ‖D‖ ≤ 3 * s ^ 4 := by
    have heq : D = z * (y - z - T₂) + (y - z - T₂) * z + (y - z) ^ 2 := by
      dsimp only [D, U]
      noncomm_ring
    rw [heq]
    exact (norm_add_le_of_le (norm_add_le_of_le (norm_mul_le_of_le hz hR₃)
      (norm_mul_le_of_le hR₃ hz)) hP2).trans_eq (by ring)
  have hz2 : ‖z ^ 2‖ ≤ s ^ 2 :=
    (norm_pow_le' z (by norm_num)).trans (pow_le_pow_left₀ (norm_nonneg z) hz 2)
  have hU2 : ‖U ^ 2‖ ≤ (3 * s ^ 3) ^ 2 :=
    (norm_pow_le' U (by norm_num)).trans (pow_le_pow_left₀ (norm_nonneg U) hU 2)
  have heq : y ^ 4 - z ^ 4 -
      (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3) =
      z ^ 2 * D + D * z ^ 2 + U ^ 2 := by
    dsimp only [D, U]
    noncomm_ring
  rw [heq]
  exact (norm_add_le_of_le (norm_add_le_of_le (norm_mul_le_of_le hz2 hD)
    (norm_mul_le_of_le hD hz2)) hU2).trans_eq (by ring)

end FQFP
