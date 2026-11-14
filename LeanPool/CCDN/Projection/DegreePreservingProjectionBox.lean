/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Height.Box
public import LeanPool.CCDN.Projection.CurvePrimitivePair
public import Mathlib.Data.Fin.VecNotation

/-!
Integral evaluation and coefficient-uniform height control for the two
moment coordinates in the degree-preserving projection.

Evaluation of the moment coordinates used by the bounded primitive pair.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Evaluating the moment coordinate with parameter `k` at `z` gives `∑ j, k ^ j * z j`. -/
lemma momentCoordinate_eval {K : Type*} [CommRing K] {n : ℕ}
    (k : ℕ) (z : Fin n → K) :
    eval z (momentCoordinate K n k) = ∑ j : Fin n, (k : K) ^ j.val * z j := by
  simp only [momentCoordinate, map_sum, map_mul, eval_C, eval_X]

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- The integer projection of `ℤⁿ` to `ℤ²` given by the two moment coordinates with parameters `k₀`
and `k₁`. -/
def degreeProjection (n k₀ k₁ : ℕ) (z : IntPoint n) : IntPoint 2 :=
  ![eval z (momentCoordinate ℤ n k₀), eval z (momentCoordinate ℤ n k₁)]

/-- The box scaling factor `(n + 1) * ((n + 1) * (d + 1)) ^ (2 * n)` for the moment projection in
`n` variables and degree `d`. -/
def projectionBoxFactor (n d : ℕ) : ℝ :=
  ((n : ℝ) + 1) * ((((n : ℝ) + 1) * ((d : ℝ) + 1)) ^ 2) ^ n

/-- The box scaling factor of the moment projection is at least one. -/
lemma projectionBoxFactor_one_le (n d : ℕ) : 1 ≤ projectionBoxFactor n d := by
  unfold projectionBoxFactor
  have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hd : (1 : ℝ) ≤ d + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hmul : (1 : ℝ) ≤ (n + 1) * (d + 1) := by nlinarith
  have hp : (1 : ℝ) ≤ ((((n : ℝ) + 1) * ((d : ℝ) + 1)) ^ 2) ^ n :=
    one_le_pow₀ (one_le_pow₀ hmul)
  nlinarith

private lemma momentCoordinate_height_of_le {n k : ℕ} {M B : ℝ}
    (hM : 1 ≤ M) (hk : (k : ℝ) ≤ M)
    (z : IntPoint n) (hz : InBox z B) :
    |(eval z (momentCoordinate ℤ n k) : ℝ)| ≤ n * M ^ n * B := by
  rw [momentCoordinate_eval, Int.cast_sum]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  calc
    _ ≤ ∑ j : Fin n, |(k : ℝ) ^ j.val * (z j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, M ^ n * B := by
      apply Finset.sum_le_sum
      intro j _
      have hp : (k : ℝ) ^ j.val ≤ M ^ n := by
        calc
          _ ≤ M ^ j.val := by gcongr
          _ ≤ _ := pow_le_pow_right₀ hM (Nat.le_of_lt j.isLt)
      simp only [abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      exact mul_le_mul hp (hz j) (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- For parameters `k₀ ≤ n ^ 2 * d` and `k₁ ≤ n * d ^ 2`, the moment projection maps the integer box
of radius `B` into the integer box of radius `projectionBoxFactor n d * B`. -/
lemma degreeProjection_box {n d k₀ k₁ : ℕ} (hk₀ : k₀ ≤ n ^ 2 * d)
    (hk₁ : k₁ ≤ n * d ^ 2) {B : ℝ} (hB : 0 ≤ B)
    {z : IntPoint n} (hz : z ∈ integerBox n B) :
    degreeProjection n k₀ k₁ z ∈ integerBox 2 (projectionBoxFactor n d * B) := by
  let M : ℝ := (((n : ℝ) + 1) * ((d : ℝ) + 1)) ^ 2
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd : (0 : ℝ) ≤ d := by positivity
  have hM : 1 ≤ M := by
    apply one_le_pow₀
    nlinarith [mul_nonneg hn hd]
  have hk₀M : (k₀ : ℝ) ≤ M := by
    have hh : (k₀ : ℝ) ≤ (n : ℝ) ^ 2 * d := by exact_mod_cast hk₀
    calc
      _ ≤ (n : ℝ) ^ 2 * d := hh
      _ ≤ ((n : ℝ) + 1) ^ 2 * ((d : ℝ) + 1) ^ 2 := by
        gcongr
        · linarith
        · nlinarith [sq_nonneg (d : ℝ)]
      _ = M := by dsimp [M]; ring
  have hk₁M : (k₁ : ℝ) ≤ M := by
    have hh : (k₁ : ℝ) ≤ (n : ℝ) * d ^ 2 := by exact_mod_cast hk₁
    calc
      _ ≤ (n : ℝ) * d ^ 2 := hh
      _ ≤ ((n : ℝ) + 1) ^ 2 * ((d : ℝ) + 1) ^ 2 := by
        gcongr
        · nlinarith [sq_nonneg (n : ℝ)]
        · linarith
      _ = M := by dsimp [M]; ring
  have hb := mem_integerBox.mp hz
  have hc : (n : ℝ) * M ^ n * B ≤ projectionBoxFactor n d * B := by
    unfold projectionBoxFactor
    gcongr
    norm_num
  apply mem_integerBox.mpr
  intro j
  fin_cases j
  · exact (momentCoordinate_height_of_le hM hk₀M z hb).trans hc
  · exact (momentCoordinate_height_of_le hM hk₁M z hb).trans hc

/-- Evaluating the integer moment coordinate at an integer point and casting to `ℚ` agrees with
evaluating the rational moment coordinate at the corresponding rational point. -/
lemma rationalPoint_moment_eval {n : ℕ} (k : ℕ) (z : IntPoint n) :
    (eval z (momentCoordinate ℤ n k) : ℚ) =
      eval (rationalPoint z) (momentCoordinate ℚ n k) := by
  simp [momentCoordinate_eval, rationalPoint]

/-- The rational point of the integer moment projection of `z` is the pair of rational moment
coordinates evaluated at `z`. -/
lemma rationalPoint_degreeProjection {n k₀ k₁ : ℕ} (z : IntPoint n) :
    rationalPoint (degreeProjection n k₀ k₁ z) =
      ![eval (rationalPoint z) (momentCoordinate ℚ n k₀),
        eval (rationalPoint z) (momentCoordinate ℚ n k₁)] := by
  funext j
  fin_cases j <;> exact rationalPoint_moment_eval _ _

end
end CCDN
