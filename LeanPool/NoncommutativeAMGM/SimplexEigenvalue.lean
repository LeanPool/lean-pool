/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.SimplexSymmetry

/-! # The explicit counterexample eigenvalue in Appendix A -/

@[expose] public section

namespace NoncommutativeAMGM
open Matrix
open scoped BigOperators

/-- The trigonometric choice of `α` in the paper. -/
noncomputable def simplexAngleAlpha (n : ℕ) (θ : ℝ) : ℝ :=
  (n : ℝ) / ((n : ℝ) - 1) * Real.cos θ ^ 2

/-- The nonnegative choice of `β` in the paper. -/
noncomputable def simplexAngleBeta (n : ℕ) (θ : ℝ) : ℝ :=
  Real.sqrt ((n : ℝ) - 1 - ((n : ℝ) - 2) * simplexAngleAlpha n θ)

/-- The square-root parameter is real and satisfies the exact normalization relation. -/
theorem simplexAngle_parameters {n : ℕ} (hn : 3 ≤ n) (θ : ℝ) :
    0 ≤ simplexAngleAlpha n θ ∧
      ((n : ℝ) - 2) * simplexAngleAlpha n θ + simplexAngleBeta n θ ^ 2 =
        (n : ℝ) - 1 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hα : 0 ≤ simplexAngleAlpha n θ := by unfold simplexAngleAlpha; positivity
  refine ⟨hα, ?_⟩
  have htwo : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
  have hc := Real.cos_sq_le_one θ
  have hbound : ((n : ℝ) - 2) * simplexAngleAlpha n θ ≤ (n : ℝ) - 1 := by
    dsimp [simplexAngleAlpha]
    calc
      _ = ((n : ℝ) - 2) * (n : ℝ) * Real.cos θ ^ 2 / ((n : ℝ) - 1) := by ring
      _ ≤ ((n : ℝ) - 2) * (n : ℝ) / ((n : ℝ) - 1) :=
        div_le_div_of_nonneg_right (mul_le_of_le_one_right (by positivity) hc) hd.le
      _ ≤ ((n : ℝ) - 1) ^ 2 / ((n : ℝ) - 1) := by
        apply div_le_div_of_nonneg_right _ hd.le
        nlinarith
      _ = (n : ℝ) - 1 := by field_simp
  have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ) - 1 -
      ((n : ℝ) - 2) * simplexAngleAlpha n θ by linarith)
  dsimp [simplexAngleBeta]
  linarith

/-- The trigonometric parameters give an actual PSD family with exact sum `nI`. -/
theorem simplexAngle_family {n : ℕ} (hn : 3 ≤ n) (θ : ℝ) :
    (∀ i, (simplexMatrix n (simplexAngleAlpha n θ) (simplexAngleBeta n θ) i).PosSemidef) ∧
      ∑ i, simplexMatrix n (simplexAngleAlpha n θ) (simplexAngleBeta n θ) i =
        (n : ℝ) • 1 := by
  obtain ⟨hα, hαβ⟩ := simplexAngle_parameters hn θ
  exact ⟨simplexMatrix_posSemidef (by omega) hα, simplexMatrix_sum (by omega) _ _ hαβ⟩

/-- Appendix A's formula for the eigenvalue of the constructed matrix average. -/
theorem simplexMean_integral_phase_eigenvector {n m ℓ : ℕ} (hn : 3 ≤ n) (hmn : m ≤ n)
    (hm : 1 ≤ m) (θ : ℝ) (hθ : Real.sin θ ≠ 0)
    (hphase : ((m - 1 : ℕ) : ℝ) * θ = (ℓ : ℝ) * Real.pi) :
    withoutReplacementMean n m
        (simplexMatrix n (simplexAngleAlpha n θ) (simplexAngleBeta n θ)) *ᵥ
          simplexAxis n =
      ((-1 : ℝ) ^ ℓ * ((n : ℝ) / ((n : ℝ) - 1) * Real.cos θ) ^ (m - 1)) •
        simplexAxis n := by
  obtain ⟨_, hαβ⟩ := simplexAngle_parameters hn θ
  rw [simplexMean_axis_eigenvector (by omega) hmn _ _ hαβ]
  have ha : 2 * simplexAngleAlpha n θ =
      2 * ((n : ℝ) / ((n : ℝ) - 1) * Real.cos θ) * Real.cos θ := by
    dsimp [simplexAngleAlpha]
    ring
  have hb : simplexAngleAlpha n θ * (n : ℝ) / ((n : ℝ) - 1) =
      ((n : ℝ) / ((n : ℝ) - 1) * Real.cos θ) ^ 2 := by
    dsimp [simplexAngleAlpha]
    ring
  rw [ha, hb, simplexRecurrence_integral_phase _ θ hm hθ hphase]

/-- Equation (7), with the paper's angle `ℓπ/(m-1)`; valid for every interior phase. -/
theorem simplexMean_angle_eigenvector {n m ℓ : ℕ} (hn : 3 ≤ n) (hmn : m ≤ n)
    (hℓ : 0 < ℓ) (hℓm : ℓ + 1 < m) :
    let θ := (ℓ : ℝ) * Real.pi / ((m : ℝ) - 1)
    withoutReplacementMean n m
        (simplexMatrix n (simplexAngleAlpha n θ) (simplexAngleBeta n θ)) *ᵥ
          simplexAxis n =
      ((-1 : ℝ) ^ ℓ * ((n : ℝ) / ((n : ℝ) - 1) * Real.cos θ) ^ (m - 1)) •
        simplexAxis n := by
  have hm : 1 ≤ m := by omega
  have hm' : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hℓm' : (ℓ : ℝ) < (m : ℝ) - 1 := by
    exact_mod_cast (show ℓ < m - 1 by omega)
  let θ := (ℓ : ℝ) * Real.pi / ((m : ℝ) - 1)
  have hθ0 : 0 < θ := by dsimp [θ]; positivity
  have hθπ : θ < Real.pi := by
    dsimp [θ]
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (m : ℝ) - 1)).mpr
    nlinarith [Real.pi_pos]
  apply simplexMean_integral_phase_eigenvector hn hmn hm θ
    (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ))
  rw [Nat.cast_sub hm, Nat.cast_one]
  dsimp [θ]
  field_simp

end NoncommutativeAMGM
