/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The homogeneous kernel-to-rank ratio differs from its leading term by
at most 1/M. Exact binomial identities avoid a formal asymptotic expansion. -/

@[expose] public section
namespace CCDN
noncomputable section

private lemma shifted_choose_successor_identity (r k : ℕ) :
    (r + k + 1) * (r + k).choose r = (r + 1 + k).choose (r + 1) * (r + 1) := by
  rw [show r + 1 + k = r + k + 1 by omega]
  exact Nat.add_one_mul_choose_eq (r + k) r

/-- Sharp leading term for the fraction of polynomial coefficients in the
homogeneous kernel, normalized by degree and rank. -/
theorem hypersurface_kernel_ratio_bounds {r d M s : ℕ} (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    1 / ((d : ℝ) * (r + 1 : ℝ)) - 1 / (M : ℝ) ≤
        ((r + 1 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) ∧
      ((r + 1 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) ≤
        1 / ((d : ℝ) * (r + 1 : ℝ)) + 1 / (M : ℝ) := by
  obtain ⟨hlo, hhi⟩ := hypersurface_rank_binomial_bounds hdM hr
  have hs : 0 < s := lt_of_lt_of_le
    (Nat.mul_pos hd (Nat.choose_pos (by omega : r ≤ r + (M - d)))) hlo
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hM0 : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hd hdM
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) < r + 1 := by positivity
  have hmd : (d : ℝ) ≤ M := by exact_mod_cast hdM
  let K : ℝ := (r + 1 + (M - d)).choose (M - d)
  let Qlo : ℝ := (r + (M - d)).choose r
  let Qhi : ℝ := (r + M).choose r
  have hlow : (d : ℝ) * Qlo ≤ s := by
    dsimp only [Qlo]
    exact_mod_cast hlo
  have hhigh : (s : ℝ) ≤ (d : ℝ) * Qhi := by
    dsimp only [Qhi]
    exact_mod_cast hhi
  have hK : ((r : ℝ) + (M - d) + 1) * Qlo = K * (r + 1) := by
    have hh := shifted_choose_successor_identity r (M - d)
    rw [Nat.choose_symm_add (a := r + 1) (b := M - d)] at hh
    have hhR := congrArg (fun x : ℕ => (x : ℝ)) hh
    push_cast [Nat.cast_sub hdM] at hhR
    exact hhR
  have hR : ((r : ℝ) + M + 1) * Qhi = ((s : ℝ) + K) * (r + 1) := by
    have hh := shifted_choose_successor_identity r M
    rw [Nat.choose_symm_add (a := r + 1) (b := M), ← hr] at hh
    have hhR := congrArg (fun x : ℕ => (x : ℝ)) hh
    push_cast [Nat.cast_sub hdM] at hhR
    exact hhR
  have hKmul : (d : ℝ) * (r + 1) * K ≤ ((M : ℝ) + r + 1) * s := by
    have hh := mul_le_mul_of_nonneg_left hlow
      (show 0 ≤ (r : ℝ) + (M - d) + 1 by have := Nat.cast_nonneg (α := ℝ) r; linarith)
    nlinarith [mul_nonneg hd0.le hs0.le]
  have hRmul : ((M : ℝ) + r + 1) * s ≤ (d : ℝ) * (r + 1) * ((s : ℝ) + K) := by
    have hh := mul_le_mul_of_nonneg_left hhigh (show 0 ≤ (r : ℝ) + M + 1 by positivity)
    nlinarith
  change 1 / ((d : ℝ) * (r + 1 : ℝ)) - 1 / (M : ℝ) ≤ K / ((M : ℝ) * s) ∧
    K / ((M : ℝ) * s) ≤ 1 / ((d : ℝ) * (r + 1 : ℝ)) + 1 / (M : ℝ)
  constructor
  · apply (le_div_iff₀ (mul_pos hM0 hs0)).mpr
    field_simp
    nlinarith [mul_nonneg hr0.le hs0.le]
  · apply (div_le_iff₀ (mul_pos hM0 hs0)).mpr
    field_simp
    have hh : ((r : ℝ) + 1) * s ≤ (d : ℝ) * (r + 1) * s := by
      nlinarith [mul_le_mul_of_nonneg_right hd1 (mul_nonneg hr0.le hs0.le)]
    nlinarith

end
end CCDN
