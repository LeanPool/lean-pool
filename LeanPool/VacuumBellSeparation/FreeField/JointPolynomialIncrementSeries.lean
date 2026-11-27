/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialIncrementNuclear

/-! # Genuine summation and a cubic majorant for the actual increments -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian Filter
open scoped Topology

theorem sum_jointPolynomialIncrement {μ s : ℝ}
    (hμ : 0 < μ) (hs : 600 ≤ s) (N : ℕ) :
    (∑ n ∈ Finset.range N, jointPolynomialIncrement hμ hs n) = jointPolynomialKernelOperator hμ
      hs N := by
  induction N with
  | zero => simp only [Finset.sum_range_zero, jointPolynomialKernelOperator_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, jointPolynomialIncrement]
    abel

theorem summable_norm_jointPolynomialIncrement {μ s : ℝ}
    (hμ : 0 < μ) (hs : 157286400 ≤ s) :
    Summable (fun n => ‖jointPolynomialIncrement hμ (show 600 ≤ s by linarith) n‖) := by
  have hs₀ : 0 < s := by linarith
  have hq₀ : 0 ≤ 78643200 / s := by positivity
  have hq₁ : 78643200 / s < 1 := (div_lt_one hs₀).mpr (by linarith)
  exact ((summable_geometric_of_lt_one hq₀ hq₁).mul_left
    (2 * jointPolynomialErrorConstant * jointCommonEnvelope μ s)).of_nonneg_of_le
      (fun n => norm_nonneg (jointPolynomialIncrement hμ (show 600 ≤ s by linarith) n))
      (norm_jointPolynomialIncrement_le hμ hs)

-- The normed-group summation lemma must be matched against the operator-space
-- `HasSum` instances on the completed source space; this instance unification is
-- slow but terminates (about 94 s in a test build).
theorem hasSum_jointPolynomialIncrement {μ s : ℝ}
    (hμ : 0 < μ) (hs : 157286400 ≤ s) :
    HasSum (jointPolynomialIncrement hμ (show 600 ≤ s by linarith))
      (jointDifferenceKernelOperator hμ (show 600 ≤ s by linarith)) := by
  have hsum := summable_norm_jointPolynomialIncrement hμ hs
  have htend : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, jointPolynomialIncrement hμ (show 600 ≤ s by linarith) n)
      Filter.atTop (𝓝 (jointDifferenceKernelOperator hμ (show 600 ≤ s by linarith))) := by
    simpa only [sum_jointPolynomialIncrement] using jointPolynomialKernelOperator_tendsto hμ hs
  -- Fix the normed group first, so its instances are synthesized before unification.
  exact (hasSum_iff_tendsto_nat_of_summable_norm
    (E := SourceHilbert hμ (jointSourceRegion s) →L[ℝ] SourceHilbert hμ (jointSourceRegion s))
    hsum).mpr htend

theorem continuous_complexify_operator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Continuous (fun A : E →L[ℝ] E => complexify A) := by
  have hi : Isometry (fun A : E →L[ℝ] E => complexify A) :=
    isometry_iff_dist_eq.mpr fun A B => by
      rw [dist_eq_norm, dist_eq_norm, ← complexify_sub_real, norm_complexify]
  exact hi.continuous

theorem hasSum_complexified_jointPolynomialIncrement {μ s : ℝ}
    (hμ : 0 < μ) (hs : 157286400 ≤ s) :
    HasSum (fun n => complexify (jointPolynomialIncrement hμ (show 600 ≤ s by linarith) n))
      (complexify (jointDifferenceKernelOperator hμ (show 600 ≤ s by linarith))) := by
  let φ : (SourceHilbert hμ (jointSourceRegion s) →L[ℝ] SourceHilbert hμ (jointSourceRegion s)) →+
      (ComplexSourceHilbert hμ (jointSourceRegion s) →L[ℂ] ComplexSourceHilbert hμ
        (jointSourceRegion s)) :=
    { toFun := complexify, map_zero' := complexify_zero, map_add' := complexify_add }
  exact (hasSum_jointPolynomialIncrement hμ hs).map φ continuous_complexify_operator

theorem jointPolynomialIncrementRank_le (n : ℕ) :
    (jointPolynomialIncrementRank n : ℝ) ≤ 2000 * ((n : ℝ) + 1) ^ 3 := by
  have h : 9 * ((n : ℝ) + 1) + 1 ≤ 10 * ((n : ℝ) + 1)
    := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 9 * ((n : ℝ) + 1) + 1) h 3
  simp only [jointPolynomialIncrementRank, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat]
  nlinarith

theorem nuclear_jointPolynomialIncrement_cubic {μ s : ℝ}
    (hμ : 0 < μ) (hs : 157286400 ≤ s) (n : ℕ) :
    operatorTraceNorm (complexify (jointPolynomialIncrement hμ (show 600 ≤ s by linarith) n)) ≤
      ENNReal.ofReal ((4000 * jointPolynomialErrorConstant * jointCommonEnvelope μ s) *
        ((n : ℝ) + 1) ^ 3 * (78643200 / s) ^ n) := by
  apply (nuclear_jointPolynomialIncrement_le hμ hs n).trans
  apply ENNReal.ofReal_le_ofReal
  have hC := jointPolynomialErrorConstant_pos.le
  have hE := jointCommonEnvelope_nonneg μ s
  have hs₀ : 0 < s := by linarith
  calc
    _ ≤ (2000 * ((n : ℝ) + 1) ^ 3) *
        (2 * jointPolynomialErrorConstant * jointCommonEnvelope μ s * (78643200 / s) ^ n) :=
      mul_le_mul_of_nonneg_right (jointPolynomialIncrementRank_le n) (by positivity)
    _ = _ := by ring

end VacuumBellSeparation
