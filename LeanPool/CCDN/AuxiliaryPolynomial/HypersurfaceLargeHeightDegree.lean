/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceRankLogarithm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceKernelRatio
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceRankRoots
import LeanPool.CCDN.AuxiliaryPolynomial.LargeHeightRatios
import LeanPool.CCDN.ForMathlib.Log

/-! The large-height auxiliary-degree calculation eliminates both the radius
and coefficient height, leaving O_r(d^(4-1/r)). -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The additive error term, depending only on the dimension `r` and the constants `E` and `T`,
in the large-height bound `log M ≤ hypersurfaceLargeHeightError r E T + (4 - 1/r) log d`. -/
def hypersurfaceLargeHeightError (r : ℕ) (E T : ℝ) : ℝ :=
  Real.log (8 * (r : ℝ)) + (E + hypersurfaceRankLogError r + T) / r

/-- The large-height normalized determinant inequality gives a degree bound
independent of B and H; positioning is stated with its precise height cost. -/
theorem hypersurface_large_height_log_degree_bound {r d M s : ℕ}
    (hrpos : 0 < r) (hd : 0 < d) (hM : 8 * d * (r + 1) ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M)
    (B L H E T : ℝ) (hB : 1 ≤ B) (hL : 1 ≤ L) (hH : 1 ≤ H) (hT : 0 ≤ T)
    (hheight : 2 * d * (r + 1 : ℝ) * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log L + T * d * (d : ℝ) ^ (1 / (r : ℝ)))
    (hcomparison : (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) /
        ((r + 1 : ℝ) * M) *
        (Real.log s - (r : ℝ) * (4 * Real.log d + Real.log (1 + Real.log H / (d : ℝ) ^ 2)) - E) ≤
      Real.log B - ((r + 1 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) * Real.log L) :
    Real.log M ≤ hypersurfaceLargeHeightError r E T + (4 - 1 / (r : ℝ)) * Real.log d := by
  have hM2 : 2 * d ≤ M := by nlinarith
  have hdM : d ≤ M := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hrpos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hd hdM
  have hX : (0 : ℝ) < (d : ℝ) ^ (1 / (r : ℝ)) := by positivity
  obtain ⟨hl, hu⟩ := hypersurface_rank_root_bounds hrpos hdM hr
  have halow : (d : ℝ) ^ (1 / (r : ℝ)) * ((M : ℝ) - d) / ((r + 1 : ℝ) * M) ≤
      (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) / ((r + 1 : ℝ) * M) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have haup := div_le_div_of_nonneg_right hu (show 0 ≤ (r + 1 : ℝ) * M by positivity)
  have hk := (hypersurface_kernel_ratio_bounds hd hdM hr).1
  have hh := auxiliary_large_height_bracket_bound (r := (r : ℝ)) (Nat.cast_nonneg r)
    hd1 (by exact_mod_cast hM) hX halow haup (by positivity) hk
    (Real.log_nonneg hB) (Real.log_nonneg hL) hT hheight hposition hcomparison
  have hlog := (abs_le.mp (hypersurface_rank_log_error hrpos hd hM2 hr)).1
  have hXle : (d : ℝ) ^ (1 / (r : ℝ)) ≤ d := by
    calc
      _ ≤ (d : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hd1 ((div_le_one hr0).mpr hr1)
      _ = _ := Real.rpow_one _
  have hHlog := Real.log_nonneg hH
  have hcost := log_one_add_le_linear_add_log
    (div_nonneg hHlog (sq_nonneg (d : ℝ))) (show 1 ≤ 8 * (r : ℝ) by linarith)
  have hcost' := mul_le_mul_of_nonneg_left hcost hr0.le
  have he : (r : ℝ) * (Real.log H / (d : ℝ) ^ 2 / (8 * (r : ℝ))) =
      Real.log H / (8 * (d : ℝ) ^ 2) := by field_simp
  have hcancel : (r : ℝ) * Real.log (1 + Real.log H / (d : ℝ) ^ 2) -
      Real.log H / (8 * d * (d : ℝ) ^ (1 / (r : ℝ))) ≤ r * Real.log (8 * (r : ℝ)) := by
    have hden : 8 * (d : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)) ≤ 8 * (d : ℝ) ^ 2 := by nlinarith
    have hdiv := div_le_div_of_nonneg_left hHlog
      (show 0 < 8 * d * (d : ℝ) ^ (1 / (r : ℝ)) by positivity) hden
    rw [mul_add, he] at hcost'
    linarith
  have hraw : (r : ℝ) * Real.log M ≤ (4 * (r : ℝ) - 1) * Real.log d +
      r * Real.log (8 * (r : ℝ)) + E + hypersurfaceRankLogError r + T := by nlinarith
  have hdiv := div_le_div_of_nonneg_right hraw hr0.le
  rw [mul_div_cancel_left₀ (Real.log M) hr0.ne'] at hdiv
  convert hdiv using 1
  unfold hypersurfaceLargeHeightError
  field_simp
  ring

/-- Exponentiating a logarithmic degree bound: if `log M ≤ C + (4 - 1/r) log d` with `d` and `M`
positive, then `M ≤ exp C * d ^ (4 - 1/r)`. -/
lemma hypersurface_large_degree_bound_of_log_bound {r d M : ℕ} {C : ℝ}
    (hd : 0 < d) (hM : 0 < M)
    (hlog : Real.log M ≤ C + (4 - 1 / (r : ℝ)) * Real.log d) :
    (M : ℝ) ≤ Real.exp C * (d : ℝ) ^ (4 - 1 / (r : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine Real.natCast_le_of_log_le_log hM (by positivity) ?_
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_rpow hdR]
  exact hlog

end
end CCDN
