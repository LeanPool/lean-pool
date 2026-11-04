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
import LeanPool.CCDN.AuxiliaryPolynomial.RatioEstimates
import LeanPool.CCDN.ForMathlib.Log

/-! The small-height numerical auxiliary-degree bound, with exact box and
coefficient exponents and a constant depending only on dimension. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The additive error term, depending only on the dimension `r` and the constant `E`, in the
small-height logarithmic bound on the auxiliary degree `M`. -/
def hypersurfaceSmallHeightError (r : ℕ) (E : ℝ) : ℝ :=
  (E + hypersurfaceRankLogError r + 4 * (r + 1 : ℝ) ^ 2) / r

/-- Solve the normalized exact-rank inequality in the small-height range. -/
theorem hypersurface_small_height_log_degree_bound {r d M s : ℕ}
    (hrpos : 0 < r) (hd : 0 < d) (hM : 2 * d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M)
    (B L A E : ℝ) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hheight : Real.log L ≤ 2 * d * (r + 1 : ℝ) * Real.log B)
    (hscale : (d : ℝ) * Real.log B ≤ (d : ℝ) ^ (1 / (r : ℝ)) * M)
    (hcomparison : (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) /
        ((r + 1 : ℝ) * M) *
        (Real.log s - (r : ℝ) * (4 * Real.log d + Real.log A) - E) ≤
      Real.log B - ((r + 1 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) * Real.log L) :
    Real.log M ≤ hypersurfaceSmallHeightError r E + (4 - 1 / (r : ℝ)) * Real.log d + Real.log A +
      (r + 1 : ℝ) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) * Real.log B -
        Real.log L / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ))) := by
  have hdM : d ≤ M := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hd hdM
  have hX : (0 : ℝ) < (d : ℝ) ^ (1 / (r : ℝ)) := by positivity
  obtain ⟨hl, hu⟩ := hypersurface_rank_root_bounds hrpos hdM hr
  have halow : (d : ℝ) ^ (1 / (r : ℝ)) * ((M : ℝ) - d) / ((r + 1 : ℝ) * M) ≤
      (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) / ((r + 1 : ℝ) * M) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have haup := div_le_div_of_nonneg_right hu (show 0 ≤ (r + 1 : ℝ) * M by positivity)
  have hk := (hypersurface_kernel_ratio_bounds hd hdM hr).1
  have hh := auxiliary_small_height_bracket_bound (r := (r : ℝ)) (Nat.cast_nonneg r)
    (by exact_mod_cast hd) (by exact_mod_cast hM) hX halow haup (by positivity) hk
    (Real.log_nonneg hB) (Real.log_nonneg hL) hheight hscale hcomparison
  have hlog := (abs_le.mp (hypersurface_rank_log_error hrpos hd hM hr)).1
  have hraw : (r : ℝ) * Real.log M ≤ (r + 1 : ℝ) / (d : ℝ) ^ (1 / (r : ℝ)) * Real.log B -
      Real.log L / ((d : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) +
      4 * (r + 1 : ℝ) ^ 2 + E + hypersurfaceRankLogError r +
      (4 * (r : ℝ) - 1) * Real.log d + r * Real.log A := by
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hraw hr0.le
  rw [mul_div_cancel_left₀ (Real.log M) hr0.ne'] at hdiv
  convert hdiv using 1
  unfold hypersurfaceSmallHeightError
  field_simp
  ring

/-- Exponentiating retains all exponents in CCDN's coefficient-sensitive
auxiliary bound. -/
theorem hypersurface_degree_bound_of_log_bound {r d M : ℕ} {B L A C : ℝ}
    (hd : 0 < d) (hM : 0 < M) (hB : 0 < B) (hL : 0 < L) (hA : 0 < A)
    (hlog : Real.log M ≤ C + (4 - 1 / (r : ℝ)) * Real.log d + Real.log A +
      (r + 1 : ℝ) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) * Real.log B -
        Real.log L / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) :
    (M : ℝ) ≤ Real.exp C * (d : ℝ) ^ (4 - 1 / (r : ℝ)) * A *
      B ^ ((r + 1 : ℝ) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) /
        L ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine Real.natCast_le_of_log_le_log hM (by positivity) ?_
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hA.ne',
    Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
    Real.log_rpow hdR, Real.log_rpow hB, Real.log_rpow hL]
  convert hlog using 1
  ring

end
end CCDN
