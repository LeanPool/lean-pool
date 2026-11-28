/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Cube.Splines
public import LeanPool.FunctionSpaces.Domains.Cube.PiecewiseJackson

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Jackson's inequality for tensor splines on the cube

For `1 ≤ p < ∞` and `r ≥ 1` there is `C_J < ∞` with `E_{2^k}(f)_p ≤ C_J ω_r(f, 2^(-k))_p` for every
`f ∈ L_p(Q)`, `Q = [0, 1]^d`, and every level `k`, where `E` is the error of best approximation
by splines of order `r` in each variable (`Cube.exists_approxError_cubeSplineScheme_le`).

For `k ≥ r + 2` the approximant of a bounded continuous `f` is the tensor quasi-interpolant. In
coordinate `i`, every slice of `f - Q_k^{(i)} f` is the error of the quasi-interpolant in one
variable, and `Interval.exists_eLpNorm_sub_qi_le_of_taylor` bounds it by the smoothings of `f` in
coordinate `i` on `{x_i ≤ 3/4}` and `{x_i ≥ 1/4}` (`Cube.exists_left_cubeSmoothing`,
`Cube.exists_right_cubeSmoothing` with `L = 2^(-k)`); the windows of the quasi-interpolant have
length at most `1/4`. The transfer lemma `Cube.eLpNorm_sub_slicewise_le_of_smoothing` passes the
bound to the cube (`Cube.exists_eLpNorm_sub_slicewise_qiKernel_le`), and the errors telescope over
the coordinates (`Cube.KernelOp.eLpNorm_sub_foldSlicewise_le_of_coord`). The coarse levels
`k ≤ r + 1` use Whitney's inequality on the cube at the scale `2^(-(r+1))`: the splines of level
`0` contain the polynomials of degree `< r` in each variable.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal BoundedContinuousFunction

namespace Cube

open Interval

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Jackson's estimate for splines in one coordinate**: there is `B < ∞` with
`‖f - Q_k^{(i)} f‖_{L_p(Q)} ≤ B ω_r^{(i)}(f, 2^(-k))_p` for every continuous `f`, every
coordinate `i` and every `k ≥ r + 2`. -/
theorem exists_eLpNorm_sub_slicewise_qiKernel_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ {f : (Fin d → ℝ) → ℂ}, Continuous f → ∀ (i : Fin d) {k : ℕ},
      r + 2 ≤ k → eLpNorm (fun x => f x - (qiKernel hr k).slicewise i f x) p (cubeVol d) ≤
        B * coordModulus r p i f (1 / 2 ^ k) := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨A, hA, hAb⟩ := exists_eLpNorm_sub_qi_le_of_taylor (p := p) hr hp
  have hJ : 1 + (r : ℝ≥0∞) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r))
      (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r)))⟩
  refine ⟨A * (2 * (1 + (r : ℝ≥0∞) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)))),
    ENNReal.mul_ne_top hA (ENNReal.mul_ne_top (by simp) hJ), fun {f} hf i {k} hk => ?_⟩
  have hL : (0 : ℝ) < 1 / 2 ^ k := by positivity
  have hwL : (3 / 4 : ℝ) + 1 / 2 ^ k ≤ 1 := by
    have : (1 : ℝ) / 2 ^ k ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  refine eLpNorm_sub_slicewise_le_of_smoothing (qiKernel hr k) hf hr hp1 hp i hL hwL
    (c := A) (M := ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r) (fun hu hG₁ hD₁ hG₂ hD₂ hTL hTR => ?_)
    fun ha hb => add_ofReal_div_pow_mul_le r k ha hb
  rw [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num, qiKernel_apply hr k hu.integrableOn_Icc]
  exact hAb hk hu.measurable (fun m _ => integrableOn_dyadicIco_of_continuous hu k m) hG₁ hD₁ hG₂
    hD₂ hTL hTR

/-- **Jackson's inequality for tensor splines on the cube**: for `1 ≤ p < ∞` and `r ≥ 1` there is
`C_J < ∞` with `E_{2^k}(f)_p ≤ C_J ω_r(f, 2^(-k))_p` for every `f ∈ L_p(Q)` and every `k ≥ 0`:
the tensor quasi-interpolant for `k ≥ r + 2`, Whitney's inequality for `k ≤ r + 1`. -/
theorem exists_approxError_cubeSplineScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ CJ : ℝ≥0∞, CJ ≠ ∞ ∧ ∀ (f : Lp ℂ p (cubeVol d)) (k : ℕ),
      (cubeSplineScheme p d r).approxError f (2 ^ k) ≤ CJ * lpCubeModulus p r f k := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨B, hB, hBb⟩ := exists_eLpNorm_sub_slicewise_qiKernel_le (d := d) (p := p) hr hp
  obtain ⟨Cq, hCq, hCqb⟩ := exists_eLpNorm_qiKernel_apply_le (p := p) hr hp
  obtain ⟨W, hW, hWb⟩ :=
    exists_approxError_cubePPScheme_one_le (d := d) (p := p) hr hp (m := r + 1) (by omega)
  have hF : (1 + Cq) ^ d * B ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hCq⟩)) hB
  refine ⟨W + (1 + Cq) ^ d * B, ENNReal.add_ne_top.2 ⟨hW, hF⟩, fun f k => ?_⟩
  rcases lt_or_ge k (r + 2) with hk | hk
  · -- the coarse levels: Whitney's inequality
    calc (cubeSplineScheme p d r).approxError f (2 ^ k)
        ≤ (cubeSplineScheme p d r).approxError f 1 :=
          ApproximationScheme.approxError_anti f Nat.one_le_two_pow
      _ ≤ (cubePPScheme p d r).approxError f 1 := approxError_cubeSplineScheme_one_le r f
      _ ≤ W * lpCubeModulus p r f (r + 1) := hWb f
      _ ≤ (W + (1 + Cq) ^ d * B) * lpCubeModulus p r f k :=
          mul_le_mul' le_self_add (lpCubeModulus_anti r f (by omega))
  · -- the fine levels: the tensor quasi-interpolant
    refine (approxError_le_of_continuous hp hF (fun g => ?_) f).trans
      (mul_le_mul' le_add_self le_rfl)
    have hgb : BddMeas (g : (Fin d → ℝ) → ℂ) :=
      ⟨g.continuous.measurable, ‖g‖, g.norm_coe_le_norm⟩
    have hS := isCubeSpline_cubeQI hr k hgb
    exact ⟨cubeQI hr k g, ⟨(hS.1.memLp p (cubeVol d)).toLp _,
      mem_cubeSplineScheme_two_pow.2 ⟨_, hS, MemLp.coeFn_toLp _⟩, MemLp.coeFn_toLp _⟩,
      (qiKernel hr k).eLpNorm_sub_foldSlicewise_le_of_coord hp1 hp (hCqb k) hgb
        fun i => hBb g.continuous i hk⟩

end Cube
