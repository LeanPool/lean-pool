/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.IdealWeakForm

/-!
# The weak form of the ideal induction equation under time rescaling

For a real factor `c`, replacing the velocity `v` by `c v` and running time at speed `c`
preserves the weak form of the ideal induction equation of `FastDynamo/Dynamics/IdealWeakForm.lean`:
if `W` solves the equation of `v` on `[−|c| T, |c| T]`, then `t ↦ W (c t)` solves the equation of
`c v` on `[−T, T]`.  Both sides of the weak identity scale by `c`: the stretching
`(W·∇)(c v) = c (W·∇)v` and the advection `(c v·∇)φ = c (v·∇)φ` are pointwise, and the change of
variables `τ ↦ c τ` in the time integral produces the same factor.  Consequently
`t ↦ G (c t)` is a solution group for `c v` whenever `G` is one for `v`.  This is the form of
Remark 1.6 of the paper ("the particle flow and ideal induction group for `uNorm` are the
corresponding objects for `u` evaluated at time `t / M`") for the weak formulation.

## Contents

* `r3Complexify_smul`, `literalFDeriv_smul`, `literalStretch_smul`, `literalAdvection_smul`:
  the pointwise scaling of the coefficients;
* `IsIdealWeakSolution.timeRescale`, `IsIdealSolutionGroup.timeRescale`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-- The complexification of `c M` is `c` times the complexification of `M`. -/
theorem r3Complexify_smul (c : ℝ) (M : R3 →L[ℝ] R3) :
    r3Complexify (c • M) = (c : ℂ) • r3Complexify M := by
  refine ContinuousLinearMap.ext fun w ↦ PiLp.ext fun i ↦ ?_
  rw [smul_apply, PiLp.smul_apply, r3Complexify_apply, r3Complexify_apply,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [smul_apply, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- The derivative of `c v` is `c` times the derivative of `v`. -/
theorem literalFDeriv_smul (c : ℝ) (v : Torus 3 → R3) (x : Torus 3) :
    literalFDeriv (c • v) x = c • literalFDeriv v x := by
  have hfun : (fun a : R3 ↦ (c • v) (literalTorusPoint a)) =
      c • fun a : R3 ↦ v (literalTorusPoint a) := rfl
  rw [literalFDeriv, literalFDeriv, hfun, fderiv_const_smul_field]
  rfl

/-- The stretching by `c v` is `c` times the stretching by `v`. -/
theorem literalStretch_smul (c : ℝ) (v : Torus 3 → R3) (B : Torus 3 → C3) (x : Torus 3) :
    literalStretch (c • v) B x = (c : ℂ) • literalStretch v B x := by
  rw [literalStretch, literalStretch, literalFDeriv_smul, r3Complexify_smul]
  rfl

/-- The advection by `c v` is `c` times the advection by `v`. -/
theorem literalAdvection_smul (c : ℝ) (v : Torus 3 → R3) (φ : Torus 3 → C3) (x : Torus 3) :
    literalAdvection (c • v) φ x = (c : ℂ) • literalAdvection v φ x := by
  rw [literalAdvection, literalAdvection, Pi.smul_apply, map_smul, Complex.coe_smul]

/-- **Time rescaling of weak solutions**: if `W` is a weak solution of the ideal induction
equation of `v` on `[−|c| T, |c| T]`, then `t ↦ W (c t)` is a weak solution of the equation
of `c v` on `[−T, T]`. -/
theorem IsIdealWeakSolution.timeRescale {v : Torus 3 → R3} {T : ℝ} {W : ℝ → LiteralC3L2}
    (c : ℝ) (h : IsIdealWeakSolution v (|c| * T) W) :
    IsIdealWeakSolution (c • v) T fun t ↦ W (c * t) := by
  have hmaps : Set.MapsTo (fun t : ℝ ↦ c * t) (Set.Icc (-T) T) (Set.Icc (-(|c| * T)) (|c| * T)) :=
    fun t ht ↦ by
      have habs : |c * t| ≤ |c| * T := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) (abs_nonneg c)
      exact abs_le.1 habs
  refine ⟨h.continuousOn.comp (continuous_const.mul continuous_id).continuousOn hmaps, ?_⟩
  intro φ hφ s hs t ht
  rw [h.weak φ hφ (c * s) (hmaps hs) (c * t) (hmaps ht)]
  simp_rw [literalStretch_smul, literalAdvection_smul, inner_smul_right, inner_smul_left,
    Complex.conj_ofReal, ← mul_add, integral_const_mul, intervalIntegral.integral_const_mul,
    ← intervalIntegral.smul_integral_comp_mul_left (c := c), Complex.real_smul]

/-- **Time rescaling of solution groups**: if `G` is a solution group of the ideal induction
equation of `v`, then `t ↦ G (c t)` is a solution group of the equation of `c v`. -/
theorem IsIdealSolutionGroup.timeRescale {v : Torus 3 → R3}
    {G : ℝ → literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace}
    (h : IsIdealSolutionGroup v G) (c : ℝ) :
    IsIdealSolutionGroup (c • v) fun t ↦ G (c * t) where
  group_zero := by
    show G (c * 0) = _
    rw [mul_zero]
    exact h.group_zero
  group_add s t := by
    show G (c * (s + t)) = (G (c * s)).comp (G (c * t))
    rw [mul_add]
    exact h.group_add _ _
  weakSolution B T := (h.weakSolution B (|c| * T)).timeRescale c

end

end FastDynamo
