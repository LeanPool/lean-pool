/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# The two exceptional cubic graphs

The rational graphs are defined everywhere, but all calculus statements carry
an explicit nonzero trace hypothesis. Their tangent maps are given in fixed
Euclidean coordinates.
-/

@[expose] public section

namespace PlanarMidpoint

noncomputable section

/-- The squared Euclidean length of the trace vector. -/
def radiusSq (τ : E) : ℝ := τ 0 ^ 2 + τ 1 ^ 2

/-- The pure-cube exceptional graph, extended by zero at zero trace. -/
def Q (τ : E) : Coeff :=
  ![τ 0 ^ 3 / radiusSq τ, τ 0 ^ 2 * τ 1 / radiusSq τ,
    τ 0 * τ 1 ^ 2 / radiusSq τ, τ 1 ^ 3 / radiusSq τ]

/-- The second exceptional cubic graph, extended by zero at zero trace. -/
def R (τ : E) : Coeff :=
  ![3 * τ 0 - 3 * Q τ 0, τ 1 - 3 * Q τ 1,
    τ 0 - 3 * Q τ 2, 3 * τ 1 - 3 * Q τ 3]

theorem radiusSq_pos {τ : E} (hτ : τ ≠ 0) : 0 < radiusSq τ := by
  have hn : τ 0 ≠ 0 ∨ τ 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hτ (vec_ext h.1 h.2)
  rcases hn with h | h <;> unfold radiusSq <;> positivity

theorem radiusSq_ne_zero {τ : E} (hτ : τ ≠ 0) : radiusSq τ ≠ 0 :=
  ne_of_gt (radiusSq_pos hτ)

theorem trace_Q {τ : E} (hτ : τ ≠ 0) : trace (Q τ) = τ := by
  have hρ := radiusSq_ne_zero hτ
  apply vec_ext
  · change τ 0 ^ 3 / radiusSq τ + τ 0 * τ 1 ^ 2 / radiusSq τ = τ 0
    field_simp
    simp [radiusSq]
  · change τ 0 ^ 2 * τ 1 / radiusSq τ + τ 1 ^ 3 / radiusSq τ = τ 1
    field_simp
    simp [radiusSq]

theorem trace_R {τ : E} (hτ : τ ≠ 0) : trace (R τ) = τ := by
  have hρ := radiusSq_ne_zero hτ
  apply vec_ext <;> simp [trace, R, Q] <;> field_simp <;> simp [radiusSq]

theorem cubic_Q_trace {τ : E} (hτ : τ ≠ 0) :
    cubic (Q τ) τ τ τ = radiusSq τ ^ 2 := by
  have hρ := radiusSq_ne_zero hτ
  simp [cubic, Q]
  field_simp
  simp [radiusSq]
  ring

theorem cubic_R_trace {τ : E} (hτ : τ ≠ 0) :
    cubic (R τ) τ τ τ = 0 := by
  have hρ := radiusSq_ne_zero hτ
  simp [cubic, R, Q]
  field_simp
  simp [radiusSq]
  ring

theorem Q_ne_R {τ : E} (hτ : τ ≠ 0) : Q τ ≠ R τ := by
  intro he
  have h := congrArg (fun c => cubic c τ τ τ) he
  rw [cubic_Q_trace hτ, cubic_R_trace hτ] at h
  exact (pow_ne_zero 2 (radiusSq_ne_zero hτ)) h

/-- Continuous linear evaluation of a standard Euclidean coordinate. -/
def pr (i : Fin 2) : E →L[ℝ] ℝ := EuclideanSpace.proj i

/-- Numerators of the four rows of the derivative of `Q`. -/
def QNum (τ : E) : Fin 4 → Fin 2 → ℝ :=
  ![![τ 0 ^ 2 * (τ 0 ^ 2 + 3 * τ 1 ^ 2), -2 * τ 0 ^ 3 * τ 1],
    ![2 * τ 0 * τ 1 ^ 3, τ 0 ^ 2 * (τ 0 ^ 2 - τ 1 ^ 2)],
    ![τ 1 ^ 2 * (τ 1 ^ 2 - τ 0 ^ 2), 2 * τ 0 ^ 3 * τ 1],
    ![-2 * τ 0 * τ 1 ^ 3, τ 1 ^ 2 * (3 * τ 0 ^ 2 + τ 1 ^ 2)]]

/-- The derivative of the pure-cube graph away from zero trace. -/
def QDeriv (τ : E) : E →L[ℝ] Coeff :=
  ContinuousLinearMap.pi fun i =>
    ((radiusSq τ ^ 2)⁻¹ * QNum τ i 0) • pr 0 + ((radiusSq τ ^ 2)⁻¹ * QNum τ i 1) • pr 1

theorem QDeriv_apply (τ v : E) (i : Fin 4) :
    QDeriv τ v i = (QNum τ i 0 * v 0 + QNum τ i 1 * v 1) / radiusSq τ ^ 2 := by
  simp [QDeriv, pr, div_eq_mul_inv]
  ring

theorem hasFDerivAt_Q {τ : E} (hτ : τ ≠ 0) : HasFDerivAt Q (QDeriv τ) τ := by
  have hρ := radiusSq_ne_zero hτ
  have h0 : HasFDerivAt (fun x : E => x 0) (pr 0) τ := (pr 0).hasFDerivAt
  have h1 : HasFDerivAt (fun x : E => x 1) (pr 1) τ := (pr 1).hasFDerivAt
  have hr := (h0.pow 2).add (h1.pow 2)
  have hi := (hasDerivAt_inv hρ).comp_hasFDerivAt τ hr
  change HasFDerivAt (fun τ i => Q τ i) _ τ
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert (h0.pow 3).mul hi using 1
    · ext x; simp [Q, radiusSq, div_eq_mul_inv]
    · ext v; simp [QNum, pr]; field_simp [hρ]; simp [radiusSq]; ring_nf; simp
  · convert ((h0.pow 2).mul h1).mul hi using 1
    · ext x; simp [Q, radiusSq, div_eq_mul_inv]
    · ext v; simp [QNum, pr]; field_simp [hρ]; simp [radiusSq]; ring_nf; simp
  · convert (h0.mul (h1.pow 2)).mul hi using 1
    · ext x; simp [Q, radiusSq, div_eq_mul_inv]
    · ext v; simp [QNum, pr]; field_simp [hρ]; simp [radiusSq]; ring_nf; simp
  · convert (h1.pow 3).mul hi using 1
    · ext x; simp [Q, radiusSq, div_eq_mul_inv]
    · ext v; simp [QNum, pr]; field_simp [hρ]; simp [radiusSq]; ring_nf; simp

/-- The linear part of the second exceptional graph. -/
def linearR : E →L[ℝ] Coeff :=
  ContinuousLinearMap.pi ![3 • pr 0, pr 1, pr 0, 3 • pr 1]

/-- The derivative of the second exceptional graph away from zero trace. -/
def RDeriv (τ : E) : E →L[ℝ] Coeff := linearR - 3 • QDeriv τ

/-- Numerators of the tangent map to the second exceptional graph. -/
def RNum (τ : E) : Fin 4 → Fin 2 → ℝ :=
  ![![-3 * (τ 0) ^ 2 * (τ 1) ^ 2 + 3 * (τ 1) ^ 4, 6 * (τ 0) ^ 3 * (τ 1)],
    ![-6 * (τ 0) * (τ 1) ^ 3, -2 * (τ 0) ^ 4 + 5 * (τ 0) ^ 2 * (τ 1) ^ 2 + (τ 1) ^ 4],
    ![(τ 0) ^ 4 + 5 * (τ 0) ^ 2 * (τ 1) ^ 2 - 2 * (τ 1) ^ 4, -6 * (τ 0) ^ 3 * (τ 1)],
    ![6 * (τ 0) * (τ 1) ^ 3, 3 * (τ 0) ^ 4 - 3 * (τ 0) ^ 2 * (τ 1) ^ 2]]

theorem hasFDerivAt_R {τ : E} (hτ : τ ≠ 0) : HasFDerivAt R (RDeriv τ) τ := by
  convert linearR.hasFDerivAt.sub ((hasFDerivAt_Q hτ).const_smul 3) using 1
  · ext x i
    fin_cases i <;> simp [linearR, R, pr]
  · rfl

theorem RDeriv_apply {τ : E} (hτ : τ ≠ 0) (v : E) (i : Fin 4) :
    RDeriv τ v i = (RNum τ i 0 * v 0 + RNum τ i 1 * v 1) / radiusSq τ ^ 2 := by
  have hρ := radiusSq_ne_zero hτ
  fin_cases i <;> simp [RDeriv, linearR, QDeriv, QNum, RNum, pr] <;>
    field_simp [hρ] <;> simp [radiusSq] <;> ring_nf

/-- The trace map is a fixed continuous linear map. -/
def traceCLM : Coeff →L[ℝ] E :=
  ((ContinuousLinearMap.proj 0 : Coeff →L[ℝ] ℝ) + ContinuousLinearMap.proj 2).smulRight (vec 1 0)
      + ((ContinuousLinearMap.proj 1 : Coeff →L[ℝ] ℝ) + ContinuousLinearMap.proj 3).smulRight (vec
      0 1)

@[simp] theorem traceCLM_apply (c : Coeff) : traceCLM c = trace c := by
  apply vec_ext <;> simp [traceCLM, trace, vec]

theorem continuous_trace : Continuous trace := by
  convert traceCLM.continuous using 1
  funext c
  exact (traceCLM_apply c).symm

theorem differentiableAt_Q {τ : E} (hτ : τ ≠ 0) : DifferentiableAt ℝ Q τ :=
  (hasFDerivAt_Q hτ).differentiableAt

theorem differentiableAt_R {τ : E} (hτ : τ ≠ 0) : DifferentiableAt ℝ R τ :=
  (hasFDerivAt_R hτ).differentiableAt

theorem continuousAt_Q {τ : E} (hτ : τ ≠ 0) : ContinuousAt Q τ :=
  (differentiableAt_Q hτ).continuousAt

theorem continuousAt_R {τ : E} (hτ : τ ≠ 0) : ContinuousAt R τ :=
  (differentiableAt_R hτ).continuousAt

private theorem abs_sq_mul_div_le (s t u : ℝ) :
    |s ^ 2 * u / (s ^ 2 + t ^ 2)| ≤ |u| := by
  have hρ : 0 ≤ s ^ 2 + t ^ 2 := by positivity
  by_cases hz : s ^ 2 + t ^ 2 = 0
  · simp [hz]
  have hp : 0 < s ^ 2 + t ^ 2 := lt_of_le_of_ne hρ (Ne.symm hz)
  rw [abs_div, abs_mul, abs_sq, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  nlinarith [mul_nonneg (sq_nonneg t) (abs_nonneg u)]

theorem norm_Q_le (τ : E) : ‖Q τ‖ ≤ ‖τ‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg τ)).mpr
  intro i
  have h0 : |τ 0| ≤ ‖τ‖ := by simpa using PiLp.norm_apply_le τ 0
  have h1 : |τ 1| ≤ ‖τ‖ := by simpa using PiLp.norm_apply_le τ 1
  fin_cases i
  · change |τ 0 ^ 3 / radiusSq τ| ≤ ‖τ‖
    simpa only [radiusSq, pow_succ] using
      (abs_sq_mul_div_le (τ 0) (τ 1) (τ 0)).trans h0
  · change |τ 0 ^ 2 * τ 1 / radiusSq τ| ≤ ‖τ‖
    exact (abs_sq_mul_div_le (τ 0) (τ 1) (τ 1)).trans h1
  · change |τ 0 * τ 1 ^ 2 / radiusSq τ| ≤ ‖τ‖
    simpa only [radiusSq, mul_comm, add_comm] using
      (abs_sq_mul_div_le (τ 1) (τ 0) (τ 0)).trans h0
  · change |τ 1 ^ 3 / radiusSq τ| ≤ ‖τ‖
    simpa only [radiusSq, pow_succ, add_comm] using
      (abs_sq_mul_div_le (τ 1) (τ 0) (τ 1)).trans h1

@[simp] theorem Q_zero : Q 0 = 0 := by
  ext i
  fin_cases i <;> simp [Q, radiusSq]

@[simp] theorem R_zero : R 0 = 0 := by
  ext i
  fin_cases i <;> simp [R]

/-- The rational expression has a continuous extension through the zero trace. -/
theorem continuous_Q : Continuous Q := by
  apply continuous_iff_continuousAt.mpr
  intro τ
  by_cases hτ : τ = 0
  · subst τ
    change Filter.Tendsto Q (nhds 0) (nhds (Q 0))
    rw [Q_zero]
    exact squeeze_zero_norm norm_Q_le (by simpa only [norm_zero] using (continuous_norm.tendsto (0
        : E)))
  · exact continuousAt_Q hτ

theorem continuous_R : Continuous R := by
  have h := linearR.continuous.sub (continuous_Q.const_smul (3 : ℝ))
  convert h using 1
  ext x i
  fin_cases i <;> simp [linearR, R, pr]

end
end PlanarMidpoint
