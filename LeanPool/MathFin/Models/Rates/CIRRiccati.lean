/-
Copyright (c) 2026 Alfredo Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfredo Garcia
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The CIR loadings solve their term-structure equations

The Cox–Ingersoll–Ross bond price has the affine form `P(0, T) = exp(A(T) − B(T) · r₀)`, so the
`A` here is the logarithm of the multiplicative factor that `vasicekBondA` and Brigo–Mercurio call
`A`. With `γ = √(κ² + 2σ²)` and `D(T) = (γ + κ)(e^{γT} − 1) + 2γ`, the closed form
`B(T) = 2(e^{γT} − 1) / D(T)` solves `B' = 1 − κB − ½σ²B²` with `B(0) = 0`.

After differentiating the quotient, the equation is the identity
`D² − 2κ(e^{γT} − 1) D − 2σ²(e^{γT} − 1)² = 4γ² e^{γT}`, which holds because
`γ² = κ² + 2σ²`. The hypothesis `κ² + 2σ² > 0` is the weakest that keeps `γ > 0`; at
`κ = σ = 0` the denominator is identically zero. Since `|κ| ≤ γ`, `D(T) > 0` for every
real `T`, so no `T ≥ 0` hypothesis is needed.

The level loading `A(T) = (2κθ/σ²) · log(2γ e^{(κ+γ)T/2} / D(T))` solves `A' = −κθB` with
`A(0) = 0`, for `σ ≠ 0`. Its equation reduces to
`(κ + γ) D / 2 − (γ + κ) γ e^{γT} = −σ² (e^{γT} − 1)`, again because `γ² = κ² + 2σ²`.

Only these equations are proved. The bond price `𝔼[exp(−∫₀ᵀ r_s ds)]` needs the affine
(Feynman–Kac) framework, which is not formalized.

## Main definitions

* `cirGamma`: `γ = √(κ² + 2σ²)`.
* `cirDenom`: `D(T) = (γ + κ)(e^{γT} − 1) + 2γ`.
* `cirBondB`: the CIR rate loading `B(T) = 2(e^{γT} − 1) / D(T)`.
* `cirBondA`: the CIR level loading in log form,
  `A(T) = (2κθ/σ²) · log(2γ e^{(κ+γ)T/2} / D(T))`.

## Main results

* `cirBondB_zero`: `B(0) = 0`.
* `hasDerivAt_cirBondB`: `B' = 1 − κB − ½σ²B²` at every `T`, for `κ² + 2σ² > 0`.
* `cirBondA_zero`: `A(0) = 0`.
* `hasDerivAt_cirBondA`: `A' = −κθB` at every `T`, for `σ ≠ 0`.

## References

* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  §3.2.3
* [J. C. Cox, J. E. Ingersoll and S. A. Ross, *A theory of the term structure of interest
  rates*][CoxIngersollRoss1985]

## Tags

Cox–Ingersoll–Ross, CIR model, Riccati equation, affine bond price, square-root diffusion,
short rate, MSC 91G30, MSC 60J60, JEL E43
-/

@[expose] public section

namespace MathFin

/-- `γ = √(κ² + 2σ²)`. -/
noncomputable def cirGamma (κ σ : ℝ) : ℝ := Real.sqrt (κ ^ 2 + 2 * σ ^ 2)

lemma cirGamma_sq (κ σ : ℝ) : cirGamma κ σ ^ 2 = κ ^ 2 + 2 * σ ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma cirGamma_pos {κ σ : ℝ} (h : 0 < κ ^ 2 + 2 * σ ^ 2) : 0 < cirGamma κ σ :=
  Real.sqrt_pos.mpr h

/-- `D(T) = (γ + κ)(e^{γT} − 1) + 2γ`. -/
noncomputable def cirDenom (κ σ T : ℝ) : ℝ :=
  (cirGamma κ σ + κ) * (Real.exp (cirGamma κ σ * T) - 1) + 2 * cirGamma κ σ

/-- The CIR rate loading `B(T) = 2(e^{γT} − 1) / D(T)`. -/
noncomputable def cirBondB (κ σ T : ℝ) : ℝ :=
  2 * (Real.exp (cirGamma κ σ * T) - 1) / cirDenom κ σ T

/-- `D(T) > 0` at every `T`, since `|κ| ≤ γ`. -/
lemma cirDenom_pos {κ σ : ℝ} (h : 0 < κ ^ 2 + 2 * σ ^ 2) (T : ℝ) : 0 < cirDenom κ σ T := by
  have hγ := cirGamma_pos h
  have hκ : |κ| ≤ cirGamma κ σ := Real.abs_le_sqrt (by nlinarith [sq_nonneg σ])
  have hE := Real.exp_pos (cirGamma κ σ * T)
  unfold cirDenom
  nlinarith [le_abs_self κ, neg_abs_le κ,
    mul_nonneg (by linarith [neg_abs_le κ] : 0 ≤ cirGamma κ σ + κ) hE.le]

private lemma hasDerivAt_exp_cirGamma (κ σ T : ℝ) :
    HasDerivAt (fun t ↦ Real.exp (cirGamma κ σ * t))
      (Real.exp (cirGamma κ σ * T) * cirGamma κ σ) T := by
  simpa using ((hasDerivAt_id T).const_mul (cirGamma κ σ)).exp

/-- `D'(T) = (γ + κ) γ e^{γT}`. -/
lemma hasDerivAt_cirDenom (κ σ T : ℝ) :
    HasDerivAt (cirDenom κ σ)
      ((cirGamma κ σ + κ) * (Real.exp (cirGamma κ σ * T) * cirGamma κ σ)) T :=
  (((hasDerivAt_exp_cirGamma κ σ T).sub_const 1).const_mul (cirGamma κ σ + κ)).add_const
    (2 * cirGamma κ σ)

lemma cirBondB_zero (κ σ : ℝ) : cirBondB κ σ 0 = 0 := by
  simp [cirBondB]

/-- **The CIR rate loading solves the Riccati equation** `B' = 1 − κB − ½σ²B²`. The proof
reduces it to `D² − 2κ(e^{γT} − 1) D − 2σ²(e^{γT} − 1)² = 4γ² e^{γT}`, using `γ² = κ² + 2σ²`. -/
theorem hasDerivAt_cirBondB {κ σ : ℝ} (h : 0 < κ ^ 2 + 2 * σ ^ 2) (T : ℝ) :
    HasDerivAt (cirBondB κ σ)
      (1 - κ * cirBondB κ σ T - σ ^ 2 / 2 * cirBondB κ σ T ^ 2) T := by
  have hγ := cirGamma_sq κ σ
  have hD := (cirDenom_pos h T).ne'
  have hB := (((hasDerivAt_exp_cirGamma κ σ T).sub_const 1).const_mul 2).div
    (hasDerivAt_cirDenom κ σ T) hD
  have hfun : cirBondB κ σ =
      (fun t ↦ 2 * (Real.exp (cirGamma κ σ * t) - 1)) / fun t ↦ cirDenom κ σ t := rfl
  rw [hfun]
  refine hB.congr_deriv ?_
  simp only [Pi.div_apply]
  unfold cirDenom at *
  field_simp
  linear_combination -(Real.exp (cirGamma κ σ * T) - 1) ^ 2 * hγ

/-- The CIR level loading in log form, `A(T) = (2κθ/σ²) · log(2γ e^{(κ+γ)T/2} / D(T))`: the
constant term of the exponent in `P = exp(A − B · r₀)`, so `A(0) = 0`. -/
noncomputable def cirBondA (κ θ σ T : ℝ) : ℝ :=
  2 * κ * θ / σ ^ 2 *
    Real.log (2 * cirGamma κ σ * Real.exp ((κ + cirGamma κ σ) * T / 2) / cirDenom κ σ T)

lemma cirBondA_zero (κ θ σ : ℝ) : cirBondA κ θ σ 0 = 0 := by
  by_cases hγ : cirGamma κ σ = 0 <;> simp [cirBondA, cirDenom, hγ]

/-- **The CIR level loading solves `A' = −κθB`.** The proof reduces it to
`(κ + γ) D / 2 − (γ + κ) γ e^{γT} = −σ² (e^{γT} − 1)`, using `γ² = κ² + 2σ²`. -/
theorem hasDerivAt_cirBondA (κ θ : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (T : ℝ) :
    HasDerivAt (cirBondA κ θ σ) (-(κ * θ) * cirBondB κ σ T) T := by
  have h : 0 < κ ^ 2 + 2 * σ ^ 2 := by positivity
  have hγ := cirGamma_sq κ σ
  have hγpos := cirGamma_pos h
  have hD := cirDenom_pos h T
  have hF : HasDerivAt (fun t ↦ 2 * cirGamma κ σ * Real.exp ((κ + cirGamma κ σ) * t / 2))
      (2 * cirGamma κ σ *
          (Real.exp ((κ + cirGamma κ σ) * T / 2) * ((κ + cirGamma κ σ) / 2))) T := by
    simpa using (((hasDerivAt_id T).const_mul (κ + cirGamma κ σ)).div_const 2).exp.const_mul
      (2 * cirGamma κ σ)
  have hg := hF.div (hasDerivAt_cirDenom κ σ T) hD.ne'
  have hA := (hg.log (div_pos (by positivity) hD).ne').const_mul (2 * κ * θ / σ ^ 2)
  have hfun : cirBondA κ θ σ = fun t ↦ 2 * κ * θ / σ ^ 2 *
      Real.log (((fun t ↦ 2 * cirGamma κ σ * Real.exp ((κ + cirGamma κ σ) * t / 2)) /
        fun t ↦ cirDenom κ σ t) t) := rfl
  rw [hfun]
  refine hA.congr_deriv ?_
  have hF0 := (Real.exp_pos ((κ + cirGamma κ σ) * T / 2)).ne'
  simp only [Pi.div_apply, cirBondB]
  unfold cirDenom at *
  field_simp
  linear_combination κ * θ * (1 - Real.exp (cirGamma κ σ * T)) * hγ

end MathFin
