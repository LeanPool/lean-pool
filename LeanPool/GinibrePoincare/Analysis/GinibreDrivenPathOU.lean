/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathOU.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathFactorization
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Explicit additive-noise Ornstein--Uhlenbeck paths

The convolution is defined using an ordinary Bochner integral, so continuous
noise suffices. Its differentiable correction solves the actual drift equation.
-/

@[expose] public section

open MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The differentiable correction to the cumulative continuous driving noise. -/
def drivenOUCorrection (κ : ℝ) (x : E) (N : ℝ → E) (t : ℝ) : E :=
  Real.exp (-κ * t) • (x - κ • ∫ s in (0 : ℝ)..t, Real.exp (κ * s) • N s)

/-- The OU path, expressed without a stochastic-integral certificate. -/
def drivenOUPath (κ : ℝ) (x : E) (N : ℝ → E) (t : ℝ) : E :=
  N t + drivenOUCorrection κ x N t

omit [CompleteSpace E] in
@[simp] theorem drivenOUCorrection_zero (κ : ℝ) (x : E) (N : ℝ → E) :
    drivenOUCorrection κ x N 0 = x := by simp [drivenOUCorrection]

theorem drivenOUCorrection_hasDerivAt (κ : ℝ) (x : E) (N : ℝ → E)
    (hN : Continuous N) (t : ℝ) :
    HasDerivAt (drivenOUCorrection κ x N) (-κ • drivenOUPath κ x N t) t := by
  have hc : Continuous (fun s : ℝ => Real.exp (κ * s) • N s) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul hN
  have hA := (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have he : HasDerivAt (fun s : ℝ => Real.exp (-κ * s))
      (Real.exp (-κ * t) * (-κ)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-κ)).exp
  have h := he.smul ((hasDerivAt_const t x).sub (hA.const_smul κ))
  have hexp : Real.exp (-κ * t) * Real.exp (κ * t) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  convert h using 1
  · rfl
  · simp only [drivenOUPath, drivenOUCorrection, zero_sub, smul_neg, smul_smul,
      smul_add, smul_sub, neg_smul, Pi.sub_apply, Pi.smul_apply]
    rw [show Real.exp (-κ * t) * (κ * Real.exp (κ * t)) = κ by
      calc
        _ = κ * (Real.exp (-κ * t) * Real.exp (κ * t)) := by ring
        _ = κ := by rw [hexp]; ring]
    module

theorem drivenOUPath_continuous (κ : ℝ) (x : E) (N : ℝ → E)
    (hN : Continuous N) : Continuous (drivenOUPath κ x N) := by
  exact hN.add (continuous_iff_continuousAt.mpr fun t =>
    (drivenOUCorrection_hasDerivAt κ x N hN t).continuousAt)

/-- The explicit path satisfies the additive-noise integral equation for every
real time; no differentiability of the driving noise is required. -/
theorem drivenOUPath_integral_equation (κ : ℝ) (x : E) (N : ℝ → E)
    (hN : Continuous N) (t : ℝ) :
    drivenOUPath κ x N t = x + N t +
      ∫ s in (0 : ℝ)..t, -κ • drivenOUPath κ x N s := by
  have hi : IntervalIntegrable (fun s => -κ • drivenOUPath κ x N s) volume 0 t :=
    ((drivenOUPath_continuous κ x N hN).const_smul (-κ)).intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => drivenOUCorrection_hasDerivAt κ x N hN s) hi
  rw [hFTC, drivenOUCorrection_zero]
  simp only [drivenOUPath]
  abel

/-- Uniqueness of the continuous path satisfying the actual OU Volterra equation. -/
theorem drivenOUPath_unique (κ : ℝ) (x : E) (N X : ℝ → E)
    (hN : Continuous N) (hX : Continuous X)
    (hEq : ∀ t : ℝ, X t = x + N t + ∫ s in (0 : ℝ)..t, -κ • X s) :
    X = drivenOUPath κ x N := by
  let Y := drivenOUPath κ x N
  have hY : Continuous Y := drivenOUPath_continuous κ x N hN
  have hD : ∀ t : ℝ, HasDerivAt (fun s => X s - Y s) (-κ • (X t - Y t)) t := by
    intro t
    have hXI := (((hX.const_smul (-κ)).integral_hasStrictDerivAt 0 t).hasDerivAt)
    have hYI := (((hY.const_smul (-κ)).integral_hasStrictDerivAt 0 t).hasDerivAt)
    have he : (fun s => X s - Y s) =
        (fun s => (∫ r in (0 : ℝ)..s, -κ • X r) -
          (∫ r in (0 : ℝ)..s, -κ • Y r)) := by
      funext s
      rw [hEq s]
      have hYs : Y s = x + N s + ∫ r in (0 : ℝ)..s, -κ • Y r :=
        drivenOUPath_integral_equation κ x N hN s
      rw [hYs]
      abel
    rw [he]
    have hh := hXI.sub hYI
    change HasDerivAt (fun s => (∫ r in (0 : ℝ)..s, -κ • X r) -
      (∫ r in (0 : ℝ)..s, -κ • Y r)) (-κ • X t - -κ • Y t) t at hh
    simpa only [smul_sub] using hh
  have hZ : ∀ t : ℝ, HasDerivAt (fun s => Real.exp (κ * s) • (X s - Y s)) 0 t := by
    intro t
    have he := ((hasDerivAt_id t).const_mul κ).exp
    have hh := he.smul (hD t)
    simp only [id_eq, mul_one] at hh
    change HasDerivAt (fun s => Real.exp (κ * s) • (X s - Y s))
      (Real.exp (κ * t) • (-κ • (X t - Y t)) +
        (Real.exp (κ * t) * κ) • (X t - Y t)) t at hh
    convert hh using 1
    rw [smul_smul]
    simp only [mul_neg, neg_smul, neg_add_cancel]
  funext t
  have hz := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (fun s _ => hZ s) (continuous_const.intervalIntegrable 0 t)
  have h0 : X 0 = Y 0 := by
    rw [hEq 0]; simp [Y, drivenOUPath, add_comm]
  have hzt : Real.exp (κ * t) • (X t - Y t) = 0 := by
    simpa [h0] using hz.symm
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzt).resolve_left (Real.exp_ne_zero _))

end
end GinibrePoincare
