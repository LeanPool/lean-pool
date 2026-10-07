/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.Deriv.Add
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Finite-family Hilbert energy chain rule

The high-order Sobolev energy is a finite sum of squared `L²` norms.
Differentiating the Hilbert-space curves gives the time term in
`eq:lps-regularized-Hm-identity`.
-/

public section

open MeasureTheory
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The derivative of a finite sum of squared `L²` norms is twice
the sum of the corresponding inner products
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_finite_l2_energy_chain
    {ι : Type*} (s : Finset ι)
    (F : ι → ℝ → Lp ℝ 2 (volume : Measure Vec3))
    (G : ι → Lp ℝ 2 (volume : Measure Vec3))
    (t : ℝ)
    (hF : ∀ i ∈ s, HasDerivAt (F i) (G i) t) :
    HasDerivAt
      (fun τ => ∑ i ∈ s, ‖F i τ‖ ^ 2)
      (2 * ∑ i ∈ s, inner ℝ (F i t) (G i)) t := by
  have hsum := HasDerivAt.fun_sum (u := s)
    (fun i hi => (hF i hi).norm_sq)
  convert hsum using 1
  rw [Finset.mul_sum]

/-- The real `L²` inner product is the integral of the scalar product
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_scalar_l2_inner_integral
    (F G : Lp ℝ 2 (volume : Measure Vec3)) :
    inner ℝ F G = ∫ x : Vec3, F x * G x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [mul_comm]

/-- The squared real `L²` norm is the scalar square integral
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_scalar_l2_norm_sq_integral
    (F : Lp ℝ 2 (volume : Measure Vec3)) :
    ‖F‖ ^ 2 = ∫ x : Vec3, (F x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq F, L2.inner_def]
  simp [Real.norm_eq_abs]

/-- A square-integrable representative has the expected real `L²`
norm formula (`eq:lps-regularized-Hm-identity`). -/
theorem lps_scalar_l2_toLp_norm_sq_integral
    {f : Vec3 → ℝ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ x : Vec3, f x ^ 2 := by
  rw [lps_scalar_l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf] with x hx
  rw [hx]

/-- Representatives of two square-integrable fields compute their
real `L²` inner product by integration
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_scalar_l2_toLp_inner_integral
    {f g : Vec3 → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    inner ℝ (hf.toLp f) (hg.toLp g) =
      ∫ x : Vec3, f x * g x := by
  rw [lps_scalar_l2_inner_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x hfx hgx
  rw [hfx, hgx]

end ESS
