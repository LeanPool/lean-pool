/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathOUUniqueness.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathOU

/-! # Uniqueness on the actual nonnegative-time driven domain -/

@[expose] public section
open MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem drivenOUPath_unique_nonneg (κ : ℝ) (x : E) (N X : ℝ → E)
    (hN : Continuous N) (hX : Continuous X)
    (hEq : ∀ t : ℝ, 0 ≤ t → X t = x + N t + ∫ s in (0 : ℝ)..t, -κ • X s)
    (t : ℝ) (ht : 0 ≤ t) : X t = drivenOUPath κ x N t := by
  let Y := drivenOUPath κ x N
  have hY : Continuous Y := drivenOUPath_continuous κ x N hN
  have hD : ∀ s : ℝ, 0 < s → HasDerivAt (fun u => X u - Y u) (-κ • (X s - Y s)) s := by
    intro s hs
    have hXI := (((hX.const_smul (-κ)).integral_hasStrictDerivAt 0 s).hasDerivAt)
    have hYI := (((hY.const_smul (-κ)).integral_hasStrictDerivAt 0 s).hasDerivAt)
    have hh := hXI.sub hYI
    change HasDerivAt (fun u => (∫ r in (0 : ℝ)..u, -κ • X r) -
      (∫ r in (0 : ℝ)..u, -κ • Y r)) (-κ • X s - -κ • Y s) s at hh
    have he : (fun u => X u - Y u) =ᶠ[𝓝 s]
        (fun u => (∫ r in (0 : ℝ)..u, -κ • X r) -
          (∫ r in (0 : ℝ)..u, -κ • Y r)) := by
      filter_upwards [Ioi_mem_nhds hs] with u hu
      rw [hEq u hu.le]
      have hYu : Y u = x + N u + ∫ r in (0 : ℝ)..u, -κ • Y r :=
        drivenOUPath_integral_equation κ x N hN u
      rw [hYu]
      abel
    simpa only [smul_sub] using hh.congr_of_eventuallyEq he
  have hZ : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun u => Real.exp (κ * u) • (X u - Y u)) 0 s := by
    intro s hs
    have he := ((hasDerivAt_id s).const_mul κ).exp
    have hh := he.smul (hD s hs)
    simp only [id_eq, mul_one] at hh
    change HasDerivAt (fun u => Real.exp (κ * u) • (X u - Y u))
      (Real.exp (κ * s) • (-κ • (X s - Y s)) +
        (Real.exp (κ * s) * κ) • (X s - Y s)) s at hh
    convert hh using 1
    rw [smul_smul]
    simp only [mul_neg, neg_smul, neg_add_cancel]
  have hcont : Continuous (fun u => Real.exp (κ * u) • (X u - Y u)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul (hX.sub hY)
  have hz := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hcont.continuousOn
    (fun s hs => (hZ s hs.1).hasDerivWithinAt) (continuous_const.intervalIntegrable 0 t)
  have h0 : X 0 = Y 0 := by
    rw [hEq 0 le_rfl]; simp [Y, drivenOUPath, add_comm]
  have hzt : Real.exp (κ * t) • (X t - Y t) = 0 := by
    simpa [h0] using hz.symm
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzt).resolve_left (Real.exp_ne_zero _))

end
end GinibrePoincare
