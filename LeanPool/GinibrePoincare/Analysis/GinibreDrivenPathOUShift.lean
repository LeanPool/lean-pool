/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathOUShift.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathOUUniqueness

/-! # Exact time-shift decomposition of the actual OU convolution -/

@[expose] public section
open MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem drivenOUPath_shift (κ : ℝ) (x : E) (N : ℝ → E) (hN : Continuous N)
    (s t : ℝ) :
    drivenOUPath κ x N (s + t) =
      drivenOUPath κ (drivenOUPath κ x N s) (fun u => N (s + u) - N s) t := by
  let X := drivenOUPath κ x N
  have hX : Continuous X := drivenOUPath_continuous κ x N hN
  have hshiftN : Continuous (fun u => N (s + u) - N s) :=
    (hN.comp (continuous_const.add continuous_id)).sub continuous_const
  have hshiftX : Continuous (fun u => X (s + u)) :=
    hX.comp (continuous_const.add continuous_id)
  have heq (u : ℝ) : X (s + u) = X s + (N (s + u) - N s) +
      ∫ r in (0 : ℝ)..u, -κ • X (s + r) := by
    have hsu := drivenOUPath_integral_equation κ x N hN (s + u)
    have hs := drivenOUPath_integral_equation κ x N hN s
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (f := fun r => -κ • X r) (μ := volume)
      ((hX.const_smul (-κ)).intervalIntegrable 0 s)
      ((hX.const_smul (-κ)).intervalIntegrable s (s + u))
    have htranslate : (∫ r in (0 : ℝ)..u, -κ • X (s + r)) =
        ∫ r in s..(s + u), -κ • X r := by
      simpa only [add_zero] using intervalIntegral.integral_comp_add_left
        (f := fun r => -κ • X r) (a := (0 : ℝ)) (b := u) s
    rw [htranslate]
    change X (s + u) = x + N (s + u) + ∫ r in (0 : ℝ)..(s + u), -κ • X r at hsu
    change X s = x + N s + ∫ r in (0 : ℝ)..s, -κ • X r at hs
    rw [← hi] at hsu
    rw [hsu, hs]
    abel
  exact congrFun (drivenOUPath_unique κ (X s) (fun u => N (s + u) - N s)
    (fun u => X (s + u)) hshiftN hshiftX heq) t

omit [CompleteSpace E] in
theorem drivenOUPath_initial_split (κ : ℝ) (x : E) (N : ℝ → E) (t : ℝ) :
    drivenOUPath κ x N t = Real.exp (-κ * t) • x + drivenOUPath κ 0 N t := by
  simp only [drivenOUPath, drivenOUCorrection, smul_sub, zero_sub, smul_neg]
  abel

omit [CompleteSpace E] in
/-- At nonnegative time only noise values in the actual elapsed time interval
enter the explicit solution. -/
theorem drivenOUPath_congr_nonneg (κ : ℝ) (x : E) (N M : ℝ → E) (t : ℝ) (ht : 0 ≤ t)
    (heq : ∀ s ∈ Set.Icc 0 t, N s = M s) :
    drivenOUPath κ x N t = drivenOUPath κ x M t := by
  have hI : (∫ s in (0 : ℝ)..t, Real.exp (κ * s) • N s) =
      ∫ s in (0 : ℝ)..t, Real.exp (κ * s) • M s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    change Real.exp (κ * s) • N s = Real.exp (κ * s) • M s
    rw [heq s hs]
  simp only [drivenOUPath, drivenOUCorrection, heq t ⟨ht, le_rfl⟩, hI]

end
end GinibrePoincare
