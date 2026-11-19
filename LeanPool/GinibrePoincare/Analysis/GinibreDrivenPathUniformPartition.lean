/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathUniformPartition.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathRiemannConvergence

/-! # Uniform-partition convergence of actual weighted increments -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GinibrePoincare
noncomputable section

/-- Real sampling time on a uniform partition of `[0,t]`. -/
def ginibreUniformTime (t : ℝ) (n i : ℕ) : ℝ := t * (i : ℝ) / ((n : ℝ) + 1)

@[simp] theorem ginibreUniformTime_zero (t : ℝ) (n : ℕ) : ginibreUniformTime t n 0 = 0 := by
  simp [ginibreUniformTime]

@[simp] theorem ginibreUniformTime_end (t : ℝ) (n : ℕ) : ginibreUniformTime t n (n + 1) = t := by
  unfold ginibreUniformTime
  rw [Nat.cast_add, Nat.cast_one]
  exact mul_div_cancel_right₀ _ (by positivity)

theorem ginibreUniformTime_mono (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    Monotone (ginibreUniformTime t n) := by
  intro i j hij
  unfold ginibreUniformTime
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) ht)
    (by positivity)

theorem ginibreUniformTime_increment (t : ℝ) (n i : ℕ) :
    ginibreUniformTime t n (i + 1) - ginibreUniformTime t n i = t / ((n : ℝ) + 1) := by
  simp only [ginibreUniformTime, Nat.cast_add, Nat.cast_one]
  ring

theorem ginibreWeightedUniformIncrements_tendsto_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w w' : ℝ → ℝ) (N : ℝ → E) (hw : ∀ s, HasDerivAt w (w' s) s)
    (hw' : Continuous w') (hN : Continuous N) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), w (ginibreUniformTime t n i) •
      (N (ginibreUniformTime t n (i + 1)) - N (ginibreUniformTime t n i))) atTop
      (𝓝 (w t • N t - w 0 • N 0 - ∫ s in (0 : ℝ)..t, w' s • N s)) := by
  apply ginibreWeightedIncrements_tendsto_integral w w' N hw hw' hN 0 t ht
    (ginibreUniformTime t) (fun n => n + 1) (fun n => t / ((n : ℝ) + 1))
  · exact ginibreUniformTime_mono t ht
  · exact ginibreUniformTime_zero t
  · exact ginibreUniformTime_end t
  · intro n i _; exact (ginibreUniformTime_increment t n i).le
  · have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [mul_zero, mul_one_div] using h

/-- Genuine uniform scalar Riemann sums for a continuously differentiable
weight, obtained from the weighted-increment convergence theorem. -/
theorem ginibreUniformScalarRiemann_tendsto (w w' : ℝ → ℝ)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w')
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), w (ginibreUniformTime t n i) *
      (ginibreUniformTime t n (i + 1) - ginibreUniformTime t n i)) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, w s)) := by
  have hwc : Continuous w := continuous_iff_continuousAt.mpr fun s => (hw s).continuousAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (fun s _ => (hasDerivAt_id s).mul (hw s))
    (((continuous_const.mul hwc).add (continuous_id.mul hw')).intervalIntegrable 0 t)
  simp only [id_eq, one_mul] at hFTC
  rw [intervalIntegral.integral_add (f := w) (g := fun s => s * w' s)
    (a := (0 : ℝ)) (b := t) (μ := volume) (hwc.intervalIntegrable 0 t)
    ((continuous_id.mul hw').intervalIntegrable 0 t)] at hFTC
  simp only [Pi.mul_apply, id_eq] at hFTC
  have he : w t * t - w 0 * 0 - (∫ s in (0 : ℝ)..t, w' s * s) =
      (∫ s in (0 : ℝ)..t, w s) := by
    have hcomm : (fun s : ℝ => w' s * s) = (fun s : ℝ => s * w' s) := by
      funext s; ring
    rw [hcomm]
    simp only [zero_mul, mul_zero, sub_zero] at hFTC ⊢
    nlinarith [hFTC]
  have h := ginibreWeightedUniformIncrements_tendsto_integral w w' id hw hw'
    continuous_id t ht
  simpa only [id_eq, smul_eq_mul, he] using h

end
end GinibrePoincare
