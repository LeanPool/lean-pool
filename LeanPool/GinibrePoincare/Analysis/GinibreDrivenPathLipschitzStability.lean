/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathLipschitzStability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathContinuousNoisePicard
public import Mathlib.Analysis.ODE.Gronwall

/-! Continuous-noise dependence is derived from the actual Volterra equation. -/

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem drivenVolterra_lipschitz_stability (b : E → E) (L : ℝ≥0) (hb : LipschitzWith L b)
    (x : E) (N M X Y : ℝ → E) (hX : Continuous X) (hY : Continuous Y)
    (T δ : ℝ) (_ : 0 ≤ T) (_ : 0 ≤ δ)
    (hEqX : ∀ t ∈ Icc 0 T, X t = x + N t + ∫ s in (0 : ℝ)..t, b (X s))
    (hEqY : ∀ t ∈ Icc 0 T, Y t = x + M t + ∫ s in (0 : ℝ)..t, b (Y s))
    (hNoise : ∀ t ∈ Icc 0 T, ‖N t - M t‖ ≤ δ) :
    ∀ t ∈ Icc 0 T, ‖X t-Y t‖ ≤ δ+gronwallBound 0 L ((L : ℝ)*δ) t := by
  let W := fun t => (∫ s in (0 : ℝ)..t, b (X s))-(∫ s in (0 : ℝ)..t, b (Y s))
  have hbX : Continuous (fun s => b (X s)) := hb.continuous.comp hX
  have hbY : Continuous (fun s => b (Y s)) := hb.continuous.comp hY
  have hD (s : ℝ) : HasDerivAt W (b (X s)-b (Y s)) s :=
    ((hbX.integral_hasStrictDerivAt 0 s).hasDerivAt).sub ((hbY.integral_hasStrictDerivAt 0
        s).hasDerivAt)
  have hW : Continuous W := continuous_iff_continuousAt.mpr fun s => (hD s).continuousAt
  have hDiff (s : ℝ) (hs : s ∈ Icc 0 T) : X s-Y s = N s-M s+W s := by
    rw [hEqX s hs, hEqY s hs]
    dsimp [W]
    abel
  have hXY (s : ℝ) (hs : s ∈ Icc 0 T) : ‖X s-Y s‖ ≤ δ+‖W s‖ := by
    rw [hDiff s hs]
    have hh := norm_add_le (N s-M s) (W s)
    linarith [hNoise s hs]
  have hbound (s : ℝ) (hs : s ∈ Ico 0 T) :
      ‖b (X s)-b (Y s)‖ ≤ (L : ℝ)*‖W s‖+(L : ℝ)*δ := by
    have h := hb.norm_sub_le (X s) (Y s)
    have hxy := hXY s ⟨hs.1, hs.2.le⟩
    nlinarith [mul_le_mul_of_nonneg_left hxy L.coe_nonneg]
  have hGr := norm_le_gronwallBound_of_norm_deriv_right_le hW.continuousOn
    (fun s hs => (hD s).hasDerivWithinAt)
    (show ‖W 0‖ ≤ (0 : ℝ) by simp [W]) hbound
  intro t ht
  have hg : ‖W t‖ ≤ gronwallBound 0 L ((L : ℝ)*δ) t := by
    simpa only [sub_zero] using hGr t ht
  linarith [hXY t ht]

theorem drivenVolterra_noise_gronwall_identity (L : ℝ≥0) (δ t : ℝ) :
    δ+gronwallBound 0 L ((L : ℝ)*δ) t = δ*Real.exp ((L : ℝ)*t) := by
  by_cases hL : (L : ℝ) = 0
  · simp [gronwallBound, hL]
  · rw [gronwallBound_of_K_ne_0 hL]
    field_simp
    ring

theorem drivenVolterra_lipschitz_stability_exp (b : E → E) (L : ℝ≥0) (hb : LipschitzWith L b)
    (x : E) (N M X Y : ℝ → E) (hX : Continuous X) (hY : Continuous Y)
    (T δ : ℝ) (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (hEqX : ∀ t ∈ Icc 0 T, X t = x + N t + ∫ s in (0 : ℝ)..t, b (X s))
    (hEqY : ∀ t ∈ Icc 0 T, Y t = x + M t + ∫ s in (0 : ℝ)..t, b (Y s))
    (hNoise : ∀ t ∈ Icc 0 T, ‖N t - M t‖ ≤ δ) :
    ∀ t ∈ Icc 0 T, ‖X t-Y t‖ ≤ δ*Real.exp ((L : ℝ)*T) := by
  intro t ht
  have h := drivenVolterra_lipschitz_stability b L hb x N M X Y hX hY T δ hT hδ hEqX hEqY hNoise t
      ht
  rw [drivenVolterra_noise_gronwall_identity] at h
  apply h.trans
  gcongr
  exact ht.2

end
end GinibrePoincare
