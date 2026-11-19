/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralVanishingAmplitude.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedContinuous

/-! A continuous amplitude vanishing initially removes an integrand's
possible discontinuity at the initial time. -/

@[expose] public section
open Set Filter
open scoped Topology NNReal
namespace GinibrePoincare

theorem continuous_mul_punctured_of_initial_zero (a f : ℝ≥0 → ℝ)
    (ha : Continuous a) (hf : ContinuousOn f (Ioi 0))
    (C : ℝ) (_ : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C) (hz : a 0 = 0) :
    Continuous (fun t => a t*f t) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t=0
  · subst t
    have hlim : Tendsto (fun t : ℝ≥0 => ‖a t‖*C) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, hz, norm_zero, zero_mul] using (ha.norm.continuousAt (x :=
          0)).mul_const C
    have hnorm : Tendsto (fun t : ℝ≥0 => ‖a t*f t‖) (𝓝 0) (𝓝 0) :=
      squeeze_zero (fun t => norm_nonneg _) (fun t => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)) hlim
    simpa only [ContinuousAt, hz, zero_mul] using tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  · have hpos : 0 < t := lt_of_le_of_ne bot_le (Ne.symm ht)
    exact ha.continuousAt.mul (hf.continuousAt (isOpen_Ioi.mem_nhds hpos))

end GinibrePoincare
