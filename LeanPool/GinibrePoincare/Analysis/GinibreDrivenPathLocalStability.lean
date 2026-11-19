/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathLocalStability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathLipschitzStability

/-! Noise stability applies to actual paths on their finite existence interval. -/

@[expose] public section
open MeasureTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem drivenVolterra_lipschitz_stability_on (b : E → E) (L : ℝ≥0) (hb : LipschitzWith L b)
    (x : E) (N M X Y : ℝ → E) (T δ : ℝ) (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (hX : ContinuousOn X (Icc 0 T)) (hY : ContinuousOn Y (Icc 0 T))
    (hEqX : ∀ t ∈ Icc 0 T, X t = x + N t + ∫ s in (0 : ℝ)..t, b (X s))
    (hEqY : ∀ t ∈ Icc 0 T, Y t = x + M t + ∫ s in (0 : ℝ)..t, b (Y s))
    (hNoise : ∀ t ∈ Icc 0 T, ‖N t - M t‖ ≤ δ) :
    ∀ t ∈ Icc 0 T, ‖X t-Y t‖ ≤ δ*Real.exp ((L : ℝ)*T) := by
  let p := fun t : ℝ => (Set.projIcc 0 T hT t : ℝ)
  have hp : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hpr (t : ℝ) : p t ∈ Icc 0 T := (Set.projIcc 0 T hT t).property
  have hpe (t : ℝ) (ht : t ∈ Icc 0 T) : p t = t :=
    congrArg Subtype.val (Set.projIcc_of_mem hT ht)
  have hInt (A : ℝ → E) (t : ℝ) (ht : t ∈ Icc 0 T) :
      (∫ s in (0 : ℝ)..t, b (A (p s))) = (∫ s in (0 : ℝ)..t, b (A s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    dsimp only
    rw [hpe s ⟨hs.1, hs.2.trans ht.2⟩]
  have hEqXc (t : ℝ) (ht : t ∈ Icc 0 T) :
      (X ∘ p) t = x+N t+∫ s in (0 : ℝ)..t, b ((X ∘ p) s) := by
    dsimp only [Function.comp_apply]
    rw [hpe t ht, hInt X t ht]
    exact hEqX t ht
  have hEqYc (t : ℝ) (ht : t ∈ Icc 0 T) :
      (Y ∘ p) t = x+M t+∫ s in (0 : ℝ)..t, b ((Y ∘ p) s) := by
    dsimp only [Function.comp_apply]
    rw [hpe t ht, hInt Y t ht]
    exact hEqY t ht
  have h := drivenVolterra_lipschitz_stability_exp b L hb x N M (X ∘ p) (Y ∘ p)
    (hX.comp_continuous hp hpr) (hY.comp_continuous hp hpr) T δ hT hδ hEqXc hEqYc hNoise
  intro t ht
  simpa only [Function.comp_apply, hpe t ht] using h t ht

end
end GinibrePoincare
