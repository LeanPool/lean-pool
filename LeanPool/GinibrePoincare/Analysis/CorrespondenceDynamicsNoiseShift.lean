/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDynamicsNoiseShift.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsStoppingFinite
/-!
# Correspondence dynamics noise shift

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `correspondenceNoiseShift_continuous`, `correspondenceNoiseShift_actual`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Shift a continuous noise path, retaining its zero extension to negative times. -/
def correspondenceNoiseShift (n : ℕ) (s : ℝ≥0) (N : GinibreContinuousNoise n) :
    GinibreContinuousNoise n :=
  ⟨⟨fun t => N.val ((s : ℝ) + max t 0) - N.val s,
    (N.val.continuous.comp (continuous_const.add (continuous_id.max continuous_const))).sub
      continuous_const⟩, by simp⟩

theorem correspondenceNoiseShift_continuous (n : ℕ) :
    Continuous (fun p : ℝ≥0 × GinibreContinuousNoise n => correspondenceNoiseShift n p.1 p.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hN : Continuous (fun p : (ℝ≥0 × GinibreContinuousNoise n) × ℝ => p.1.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hs : Continuous (fun p : (ℝ≥0 × GinibreContinuousNoise n) × ℝ => (p.1.1 : ℝ)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  exact (continuous_eval.comp (hN.prodMk (hs.add (continuous_snd.max continuous_const)))).sub
    (continuous_eval.comp (hN.prodMk hs))

theorem correspondenceNoiseShift_actual {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (α : ℝ) (s : ℝ≥0) :
    (fun ω => correspondenceNoiseShift n s (ginibreBrownianFullContinuousNoise n B α ω)) =ᵐ[P]
      ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α := by
  have hshift := (brownianFamilyShift_isBrownian_independent B P hB hind s).1
  filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB α,
    ginibreBrownianFullContinuousNoise_ae n _ P hshift α] with ω hN hS
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change (ginibreBrownianFullContinuousNoise n B α ω).val ((s : ℝ)+max t 0) -
    (ginibreBrownianFullContinuousNoise n B α ω).val s = _
  rw [hN, hN, hS]
  have hh := ginibreConfigurationBrownianNoise_shift_nonneg n B α s ω (max t 0) (le_max_right _ _)
  rw [← hh]
  change (fun j => Real.sqrt (2*α/(n : ℝ)^2) •
      ((brownianFamilyShift B s (j, 0) (max t 0).toNNReal ω : ℂ) + Complex.I *
        (brownianFamilyShift B s (j, 1) (max t 0).toNNReal ω : ℂ))) = _
  have ht : (max t 0).toNNReal = t.toNNReal := by
    apply Subtype.ext
    simp [Real.toNNReal]
  rw [ht]
  rfl

end
end GinibrePoincare
