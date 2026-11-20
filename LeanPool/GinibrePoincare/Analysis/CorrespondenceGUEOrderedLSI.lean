/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEOrderedLSI.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEExpectationConvergence
/-!
# Correspondence GUE ordered LSI

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueDoubledOrderedMeasure_square_lsi`.
-/

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

theorem gueDoubledRegularized_compact_expectation_tendsto {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ) (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun k => ∫ x, f x ∂bakryEmeryNormalizedGibbs volume
      (gueDoubledRegularizedPotential n (gueRegularizationScale k))) atTop
      (nhds (∫ x, f x ∂gueDoubledOrderedMeasure n)) := by
  obtain ⟨C, hC⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hs.norm
  have hb (x) : ‖f x‖≤C := hC (mem_range_self x)
  rw [gueDoubledOrderedMeasure_integral]
  exact gueDoubledRegularized_expectation_tendsto hn f hf C
    ((norm_nonneg (f 0)).trans (hb 0)) hb

theorem gueDoubledRegularized_entropy_tendsto {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun k => squareEntropy (bakryEmeryNormalizedGibbs volume
      (gueDoubledRegularizedPotential n (gueRegularizationScale k))) f) atTop
      (nhds (squareEntropy (gueDoubledOrderedMeasure n) f)) := by
  have hs := gueDoubledRegularized_compact_expectation_tendsto hn (fun x => f x^2)
    (hf.pow 2) (by
      apply hc.mono
      intro x hx hz
      apply hx
      simp [hz])
  have hl := gueDoubledRegularized_compact_expectation_tendsto hn
    (fun x => f x^2*Real.log (f x^2)) (continuous_square_mul_log hf)
    (compactSupport_square_mul_log hc)
  unfold squareEntropy
  exact hl.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hs)

/-- Sharp-curvature log-Sobolev bound for the actual ordered GUE density,
with independent auxiliary Gaussian coordinates. -/
theorem gueDoubledOrderedMeasure_square_lsi {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ)
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    squareEntropy (gueDoubledOrderedMeasure n) f ≤
      (2/(n : ℝ))*∫ x, ‖gradient f x‖^2 ∂gueDoubledOrderedMeasure n := by
  have he := gueDoubledRegularized_entropy_tendsto hn f hf.continuous hs
  have hg : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n×Fin 2))).symm.continuous.comp
      (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have hgs : HasCompactSupport (fun x => ‖gradient f x‖^2) :=
    ((hs.fderiv ℝ).comp_left
      (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n×Fin 2))).symm) (map_zero
          _)).comp_left
      (g := fun x : EuclideanSpace ℝ (Fin n×Fin 2) => ‖x‖^2) (by simp)
  have hi := gueDoubledRegularized_compact_expectation_tendsto hn
    (fun x => ‖gradient f x‖^2) (hg.norm.pow 2) hgs
  exact le_of_tendsto_of_tendsto he (tendsto_const_nhds.mul hi)
    (Eventually.of_forall (fun k => gueDoubledRegularizedGibbs_lsi hn
      (gueRegularizationScale_pos k) f hf hs))

end
end GinibrePoincare
