/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevLocalSlices.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevLocalIntegrability
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Ordinary local integrability on almost every real coordinate line -/

@[expose] public section
open MeasureTheory Filter
namespace GinibrePoincare
noncomputable section

theorem locallyIntegrable_real_product_slices
    {Y : Type*} [NormedAddCommGroup Y] [ProperSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (ν : Measure Y) [SFinite ν] (f : ℝ × Y → ℝ)
    (hf : LocallyIntegrable f ((volume : Measure ℝ).prod ν)) :
    ∀ᵐ y ∂ν, LocallyIntegrable (fun t => f (t, y)) volume := by
  have hi (k : ℕ) : Integrable
      ((Metric.closedBall (0 : ℝ × Y) (k : ℝ)).indicator f)
      ((volume : Measure ℝ).prod ν) :=
    (hf.integrableOn_isCompact (isCompact_closedBall _ _)).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  have ha : ∀ᵐ y ∂ν, ∀ k : ℕ, Integrable
      (fun t => (Metric.closedBall (0 : ℝ × Y) (k : ℝ)).indicator f (t, y)) volume :=
    ae_all_iff.mpr fun k => (hi k).prod_left_ae
  filter_upwards [ha] with y hy
  intro t
  obtain ⟨k, hk⟩ := exists_nat_gt (‖(t, y)‖ + 1)
  refine ⟨Metric.ball t 1, Metric.ball_mem_nhds t zero_lt_one, ?_⟩
  apply ((hy k).integrableOn).congr_fun _ Metric.isOpen_ball.measurableSet
  intro s hs
  apply Set.indicator_of_mem
  rw [Metric.mem_closedBall, dist_zero_right]
  have hst : ‖s - t‖ < 1 := by simpa [Real.dist_eq] using hs
  have hd : ‖(s, y) - (t, y)‖ < 1 := by simpa [Prod.norm_def] using hst
  have hb := norm_le_norm_sub_add (s, y) (t, y)
  linarith

end
end GinibrePoincare
