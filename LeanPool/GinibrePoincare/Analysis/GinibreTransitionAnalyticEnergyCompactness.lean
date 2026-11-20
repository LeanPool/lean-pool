/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticEnergyCompactness.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticCaccioppoli
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Genuine L² membership follows from locally cut off finite-energy bounds
and almost-everywhere convergence. -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section

theorem actualL2_toLp_norm_sq {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure Ω)
    (f : Ω → E) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq]

theorem actualL2Limit_memLp_of_energy_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure Ω)
    (f : ℕ → Ω → E) (g : Ω → E) (hf : ∀ n, MemLp (f n) 2 μ)
    (hg : AEStronglyMeasurable g μ) (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ n, (∫ x, ‖f n x‖ ^ 2 ∂μ) ≤ D)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : MemLp g 2 μ := by
  have hn (n : ℕ) : ‖(hf n).toLp (f n)‖ ≤ Real.sqrt D := by
    have hh := hb n
    rw [← actualL2_toLp_norm_sq μ (f n) (hf n)] at hh
    exact (Real.le_sqrt (norm_nonneg _) hD).mpr hh
  have he (n : ℕ) : eLpNorm (f n) 2 μ ≤ ENNReal.ofReal (Real.sqrt D) := by
    rw [← Lp.eNorm_toLp (hf n), ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hn n)
  exact (Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall he) (fun n => (hf
      n).aestronglyMeasurable) hg ht).trans_lt
    ENNReal.ofReal_lt_top

end
end GinibrePoincare
