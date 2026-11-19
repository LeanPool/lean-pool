/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticProbabilityRestriction.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticProbabilityOperations

/-! Restricting genuine convergence in probability to any fixed event. -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem ginibre_tendstoInMeasure_indicator {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (E : Set Ω)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (hf : TendstoInMeasure P f atTop g) :
    TendstoInMeasure P (fun n => E.indicator (f n)) atTop (E.indicator g) := by
  classical
  rw [tendstoInMeasure_iff_measureReal_norm] at hf ⊢
  intro ε hε
  apply squeeze_zero (fun n => measureReal_nonneg)
    (fun n => measureReal_mono (show
      {ω | ε ≤ ‖E.indicator (f n) ω-E.indicator g ω‖} ⊆ {ω | ε ≤ ‖f n ω-g ω‖} from by
        intro ω hω
        by_cases he : ω ∈ E
        · simpa only [Set.mem_ofPred_eq, Set.indicator_of_mem he] using hω
        · simp only [Set.mem_ofPred_eq, Set.indicator_of_notMem he, sub_self, norm_zero] at hω
          exact False.elim (not_le.mpr hε hω)))
    (hf ε hε)
end
end GinibrePoincare
