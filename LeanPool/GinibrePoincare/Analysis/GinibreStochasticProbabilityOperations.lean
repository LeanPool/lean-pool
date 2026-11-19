/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticProbabilityOperations.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticMeanSquareInProbability

/-! Elementary real algebra of convergence in probability. -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem ginibre_tendstoInMeasure_add {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f h : ℕ → Ω → ℝ) (g k : Ω → ℝ)
    (hf : TendstoInMeasure P f atTop g) (hh : TendstoInMeasure P h atTop k) :
    TendstoInMeasure P (fun n ω => f n ω+h n ω) atTop (fun ω => g ω+k ω) := by
  rw [tendstoInMeasure_iff_measureReal_norm] at hf hh ⊢
  intro ε hε
  apply squeeze_zero (fun n => measureReal_nonneg)
    (fun n => (measureReal_mono (show {ω | ε ≤ ‖f n ω+h n ω-(g ω+k ω)‖} ⊆
      {ω | ε/2 ≤ ‖f n ω-g ω‖} ∪ {ω | ε/2 ≤ ‖h n ω-k ω‖} from by
        intro ω hw
        by_contra hc
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hc
        have hnorm := norm_add_le (f n ω-g ω) (h n ω-k ω)
        have he : f n ω+h n ω-(g ω+k ω) = (f n ω-g ω)+(h n ω-k ω) := by ring
        change ε ≤ ‖f n ω+h n ω-(g ω+k ω)‖ at hw
        rw [he] at hw
        linarith)).trans (measureReal_union_le _ _))
  simpa only [add_zero] using (hf (ε/2) (by positivity)).add (hh (ε/2) (by positivity))

theorem ginibre_tendstoInMeasure_neg {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf : TendstoInMeasure P f atTop g) :
    TendstoInMeasure P (fun n ω => -f n ω) atTop (fun ω => -g ω) := by
  rw [tendstoInMeasure_iff_measureReal_norm] at hf ⊢
  intro ε hε
  simpa only [neg_sub_neg, norm_sub_rev] using hf ε hε

theorem ginibre_tendstoInMeasure_const_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (c : ℝ)
    (hf : TendstoInMeasure P f atTop g) :
    TendstoInMeasure P (fun n ω => c*f n ω) atTop (fun ω => c*g ω) := by
  rw [tendstoInMeasure_iff_measureReal_norm] at hf ⊢
  intro ε hε
  by_cases hc : c = 0
  · subst c
    simp [not_le.mpr hε]
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have h := hf (ε/‖c‖) (div_pos hε hcpos)
    convert h using 1
    funext n
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, ← mul_sub, norm_mul]
    rw [div_le_iff₀ hcpos, mul_comm]

end
end GinibrePoincare
