/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitCountableEvaluation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitApproximation
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! Evaluating an adapted process at a bounded countable-range random time. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem adapted_countable_time_evaluation_measurable {Ω E : Type*}
    [mAmbient : MeasurableSpace Ω] [MeasurableSpace E]
    (F : Filtration ℝ≥0 mAmbient) (u : ℝ≥0 → Ω → E)
    (hu : Adapted F u) (s : ℝ≥0) (q : Ω → ℝ≥0)
    (hq : @Measurable Ω ℝ≥0 (F s) _ q) (hcount : (Set.range q).Countable)
    (hbound : ∀ ω, q ω ≤ s) : @Measurable Ω E (F s) _ (fun ω => u (q ω) ω) := by
  have : Countable (Set.range q) := hcount.to_subtype
  have hEval : @Measurable (Ω × Set.range q) E
      (@Prod.instMeasurableSpace Ω (Set.range q) (F s) _) _
      (fun p => u p.2 p.1) := by
    apply measurable_from_prod_countable_left
    intro t
    obtain ⟨ω, hω⟩ := t.property
    have ht : t.val ≤ s := by rw [← hω]; exact hbound ω
    exact (hu t).mono (F.mono ht) le_rfl
  exact hEval.comp (measurable_id.prodMk (hq.subtype_mk (h := fun ω => Set.mem_range_self ω)))

theorem adapted_capped_upper_grid_evaluation_measurable {Ω E : Type*}
    [mAmbient : MeasurableSpace Ω] [MeasurableSpace E]
    (F : Filtration ℝ≥0 mAmbient) (u : ℝ≥0 → Ω → E)
    (hu : Adapted F u) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop ℝ≥0))) (m : ℕ) (s : ℝ≥0) :
    @Measurable Ω E (F s) _ (fun ω => u (min s (stoppingUpperGrid m (σ ω))) ω) := by
  let q := fun ω => min s (stoppingUpperGrid m (σ ω))
  have hStop := (stoppingUpperGrid_isStoppingTime hσ m).min_const s
  have hm := hStop.measurable_of_le (fun ω => min_le_right _ _)
  have hq : @Measurable Ω ℝ≥0 (F s) _ q := by
    have h := ENNReal.measurable_toNNReal.comp hm
    convert h using 1
    funext ω
    change min s (stoppingUpperGrid m (σ ω)) =
      (min (stoppingUpperGrid m (σ ω) : ℝ≥0∞) (s : ℝ≥0∞)).toNNReal
    rw [← ENNReal.coe_min, ENNReal.toNNReal_coe, min_comm]
  have hcount : (Set.range q).Countable := by
    apply (Set.countable_range (fun k : ℕ => min s
      ((k : ℝ≥0)/((m+1 : ℕ) : ℝ≥0)))).mono
    rintro x ⟨ω, rfl⟩
    exact ⟨Nat.ceil (((m+1 : ℕ) : ℝ≥0)*σ ω), rfl⟩
  exact adapted_countable_time_evaluation_measurable F u hu s q hq hcount
    (fun ω => min_le_left _ _)

end
end GinibrePoincare
