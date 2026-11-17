/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Convergence in probability -/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

lemma TendstoInMeasure.add {ι E : Type*} [NormedAddCommGroup E]
    {f g : ι → Ω → E} {l₁ l₂ : Ω → E} {u : Filter ι}
    (hf : TendstoInMeasure μ f u l₁) (hg : TendstoInMeasure μ g u l₂) :
    TendstoInMeasure μ (fun n ω ↦ f n ω + g n ω) u (fun ω ↦ l₁ ω + l₂ ω) := by
  unfold TendstoInMeasure at hf hg ⊢
  intro ε hε
  have hε' : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  specialize hf (ε / 2) hε'
  specialize hg (ε / 2) hε'
  simp only
  have h_subset1 i : {x | ε ≤ edist (f i x + g i x) (l₁ x + l₂ x)}
      ⊆ {x | ε ≤ edist (f i x) (l₁ x) + edist (g i x) (l₂ x)} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact hx.trans (edist_add_add_le _ _ _ _)
  have h_subset2 i : {x | ε ≤ edist (f i x + g i x) (l₁ x + l₂ x)}
      ⊆ {x | ε / 2 ≤ edist (f i x) (l₁ x)} ∪ {x | ε / 2 ≤ edist (g i x) (l₂ x)} := by
    refine (h_subset1 i).trans fun x ↦ ?_
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    contrapose!
    intro ⟨h1, h2⟩
    conv_rhs => rw [← ENNReal.add_halves ε]
    gcongr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun i ↦ μ {x | ε / 2 ≤ edist (f i x) (l₁ x)} + μ {x | ε / 2 ≤ edist (g i x) (l₂ x)})
    ?_ (by positivity) ?_
  · rw [← add_zero (0 : ℝ≥0∞)]
    exact hf.add hg
  · intro i
    simp only
    grw [measure_mono (h_subset2 i)]
    exact measure_union_le _ _

end MeasureTheory
