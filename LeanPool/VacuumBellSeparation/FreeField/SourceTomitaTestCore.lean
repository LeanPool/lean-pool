/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceTomita

/-!
# Compact smooth sources form the actual Tomita graph core

The equality is between closed graph sets in the original one-particle
Hilbert space. The dense source completions approximate both graph
coordinates simultaneously. It holds before any boundedness or separating
hypothesis, and in particular for the genuine halfspace source graph.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Gaussian.HilbertComplexification

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- Source Tomita test graph. -/
def sourceTomitaTestGraph : Set (Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m)) :=
  {p | ∃ u v : SourceTestSpace hm U,
    p = (timeZeroL2 hm u.1 + Complex.I • timeZeroL2 hm v.1,
      timeZeroL2 hm u.1 - Complex.I • timeZeroL2 hm v.1)}

theorem sourceTomitaTestGraph_subset : sourceTomitaTestGraph hm U ⊆ sourceTomitaGraph hm U := by
  rintro p ⟨u, v, rfl⟩
  refine ⟨mk (u : SourceHilbert hm U) (v : SourceHilbert hm U), ?_, ?_⟩
  · change sourceEmbedding hm U (u : SourceHilbert hm U) +
      Complex.I • sourceEmbedding hm U (v : SourceHilbert hm U) = _
    rw [sourceEmbedding_coe, sourceEmbedding_coe]
  · change sourceEmbedding hm U (u : SourceHilbert hm U) +
      Complex.I • sourceEmbedding hm U (-(v : SourceHilbert hm U)) = _
    rw [map_neg, smul_neg, sourceEmbedding_coe, sourceEmbedding_coe, sub_eq_add_neg]

theorem sourceTomita_pair_mem_closure_test (u v : SourceHilbert hm U) :
    (sourceEmbedding hm U u + Complex.I • sourceEmbedding hm U v,
      sourceEmbedding hm U u - Complex.I • sourceEmbedding hm U v) ∈
        closure (sourceTomitaTestGraph hm U) := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_closure.preimage (by fun_prop)) ?_
  intro u
  refine UniformSpace.Completion.induction_on v
    (isClosed_closure.preimage (by fun_prop)) ?_
  intro v
  apply subset_closure
  exact ⟨u, v, by rw [sourceEmbedding_coe, sourceEmbedding_coe]⟩

/-- Literal graph-core equality, rather than density of only the first projection. -/
theorem closure_sourceTomitaTestGraph :
    closure (sourceTomitaTestGraph hm U) = sourceTomitaGraph hm U := by
  apply Set.Subset.antisymm
  · exact closure_minimal (sourceTomitaTestGraph_subset hm U) (sourceTomitaGraph_isClosed hm U)
  · rintro p ⟨z, hx, hy⟩
    have h := sourceTomita_pair_mem_closure_test hm U z.re z.im
    have hp : p = (sourceEmbedding hm U z.re + Complex.I • sourceEmbedding hm U z.im,
        sourceEmbedding hm U z.re - Complex.I • sourceEmbedding hm U z.im) := by
      apply Prod.ext
      · exact hx.symm
      · rw [← hy]
        change sourceEmbedding hm U z.re + Complex.I • sourceEmbedding hm U (-z.im) = _
        rw [map_neg, smul_neg, sub_eq_add_neg]
    rwa [hp]

end VacuumBellSeparation
