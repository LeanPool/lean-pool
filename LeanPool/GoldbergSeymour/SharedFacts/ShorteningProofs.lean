/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.MissingColors

/-!
# Proper recoloring of one edge

The endpoint-missing-color argument from the credited Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12, independent of hierarchy construction.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ShorteningProofs

open scoped Sym2

/-- Assigning an edge a color missing at both endpoints preserves properness. -/
theorem properRecoloring {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {mu sigma : PartialEdgeColoring E k}
    (proper : IsProperEdgeColoring G mu) (f : E) (alpha : Fin k) (y w : V)
    (hends : G.ends f = s(y, w))
    (missingFirst : alpha ∈ MissingColors G mu y)
    (missingSecond : alpha ∈ MissingColors G mu w)
    (selected : sigma f = some alpha)
    (fixed : ∀ e, e ≠ f → sigma e = mu e) : IsProperEdgeColoring G sigma := by
  classical
  intro e g c heg hadj he hg
  by_cases hef : e = f
  · subst e
    have hgf : g ≠ f := heg.symm
    have hc : c = alpha := Option.some.inj (he.symm.trans selected)
    subst c
    rw [fixed g hgf] at hg
    obtain ⟨v, hvf, hvg⟩ := hadj
    have hv : v = y ∨ v = w := by simpa only [Incident, hends, Sym2.mem_iff] using hvf
    rcases hv with rfl | rfl
    · exact (Finset.mem_sdiff.mp missingFirst).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hvg, hg⟩)
    · exact (Finset.mem_sdiff.mp missingSecond).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hvg, hg⟩)
  · by_cases hgf : g = f
    · subst g
      have hc : c = alpha := Option.some.inj (hg.symm.trans selected)
      subst c
      rw [fixed e hef] at he
      obtain ⟨v, hve, hvf⟩ := hadj
      have hv : v = y ∨ v = w := by simpa only [Incident, hends, Sym2.mem_iff] using hvf
      rcases hv with rfl | rfl
      · exact (Finset.mem_sdiff.mp missingFirst).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, hve, he⟩)
      · exact (Finset.mem_sdiff.mp missingSecond).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, hve, he⟩)
    · exact proper heg hadj ((fixed e hef).symm.trans he)
        ((fixed g hgf).symm.trans hg)

end GoldbergSeymour.SharedFacts.ShorteningProofs

end
