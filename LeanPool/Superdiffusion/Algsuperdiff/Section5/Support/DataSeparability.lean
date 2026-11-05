/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionSelector

/-!
# DataSeparability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Every class of continuous forcing fields on the closed cube has a countable dense subclass

The forcing fields of Section 5.1 are continuous on the closed cube, so they are
points of `C(closedCubeAt y n, Vec d)`.  That space is second countable — the
closed cube is a compact second-countable locally compact space and `Vec d` is
second countable — and second countability is inherited by every subspace, so
**every** class of such fields, in particular the normalized one, has a
countable subclass dense in it for the supremum distance.  No compactness and no
Arzelà–Ascoli argument is needed.

## Main definitions

* `extendVec y n G` — the field on `ℝ^d` determined by a continuous field on the
  closed cube, through the coordinatewise retraction.

## References

* ABK26, the localized error and regularity quantities of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open scoped Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. The field determined by a continuous field on the closed cube -/

/-- The forcing field determined by a continuous field on the closed cube. -/
def extendVec (y : Vec d) (n : ℤ) (G : C(closedCubeAt y n, Vec d)) : Vec d → Vec d :=
  fun x => G ⟨clampTo y n x, clampTo_mem y n x⟩

theorem extendVec_apply_of_mem {y : Vec d} {n : ℤ} (G : C(closedCubeAt y n, Vec d))
    {x : Vec d} (hx : x ∈ closedCubeAt y n) : extendVec y n G x = G ⟨x, hx⟩ := by
  simp only [extendVec]
  congr 1
  exact Subtype.ext (clampTo_eq_self hx)

/-! ## 2. Every class has a countable dense subclass -/

/-- **Second countability supplies the countable subclass.**  For every class of
continuous fields on the closed cube and every member of it, some member of a
fixed countable subclass is arbitrarily close in the supremum distance. -/
theorem exists_countable_subset_dense (y : Vec d) (n : ℤ)
    (s : Set C(closedCubeAt y n, Vec d)) :
    ∃ t : Set C(closedCubeAt y n, Vec d), t.Countable ∧ t ⊆ s ∧
      ∀ F ∈ s, ∀ eps : ℝ, 0 < eps → ∃ G ∈ t, dist G F < eps := by
  obtain ⟨c, hccount, hcdense⟩ :=
    TopologicalSpace.exists_countable_dense (α := (s : Set C(closedCubeAt y n, Vec d)))
  refine ⟨Subtype.val '' c, hccount.image _, ?_, ?_⟩
  · rintro _ ⟨G, -, rfl⟩
    exact G.2
  · intro F hF eps heps
    obtain ⟨G, hGc, hGdist⟩ :=
      Metric.mem_closure_iff.1 (hcdense ⟨F, hF⟩) eps heps
    refine ⟨(G : C(closedCubeAt y n, Vec d)), ⟨G, hGc, rfl⟩, ?_⟩
    rw [dist_comm]
    simpa [Subtype.dist_eq] using hGdist

end

end Algsuperdiff.Section5.Support
