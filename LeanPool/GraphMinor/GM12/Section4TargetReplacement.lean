/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SplitMinorModel
import LeanPool.GraphMinor.GM12.Section4NoIsolated
import LeanPool.GraphMinor.Minor.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# The target replacement in XII (4.3)

Graph Minors XII (4.3), page 249, starts by replacing a drawable
target by a loopless graph in which every vertex is incident with
at least two edges. Starting with a drawing, add pendant edges
at isolated vertices, subdivide every edge, and add parallel
copies. The original drawing is a subgraph of the first step.
Contracting all right subdivision halves recovers that step, and
the final parallel augmentation retains the subdivision. Thus the
original graph is a minor of the loopless replacement.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A subdrawing is a subgraph, and hence isomorphic to a minor
of the ambient drawing's graph. -/
theorem isIsoMinor_of_subdrawing
    {S : Type*} [TopologicalSpace S] {Γ H : Drawing S} (h : Γ.IsSubdrawing H) :
    IsIsoMinor Γ.toGraph H.toGraph := by
  have hle : Γ.toGraph ≤ H.toGraph :=
    ⟨h.1, fun _ _ _ hl => (h.isLink_iff hl.edge_mem).mp hl⟩
  obtain ⟨K, hK, C, hC, hIso⟩ := IsIsoMinor.refl Γ.toGraph
  exact ⟨K, hK.trans hle, C, hC, hIso⟩

/-- The loopless minimum-degree-two target replacement used at the
start of Graph Minors XII (4.3), page 249, for an actual drawing
of the target graph. -/
theorem exists_loopless_minimum_degree_two_minor
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) :
    ∃ H : Drawing S, IsIsoMinor Γ.toGraph H.toGraph ∧
      (∀ e v, ¬ H.toGraph.IsLink e v v) ∧
      ∀ v ∈ H.V, ∃ e f, e ≠ f ∧ H.toGraph.Inc e v ∧ H.toGraph.Inc f v := by
  obtain ⟨Γ₀, K, H, A, B, m, x, y, hΓ₀, hd, hKH, hloop, htwo⟩ :=
    exists_loopless_minimum_degree_two_replacement hS Γ
  have hminor : IsIsoMinor Γ₀.toGraph K.toGraph := isIsoMinor_of_isMinorModel Γ₀.toGraph K.toGraph
    Γ₀.finite_V Γ₀.finite_edges K.finite_V K.finite_edges (splitBranch Γ₀ m y) A
    (isMinorModel_of_splitData hd)
  exact ⟨H, (isIsoMinor_of_subdrawing hΓ₀).trans
    (hminor.trans (isIsoMinor_of_subdrawing hKH)), hloop, htwo⟩

end GraphMinor.GM12
