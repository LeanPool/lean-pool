/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section46EdgeIncidence
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# The lifted first edge of each path

For a path with distinct ends, its simple walk starts with a non-loop edge.
The normal net lifts that edge to a single incidence over the initial
vertex. These are the incidences counted on page 225 of VII (4.6).
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

/-- A nontrivial path in the original graph has a first edge with a unique
lifted incidence over its initial vertex, as in VII (4.6), page 225. -/
theorem Net.exists_lifted_first_edge {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {G J P : Drawing S}
    (hJ : N.IsSeamGraphFor J) (hnorm : G.IsNormal J.U)
    (hPG : P.IsSubdrawing G) {a b : S} (hab : a ≠ b)
    (hP : P.IsPathBetween a b) :
    ∃ e ∈ P.E, ∃ a' : N.D, N.φ a' = a ∧ a' ∈ closure (N.φ ⁻¹' e) ∧
      ∀ x ∈ closure (N.φ ⁻¹' e), N.φ x = a → x = a' := by
  obtain ⟨W, hsimple, _, hPE⟩ := hP
  cases W with
  | nil hv => exact (hab rfl).elim
  | @cons a w b e hl W =>
    have heP : e ∈ P.E := by
      rw [hPE]
      exact List.mem_cons_self
    have hne : a ≠ w := fun h =>
      (List.nodup_cons.mp hsimple).1 (h ▸ W.start_mem_support)
    have hlink : G.toGraph.IsLink e a w := (hPG.isLink_iff heP).mp hl
    have heG : e ∈ G.E := hPG.2 heP
    have hcap : closure e ∩ G.V = {a, w} := hlink.2.2.2
    have hline : IsLineWithEnds (closure e) a w := by
      rcases G.edge_cond e heG with ⟨u, v, _, huv, hL⟩ | ⟨u, hu, _⟩
      · have hpair : ({u, v} : Set S) = {a, w} := huv.symm.trans hcap
        rcases pair_eq_pair_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hL
        · exact hL.symm
      · have hau : a = u := by
          have ha : a ∈ ({u} : Set S) := hu ▸ (hcap ▸ mem_insert a {w})
          exact ha
        have hwu : w = u := by
          have hw : w ∈ ({u} : Set S) := hu ▸ (hcap ▸ mem_insert_of_mem a (mem_singleton w))
          exact hw
        exact (hne (hau.trans hwu.symm)).elim
    obtain ⟨a', ha', ha'e, huniq⟩ :=
      N.exists_unique_lifted_edge_end hS hJ hnorm heG hcap hline
    exact ⟨e, heP, a', ha', ha'e, huniq⟩

end GraphMinor.GM07
