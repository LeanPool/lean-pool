/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section2Base
public import LeanPool.GraphMinor.GM07.Section2MinVal
import LeanPool.GraphMinor.GM11.PerimeterPull
import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.Surface.SphereDisc

/-!
# Graph Minors VII, (2.1): seam graphs as printed

Graph Minors VII, (2.1) (page 215), says that a graph `J` in `Σ` is a seam graph for some net if
and only if

* (i) `bd(Σ) ⊆ U(J)`, and every edge of `J` is either included in `bd(Σ)` or disjoint from it;
* (ii) `J - bd(Σ)` has no isolated vertices;
* (iii) `J` has a unique region; and
* (iv) every `O`-arc included in that region is null-homotopic.

This file proves conditions (i) and (ii) for seam graphs; `theorem_2_1_forward`
(`GraphMinor/GM07/Section2.lean`) then gives the forward direction with all four conditions as
printed. Condition (ii) uses `deleteBd`, the paper's `J - bd(Σ)` from page 214,
which keeps every vertex of `J` and the edges of `J` that miss `bd(Σ)`. The two new facts are that
the open image of each pasted side is an edge of `J` that misses `bd(Σ)` (`Net.e_int_mem_E`,
`Net.disjoint_e_int_bd`), and that every other edge of `J` lies in `bd(Σ)`
(`Net.seamGraph_edges_eq`).

The printed converse is false. A seam graph needs a pair, since the paper defines it only "provided
that $\Pi \ne \emptyset$". The empty graph in the sphere satisfies (i)–(iv), and it has no vertex,
so
it is not a seam graph (`not_theorem_2_1_proof`). A graph whose point set is not connected, such as
two
disjoint edges in the sphere, is another counterexample, since the point set of a seam graph is the
image of a circle. The converse for `U(J)` connected is in `GraphMinor/GM07/Section2Converse.lean`.
If `U(J)` is not empty, then (i) and (ii) give an edge of `J` that misses `bd(Σ)`
(`exists_edge_disjoint_bd_of_nonempty`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

namespace Net

/-- Condition (i) of Graph Minors VII, (2.1) (page 215), for a seam graph. The pasted sides give
edges that miss `bd(Σ)`, and every other edge is a piece of `bd(Σ)` (`seamGraph_edges_eq`). This is
the paper's "the sets $\{f_i(x) \colon 0 < x < 1\}$ $(1 \le i \le r)$ are all edges of $J$, and each
is disjoint from $bd(\Sigma)$; and any other edge of $J$ is included in $bd(\Sigma)$" (page 216). -/
theorem bd_subset_and_edges_seamGraph (hS : IsSurface S) (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) :
    bd S ⊆ J.U ∧ ∀ e ∈ J.E, e ⊆ bd S ∨ e ∩ bd S = ∅ := by
  have : T2Space S := hS.2.1
  refine ⟨hJ.2.1 ▸ N.bd_subset_seamU, fun e he => ?_⟩
  rw [(N.seamGraph_edges_eq hS hJ).1] at he
  rcases he with ⟨i, rfl⟩ | he
  · exact Or.inr (disjoint_iff_inter_eq_empty.mp (N.disjoint_e_int_bd hS i))
  · exact Or.inl (he.2.1.trans sdiff_subset)

/-- Condition (ii) of Graph Minors VII, (2.1) (page 215), for a seam graph: `J - bd(Σ)` has no
isolated vertices. Each vertex of `J` is an end `φ(f_i(0))` or `φ(f_i(1))` of some pair, and the
open image of `f_i` is an edge of `J` that misses `bd(Σ)` and has this vertex in its closure. -/
theorem hasNoIsolatedVertices_deleteBd_seamGraph [T1Space S] (hS : IsSurface S) (N : Net S)
    {J : Drawing S} (hJ : N.IsSeamGraphFor J) : HasNoIsolatedVertices (deleteBd J) := by
  have : T2Space S := hS.2.1
  intro v hv
  have hvJ : v ∈ J.V := J.spanV_subset _ _ hv
  have hv' : v ∈ N.seamV := hJ.2.2 ▸ hvJ
  obtain ⟨i, hi⟩ := hv'
  have heE : N.interiorSeamEdge i ∈ J.E := N.e_int_mem_E hJ i
  have hdisj : N.interiorSeamEdge i ∩ bd S = ∅ :=
    disjoint_iff_inter_eq_empty.mp (N.disjoint_e_int_bd hS i)
  have hcl : v ∈ closure (N.interiorSeamEdge i) := by
    have h := N.tilde_e_int hJ i
    rw [tilde_eq_closure_inter_V J heE] at h
    have hmem : v ∈ closure (N.interiorSeamEdge i) ∩ J.V := by
      rw [h]
      rcases hi with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact hmem.1
  have hE : N.interiorSeamEdge i ∈ (deleteBd J).E := by
    rw [deleteBd, Drawing.span_E]
    exact ⟨⟨heE, hdisj⟩, heE⟩
  exact ⟨N.interiorSeamEdge i, hE, hv, Or.inl hE, hcl⟩

end Net

/-! ## The printed converse fails -/

theorem emptyDrawing_E : (emptyDrawing S).E = ∅ := by
  ext e
  refine ⟨fun he => ?_, fun he => he.elim⟩
  exact he.1.ne_empty (subset_empty_iff.mp (he.2.1.trans sdiff_subset))

/-- In a sphere, the empty graph satisfies conditions (i)–(iv) of Graph Minors VII, (2.1)
(page 215). The sphere has no boundary, so (i) and (ii) hold trivially. Its only region is the
whole sphere, and every `O`-arc of the sphere bounds a closed disc (`sphere_disc`), so it is
null-homotopic. -/
theorem emptyDrawing_conditions_of_isSphere [T1Space S] (hS : IsSphere S) :
    (bd S ⊆ (emptyDrawing S).U ∧ ∀ e ∈ (emptyDrawing S).E, e ⊆ bd S ∨ e ∩ bd S = ∅) ∧
    HasNoIsolatedVertices (deleteBd (emptyDrawing S)) ∧
    (emptyDrawing S).R.ncard = 1 ∧
    (∀ r ∈ (emptyDrawing S).R, ∀ F : Set S, F ⊆ r → IsOArc F → IsNullHomotopicOArc F) := by
  obtain ⟨hcl, hconn⟩ := GM11.IsSphere.isClosedSurface hS
  have hbd : bd S = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => hx (hcl.2.2 x)
  have hR : (emptyDrawing S).R = {univ} := by
    ext r
    simp only [Drawing.R, componentsIn, mem_image, mem_singleton_iff]
    have hU : (emptyDrawing S).U = ∅ := rfl
    rw [hU, sdiff_empty]
    constructor
    · rintro ⟨x, -, rfl⟩
      rw [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
    · rintro rfl
      obtain ⟨x⟩ := hconn.toNonempty
      exact ⟨x, mem_univ x, by rw [connectedComponentIn_univ,
        PreconnectedSpace.connectedComponent_eq_univ]⟩
  refine ⟨⟨hbd ▸ empty_subset _, fun e he => by rw [emptyDrawing_E] at he; exact he.elim⟩,
    fun v hv => ((emptyDrawing S).spanV_subset _ _ hv).elim, by rw [hR, ncard_singleton],
    fun _ _ F _ hF => ?_⟩
  obtain ⟨Δ, -, -, hΔ, -, hΔF, -⟩ := sphere_disc S hS F hF
  exact isNullHomotopicOArcIn_of_subset_disc hF (subset_univ Δ) hΔ (hΔF ▸ discBd_subset Δ)

/-- **Graph Minors VII, (2.1)**: the printed converse is false. In the sphere, the empty graph
satisfies (i)–(iv) (`emptyDrawing_conditions_of_isSphere`), but it is not a seam graph, because a
seam graph is defined only "provided that $\Pi \ne \emptyset$" (page 215), and then it has a vertex
(`not_isSeamGraph_emptyDrawing`). -/
theorem not_theorem_2_1_proof :
    ¬ ∀ (S : Type) [TopologicalSpace S] [T1Space S], IsSurface S → ConnectedSpace S →
      ∀ J : Drawing S,
        (bd S ⊆ J.U ∧ ∀ e ∈ J.E, e ⊆ bd S ∨ e ∩ bd S = ∅) →
        HasNoIsolatedVertices (deleteBd J) →
        J.R.ncard = 1 →
        (∀ r ∈ J.R, ∀ F : Set S, F ⊆ r → IsOArc F → IsNullHomotopicOArc F) →
        IsSeamGraph J := by
  intro h
  have hS : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  obtain ⟨hcl, hconn⟩ := GM11.IsSphere.isClosedSurface hS
  have : T2Space (OnePoint EuclideanPlane) := hcl.2.1
  obtain ⟨h1, h2, h3, h4⟩ := emptyDrawing_conditions_of_isSphere hS
  exact not_isSeamGraph_emptyDrawing
    (h (OnePoint EuclideanPlane) hcl.isSurface hconn _ h1 h2 h3 h4)

/-- If `J` satisfies conditions (i) and (ii) of Graph Minors VII, (2.1) (page 215), and `U(J)` is
not empty, then some edge of `J` misses `bd(Σ)`. The proof: `J` has a vertex, since a point of
`U(J)`
is either a vertex or lies on an edge, and every edge has an end. By (ii) this vertex is the end of
an
edge of `J - bd(Σ)`, which is an edge of `J` that misses `bd(Σ)`. -/
theorem exists_edge_disjoint_bd_of_nonempty [T1Space S] {J : Drawing S}
    (h2 : HasNoIsolatedVertices (deleteBd J)) (hU : J.U.Nonempty) :
    ∃ e ∈ J.E, e ∩ bd S = ∅ := by
  obtain ⟨v, hv⟩ : J.V.Nonempty := by
    obtain ⟨x, hx⟩ := hU
    by_cases hxV : x ∈ J.V
    · exact ⟨x, hxV⟩
    · have hxe : x ∈ J.U \ J.V := ⟨hx, hxV⟩
      have he : pathComponentIn (J.U \ J.V) x ∈ J.E := pathComponentIn_mem_arcComponentsIn hxe
      rcases J.edge_cond _ he with ⟨u, w, -, huw, -⟩ | ⟨u, hu, -⟩
      · have hu : u ∈ closure (pathComponentIn (J.U \ J.V) x) ∩ J.V := by
          rw [huw]
          exact Or.inl rfl
        exact ⟨u, hu.2⟩
      · have hu' : u ∈ closure (pathComponentIn (J.U \ J.V) x) ∩ J.V := by
          rw [hu]
          exact rfl
        exact ⟨u, hu'.2⟩
  have hvD : v ∈ (deleteBd J).V := Or.inl ⟨hv, hv⟩
  obtain ⟨e, he, -⟩ := h2 v hvD
  rw [deleteBd, Drawing.span_E] at he
  exact ⟨e, he.1.1, he.1.2⟩

end GraphMinor.GM07
