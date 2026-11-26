/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section2MinVal
import LeanPool.GraphMinor.GM07.Section46Constants
import LeanPool.GraphMinor.Surface.Cuffs

/-!
# Long and short seam edges in VII (4.6)

On page 225 an edge is long when its closure meets at least `2μ + w + 2`
vertices of `G`. All other seam edges are short. The boundary vertex bound
excludes long edges on cuffs. Short edges have at most `w + 2μ + 1` contacts,
which is the bound later used for `L`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The long seam edges of VII (4.6), page 225:
“*long* if $|\bar{e} \cap V(G)| \ge 2\mu + w + 2$”. -/
def longSeamEdges (G J : Drawing S) (μ w : ℕ) : Set (Set S) :=
  {e ∈ J.E | 2 * μ + w + 2 ≤ (closure e ∩ G.V).ncard}

/-- The short edges of VII (4.6), page 225, are the seam edges which are
not long. -/
def shortSeamEdges (G J : Drawing S) (μ w : ℕ) : Set (Set S) :=
  J.E \ longSeamEdges G J μ w

/-- The short-edge contact bound used in VII (4.6), page 226. -/
theorem shortSeamEdge_ncard_le {G J : Drawing S} {μ w : ℕ} {e : Set S}
    (he : e ∈ shortSeamEdges G J μ w) :
    (closure e ∩ G.V).ncard ≤ w + 2 * μ + 1 := by
  have hn : ¬2 * μ + w + 2 ≤ (closure e ∩ G.V).ncard := fun h => he.2 ⟨he.1, h⟩
  omega

/-- A seam edge with more contacts than the entire boundary has none
of its open points on the boundary, as in VII (4.6), page 225. -/
theorem longSeamEdge_disjoint_bd_of_ncard_lt (hS : IsSurface S) (N : Net S)
    {G J : Drawing S} (hJ : N.IsSeamGraphFor J) {μ w : ℕ}
    (hsmall : (G.V ∩ bd S).ncard < 2 * μ + w + 2) {e : Set S}
    (he : e ∈ longSeamEdges G J μ w) : Disjoint e (bd S) := by
  have : T2Space S := hS.2.1
  have heJ := he.1
  rw [(N.seamGraph_edges_eq hS hJ).1] at heJ
  rcases heJ with ⟨i, rfl⟩ | heB
  · exact N.disjoint_e_int_bd hS i
  · have hcl : closure e ⊆ bd S :=
      closure_minimal (heB.2.1.trans sdiff_subset) (isClosed_bd S)
    have hsub : closure e ∩ G.V ⊆ G.V ∩ bd S := fun x hx => ⟨hx.2, hcl hx.1⟩
    have hcard := Set.ncard_le_ncard hsub (G.finite_V.subset inter_subset_left)
    have hlong := he.2
    have hcontra : False := by omega
    exact hcontra.elim

/-- Every long seam edge is off the cuffs, as in VII (4.6), page 225. -/
theorem longSeamEdge_disjoint_bd (hS : IsSurface S) (N : Net S)
    {G J : Drawing S} (hJ : N.IsSeamGraphFor J) {a b c k : ℕ}
    (hbd : (G.V ∩ bd S).ncard ≤ 2 * k) {e : Set S}
    (he : e ∈ longSeamEdges G J (muModel a b c k) (wMaxModel a b c k)) :
    Disjoint e (bd S) := by
  have : T2Space S := hS.2.1
  have heJ := he.1
  rw [(N.seamGraph_edges_eq hS hJ).1] at heJ
  rcases heJ with ⟨i, rfl⟩ | heB
  · exact N.disjoint_e_int_bd hS i
  · have heSub : e ⊆ bd S := heB.2.1.trans sdiff_subset
    have hcl : closure e ⊆ bd S := closure_minimal heSub (isClosed_bd S)
    have hsub : closure e ∩ G.V ⊆ G.V ∩ bd S := fun x hx => ⟨hx.2, hcl hx.1⟩
    have hcard := Set.ncard_le_ncard hsub (G.finite_V.subset inter_subset_left)
    have hk : 2 * k ≤ muModel a b c k := by
      unfold muModel
      exact Nat.le_add_left _ _
    have hlong := he.2
    have hcontra : False := by omega
    exact hcontra.elim

end GraphMinor.GM07
