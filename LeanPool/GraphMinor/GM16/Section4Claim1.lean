/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallRows
public import LeanPool.GraphMinor.GM10.Defs
import LeanPool.GraphMinor.GM16.Section4WallRowImages

/-!
# Claim (1) in the proof of XVI (4.2)

The paper defines the wall tangle by placing a complete horizontal
row on the large side. Contracting the horizontal pairs induces a
tangle from the smaller grid. Its small side contains no complete
wall row. Every separation of order less than `θ` has an uncut row,
so the two definitions of the tangle agree.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph Hypergraph GM10

/-- The set `𝒯₁` in XVI (4.2), page 53: the separations of order less
than `θ` whose large side includes a horizontal row of the wall. -/
def sphereWallTangle (θ : ℕ) :
    Set (Hypergraph (Fin (2 * θ + 1) × Fin θ) (Sym2 (Fin (2 * θ + 1) × Fin θ)) ×
      Hypergraph (Fin (2 * θ + 1) × Fin θ) (Sym2 (Fin (2 * θ + 1) × Fin θ))) :=
  {p | (Hypergraph.ofGraph (sphereWallGraph θ) (Set.toFinite _) (Set.toFinite _)).IsSeparation p.1
    p.2 ∧
    separationOrder p.1 p.2 < θ ∧ ∃ j : Fin θ, E(sphereWallRow θ j) ⊆ p.2.edgeSet}

/-- Graph Minors XVI, (4.2), Claim (1), page 53: `𝒯₁` is a tangle
of order `θ` in `N₁`. The proof follows the paper's contraction to the
smaller grid, X (7.3), and induction of tangles by X (6.1). -/
theorem theorem_4_2_claim_1 {θ : ℕ} (hθ : 2 ≤ θ) :
    IsTangle (Hypergraph.ofGraph (sphereWallGraph θ) (Set.toFinite _) (Set.toFinite _)) θ
      (sphereWallTangle θ) := by
  obtain ⟨N₂, hV₂, hE₂, _, hImage, _, hT₁⟩ := exists_induced_wall_tangle θ hθ
  have hEq : sphereWallTangle θ = inducedTangle
      (Hypergraph.ofGraph (sphereWallGraph θ) (Set.toFinite _) (Set.toFinite _))
      (Hypergraph.ofGraph N₂ hV₂ hE₂)
      (imageHypergraphTangle (sphereWallPair θ) (sphereWallGridEdge θ) (gridTangle θ)) θ := by
    ext ⟨A, B⟩
    constructor
    · rintro ⟨hSep, hOrd, j, hRow⟩
      rcases hT₁.axiom1 hSep hOrd with hm | hm
      · exact hm
      · exact (induced_wall_tangle_no_small_row hθ hV₂ hE₂ hImage hm j hRow).elim
    · intro hm
      have hSep := hT₁.isSeparation hm
      have hOrd := hT₁.order_lt hm
      refine ⟨hSep, hOrd, ?_⟩
      obtain ⟨j, hRow⟩ := sphereWall_separation_has_row hSep hOrd
      refine ⟨j, ?_⟩
      rcases hRow with hA | hB
      · exact (induced_wall_tangle_no_small_row hθ hV₂ hE₂ hImage hm j hA).elim
      · exact hB
  rw [hEq]
  exact hT₁

end GraphMinor.GM16
