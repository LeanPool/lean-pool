/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.GM06.Section2Dual
import LeanPool.GraphMinor.GM11.Section6

/-!
# Bounding a division count by either boundary arc

For the VI (3.6) reduction in XII (3.2), pages 247--248,
each division part counted between two boundary points meets both
closed boundary arcs. A part containing an endpoint meets each arc
there. A crossing part has points on opposite sides of the two
endpoints. Choosing one point on an arc from each counted part is
injective, since division parts are disjoint. Thus the division count
is at most the number of prescribed vertices on either arc.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM06 GM11

private theorem crossing_pair_meets_boundary_arc
    {S : Type*} [TopologicalSpace S] {A B : Set S} {x y u v : S}
    (hC : IsOArc (A ∪ B)) (hA : IsLineWithEnds A x y) (hB : IsLineWithEnds B x y)
    (hc : CrossesOn (A ∪ B) u v x y) : u ∈ A ∨ v ∈ A := by
  by_contra hn
  push Not at hn
  have hend : ({x, y} : Set S) ⊆ A := by
    obtain ⟨f, hf0, hf1⟩ := hA
    intro z hz
    rcases hz with rfl | rfl
    · exact hf0 ▸ (f 0).property
    · exact hf1 ▸ (f 1).property
  rcases GM06.CrossesOn.comm hC hc with ⟨_, hu, _, hv, _, _, _, _, _, _, hcomp⟩
  have huB : u ∈ B := hu.resolve_left hn.1
  have hvB : v ∈ B := hv.resolve_left hn.2
  have huI : u ∈ B \ {x, y} := ⟨huB, fun h => hn.1 (hend h)⟩
  have hvI : v ∈ B \ {x, y} := ⟨hvB, fun h => hn.2 (hend h)⟩
  have hsub : B \ {x, y} ⊆ (A ∪ B) \ {x, y} := fun z hz => ⟨Or.inr hz.1, hz.2⟩
  have hvComp := (GM11.IsLineWithEnds.isPreconnected_sdiff_pair hB).subset_connectedComponentIn
    huI hsub hvI
  exact hcomp (connectedComponentIn_eq hvComp)

/-- The VI division count between the ends of two boundary arcs is
bounded by the vertex count of either arc, as needed in XII (3.2). -/
theorem divisionCount_le_boundary_arc_count
    {S : Type*} [TopologicalSpace S] {V A B : Set S} {x y : S} {Δ : Set (Set S)}
    (hV : V.Finite) (hΔ : IsDivision Δ) (hΔV : divisionUnion Δ ⊆ V)
    (hC : IsOArc (A ∪ B)) (hA : IsLineWithEnds A x y) (hB : IsLineWithEnds B x y) :
    divisionCount (A ∪ B) Δ x y ≤ (V ∩ A).ncard := by
  classical
  let Cnt : Set (Set S) := {δ ∈ Δ | (δ ∩ {x, y}).Nonempty ∨
    ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn (A ∪ B) u v x y}
  have hend : ({x, y} : Set S) ⊆ A := by
    obtain ⟨f, hf0, hf1⟩ := hA
    intro z hz
    rcases hz with rfl | rfl
    · exact hf0 ▸ (f 0).property
    · exact hf1 ▸ (f 1).property
  have hhit : ∀ δ ∈ Cnt, ∃ v, v ∈ δ ∧ v ∈ A := by
    rintro δ ⟨_, hδ⟩
    rcases hδ with ⟨v, hvδ, hvend⟩ | ⟨u, huδ, v, hvδ, hcross⟩
    · exact ⟨v, hvδ, hend hvend⟩
    · rcases crossing_pair_meets_boundary_arc hC hA hB hcross with huA | hvA
      · exact ⟨u, huδ, huA⟩
      · exact ⟨v, hvδ, hvA⟩
  choose f hfδ hfA using hhit
  let g : Set S → S := fun δ => if h : δ ∈ Cnt then f δ h else x
  have hmaps : MapsTo g Cnt (V ∩ A) := by
    intro δ hδ
    simp only [g, hδ, ↓reduceDIte]
    exact ⟨hΔV (mem_sUnion_of_mem (hfδ δ hδ) hδ.1), hfA δ hδ⟩
  have hinj : InjOn g Cnt := by
    intro δ₁ hδ₁ δ₂ hδ₂ heq
    simp only [g, hδ₁, hδ₂, ↓reduceDIte] at heq
    by_contra hne
    exact Set.disjoint_left.mp (hΔ.2.2 hδ₁.1 hδ₂.1 hne) (hfδ δ₁ hδ₁)
      (heq.symm ▸ hfδ δ₂ hδ₂)
  exact Set.ncard_le_ncard_of_injOn g hmaps hinj (hV.inter_of_left A)

end GraphMinor.GM12
