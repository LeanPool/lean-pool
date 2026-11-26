/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM11.Walks

/-!
# A path crossing a zone has a boundary vertex

At the first vertex outside the open zone, the entering edge lies
in the zone and its closure contains that vertex. Hence the vertex
lies on the boundary. This supplies the intersection with the annulus
in XVI (8.1), Claim (14).
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- A walk from inside a zone to outside it contains a boundary vertex. -/
theorem graphWalk_meets_zone_boundary {H : Drawing S}
    {d : Set S → Set S → ℕ} {γ : ℕ} {z Λ : Set S}
    (hZone : IsLambdaZoneAround H d γ z Λ) {a b : S}
    (W : GraphWalk H.toGraph a b) (ha : a ∈ Λ) (hb : b ∉ Λ) :
    ∃ v ∈ W.support, v ∈ H.V ∩ subBd Λ := by
  induction W with
  | nil _ => exact False.elim (hb ha)
  | @cons a c b e hl W ih =>
    by_cases hc : c ∈ Λ
    · obtain ⟨v, hv, hvBd⟩ := ih hc hb
      exact ⟨v, List.mem_cons_of_mem _ hv, hvBd⟩
    · have heIn : e ⊆ Λ := by
        rcases edge_subset_or_subset_compl_of_zone hZone hl.1 with he | he
        · exact he
        · have hcl := closure_minimal he (isClosed_univ.sdiff hZone.isOpenDisc.1)
          have haCl : a ∈ closure e := (hl.2.2.2.symm ▸ (show a ∈ ({a, c} : Set S) from Or.inl
            rfl)).1
          exact False.elim ((hcl haCl).2 ha)
      have hcCl : c ∈ closure e := (hl.2.2.2.symm ▸ (show c ∈ ({a, c} : Set S) from Or.inr rfl)).1
      refine ⟨c, List.mem_cons_of_mem _ W.start_mem_support, hl.2.2.1, ?_⟩
      exact ⟨closure_mono heIn hcCl, subset_closure ⟨mem_univ _, hc⟩⟩

/-- A path subdrawing from inside a zone to outside it meets the
boundary at a vertex of that path. -/
theorem drawingPath_meets_zone_boundary {H P : Drawing S}
    {d : Set S → Set S → ℕ} {γ : ℕ} {z Λ : Set S}
    (hZone : IsLambdaZoneAround H d γ z Λ) {a b : S}
    (hP : P.IsSubdrawing H) (hPath : P.IsPathBetween a b)
    (ha : a ∈ Λ) (hb : b ∉ Λ) : (P.V ∩ (H.V ∩ subBd Λ)).Nonempty := by
  obtain ⟨W, _, hV, _⟩ := hPath
  obtain ⟨W', hs, _⟩ := hP.exists_walk_up W
  obtain ⟨v, hv, hvBd⟩ := graphWalk_meets_zone_boundary hZone W' ha hb
  exact ⟨v, hV.symm ▸ (hs ▸ hv), hvBd⟩

end GraphMinor.GM16
