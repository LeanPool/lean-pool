/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6HairFamily
public import LeanPool.GraphMinor.GM16.Section6CliquePaths
import LeanPool.GraphMinor.GM16.Section5Proof
import LeanPool.GraphMinor.GM16.Section5Degree
import LeanPool.GraphMinor.GM16.Section6Linkages
import LeanPool.GraphMinor.GM16.Section6Animals

import LeanPool.GraphMinor.GM12.Bridge

/-!
# Bounding the active hairs in XVI (6.3)

Apply (5.3) to the marked vertices in components of the truncated hair
union containing two marked vertices. Its path alternative gives the
controlled clique minor by (5.2). In its fan alternative, the centre is
outside the old drawing because its old vertices have at most one
neighbor. Shortening the fan gives the extra horn. If both desired
outcomes fail, at most `(μ - 1) * τ'` hairs are active.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w

/-- Graph Minors XVI, proof of (6.3), Claims (1) and (2) and their
application of (5.3), page 60. The only exclusions are the two desired
outcomes of (6.3), not intermediate claims of its proof. -/
theorem theorem_6_3_active_bound
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {α : Type u} {β : Type v} {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {p τ τ' χ δ θ_star θ_span θ σ ψ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {X : Set α} {Y : Set S}
    (hAnim : IsAnimal G T_star θ_star H η θ_span T d X Y χ δ θ σ)
    (F : HairFamily G H η d X Y θ)
    (hθ : cliquePathThreshold.{u, v, w} hS hConn p ≤ θ)
    (hψ : 1 ≤ ψ) (hψθ : ψ ≤ θ) (hτσ : τ ≤ σ) (hττ' : τ ≤ τ') (hτ' : 2 ≤ τ')
    (hNoClique : ¬ ControlsMinor G (completeGraph p) T_star)
    (hNoHorn : ¬ HasHairlessAnimal S G T_star θ_star (χ + 1) ψ τ) :
    F.active.ncard ≤ (p * (p - 1) / 2 - 1) * τ' := by
  classical
  have hSaved := hAnim
  obtain ⟨_, horder, hSpan, hMet, _, _, hYsub, _, _, _, hsep⟩ := hAnim
  let μ := p * (p - 1) / 2
  let A := activeMarkedVertices F.unionGraph (η.vMap '' Y)
  have hG0V := hSpan.isControlling.isTangle_star.finite_V.subset F.union_le.vertexSet_mono
  have hG0E := hSpan.isControlling.isTangle_star.finite_E.subset F.union_le.edgeSet_mono
  have hAold : A ⊆ V(η.imageGraph) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx.1
    exact η.bijOn_v.mapsTo (hYsub hy)
  by_contra hnot
  have hlarge : τ' * (μ - 1) < A.ncard := by
    have hc := F.active_card_eq hYsub
    change F.active.ncard = A.ncard at hc
    rw [← hc]
    simpa only [Nat.mul_comm] using Nat.lt_of_not_ge hnot
  rcases theorem_5_3_proof F.unionGraph A μ τ' hG0V hG0E
      (activeMarkedVertices_subset_vertexSet _ _) (activeMarkedVertices_component_hyp _ _) hlarge
        with
    ⟨P, a, b, hPP, hP⟩ | ⟨x, P, b, hxG0, hinter, hP⟩
  · apply hNoClique
    apply (cliquePathThreshold_spec hS hConn p).2 G F.unionGraph θ_star θ_span
      T_star H η T d Y P a b hSpan hMet (hθ.trans horder) hYsub
      (fun y hy z hz hyz => hθ.trans (hsep y hy z hz hyz)) F.union_le
      F.union_edges_disjoint_old F.union_inter_old.subset
    · intro i
      obtain ⟨ha, hb, hab, hp, _⟩ := hP i
      exact ⟨hAold ha, hAold hb, hab, hp⟩
    · exact hPP
  · have hxH : x ∉ V(η.imageGraph) := by
      intro hxH
      have hleaf := F.union_old_neighbors_subsingleton hYsub hxH
      have hbound : {z | F.unionGraph.Adj x z}.ncard ≤ 1 :=
        (ncard_le_one hleaf.finite).mpr (fun _ ha _ hb => hleaf ha hb)
      have hfan := fan_card_le_neighbors_ncard hG0V
        (fun i => ⟨(hP i).2.1, (hP i).2.2.1⟩)
        (fun i j hij => (hinter i j hij).1.subset)
      omega
    obtain ⟨R, ends, hHorn⟩ := horn_of_fan_in_subgraph F.union_le hxG0 hxH
      F.union_inter_old.subset hYsub
      (fun y hy z hz hyz => hψθ.trans (hsep y hy z hz hyz))
      (fun i => ⟨hAold (hP i).1, (hP i).2.2.1⟩) hinter
    have hxX : x ∉ X := by
      intro hxX
      exact (Set.disjoint_left.mp F.union_avoids_horns) hxX hxG0
    apply hNoHorn
    apply hSaved.add_horn hψ hψθ hτσ hxX
    exact ⟨_, _, hHorn.mono le_rfl hττ'⟩

end GraphMinor.GM16
