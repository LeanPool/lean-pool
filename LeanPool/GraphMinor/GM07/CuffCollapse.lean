/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffBoxBuild
public import LeanPool.GraphMinor.GM07.CuffForest

/-!
# The graph after the collapse

Graph Minors VII, (5.9), pages 235 and 236. The map `ρ` is one to one on the set `A`, and no point
outside `A` goes to a point of `ρ '' A`. If all edges of a graph lie in `A`, then its image is a
drawing whose edges are the images of the edges. An edge whose two ends go to one point becomes a
loop.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- Two lines with the same ends that meet only at the ends form an `O`-arc. -/
theorem isOArc_of_two_lines {L₁ L₂ : Set S} {p q : S} (h₁ : IsLineWithEnds L₁ p q)
  (h₂ : IsLineWithEnds L₂ p q) (hi : L₁ ∩ L₂ = {p, q}) : IsOArc (L₁ ∪ L₂) := by
  obtain ⟨a, ha, rfl, h0, h1⟩ := h₁.exists_arc
  obtain ⟨b, hb, rfl, h0', h1'⟩ := h₂.exists_arc
  refine oArc_of_two_arcs ha hb (h0.trans h0'.symm) (h1.trans h1'.symm) fun s t he => ?_
  have hm : a s ∈ range a ∩ range b := ⟨⟨s, rfl⟩, ⟨t, he.symm⟩⟩
  rw [hi] at hm
  rcases hm with h3 | h3
  · left
    exact ⟨ha.2 (h3.trans h0.symm), hb.2 (he.symm.trans h3 |>.trans h0'.symm)⟩
  · right
    exact ⟨ha.2 (h3.trans h1.symm), hb.2 (he.symm.trans h3 |>.trans h1'.symm)⟩

/-- A line whose image is one to one, except that the two ends go to one point, has image an
`O`-arc. -/
theorem isOArc_image_of_ends {L : Set S} {u v : S} (hL : IsLineWithEnds L u v) {ρ : S → S}
  (hc : Continuous ρ) (hi : ∀ x ∈ L, ∀ y ∈ L, ρ x = ρ y → x = y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y
    = u)) (huv : u ≠ v) (he : ρ u = ρ v) : IsOArc (ρ '' L) := by
  obtain ⟨z, hz, hne⟩ := exists_mem_diff_of_line hL
  have hzu : z ≠ u := fun h => hne (.inl h)
  have hzv : z ≠ v := fun h => hne (.inr h)
  obtain ⟨L₁, L₂, h₁, h₂, hu, hin⟩ := hL.split hz hzu hzv
  have hL₁ : L₁ ⊆ L := hu ▸ subset_union_left
  have hL₂ : L₂ ⊆ L := hu ▸ subset_union_right
  have hv₁ : v ∉ L₁ := fun h => by
    have h3 : v ∈ L₁ ∩ L₂ := ⟨h, h₂.right_mem⟩
    rw [hin] at h3
    exact hzv h3.symm
  have hu₂ : u ∉ L₂ := fun h => by
    have h3 : u ∈ L₁ ∩ L₂ := ⟨h₁.left_mem, h⟩
    rw [hin] at h3
    exact hzu h3.symm
  have hinj₁ : InjOn ρ L₁ := fun a ha b hb hab => by
    rcases hi a (hL₁ ha) b (hL₁ hb) hab with h | ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact h
    · exact absurd hb hv₁
    · exact absurd ha hv₁
  have hinj₂ : InjOn ρ L₂ := fun a ha b hb hab => by
    rcases hi a (hL₂ ha) b (hL₂ hb) hab with h | ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact h
    · exact absurd ha hu₂
    · exact absurd hb hu₂
  have hl₁ := isLineWithEnds_image h₁ hc.continuousOn hinj₁
  have hl₂ := isLineWithEnds_image h₂ hc.continuousOn hinj₂
  rw [← he] at hl₂
  rw [← hu, image_union]
  refine isOArc_of_two_lines hl₁ hl₂.symm (subset_antisymm ?_ ?_)
  · rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    rcases hi b (hL₂ hb) a (hL₁ ha) hab with h | ⟨h3, -⟩ | ⟨-, h4⟩
    · have h5 : a ∈ L₁ ∩ L₂ := ⟨ha, h ▸ hb⟩
      rw [hin] at h5
      refine .inr ?_
      rw [show a = z from h5]
      rfl
    · exact absurd (h3 ▸ hb) hu₂
    · refine .inl ?_
      rw [h4]
  · rintro _ (rfl | rfl)
    · exact ⟨mem_image_of_mem ρ h₁.left_mem, ⟨v, h₂.right_mem, he.symm⟩⟩
    · exact ⟨mem_image_of_mem ρ h₁.right_mem, mem_image_of_mem ρ h₂.left_mem⟩

variable [CompactSpace S]

/-- **The image of a graph.** All edges of `G` lie in `A`. Each point of `A` is the only point with
its image. Then the image of `G` is a drawing, with the images of the edges as edges. -/
theorem exists_collapse_drawing [Nonempty S] {ρ : S → S} (hρ : Continuous ρ) {A : Set S}
  (hA : ∀ x ∈ A, ∀ y, ρ y = ρ x → y = x) (G : Drawing S) (hU : G.U \ G.V ⊆ A) : ∃ G' : Drawing S,
    G'.U = ρ '' G.U ∧ G'.V = ρ '' G.V ∧ G'.E = image ρ '' G.E := by
  classical
  have hcm : IsClosedMap ρ := hρ.isClosedMap
  set F := G.U \ G.V with hF
  have hset : ρ '' G.U \ ρ '' G.V = ρ '' F := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, h1⟩
      exact ⟨x, ⟨hx, fun h2 => h1 (mem_image_of_mem ρ h2)⟩, rfl⟩
    · rintro ⟨x, ⟨hx, h1⟩, rfl⟩
      refine ⟨mem_image_of_mem ρ hx, ?_⟩
      rintro ⟨z, hz, he⟩
      rw [hA x (hU ⟨hx, h1⟩) z he] at hz
      exact h1 hz
  let g : S → S := invFunOn ρ F
  have hgl : ∀ x ∈ F, g (ρ x) = x := fun x hx => hA x (hU hx) _ (invFunOn_eq ⟨x, hx, rfl⟩)
  have hgc : ContinuousOn g (ρ '' F) := by
    refine continuousOn_iff_isClosed.mpr fun C hC => ⟨ρ '' C, hcm C hC, ?_⟩
    ext y
    constructor
    · rintro ⟨hy, hyF⟩
      obtain ⟨x, hx, rfl⟩ := hyF
      rw [mem_preimage, hgl x hx] at hy
      exact ⟨mem_image_of_mem ρ hy, mem_image_of_mem ρ hx⟩
    · rintro ⟨⟨z, hz, he⟩, hyF⟩
      obtain ⟨x, hx, rfl⟩ := hyF
      refine ⟨?_, mem_image_of_mem ρ hx⟩
      rw [mem_preimage, hgl x hx, ← hA x (hU hx) z he]
      exact hz
  have harc : arcComponentsIn (ρ '' F) = image ρ '' arcComponentsIn F
    := arcComponentsIn_image hρ.continuousOn hgc hgl
  have hcl : ∀ e : Set S, closure (ρ '' e) = ρ '' closure e := fun e =>
    (image_closure_subset_closure_image hρ).antisymm' (closure_minimal (image_mono subset_closure)
      (hcm _ isClosed_closure))
  have heF : ∀ e ∈ G.E, e ⊆ F := fun e he => he.2.1
  have hcap : ∀ e ∈ G.E, closure (ρ '' e) ∩ ρ '' G.V = ρ '' (closure e ∩ G.V) := fun e he => by
    rw [hcl]
    refine subset_antisymm ?_ (image_inter_subset _ _ _)
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨v, hv, hvx⟩⟩
    by_cases hxV : x ∈ G.V
    · exact mem_image_of_mem ρ ⟨hx, hxV⟩
    · have hxU : x ∈ G.U := G.closure_subset_U he hx
      have := hA x (hU ⟨hxU, hxV⟩) v hvx
      exact absurd (this ▸ hv) hxV
  have hinj : ∀ e ∈ G.E, ∀ x ∈ closure e, ∀ y ∈ closure e, ρ x = ρ y → x = y ∨ (x ∈ closure e ∩ G.V
    ∧ y ∈ closure e ∩ G.V) := fun e he x hx y hy hxy => by
    by_cases hxV : x ∈ G.V
    · by_cases hyV : y ∈ G.V
      · exact .inr ⟨⟨hx, hxV⟩, hy, hyV⟩
      · exact .inl (hA y (hU ⟨G.closure_subset_U he hy, hyV⟩) x hxy)
    · exact .inl (hA x (hU ⟨G.closure_subset_U he hx, hxV⟩) y hxy.symm).symm
  let Γ : Drawing S :=
    { U := ρ '' G.U
      V := ρ '' G.V
      V_subset_U := image_mono G.V_subset_U
      isClosed_U := hcm _ G.isClosed_U
      finite_V := G.finite_V.image _
      finite_edges := by
        rw [hset, harc]
        exact G.finite_edges.image _
      edge_cond := by
        rw [hset, harc]
        rintro _ ⟨e, he, rfl⟩
        rcases G.edge_cond e he with ⟨u, v, h1, h2, h3⟩ | ⟨u, h2, h3⟩
        · by_cases hρe : ρ u = ρ v
          · refine .inr ⟨ρ u, by rw [hcap e he, h2, image_pair, hρe, pair_eq_singleton], ?_⟩
            rw [hcl]
            refine isOArc_image_of_ends h3 hρ (fun x hx y hy hxy => ?_) h1 hρe
            rcases hinj e he x hx y hy hxy with h4 | ⟨h4, h5⟩
            · exact .inl h4
            · rw [h2] at h4 h5
              rcases h4 with rfl | rfl <;> rcases h5 with rfl | rfl
              · exact .inl rfl
              · exact .inr (.inl ⟨rfl, rfl⟩)
              · exact .inr (.inr ⟨rfl, rfl⟩)
              · exact .inl rfl
          · refine .inl ⟨ρ u, ρ v, hρe, by rw [hcap e he, h2, image_pair], ?_⟩
            rw [hcl]
            refine isLineWithEnds_image h3 hρ.continuousOn fun x hx y hy hxy => ?_
            rcases hinj e he x hx y hy hxy with h4 | ⟨h4, h5⟩
            · exact h4
            · rw [h2] at h4 h5
              rcases h4 with rfl | rfl <;> rcases h5 with rfl | rfl
              · rfl
              · exact absurd hxy hρe
              · exact absurd hxy.symm hρe
              · rfl
        · refine .inr ⟨ρ u, by rw [hcap e he, h2, image_singleton], ?_⟩
          rw [hcl]
          have hii : InjOn ρ (closure e) := fun x hx y hy hxy => by
            rcases hinj e he x hx y hy hxy with h4 | ⟨h4, h5⟩
            · exact h4
            · rw [h2] at h4 h5
              exact h4.trans h5.symm
          have hcomp : IsCompact (closure e) := isClosed_closure.isCompact
          obtain ⟨f', hf', hl⟩ := Surface.exists_inv_of_compactOn hcomp hρ.continuousOn hii
          exact h3.image hρ.continuousOn hf' hl }
  refine ⟨Γ, rfl, rfl, ?_⟩
  change arcComponentsIn (ρ '' G.U \ ρ '' G.V) = _
  rw [hset, harc]
  rfl

end GraphMinor.GM07
