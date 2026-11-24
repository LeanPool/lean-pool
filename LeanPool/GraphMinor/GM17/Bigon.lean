/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CapSide

/-!
# Pushing a curve off a node

We finish the proof of `CutNormalOArcPaintingStatement`, the surface part of (5.4) of Graph Minors
XVII (page 173). A normal `O`-arc `F` may pass through
nodes. The paper diverts `F` around them. We do this one node `n` at a time. We paste discs on all
cuffs (`exists_cap_discs`) and cut the closed surface along
`F`. All cells at `n`, and the disc on the cuff of `n`, come to `n` from the same side of `F`,
because a cell comes to a point from one side only and the cells
overlap the disc along the cuff. So the other lift of `n` is free (`exists_free_lift`). A thin wedge
at this lift (`exists_wedge`) is a disc `G` in the surface
that has a line of `F` around `n` on its boundary and meets the paint only at `n` (`exists_bigon`).
Swapping that line for the other side of `G` gives a curve
with one node fewer. A disc bounded by the new curve gives a disc bounded by `F` with the same
cells, by adding or removing `G` (`flip_disc`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]

/-- Pasting discs on all the cuffs of a surface. -/
theorem exists_cap_discs (n : ℕ) : ∀ (S : Type) [TopologicalSpace S] [ConnectedSpace S], IsSurface
  S → (cuffs S).ncard = n →
    ∃ (T : Type) (_ : TopologicalSpace T) (j : S → T) (cap : Set S → Set T), IsClosedSurface T
      ∧ ConnectedSpace T ∧ IsClosedEmbedding j ∧
      (∀ C ∈ cuffs S, IsClosedDisc (cap C) ∧ discBd (cap C) = j '' C ∧ range j ∩ cap C = j '' C)
        ∧ range j ∪ ⋃ C ∈ cuffs S, cap C = univ := by
  classical
  induction n with
  | zero =>
    intro S _ _ hS hn
    have hf := (cuff_statement.{0} S hS).2.1
    have he : cuffs S = ∅ := (Set.ncard_eq_zero hf).mp hn
    refine ⟨S, _, id, fun _ => ∅, ⟨hS.1, hS.2.1, fun x => ?_⟩, ‹_›, IsClosedEmbedding.id, ?_, ?_⟩
    · by_contra hcon
      have : connectedComponentIn (bd S) x ∈ cuffs S := ⟨x, hcon, rfl⟩
      rw [he] at this
      exact this
    · simp [he]
    · simp
  | succ n ih =>
    intro S _ _ hS hn
    have hf := (cuff_statement.{0} S hS).2.1
    have hne : (cuffs S).Nonempty := (Set.ncard_pos hf).mp (by omega)
    obtain ⟨C₀, hC₀⟩ := hne
    obtain ⟨S', tS', ι, Δ, hS', hι, hΔ, hcov, hmeet, hΔb, hbd⟩ := paste_disc.{0} S C₀ hS hC₀
    obtain ⟨a, b, c, ⟨e⟩⟩ := classification.{0} S hS ‹_›
    obtain ⟨-, ⟨e'⟩⟩ := paste_model hS hC₀ hS' hι hΔ hcov hmeet hΔb e
    have hconn : ConnectedSpace S' := by
      have := (isSurface_model a b (c - 1)).2
      exact e'.symm.surjective.connectedSpace e'.symm.continuous
    have hOS := (cuff_statement.{0} S hS).2.2
    have hd : ∀ C ∈ cuffs S, C ≠ C₀ → ι '' C ∈ cuffs S' := fun C hC hne =>
      image_cuff hS hC₀ hι hbd hC (cuffs_disjoint hC₀ hC hne.symm) (hOS C hC) hS'
    have hcuffs : cuffs S' = (fun C => ι '' C) '' (cuffs S \ {C₀}) := by
      ext P
      constructor
      · intro hP
        obtain ⟨x, hx, rfl⟩ := id hP
        have hx' := hx
        rw [hbd] at hx'
        obtain ⟨y, ⟨hy, hyC⟩, rfl⟩ := hx'
        have hC : connectedComponentIn (bd S) y ∈ cuffs S := ⟨y, hy, rfl⟩
        have hyy : y ∈ connectedComponentIn (bd S) y := mem_connectedComponentIn hy
        have hne : connectedComponentIn (bd S) y ≠ C₀ := fun h => hyC (h ▸ hyy)
        refine ⟨_, ⟨hC, hne⟩, ?_⟩
        exact cuffs_disjoint_eq (hd _ hC hne) hP (mem_image_of_mem _ hyy)
          (mem_connectedComponentIn hx)
      · rintro ⟨C, ⟨hC, hne⟩, rfl⟩
        exact hd C hC hne
    have hinj : InjOn (fun C => ι '' C) (cuffs S \ {C₀}) := fun C _ C' _ h =>
      (image_eq_image hι.injective).mp h
    have hcard : (cuffs S').ncard = n := by
      rw [hcuffs, hinj.ncard_image, Set.ncard_sdiff_singleton_of_mem hC₀, hn]
      rfl
    obtain ⟨T, tT, j, cap, hT, hTc, hj, hcap, hcov'⟩ := ih S' hS' hcard
    refine ⟨T, tT, j ∘ ι, fun C => if C = C₀ then j '' Δ else cap (ι '' C), hT, hTc, hj.comp hι,
      ?_, ?_⟩
    · intro C hC
      by_cases hCe : C = C₀
      · subst hCe
        simp only [ite_true]
        refine ⟨image_emb_disc hj.isEmbedding hΔ, ?_, ?_⟩
        · rw [discBd_image hj.isEmbedding, hΔb, image_comp]
        · rw [range_comp, ← image_inter hj.injective, inter_comm (range ι) Δ, inter_comm, hmeet,
            image_comp]
      · change IsClosedDisc (if C = C₀ then j '' Δ else cap (ι '' C)) ∧ discBd (if C
          = C₀ then j '' Δ else cap (ι '' C)) = (j ∘ ι) '' C ∧
          range (j ∘ ι) ∩ (if C = C₀ then j '' Δ else cap (ι '' C)) = (j ∘ ι) '' C
        rw [ite_eq_right hCe]
        obtain ⟨h1, h2, h3⟩ := hcap _ (hd C hC hCe)
        refine ⟨h1, by rw [h2, image_comp], ?_⟩
        apply subset_antisymm
        · rintro y ⟨⟨z, rfl⟩, hy⟩
          have h4 : (j ∘ ι) z ∈ j '' (ι '' C) := h3 ▸ ⟨⟨_, rfl⟩, hy⟩
          rw [image_comp]
          exact h4
        · rw [image_comp]
          rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨⟨z, rfl⟩, discBd_subset _ (h2 ▸ ⟨ι z, mem_image_of_mem _ hz, rfl⟩)⟩
    · rw [eq_univ_iff_forall]
      intro y
      rcases (hcov' ▸ mem_univ y : y ∈ range j ∪ ⋃ C ∈ cuffs S', cap C) with ⟨z, rfl⟩ | h1
      · rcases (hcov ▸ mem_univ z : z ∈ range ι ∪ Δ) with ⟨w, rfl⟩ | h1
        · exact .inl ⟨w, rfl⟩
        · refine .inr (mem_biUnion hC₀ ?_)
          simp only [ite_true]
          exact mem_image_of_mem _ h1
      · obtain ⟨C, hC, hy⟩ := mem_iUnion₂.mp h1
        rw [hcuffs] at hC
        obtain ⟨C', ⟨hC', hne⟩, rfl⟩ := hC
        refine .inr (mem_biUnion hC' ?_)
        show y ∈ if C' = C₀ then j '' Δ else cap (ι '' C')
        rw [ite_eq_right (show C' ≠ C₀ from hne)]
        exact hy

/-- Swapping one side of a disc in the boundary of another disc. -/
theorem flip_disc [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {G Δ' L₀ L₁ R : Set S} {u v : S}
  (hG : IsClosedDisc G) (_hL₀ : IsLineWithEnds L₀ u v)
    (hL₁ : IsLineWithEnds L₁ u v) (_hR : IsLineWithEnds R u v) (hbG : discBd G = L₀ ∪ L₁)
      (h01 : L₀ ∩ L₁ = {u, v}) (h0R : L₀ ∩ R = {u, v}) (h1R : L₁ ∩ R = {u, v})
    (hGR : G ∩ R = {u, v}) (hΔ' : IsClosedDisc Δ') (hbΔ : discBd Δ' = L₁ ∪ R) :
    ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = L₀ ∪ R ∧ ∀ c, Disjoint c G → (c ⊆ Δ ↔ c ⊆ Δ') := by
  have hset : (discBd G ∪ discBd Δ') \ (L₁ \ {u, v}) = L₀ ∪ R := by
    rw [hbG, hbΔ]
    ext x
    constructor
    · rintro ⟨(h | h) | (h | h), hn⟩
      · exact .inl h
      · have : x ∈ ({u, v} : Set S) := by
          by_contra hc
          exact hn ⟨h, hc⟩
        exact .inl (h01 ▸ this |>.1)
      · have : x ∈ ({u, v} : Set S) := by
          by_contra hc
          exact hn ⟨h, hc⟩
        exact .inl (h01 ▸ this |>.1)
      · exact .inr h
    · rintro (h | h)
      · exact ⟨.inl (.inl h), fun hn => hn.2 (h01 ▸ ⟨h, hn.1⟩)⟩
      · exact ⟨.inr (.inr h), fun hn => hn.2 (h1R ▸ ⟨hn.1, h⟩)⟩
  have hL₁G : L₁ ⊆ G := fun x hx => discBd_subset G (hbG ▸ Or.inr hx)
  have hL₁Δ : L₁ ⊆ Δ' := fun x hx => discBd_subset Δ' (hbΔ ▸ Or.inl hx)
  have hconn : IsPreconnected (G \ L₁) := by
    refine hG.isPreconnected_discInt.subset_closure (fun x hx => ⟨hx.1,
      fun h => hx.2 (hbG ▸ Or.inr h)⟩) ?_
    exact sdiff_subset.trans hG.subset_closure_discInt
  have hdj : Disjoint (G \ L₁) (discBd Δ') := by
    rw [hbΔ, disjoint_left]
    rintro x ⟨hx, hx'⟩ (h | h)
    · exact hx' h
    · exact hx' (h1R.symm ▸ hGR ▸ ⟨hx, h⟩ : x ∈ L₁ ∩ R).1
  rcases hΔ'.side hman hconn hdj with h | h
  · have hsub : G ⊆ Δ' := fun x hx => by
      by_cases hL : x ∈ L₁
      · exact hL₁Δ hL
      · exact (h ⟨hx, hL⟩).1
    have hmeet : discBd G ∩ discBd Δ' = L₁ := by
      rw [hbG, hbΔ]
      ext x
      constructor
      · rintro ⟨h1 | h1, h2 | h2⟩
        · exact h2
        · exact (h01 ▸ (h0R ▸ ⟨h1, h2⟩ : x ∈ ({u, v} : Set S)) : x ∈ L₀ ∩ L₁).2
        · exact h1
        · exact h1
      · exact fun hx => ⟨.inr hx, .inl hx⟩
    obtain ⟨h1, h2, -⟩ := disc_difference G Δ' L₁ u v hG hΔ' hsub hL₁ hmeet
    refine ⟨_, h1, h2.trans hset, fun c hc => ⟨fun hs x hx => ?_, fun hs => ?_⟩⟩
    · exact closure_minimal sdiff_subset hΔ'.isClosed (hs hx)
    · exact fun x hx => subset_closure ⟨hs hx, disjoint_left.mp hc hx⟩
  · have hmeet : G ∩ Δ' = L₁ := by
      apply subset_antisymm
      · rintro x ⟨hx, hx'⟩
        by_contra hL
        exact disjoint_left.mp h ⟨hx, hL⟩ hx'
      · exact subset_inter hL₁G hL₁Δ
    obtain ⟨h1, h2⟩ := disc_union G Δ' L₁ u v hG hΔ' hL₁ hmeet (hbG ▸ subset_union_right)
      (hbΔ ▸ subset_union_left)
    refine ⟨_, h1, h2.trans hset, fun c hc => ⟨fun hs x hx => ?_,
      fun hs => hs.trans subset_union_right⟩⟩
    exact (hs hx).resolve_left (disjoint_left.mp hc hx)

end GraphMinor.GM17
