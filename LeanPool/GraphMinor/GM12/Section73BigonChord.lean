/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscArcs
public import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Cutting a radial bigon along a third spoke

For the finite cleanup in XII (7.3), page 261, choose a disc between
two parallel spokes containing as few spokes as possible. If there
is a third spoke in the disc, it is a proper chord. Cutting along it
gives a smaller bigon that omits one original boundary edge. This
file proves that strict decrease from the disc cross-cut theorem.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A third parallel spoke in a bigon cuts off a bigon omitting an
old boundary edge. This is the strict-decrease step in the finite
cleanup of XII (7.3), page 261. -/
theorem exists_bigon_from_third_spoke
    {S : Type*} [TopologicalSpace S] [T2Space S] {H : Drawing S}
    {g h k Q : Set S} {v u : S} (hg : g ∈ H.E) (hh : h ∈ H.E) (hk : k ∈ H.E)
    (hgh : g ≠ h) (hkg : k ≠ g) (hkh : k ≠ h) (hvu : v ≠ u)
    (hcg : closure g ∩ H.V = {v, u}) (hch : closure h ∩ H.V = {v, u})
    (hck : closure k ∩ H.V = {v, u})
    (hQ : IsClosedDisc Q) (hbd : discBd Q = closure g ∪ closure h)
    (hkQ : closure k ⊆ Q) :
    ∃ P : Set S, IsClosedDisc P ∧ P ⊆ Q ∧
      (discBd P = closure g ∪ closure k ∨ discBd P = closure h ∪ closure k) ∧
      (¬ g ⊆ P ∨ ¬ h ⊆ P) := by
  have hLg := isLine_closure hg hvu hcg
  have hLh := isLine_closure hh hvu hch
  have hLk := isLine_closure hk hvu hck
  have hmeet : closure g ∩ closure h ⊆ {v, u} := fun x hx =>
    hcg.subset ⟨hx.1, closure_inter_subset_V hg hh hgh hx⟩
  have hkbd : closure k ∩ discBd Q = {v, u} := by
    apply Subset.antisymm
    · rintro x ⟨hxk, hxQ⟩
      rw [hbd] at hxQ
      rcases hxQ with hxg | hxh
      · exact hck.subset ⟨hxk, closure_inter_subset_V hk hg hkg ⟨hxk, hxg⟩⟩
      · exact hck.subset ⟨hxk, closure_inter_subset_V hk hh hkh ⟨hxk, hxh⟩⟩
    · intro x hx
      exact ⟨(hck.superset hx).1, hbd ▸ Or.inl (hcg.superset hx).1⟩
  obtain ⟨A₁, A₂, P₁, P₂, _, hcomp, hP₁, hP₂, hUnion, hInter, hbd₁, hbd₂, _⟩ :=
    disc_iArc Q (closure k) v u hQ hkQ hvu hLk hkbd
  have hparts : componentsIn (discBd Q \ {v, u}) =
      {closure g \ {v, u}, closure h \ {v, u}} := by
    rw [hbd, union_sdiff_distrib]
    apply componentsIn_union_eq_pair
      (isPathConnected_sdiff_pair hLg).isConnected.isPreconnected
      (isPathConnected_sdiff_pair hLh).isConnected.isPreconnected
      (isPathConnected_sdiff_pair hLg).nonempty
      (isPathConnected_sdiff_pair hLh).nonempty
    · rw [closure_sdiff_pair hLg]
      exact disjoint_left.mpr fun x hxg hxh => hxh.2 (hmeet ⟨hxg, hxh.1⟩)
    · rw [closure_sdiff_pair hLh]
      exact disjoint_left.mpr fun x hxg hxh => hxg.2 (hmeet ⟨hxg.1, hxh⟩)
  have hends : ({v, u} : Set S) ⊆ closure k := fun x hx => (hck.superset hx).1
  have hrestore : ∀ L : Set S, (L \ {v, u}) ∪ closure k = L ∪ closure k := by
    intro L
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl hx.1
      · exact Or.inr hx
    · rintro (hx | hx)
      · by_cases hxend : x ∈ ({v, u} : Set S)
        · exact Or.inr (hends hxend)
        · exact Or.inl ⟨hx, hxend⟩
      · exact Or.inr hx
  have hA₁ : A₁ = closure g \ {v, u} ∨ A₁ = closure h \ {v, u} := by
    have hmem := hcomp.superset (Or.inl rfl)
    rw [hparts] at hmem
    exact hmem
  have hA₂ : A₂ = closure g \ {v, u} ∨ A₂ = closure h \ {v, u} := by
    have hmem := hcomp.superset (Or.inr rfl)
    rw [hparts] at hmem
    exact hmem
  refine ⟨P₁, hP₁, (fun x hx => hUnion ▸ Or.inl hx), ?_, ?_⟩
  · rcases hA₁ with hA₁ | hA₁
    · exact Or.inl (hbd₁.trans (hA₁ ▸ hrestore (closure g)))
    · exact Or.inr (hbd₁.trans (hA₁ ▸ hrestore (closure h)))
  · have hmiss : ∀ a ∈ H.E, a ≠ k → A₂ = closure a \ {v, u} → ¬ a ⊆ P₁ := by
      intro a ha hak hAa haP₁
      obtain ⟨x, hxa⟩ := ha.1
      have hxV : x ∉ H.V := (ha.2.1 hxa).2
      have hxend : x ∉ ({v, u} : Set S) := fun hx => hxV (hck.superset hx).2
      have hxA₂ : x ∈ A₂ := hAa.symm ▸ ⟨subset_closure hxa, hxend⟩
      have hxP₂ : x ∈ P₂ := Surface.discBd_subset P₂ (hbd₂ ▸ Or.inl hxA₂)
      have hxk : x ∈ closure k := hInter.subset ⟨haP₁ hxa, hxP₂⟩
      exact hxV (closure_inter_subset_V ha hk hak ⟨subset_closure hxa, hxk⟩)
    rcases hA₂ with hA₂ | hA₂
    · exact Or.inl (hmiss g hg hkg.symm hA₂)
    · exact Or.inr (hmiss h hh hkh.symm hA₂)

end GraphMinor.GM12
