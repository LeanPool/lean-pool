/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72PushAway

/-!
# Pushing across the two mixed corner caps

For the vertex diversion in XII (7.2), move the boundary circle away
from each of the two local branches of the other circle. Push it off
the two mixed caps in succession, fixing the old drawing and fixing
the first cap during the second push. Inverting this homeomorphism
then moves the local branches away from the boundary circle.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- Push a closed set off a boundary cap while fixing the old drawing.
The set can meet the fixed boundary line at its first end only. -/
theorem push_cap_fixing (hS : IsClosedSurface S)
    {D A G F : Set S} {v a : S} (hD : IsClosedDisc D)
    (hA : IsLineWithEnds A v a) (ha : a ≠ v) (hAb : A ⊆ discBd D)
    (hG : IsClosed G) (hvG : v ∈ G) (haG : a ∈ G) (hGD : G ∩ D ⊆ A)
    (hF : IsClosed F) (hFA : F ∩ A ⊆ {v}) :
    ∃ h : S ≃ₜ S, (∀ x ∈ G, h x = x) ∧ (h '' F) ∩ D ⊆ {v} := by
  have : CompactSpace S := hS.1
  have haA : a ∈ A := by obtain ⟨e, _, h1⟩ := hA; exact h1 ▸ (e 1).2
  have hvA : v ∈ A := by obtain ⟨e, h0, _⟩ := hA; exact h0 ▸ (e 0).2
  obtain ⟨h, hfix, hpush⟩ := push_disc (fun x => hS.2.2 x) hD hA
    (hAb.trans (Surface.discBd_subset D)) (Or.inl ⟨hAb, hGD⟩) (hAb hvA) (hAb haA)
    hG hvG haG hF (fun _ hx => Or.inl (mem_singleton_iff.mp (hFA hx)))
  refine ⟨h, hfix, ?_⟩
  rintro x ⟨hxF, hxD⟩
  rcases mem_insert_iff.mp (hpush ⟨hxF, hxD⟩) with hxv | hxa
  · exact hxv
  · obtain ⟨y, hy, hyx⟩ := hxF
    have hya : y = a := h.injective ((hyx.trans (mem_singleton_iff.mp hxa)).trans (hfix a haG).symm)
    exact (ha (mem_singleton_iff.mp (hFA ⟨hya ▸ hy, haA⟩))).elim

/-- Push a boundary circle off two mixed caps, keeping the first cap fixed
in the second push. This is the local diversion at the vertex in XII (7.2),
page 260. -/
theorem push_two_caps_fixing (hS : IsClosedSurface S)
    {D₀ D₁ A₀ A₁ G F C O : Set S} {v a₀ a₁ : S}
    (hD₀ : IsClosedDisc D₀) (hD₁ : IsClosedDisc D₁)
    (hA₀ : IsLineWithEnds A₀ v a₀) (hA₁ : IsLineWithEnds A₁ v a₁)
    (ha₀ : a₀ ≠ v) (ha₁ : a₁ ≠ v)
    (hAb₀ : A₀ ⊆ discBd D₀) (hAb₁ : A₁ ⊆ discBd D₁)
    (hG : IsClosed G) (hvG : v ∈ G) (hA₀G : A₀ ⊆ G) (hA₁G : A₁ ⊆ G)
    (hGD₀ : G ∩ D₀ ⊆ A₀) (hGD₁ : G ∩ D₁ ⊆ A₁)
    (hDD : D₀ ∩ D₁ ⊆ G) (hF : IsClosed F) (hFG : F ∩ G ⊆ {v})
    (hcover : C ∩ O ⊆ D₀ ∪ D₁) :
    ∃ h : S ≃ₜ S, (∀ x ∈ G, h x = x) ∧ ((h '' F) ∩ C) ∩ O ⊆ {v} := by
  have ha₀G : a₀ ∈ G := by
    obtain ⟨e, _, h1⟩ := hA₀
    exact hA₀G (h1 ▸ (e 1).2)
  have ha₁G : a₁ ∈ G := by
    obtain ⟨e, _, h1⟩ := hA₁
    exact hA₁G (h1 ▸ (e 1).2)
  obtain ⟨h₀, hfix₀, hpush₀⟩ := push_cap_fixing hS hD₀ hA₀ ha₀ hAb₀ hG hvG ha₀G hGD₀ hF
    (fun x hx => hFG ⟨hx.1, hA₀G hx.2⟩)
  have hG' : IsClosed (G ∪ D₀) := hG.union hD₀.isClosed
  have hGD' : (G ∪ D₀) ∩ D₁ ⊆ A₁ := by
    rintro x ⟨hxG | hxD₀, hxD₁⟩
    · exact hGD₁ ⟨hxG, hxD₁⟩
    · exact hGD₁ ⟨hDD ⟨hxD₀, hxD₁⟩, hxD₁⟩
  have hF' : IsClosed (h₀ '' F) := h₀.isClosedMap _ hF
  have hF'A₁ : (h₀ '' F) ∩ A₁ ⊆ {v} := by
    rintro x ⟨⟨y, hy, hyx⟩, hxA⟩
    have hyx' : y = x := h₀.injective (hyx.trans (hfix₀ x (hA₁G hxA)).symm)
    exact hFG ⟨hyx' ▸ hy, hA₁G hxA⟩
  obtain ⟨h₁, hfix₁, hpush₁⟩ := push_cap_fixing hS hD₁ hA₁ ha₁ hAb₁ hG'
    (Or.inl hvG) (Or.inl ha₁G) hGD' hF' hF'A₁
  let h := h₀.trans h₁
  have hfix : ∀ x ∈ G, h x = x := by
    intro x hx
    change h₁ (h₀ x) = x
    rw [hfix₀ x hx, hfix₁ x (Or.inl hx)]
  have hpush₀' : (h '' F) ∩ D₀ ⊆ {v} := by
    rintro x ⟨⟨y, hy, hyx⟩, hxD⟩
    have heq : h₀ y = x := h₁.injective (hyx.trans (hfix₁ x (Or.inr hxD)).symm)
    exact hpush₀ ⟨⟨y, hy, heq⟩, hxD⟩
  have hpush₁' : (h '' F) ∩ D₁ ⊆ {v} := by
    rintro x ⟨⟨y, hy, hyx⟩, hxD⟩
    exact hpush₁ ⟨⟨h₀ y, ⟨y, hy, rfl⟩, hyx⟩, hxD⟩
  refine ⟨h, hfix, ?_⟩
  rintro x ⟨⟨hxF, hxC⟩, hxO⟩
  rcases hcover ⟨hxC, hxO⟩ with hxD₀ | hxD₁
  · exact hpush₀' ⟨hxF, hxD₀⟩
  · exact hpush₁' ⟨hxF, hxD₁⟩

end GraphMinor.GM12
