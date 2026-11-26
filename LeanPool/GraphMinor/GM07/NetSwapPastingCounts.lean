/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Set.Card
import LeanPool.GraphMinor.GM07.NetSwapCounts

/-!
# The finite contact count for pasting two pieces

When two boundary arcs are pasted, their common open part leaves
the boundary. Their common ends remain once. Count contacts on the
two pieces before identifying the common arc, keeping its open
part and ends separate. This is the pasting half of the exact
count in VII (2.6), page 218.
-/

public section
namespace GraphMinor.GM07
open Set

/-- A two-piece boundary whose pasted open arc is removed is the
union of the piece boundaries minus the image of that open arc. -/
theorem pasted_boundary_eq
    {I A B T : Type*} (a : I → A) (b : I → B) (α : A → T) (β : B → T)
    (hα : Function.Injective α) (ha : Function.Injective a)
    (hcross : ∀ x y, α x = β y ↔ ∃ t, x = a t ∧ y = b t)
    (hT : range α ∪ range β = univ) (KA : Set A) (KB : Set B) (O : Set I) (L : Set T)
    (hLA : ∀ x, α x ∈ L ↔ x ∈ KA ∧ x ∉ a '' O)
    (hLB : ∀ y, β y ∈ L ↔ y ∈ KB ∧ y ∉ b '' O) :
    L = (α '' KA ∪ β '' KB) \ ((α ∘ a) '' O) := by
  have hPair : ∀ t, α (a t) = β (b t) := fun t => (hcross _ _).mpr ⟨t, rfl, rfl⟩
  apply Subset.antisymm
  · intro z hz
    rcases hT.symm ▸ mem_univ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨hxK, hxO⟩ := (hLA x).mp hz
      refine ⟨Or.inl ⟨x, hxK, rfl⟩, ?_⟩
      rintro ⟨t, ht, htx⟩
      exact hxO ⟨t, ht, hα htx⟩
    · obtain ⟨hyK, hyO⟩ := (hLB y).mp hz
      refine ⟨Or.inr ⟨y, hyK, rfl⟩, ?_⟩
      rintro ⟨t, ht, hty⟩
      obtain ⟨s, has, hys⟩ := (hcross (a t) y).mp hty
      exact hyO ⟨t, ht, (congrArg b (ha has)).trans hys.symm⟩
  · rintro z ⟨(⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩), hn⟩
    · apply (hLA x).mpr
      refine ⟨hx, ?_⟩
      rintro ⟨t, ht, htx⟩
      exact hn ⟨t, ht, congrArg α htx⟩
    · apply (hLB y).mpr
      refine ⟨hy, ?_⟩
      rintro ⟨t, ht, hty⟩
      exact hn ⟨t, ht, (hPair t).trans (congrArg β hty)⟩

/-- Pasting removes two copies of each open-arc contact and one copy
of each common endpoint contact from the sum over the two pieces.
The parameter sets `O` and `E` partition the pasted arc into its
open part and its ends. -/
theorem ncard_pasting_contacts
    {I A B T S : Type*} (a : I → A) (b : I → B) (α : A → T) (β : B → T)
    (hα : Function.Injective α) (hβ : Function.Injective β) (ha : Function.Injective a)
    (hcross : ∀ x y, α x = β y ↔ ∃ t, x = a t ∧ y = b t)
    (KA : Set A) (KB : Set B) (hKA : range a ⊆ KA) (hKB : range b ⊆ KB)
    (O E : Set I) (hOE : Disjoint O E) (hCover : O ∪ E = univ)
    (φ : T → S) (V : Set S)
    (hPA : (KA ∩ (φ ∘ α) ⁻¹' V).Finite)
    (hPB : (KB ∩ (φ ∘ β) ⁻¹' V).Finite) :
    (((α '' KA ∪ β '' KB) \ ((α ∘ a) '' O)) ∩ φ ⁻¹' V).ncard +
      2 * (O ∩ (φ ∘ α ∘ a) ⁻¹' V).ncard +
      (E ∩ (φ ∘ α ∘ a) ⁻¹' V).ncard =
        (KA ∩ (φ ∘ α) ⁻¹' V).ncard + (KB ∩ (φ ∘ β) ⁻¹' V).ncard := by
  let P := α '' (KA ∩ (φ ∘ α) ⁻¹' V)
  let Q := β '' (KB ∩ (φ ∘ β) ⁻¹' V)
  let k := α ∘ a
  let W := (φ ∘ k) ⁻¹' V
  have hk : Function.Injective k := hα.comp ha
  have hPair : ∀ t, α (a t) = β (b t) := fun t => (hcross _ _).mpr ⟨t, rfl, rfl⟩
  have hInter : P ∩ Q = k '' W := by
    apply Subset.antisymm
    · rintro z ⟨⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩
      obtain ⟨t, rfl, rfl⟩ := (hcross x y).mp (hxz.trans hyz.symm)
      exact ⟨t, hx.2, hxz⟩
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨⟨a t, ⟨hKA (mem_range_self t), ht⟩, rfl⟩,
        ⟨b t, ⟨hKB (mem_range_self t), (show φ (β (b t)) ∈ V from (congrArg φ (hPair t)) ▸ ht)⟩,
          (hPair t).symm⟩⟩
  have hParts : ∀ t, t ∈ O ↔ t ∉ E := by
    intro t
    constructor
    · exact fun ht he => disjoint_left.mp hOE ht he
    · intro ht
      exact (hCover.symm ▸ mem_univ t).resolve_right ht
  have hOpen : (P ∩ Q) \ (k '' E) = k '' (O ∩ W) := by
    rw [hInter]
    apply Subset.antisymm
    · rintro z ⟨⟨t, ht, rfl⟩, hn⟩
      exact ⟨t, ⟨(hParts t).mpr (fun he => hn ⟨t, he, rfl⟩), ht⟩, rfl⟩
    · rintro z ⟨t, ⟨htO, htW⟩, rfl⟩
      refine ⟨⟨t, htW, rfl⟩, ?_⟩
      rintro ⟨s, hs, hst⟩
      exact (hParts t).mp htO (hk hst ▸ hs)
  have hEnd : (P ∩ Q) ∩ (k '' E) = k '' (E ∩ W) := by
    rw [hInter]
    apply Subset.antisymm
    · rintro z ⟨⟨t, ht, rfl⟩, ⟨s, hs, hst⟩⟩
      exact ⟨t, ⟨hk hst ▸ hs, ht⟩, rfl⟩
    · rintro z ⟨t, ⟨htE, htW⟩, rfl⟩
      exact ⟨⟨t, htW, rfl⟩, ⟨t, htE, rfl⟩⟩
  have hUnion : P ∪ Q = (α '' KA ∪ β '' KB) ∩ φ ⁻¹' V := by
    ext z
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
      · exact ⟨Or.inl ⟨x, hx.1, rfl⟩, hx.2⟩
      · exact ⟨Or.inr ⟨y, hy.1, rfl⟩, hy.2⟩
    · rintro ⟨(⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩), hz⟩
      · exact Or.inl ⟨x, ⟨hx, hz⟩, rfl⟩
      · exact Or.inr ⟨y, ⟨hy, hz⟩, rfl⟩
  have hRem : (P ∪ Q) \ ((P ∩ Q) \ (k '' E)) =
      ((α '' KA ∪ β '' KB) \ (k '' O)) ∩ φ ⁻¹' V := by
    rw [hOpen, hUnion]
    apply Subset.antisymm
    · rintro z ⟨⟨hz, hzV⟩, hn⟩
      refine ⟨⟨hz, ?_⟩, hzV⟩
      rintro ⟨t, ht, htz⟩
      exact hn ⟨t, ⟨ht, (show φ (k t) ∈ V from (congrArg φ htz).symm ▸ hzV)⟩, htz⟩
    · rintro z ⟨⟨hz, hn⟩, hzV⟩
      refine ⟨⟨hz, hzV⟩, ?_⟩
      rintro ⟨t, ht, htz⟩
      exact hn ⟨t, ht.1, htz⟩
  have hCount := ncard_boundary_after_pasting P Q (k '' E) (hPA.image α) (hPB.image β)
  rw [hRem, hOpen, hEnd, hk.injOn.ncard_image, hk.injOn.ncard_image] at hCount
  have hPCount : P.ncard = (KA ∩ (φ ∘ α) ⁻¹' V).ncard := hα.injOn.ncard_image
  have hQCount : Q.ncard = (KB ∩ (φ ∘ β) ⁻¹' V).ncard := hβ.injOn.ncard_image
  rw [hPCount, hQCount] at hCount
  exact hCount

end GraphMinor.GM07
