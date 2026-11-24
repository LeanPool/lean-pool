/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.AddCrosscap
public import LeanPool.GraphMinor.Surface.DiscRemove
public import LeanPool.GraphMinor.GM12.Section3ClosedComponents

/-!
# Removing several discs from a closed surface

We remove the interiors of finitely many pairwise disjoint closed discs from a closed connected
surface (`remove_discs`). The result is a
connected surface whose cuffs are the boundaries of the discs. The work for one disc is
`remove_disc`. Near a boundary of a disc the set we keep
agrees with the set that keeps all the other discs, so the facts are local.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

variable {S : Type} [TopologicalSpace S]

/-- Two subsets of `S` that agree on an open set `W` have homeomorphic parts in `O ⊆ W`. -/
theorem exists_local_homeo {X Y W O : Set S} (h : X ∩ W = Y ∩ W) (hO : O ⊆ W) :
    Nonempty ((Subtype.val ⁻¹' O : Set ↥X) ≃ₜ (Subtype.val ⁻¹' O : Set ↥Y)) := by
  have hXY : X ∩ O = Y ∩ O := by
    ext z
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨(h.subset ⟨h₁, hO h₂⟩).1, h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨(h.symm.subset ⟨h₁, hO h₂⟩).1, h₂⟩
  have hem : ∀ Z : Set S, IsEmbedding (fun z : (Subtype.val ⁻¹' O : Set ↥Z) => (z.1.1 : S))
    := fun Z =>
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hr : ∀ Z : Set S, range (fun z : (Subtype.val ⁻¹' O : Set ↥Z) => (z.1.1 : S)) = Z ∩ O
    := fun Z => by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.1.2, w.2⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨⟨z, h₁⟩, h₂⟩, rfl⟩
  have eq : range (fun z : (Subtype.val ⁻¹' O : Set ↥X) => (z.1.1 : S)) = range (fun z :
    (Subtype.val ⁻¹' O : Set ↥Y) => (z.1.1 : S)) := by
    rw [hr, hr, hXY]
  exact ⟨((hem X).toHomeomorph.trans (Homeomorph.setCongr eq)).trans (hem Y).toHomeomorph.symm⟩

/-- Being an interior point is local. -/
theorem IsInteriorPoint.congr_local {X Y W : Set S} (hW : IsOpen W) (h : X ∩ W
  = Y ∩ W) {x : ↥X} {y : ↥Y} (hxy : x.1 = y.1) (hx : x.1 ∈ W)
    (hi : IsInteriorPoint x) : IsInteriorPoint y := by
  obtain ⟨U, hU, hxU, hsub, ⟨f⟩⟩ := hi.exists_subset (hW.preimage continuous_subtype_val) hx
  obtain ⟨O₀, hO₀, rfl⟩ := isOpen_induced_iff.mp hU
  have heq : (Subtype.val ⁻¹' O₀ : Set ↥X) = Subtype.val ⁻¹' (O₀ ∩ W) := by
    ext z
    exact ⟨fun hz => ⟨hz, hsub hz⟩, fun hz => hz.1⟩
  obtain ⟨g⟩ := exists_local_homeo h (inter_subset_right (s := O₀) (t := W))
  exact ⟨Subtype.val ⁻¹' (O₀ ∩ W), (hO₀.inter hW).preimage continuous_subtype_val, ⟨hxy ▸ hxU,
    hxy ▸ hx⟩,
    ⟨g.symm.trans ((Homeomorph.setCongr heq.symm).trans f)⟩⟩

/-- Being a manifold point is local. -/
theorem IsManifoldPoint.congr_local {X Y W : Set S} (hW : IsOpen W) (h : X ∩ W
  = Y ∩ W) {x : ↥X} {y : ↥Y} (hxy : x.1 = y.1) (hx : x.1 ∈ W)
    (hi : IsManifoldPoint x) : IsManifoldPoint y := by
  obtain ⟨U, V, hU, hV, hxU, ⟨f⟩⟩ := hi
  obtain ⟨O₀, hO₀, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨g⟩ := exists_local_homeo h (inter_subset_right (s := O₀) (t := W))
  have hsub : (Subtype.val ⁻¹' (O₀ ∩ W) : Set ↥X) ⊆ Subtype.val ⁻¹' O₀ := fun z hz => hz.1
  have hj : IsOpenEmbedding (fun z : (Subtype.val ⁻¹' (O₀ ∩ W) : Set ↥X) => ((f
    (inclusion hsub z)).1 : EuclideanHalfSpace 2)) := by
    have h₁ : IsOpenEmbedding (inclusion hsub) := .inclusion hsub (((hO₀.inter hW).preimage
      continuous_subtype_val).preimage continuous_subtype_val)
    exact hV.isOpenEmbedding_subtypeVal.comp (f.isOpenEmbedding.comp h₁)
  exact ⟨Subtype.val ⁻¹' (O₀ ∩ W), _, (hO₀.inter hW).preimage continuous_subtype_val,
    hj.isOpen_range, ⟨hxy ▸ hxU, hxy ▸ hx⟩,
    ⟨g.symm.trans hj.toIsEmbedding.toHomeomorph⟩⟩

/-- **Removing several discs.** The interiors of finitely many pairwise disjoint closed discs come
out of a closed connected surface, and the rest is a connected surface with one cuff for each disc.
-/
theorem remove_discs (hS : IsSurface S) (hb : ∀ x : S, IsInteriorPoint x) [ConnectedSpace S] {ι :
  Type*} [Finite ι] {P : ι → Set S} (hP : ∀ i, IsClosedDisc (P i))
    (hd : Pairwise fun i j => Disjoint (P i) (P j)) :
    IsClosed (⋃ i, discInt (P i))ᶜ ∧ IsSurface ↥(⋃ i, discInt (P i))ᶜ ∧ bd ↥(⋃ i, discInt (P i))ᶜ
      = Subtype.val ⁻¹' (⋃ i, discBd (P i)) ∧
      ConnectedSpace ↥(⋃ i, discInt (P i))ᶜ ∧ cuffs ↥(⋃ i, discInt (P i))ᶜ = range fun i =>
        (Subtype.val ⁻¹' discBd (P i) : Set ↥(⋃ i, discInt (P i))ᶜ) := by
  classical
  have hman : ∀ x : S, IsManifoldPoint x := hS.2.2
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hint : ∀ i, ∀ x ∈ discBd (P i), IsInteriorPoint x := fun i x _ => hb x
  have hPc : ∀ i, IsClosed (P i) := fun i => (hP i).isClosed
  have hopen : IsOpen (⋃ i, discInt (P i)) := isOpen_iUnion fun i => (hP i).isOpen_discInt hman
  set X : Set S := (⋃ i, discInt (P i))ᶜ with hX
  have hXc : IsClosed X := hopen.isClosed_compl
  have hdB : ∀ i, discBd (P i) ⊆ P i := fun i => by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hXd : ∀ {z i}, z ∈ X → z ∈ P i → z ∈ discBd (P i) := fun {z i} hz hi => by
    by_contra hn
    exact hz (mem_iUnion.2 ⟨i, hi, hn⟩)
  have hBX : ∀ {z i}, z ∈ discBd (P i) → z ∈ X := fun {z i} hz hu => by
    obtain ⟨j, hj, hn⟩ := mem_iUnion.1 hu
    by_cases hij : j = i
    · subst hij
      exact hn hz
    · exact Set.disjoint_left.mp (hd hij) hj (hdB i hz)
  let W : ι → Set S := fun i => (⋃ j ∈ {j | j ≠ i}, P j)ᶜ
  have hWo : ∀ i, IsOpen (W i) := fun i => ((Set.toFinite _).isClosed_biUnion fun j _
    => hPc j).isOpen_compl
  have hW : ∀ i, X ∩ W i = (discInt (P i))ᶜ ∩ W i := fun i => by
    ext z
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun h => h₁ (mem_iUnion.2 ⟨i, h⟩), h₂⟩
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun hu => ?_, h₂⟩
      obtain ⟨j, hj⟩ := mem_iUnion.1 hu
      by_cases hij : j = i
      · exact h₁ (hij ▸ hj)
      · exact h₂ (mem_iUnion₂.2 ⟨j, hij, hj.1⟩)
  have hPW : ∀ {z i}, z ∈ P i → z ∈ W i := fun {z i} hz hu => by
    obtain ⟨j, hj, hm⟩ := mem_iUnion₂.1 hu
    exact Set.disjoint_left.mp (hd hj) hm hz
  have hmem : ∀ i, IsSurface ↥(discInt (P i))ᶜ ∧ bd ↥(discInt (P i))ᶜ = Subtype.val ⁻¹'
    (bd S ∪ discBd (P i)) := fun i => by
    obtain ⟨-, h₂, h₃⟩ := remove_disc hS (hP i) (fun x _ => hb x)
    exact ⟨h₂, h₃⟩
  have hbdS : bd S = ∅ := eq_empty_of_forall_notMem fun x hx => hx (hb x)
  have hoff : ∀ x : ↥X, (∀ i, x.1 ∉ P i) → IsInteriorPoint x := fun x hn => by
    have hint' : IsInteriorPoint (⟨x.1, mem_univ _⟩ : ↥(univ : Set S)) :=
      (isInteriorPoint_homeomorph_iff (Homeomorph.Set.univ S) ⟨x.1, mem_univ _⟩).mp (hb x.1)
    have hWW : IsOpen (⋃ j, P j)ᶜ := (isClosed_iUnion_of_finite hPc).isOpen_compl
    refine IsInteriorPoint.congr_local (X := univ) (Y := X) hWW ?_ rfl (by simpa using hn) hint'
    ext z
    simp only [mem_inter_iff, mem_univ, true_and, mem_compl_iff]
    constructor
    · intro h
      refine ⟨fun hu => ?_, h⟩
      obtain ⟨j, hj⟩ := mem_iUnion.1 hu
      exact h (mem_iUnion.2 ⟨j, hj.1⟩)
    · exact fun h => h.2
  have hbdX : bd ↥X = Subtype.val ⁻¹' (⋃ i, discBd (P i)) := by
    ext x
    constructor
    · intro hx
      by_contra hn
      refine hx (hoff x fun i hi => hn (mem_iUnion.2 ⟨i, hXd x.2 hi⟩))
    · intro hx hi
      obtain ⟨i, hxi⟩ := mem_iUnion.1 hx
      have hy : (⟨x.1, fun h => h.2 hxi⟩ : ↥(discInt (P i))ᶜ) ∈ bd ↥(discInt (P i))ᶜ := by
        rw [(hmem i).2]
        exact Or.inr hxi
      exact hy (IsInteriorPoint.congr_local (W := W i) (hWo i) (hW i) rfl (hPW (hdB i hxi)) hi)
  have hsurf : IsSurface ↥X := by
    have : CompactSpace ↥X := isCompact_iff_compactSpace.mp hXc.isCompact
    refine ⟨inferInstance, inferInstance, fun x => ?_⟩
    by_cases hi : ∃ i, x.1 ∈ P i
    · obtain ⟨i, hi⟩ := hi
      have hb' : x.1 ∈ discBd (P i) := hXd x.2 hi
      exact IsManifoldPoint.congr_local (hWo i) (hW i).symm rfl (hPW hi) ((hmem i).1.2.2 ⟨x.1,
        fun h => h.2 hb'⟩)
    · push Not at hi
      exact (hoff x hi).isManifoldPoint
  have hne : ∀ i, (discBd (P i)).Nonempty := fun i => (IsOArc.isConnected'
    (hP i).isOArc_discBd).nonempty
  have hXne : X.Nonempty := by
    by_cases hι : Nonempty ι
    · obtain ⟨i⟩ := hι
      obtain ⟨z, hz⟩ := hne i
      exact ⟨z, hBX hz⟩
    · have : IsEmpty ι := not_nonempty_iff.mp hι
      obtain ⟨z⟩ : Nonempty S := inferInstance
      exact ⟨z, by simp [hX]⟩
  have hcon : ConnectedSpace ↥X := by
    have hPX : ∀ i, P i ∩ X = discBd (P i) := fun i => by
      ext z
      exact ⟨fun h => hXd h.2 h.1, fun h => ⟨hdB i h, hBX h⟩⟩
    refine connected_compl hXc hXne (Set.finite_range P) ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨i, rfl⟩
      exact hPc i
    · rintro _ ⟨i, rfl⟩
      rw [hPX]
      exact (IsOArc.isConnected' (hP i).isOArc_discBd).isPreconnected
    · rintro _ ⟨i, rfl⟩
      rw [hPX]
      exact hne i
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne'
      exact hd fun h => hne' (h ▸ rfl)
    · ext z
      simp only [mem_union, mem_sUnion, mem_range, exists_exists_eq_and, mem_univ, iff_true]
      by_cases hz : z ∈ X
      · exact Or.inl hz
      · have : z ∈ ⋃ i, discInt (P i) := not_not.mp hz
        obtain ⟨i, hi⟩ := mem_iUnion.1 this
        exact Or.inr ⟨i, hi.1⟩
  refine ⟨hXc, hsurf, hbdX, hcon, ?_⟩
  have hu : (Subtype.val ⁻¹' (⋃ i, discBd (P i)) : Set ↥X) = ⋃ i, (Subtype.val ⁻¹' discBd
    (P i) : Set ↥X) := preimage_iUnion
  rw [cuffs, hbdX, hu]
  refine GM12.componentsIn_iUnion_disjoint_closed (fun i => (Subtype.val ⁻¹' discBd
    (P i) : Set ↥X)) ?_ ?_ ?_ ?_
  · exact fun i => (hP i).isOArc_discBd.isCompact.isClosed.preimage continuous_subtype_val
  · intro i
    refine (IsOArc.isConnected' (hP i).isOArc_discBd).isPreconnected.preimage_of_isClosedMap
      Subtype.val_injective
      hXc.isClosedEmbedding_subtypeVal.isClosedMap ?_
    intro z hz
    exact ⟨⟨z, hBX hz⟩, rfl⟩
  · intro i
    obtain ⟨z, hz⟩ := hne i
    exact ⟨⟨z, hBX hz⟩, hz⟩
  · intro i j hij
    refine Set.disjoint_left.mpr fun z hz hz' => ?_
    exact Set.disjoint_left.mp (hd hij) (hdB i hz) (hdB j hz')

end GraphMinor.Surface
