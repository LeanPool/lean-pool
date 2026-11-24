/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.GM07.Taper

/-!
# Pulling a drawing back along a map

Let `f : Y → S` be a continuous onto map from a compact space that is one to one over `U(G)`. Then
`f⁻¹(G)` is a drawing in `Y`
(`pullDrawing`), since `f` is a homeomorphism over `U(G)`. We use this to define the graph left
after cutting along an edge.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u v

variable {Y : Type u} {S : Type v} [TopologicalSpace Y] [TopologicalSpace S]

/-- `f` is a homeomorphism over a closed set on whose preimage it is one to one. -/
theorem exists_homeo_preimage [CompactSpace Y] [T2Space S] {f : Y → S} (hf : Continuous f)
  (hs : Function.Surjective f)
    {K : Set S} (hK : IsClosed K) (hi : InjOn f (f ⁻¹' K)) :
    ∃ k : f ⁻¹' K ≃ₜ K, ∀ p, (k p).1 = f p.1 := by
  have : CompactSpace (f ⁻¹' K) := isCompact_iff_compactSpace.mp (hK.preimage hf).isCompact
  let m : f ⁻¹' K → K := fun p => ⟨f p.1, p.2⟩
  have hmc : Continuous m := Continuous.subtype_mk (hf.comp continuous_subtype_val) _
  have hmb : Function.Bijective m := by
    constructor
    · intro p p' he
      exact Subtype.ext (hi p.2 p'.2 (congrArg Subtype.val he))
    · rintro ⟨s, hs'⟩
      obtain ⟨p, rfl⟩ := hs s
      exact ⟨⟨p, hs'⟩, rfl⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective m hmb) hmc, fun p => rfl⟩

/-- A subset of `K` is path connected exactly when its preimage is. -/
theorem isPathConnected_preimage_iff [CompactSpace Y] [T2Space S] {f : Y → S} (hf : Continuous f)
    (hs : Function.Surjective f) {K A : Set S} (hK : IsClosed K) (hi : InjOn f (f ⁻¹' K))
      (hA : A ⊆ K) :
    IsPathConnected (f ⁻¹' A) ↔ IsPathConnected A := by
  constructor
  · intro h
    have h1 := h.image hf
    rwa [image_preimage_eq _ hs] at h1
  · intro h
    obtain ⟨k, hk⟩ := exists_homeo_preimage hf hs hK hi
    have hAe : f ⁻¹' A = (fun x => (k.symm x).1) '' ((↑) ⁻¹' A : Set K) := by
      ext y
      constructor
      · intro hy
        refine ⟨⟨f y, hA hy⟩, hy, ?_⟩
        have h2 : k ⟨y, hA hy⟩ = ⟨f y, hA hy⟩ := Subtype.ext (hk _)
        rw [← h2]
        change (k.symm (k _)).1 = y
        rw [k.symm_apply_apply]
      · rintro ⟨x, hx, rfl⟩
        change f (k.symm x).1 ∈ A
        rw [← hk, k.apply_symm_apply]
        exact hx
    rw [hAe]
    have h3 : IsPathConnected ((↑) ⁻¹' A : Set K) := by
      rw [Topology.IsInducing.subtypeVal.isPathConnected_iff, image_preimage_eq_of_subset
        (by simpa using hA)]
      exact h
    exact h3.image (continuous_subtype_val.comp k.symm.continuous)

theorem arcComponentsIn_preimage [CompactSpace Y] [T2Space S] {f : Y → S} (hf : Continuous f)
  (hs : Function.Surjective f)
    {K F : Set S} (hK : IsClosed K) (hi : InjOn f (f ⁻¹' K)) (hF : F ⊆ K) :
    arcComponentsIn (f ⁻¹' F) = preimage f '' arcComponentsIn F := by
  have hconn := fun {A : Set S} (h : A ⊆ K) => isPathConnected_preimage_iff hf hs hK hi h
  ext D
  constructor
  · rintro ⟨hne, hsub, hpc, hmax⟩
    have hD : f ⁻¹' (f '' D) = D := by
      ext y
      constructor
      · rintro ⟨x, hx, he⟩
        have h1 : x ∈ f ⁻¹' K := hF (hsub hx)
        have h2 : y ∈ f ⁻¹' K := by
          change f y ∈ K
          rw [← he]
          exact h1
        rwa [← hi h1 h2 he]
      · exact fun hy => ⟨y, hy, rfl⟩
    refine ⟨f '' D, ⟨hne.image f, ?_, hpc.image hf, fun A hA hpA hCA => ?_⟩, hD⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hsub hx
    · have h1 : D ⊆ f ⁻¹' A := fun x hx => hCA (mem_image_of_mem f hx)
      have h2 := hmax _ (preimage_mono hA) ((hconn (hA.trans hF)).mpr hpA) h1
      rw [← h2, image_preimage_eq _ hs]
  · rintro ⟨C, ⟨hne, hsub, hpc, hmax⟩, rfl⟩
    refine ⟨?_, preimage_mono hsub, (hconn (hsub.trans hF)).mpr hpc, fun B hB hpB hDB => ?_⟩
    · obtain ⟨x, hx⟩ := hne
      obtain ⟨y, rfl⟩ := hs x
      exact ⟨y, hx⟩
    · have hsA : f '' B ⊆ F := by
        rintro _ ⟨x, hx, rfl⟩
        exact hB hx
      have h1 : C ⊆ f '' B := fun x hx => by
        obtain ⟨y, rfl⟩ := hs x
        exact ⟨y, hDB hx, rfl⟩
      have h2 := hmax _ hsA (hpB.image hf) h1
      apply Subset.antisymm _ hDB
      intro y hy
      change f y ∈ C
      rw [← h2]
      exact mem_image_of_mem f hy

theorem closure_preimage_of_injOn [CompactSpace Y] [T2Space S] {f : Y → S} (hf : Continuous f)
  (hs : Function.Surjective f)
    {C : Set S} (hi : InjOn f (f ⁻¹' closure C)) : closure (f ⁻¹' C) = f ⁻¹' closure C := by
  apply Subset.antisymm (closure_minimal (preimage_mono subset_closure)
    (isClosed_closure.preimage hf))
  intro y hy
  obtain ⟨k, hk⟩ := exists_homeo_preimage hf hs isClosed_closure hi
  have hx : (⟨f y, hy⟩ : closure C) ∈ closure ((↑) ⁻¹' C : Set (closure C)) := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    change f y ∈ closure ((↑) '' ((↑) ⁻¹' C : Set (closure C)))
    rwa [image_preimage_eq_of_subset (by simpa using subset_closure)]
  have hg : Continuous fun x : closure C => (k.symm x).1 := continuous_subtype_val.comp
    k.symm.continuous
  have h1 := map_mem_closure hg hx (t := f ⁻¹' C) fun x hx' => by
    change f (k.symm x).1 ∈ C
    rw [← hk, k.apply_symm_apply]
    exact hx'
  have h2 : k.symm ⟨f y, hy⟩ = ⟨y, hy⟩ := by
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext (hk ⟨y, hy⟩).symm
  simpa [h2] using h1

/-- The preimage of a drawing under a map one to one over it. -/
def pullDrawing [CompactSpace Y] [T2Space S] (G₁ : Drawing S) {f : Y → S} (hf : Continuous f)
    (hs : Function.Surjective f) (hi : InjOn f (f ⁻¹' G₁.U)) : Drawing Y where
  U := f ⁻¹' G₁.U
  V := f ⁻¹' G₁.V
  V_subset_U := preimage_mono G₁.V_subset_U
  isClosed_U := G₁.isClosed_U.preimage hf
  finite_V := G₁.finite_V.preimage (hi.mono (preimage_mono G₁.V_subset_U))
  finite_edges := by
    rw [← preimage_sdiff, arcComponentsIn_preimage hf hs G₁.isClosed_U hi sdiff_subset]
    exact G₁.finite_edges.image _
  edge_cond := by
    rw [← preimage_sdiff, arcComponentsIn_preimage hf hs G₁.isClosed_U hi sdiff_subset]
    rintro _ ⟨C, hC, rfl⟩
    have hCU : closure C ⊆ G₁.U := closure_minimal (hC.2.1.trans sdiff_subset) G₁.isClosed_U
    have hic : InjOn f (f ⁻¹' closure C) := hi.mono (preimage_mono hCU)
    rw [closure_preimage_of_injOn hf hs hic, ← preimage_inter]
    obtain ⟨k, hk⟩ := exists_homeo_preimage hf hs isClosed_closure hic
    have hlift : ∀ q : closure C, f (k.symm q).1 = q.1 := fun q => by
      rw [← hk, k.apply_symm_apply]
    rcases G₁.edge_cond C hC with ⟨u, v, huv, hcap, l, h0, h1⟩ | ⟨u, hcap, ⟨l⟩⟩
    · left
      refine ⟨(k.symm (l 0)).1, (k.symm (l 1)).1, ?_, ?_, l.trans k.symm, rfl, rfl⟩
      · intro h
        have h2 := congrArg f h
        rw [hlift, hlift, h0, h1] at h2
        exact huv h2
      · rw [hcap]
        ext y
        have hu : (k.symm (l 0)).1 ∈ f ⁻¹' closure C := (k.symm (l 0)).2
        have hv : (k.symm (l 1)).1 ∈ f ⁻¹' closure C := (k.symm (l 1)).2
        have hucl : f (k.symm (l 0)).1 = u := by rw [hlift, h0]
        have hvcl : f (k.symm (l 1)).1 = v := by rw [hlift, h1]
        have hmem : ∀ z, z ∈ closure C ∩ G₁.V ↔ z = u ∨ z = v := fun z => by rw [hcap]; simp
        simp only [mem_preimage, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro (h | h)
          · have hy : y ∈ f ⁻¹' closure C := by
              change f y ∈ closure C
              rw [h]
              exact ((hmem u).mpr (.inl rfl)).1
            exact .inl (hic hy hu (h.trans hucl.symm))
          · have hy : y ∈ f ⁻¹' closure C := by
              change f y ∈ closure C
              rw [h]
              exact ((hmem v).mpr (.inr rfl)).1
            exact .inr (hic hy hv (h.trans hvcl.symm))
        · rintro (rfl | rfl)
          · exact .inl hucl
          · exact .inr hvcl
    · right
      obtain ⟨y, hy⟩ := hs u
      refine ⟨y, ?_, ⟨l.trans k.symm⟩⟩
      rw [hcap]
      ext z
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro h
        have hu : u ∈ closure C ∩ G₁.V := by rw [hcap]; rfl
        have hy' : y ∈ f ⁻¹' closure C := by
          change f y ∈ closure C
          rw [hy]
          exact hu.1
        have hz : z ∈ f ⁻¹' closure C := by
          change f z ∈ closure C
          rw [h]
          exact hu.1
        exact hic hz hy' (h.trans hy.symm)
      · rintro rfl
        exact hy

end GraphMinor.GM07
