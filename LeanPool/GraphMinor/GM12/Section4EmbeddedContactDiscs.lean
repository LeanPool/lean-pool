/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4MeetingImages
public import LeanPool.GraphMinor.GM12.Section4OneCrossingContactDiscs

/-!
# Source contact discs after embedding the plane

For XII (4.5), claim (1), page 253, transport the planar source
and its crossing discs into a surface chart before clipping
and thickening. Compactness makes the image crossing-disc union
closed. Openness of the embedding keeps each crossing in its
interior, and injectivity preserves all one-crossing and vertex
incidence equations. The closed-surface construction then gives
the required vertex contact discs.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Carry a planar one-crossing source into a closed surface
and construct its disjoint vertex contact discs there. This is
the chart-transfer and vertex-disc step in XII (4.5), claim (1),
page 253. -/
theorem exists_embedded_contact_discs {S V E : Type} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [Finite V] [Finite E]
    (hS : IsClosedSurface S) (f : ℂ → S) (hf : Topology.IsOpenEmbedding f)
    (v : V → ℂ) (hinj : Function.Injective v) (κ : E × Bool → V) (P : E → Set ℂ)
    (hP : ∀ e, IsLineWithEnds (P e) (v (κ (e, false))) (v (κ (e, true))))
    (hPV : ∀ e w, v w ∈ P e → w = κ (e, false) ∨ w = κ (e, true))
    (hcross : ∀ e, ∃ x ∈ edgeMeetingPoints v P, P e ∩ edgeMeetingPoints v P = {x})
    (Z : Set ℂ) (hZ : IsCompact Z) (hvZ : ∀ w, v w ∉ Z)
    (hMZ : edgeMeetingPoints v P ⊆ interior Z) :
    ∃ (q : E × Bool → S) (D : V → Set S), Function.Injective q ∧
      (∀ i, q i ∈ (f '' P i.1) ∩ frontier (f '' Z)) ∧
      (∀ w, IsClosedDisc (D w)) ∧
      (∀ w z, w ≠ z → Disjoint (D w) (D z)) ∧
      ∀ w, D w ∩ (f '' Z) = {z | ∃ i, κ i = w ∧ q i = z} := by
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  let : CompactSpace S := hS.1
  have hv' : Function.Injective (f ∘ v) := hf.injective.comp hinj
  have hP' : ∀ e, IsLineWithEnds (f '' P e) ((f ∘ v) (κ (e, false)))
      ((f ∘ v) (κ (e, true))) :=
    fun e => isLineWithEnds_image_injective f hf.continuous hf.injective (hP e)
  have hPV' : ∀ e w, (f ∘ v) w ∈ f '' P e → w = κ (e, false) ∨ w = κ (e, true) := by
    rintro e w ⟨z, hz, hzw⟩
    have heq : z = v w := hf.injective hzw
    exact hPV e w (heq ▸ hz)
  have hcross' : ∀ e, ∃ x ∈ edgeMeetingPoints (f ∘ v) (fun j => f '' P j),
      (f '' P e) ∩ edgeMeetingPoints (f ∘ v) (fun j => f '' P j) = {x} := by
    intro e
    obtain ⟨x, hx, heq⟩ := hcross e
    refine ⟨f x, ?_, one_meeting_image f hf.injective v P heq⟩
    rw [edgeMeetingPoints_image f hf.injective]
    exact mem_image_of_mem f hx
  have hvZ' : ∀ w, (f ∘ v) w ∉ f '' Z := by
    rintro w ⟨z, hz, hzw⟩
    exact hvZ w ((hf.injective hzw) ▸ hz)
  have hMZ' : edgeMeetingPoints (f ∘ v) (fun e => f '' P e) ⊆ interior (f '' Z) := by
    rw [edgeMeetingPoints_image f hf.injective]
    rintro _ ⟨x, hx, rfl⟩
    exact hf.isOpenMap.image_interior_subset Z (mem_image_of_mem f (hMZ hx))
  exact exists_one_crossing_contact_discs hS (f ∘ v) hv' κ (fun e => f '' P e) hP' hPV'
    hcross' (f '' Z) (hZ.image hf.continuous).isClosed hvZ' hMZ'

end GraphMinor.GM12
