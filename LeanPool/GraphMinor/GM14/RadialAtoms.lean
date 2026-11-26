/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM11.Regions

/-!
# Corresponding atoms in radial drawings

A radial drawing has one corresponding atom for each atom of the original drawing.
-/

public section

namespace GraphMinor.GM14

open Set Surface GM11

variable {S : Type*} [TopologicalSpace S]

/-- Every atom of the original drawing has a unique corresponding
atom in its radial drawing. -/
theorem existsUnique_correspondingAtom {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) {x : Set S} (hx : x ∈ H.A) :
    ∃! x' : Set S, IsCorrespondingAtom H K x x' := by
  have hP := hK.2.1
  have hUU : H.U ∩ K.U = H.V := hP.1
  have hVV : H.V ⊆ K.V := hP.2.1
  have huniqR : ∀ r ∈ H.R, ∃! w, w ∈ r ∧ w ∈ K.V := hP.2.2.1
  have hxA := hx
  rcases hx with (⟨v, hv, rfl⟩ | hxE) | hxR
  · refine ⟨{v}, ⟨hxA, Or.inl (Or.inl ⟨v, hVV hv, rfl⟩), Or.inl ⟨v, hv, rfl, rfl⟩⟩, ?_⟩
    rintro x' ⟨-, -, ⟨u, -, hu, rfl⟩ | ⟨he, -, -⟩ | ⟨hr, -⟩⟩
    · exact hu.symm
    · exact absurd hv (he.2.1 (mem_singleton v)).2
    · exact absurd (H.V_subset_U hv) (region_subset hr (mem_singleton v))
  · obtain ⟨p₀, hp₀⟩ := hxE.1
    have hoff : ∀ y ∈ x, y ∉ K.U := fun y hy hyK => by
      have : y ∈ H.U ∩ K.U := ⟨(hxE.2.1 hy).1, hyK⟩
      rw [hUU] at this
      exact (hxE.2.1 hy).2 this
    set r₀ := connectedComponentIn (univ \ K.U) p₀
    have hr₀ : r₀ ∈ K.R := (mem_R_iff K).mpr ⟨p₀, hoff p₀ hp₀, rfl⟩
    have hsub : x ⊆ r₀ :=
      hxE.2.2.1.isConnected.isPreconnected.subset_connectedComponentIn hp₀
        fun y hy => ⟨mem_univ y, hoff y hy⟩
    refine ⟨r₀, ⟨hxA, Or.inr hr₀, Or.inr (Or.inl ⟨hxE, hr₀, hsub⟩)⟩, ?_⟩
    rintro x' ⟨-, -, ⟨u, hu, hxu, -⟩ | ⟨-, hr', hsub'⟩ | ⟨hr, -⟩⟩
    · exact absurd hu (hxE.2.1 (hxu ▸ mem_singleton u)).2
    · exact region_eq_of_mem hr' hr₀ (hsub' hp₀) (hsub hp₀)
    · exact absurd (hxE.2.1 hp₀).1 (region_subset hr hp₀)
  · obtain ⟨w, ⟨hwx, hwK⟩, hw_uniq⟩ := huniqR x hxR
    refine ⟨{w}, ⟨hxA, Or.inl (Or.inl ⟨w, hwK, rfl⟩),
      Or.inr (Or.inr ⟨hxR, w, ⟨hwK, hwx⟩, rfl⟩)⟩, ?_⟩
    rintro x' ⟨-, -, ⟨u, hu, hxu, -⟩ | ⟨he, -, -⟩ | ⟨-, u, ⟨huK, hux⟩, rfl⟩⟩
    · exact absurd (H.V_subset_U hu) (region_subset hxR (hxu ▸ mem_singleton u))
    · obtain ⟨p₀, hp₀⟩ := he.1
      exact absurd (he.2.1 hp₀).1 (region_subset hxR hp₀)
    · rw [hw_uniq u ⟨hux, huK⟩]

end GraphMinor.GM14
