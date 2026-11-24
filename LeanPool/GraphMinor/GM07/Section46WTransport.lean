/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section3
import LeanPool.GraphMinor.GM07.CuffSlide
import LeanPool.GraphMinor.GM07.Section35
import LeanPool.GraphMinor.GM07.Section46Constants
import LeanPool.GraphMinor.Surface.ModelCriterion

/-!
# The `w` bound after cutting

VII (4.6), page 226, uses the fact that `w(Σ′,2k,3(2a+b+c-1))`
depends only on the homeomorphism type of `Σ′`. Transport matchings,
forests and their homoplasties along a homeomorphism to transport every
valid bound. The upper cuff bound then places its model among the
finitely many models in the maximum defining `w`.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- Homoplasties transport under a homeomorphism, by conjugating the
boundary-fixing homeomorphism in their definition. -/
theorem ForestsHomoplastic.map_homeomorph {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (e : S ≃ₜ T) {H H' : Drawing S} (h : ForestsHomoplastic H H') :
    ForestsHomoplastic (mapDrawingHomeo e H) (mapDrawingHomeo e H') := by
  obtain ⟨α, hα, hhom⟩ := h
  let β := (e.symm.trans α).trans e
  refine ⟨β, ?_, ?_⟩
  · intro x hx
    have hxS : e.symm x ∈ bd S := by
      rw [← image_bd_homeomorph e.symm]
      exact mem_image_of_mem e.symm hx
    change e (α (e.symm x)) = x
    rw [hα _ hxS, e.apply_symm_apply]
  · have hhom' := ForestsHomotopic.map_homeo e hhom
    have heq : mapDrawingHomeo β (mapDrawingHomeo e H) = mapDrawingHomeo e (mapDrawingHomeo α H)
      := by
      cases H
      simp only [mapDrawingHomeo, Drawing.mk.injEq]
      constructor <;> ext x <;> simp [β, Homeomorph.trans_apply]
    rw [heq]
    exact hhom'

/-- Valid bounds in (3.6) transport along a homeomorphism, as used
in VII (4.6), page 226. -/
theorem IsW36Bound.map_homeomorph {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (e : S ≃ₜ T) {k n w : ℕ} (h : IsW36Bound S k n w) : IsW36Bound T k n w := by
  intro G H hG hGV hH hHV
  have hGV' : (mapDrawingHomeo e.symm G).V.ncard ≤ 2 * n := by
    change (e.symm '' G.V).ncard ≤ _
    rw [ncard_image_of_injective _ e.symm.injective]
    exact hGV
  have hHV' : ((mapDrawingHomeo e.symm H).V ∩ bd S).ncard ≤ k := by
    change (e.symm '' H.V ∩ bd S).ncard ≤ _
    rw [← image_bd_homeomorph e.symm, ← image_inter e.symm.injective,
      ncard_image_of_injective _ e.symm.injective]
    exact hHV
  obtain ⟨H', hH', hhom, hfin, hbound⟩ := h (mapDrawingHomeo e.symm G) (mapDrawingHomeo e.symm H)
    (IsMatching.map_homeo e.symm hG) hGV' (IsSurfaceForest.map_homeo e.symm hH) hHV'
  have hhom' := ForestsHomoplastic.map_homeomorph e hhom
  have hcancel : mapDrawingHomeo e (mapDrawingHomeo e.symm H) = H := by
    simpa only [Homeomorph.symm_symm] using mapDrawingHomeo_symm_mapDrawingHomeo e.symm H
  rw [hcancel] at hhom'
  have hcontacts : G.U ∩ (mapDrawingHomeo e H').U =
      e '' ((mapDrawingHomeo e.symm G).U ∩ H'.U) := by
    rw [image_inter e.injective]
    change G.U ∩ e '' H'.U = e '' (e.symm '' G.U) ∩ e '' H'.U
    simp only [image_image, Homeomorph.apply_symm_apply, image_id']
  refine ⟨mapDrawingHomeo e H', IsSurfaceForest.map_homeo e hH', hhom', ?_, ?_⟩
  · rw [hcontacts]
    exact hfin.image _
  · rw [hcontacts, ncard_image_of_injective _ e.injective]
    exact hbound

/-- The least (3.6) bound cannot increase when transporting a bound from
one homeomorphic surface, as used in VII (4.6), page 226. -/
theorem wSurface_le_of_homeomorph {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (hS : IsSurface S) (e : S ≃ₜ T) (k n : ℕ) :
    wSurface T k n ≤ wSurface S k n := by
  have hw := theorem_3_6_proof hS k n
  exact Nat.sInf_le (IsW36Bound.map_homeomorph e hw)

/-- The maximum defining `w` bounds the cut surface's (3.6) constant,
from the upper cuff bound in VII (4.6), page 226. -/
theorem wSurface_cut_model_le_wMaxModel {S' : Type} [TopologicalSpace S']
    {a b c c' k : ℕ} (hmodel : Nonempty (S' ≃ₜ SurfaceModel a b c'))
    (hc' : c' ≤ 2 * (2 * a + b + c - 1)) :
    wSurface S' (2 * k) (3 * (2 * a + b + c - 1)) ≤ wMaxModel a b c k := by
  have hmodelS : IsSurface (SurfaceModel a b c') := (modelCriterion.1 a b c').1
  exact (wSurface_le_of_homeomorph hmodelS hmodel.some.symm _ _).trans
    (wSurface_model_le_wMaxModel hc')

end GraphMinor.GM07
