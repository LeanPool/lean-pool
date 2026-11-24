/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM12.Section4ParametrizedContactDisc
import LeanPool.GraphMinor.GM12.Section4SmallSurfaceCopy
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Contact-disc shrinking in arbitrary surface universes

The target-disc construction in XII (4.5), page 253, can be
made on a small homeomorphic copy of the closed surface.
Carry the disc, its boundary parameters, and its marks there,
shrink it, and carry the resulting disc and parameters back.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Shrink a marked disc while retaining its boundary parameters,
in any universe, as needed for XII (4.5), page 253. -/
theorem exists_contact_disc_preserving_param_univ
    {S : Type*} [TopologicalSpace S] (hS : IsClosedSurface S)
    {D N : Set S} (hD : IsClosedDisc D) (φ : Circle ≃ₜ discBd D)
    (hN : N ⊆ discBd D) (hfin : N.Finite) (hne : N.Nonempty) :
    ∃ (Q : Set S) (p : Circle → S), IsClosedDisc Q ∧ Q ⊆ D ∧ Q ∩ discBd D = N ∧
      N ⊆ discBd Q ∧ Continuous p ∧ Function.Injective p ∧ range p = discBd Q ∧
      ∀ w, (φ w).val ∈ N → p w = (φ w).val := by
  classical
  obtain ⟨S₀, t₀, ⟨e⟩, hS₀⟩ := exists_small_closed_surface_copy hS
  let : TopologicalSpace S₀ := t₀
  let : T2Space S₀ := hS₀.2.1
  obtain ⟨hD₀, hbd₀⟩ := hD.image e.continuous.continuousOn e.symm.continuous.continuousOn
    (fun z _ => e.symm_apply_apply z)
  let φ₀ : Circle ≃ₜ discBd (e '' D) :=
    φ.trans ((e.image (discBd D)).trans (Homeomorph.setCongr hbd₀.symm))
  have hN₀ : e '' N ⊆ discBd (e '' D) := by
    rw [hbd₀]
    exact image_mono hN
  obtain ⟨Q₀, p₀, hQ₀, hQD₀, hQN₀, hNb₀, hpc₀, hpi₀, hpr₀, hfix₀⟩ :=
    exists_contact_disc_preserving_param hD₀ φ₀ hN₀ (hfin.image e) (hne.image e)
  obtain ⟨hQ, hQbd⟩ := hQ₀.image e.symm.continuous.continuousOn e.continuous.continuousOn
    (fun z _ => e.apply_symm_apply z)
  have hQD : e.symm '' Q₀ ⊆ D := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hQD₀ hz
    simpa only [e.symm_apply_apply] using hw
  have hQN : e.symm '' Q₀ ∩ discBd D = N := by
    apply e.injective.image_injective
    rw [image_inter e.injective, hbd₀.symm]
    have hEq : e '' (e.symm '' Q₀) = Q₀ := by
      simp only [image_image, e.apply_symm_apply, image_id']
    rw [hEq, hQN₀]
  have hNb : N ⊆ discBd (e.symm '' Q₀) := by
    intro x hx
    rw [hQbd]
    exact ⟨e x, hNb₀ (mem_image_of_mem e hx), e.symm_apply_apply x⟩
  have hpr : range (e.symm ∘ p₀) = discBd (e.symm '' Q₀) := by
    rw [range_comp, hpr₀, hQbd]
  refine ⟨e.symm '' Q₀, e.symm ∘ p₀, hQ, hQD, hQN, hNb,
    e.symm.continuous.comp hpc₀, e.symm.injective.comp hpi₀, hpr, ?_⟩
  intro w hw
  have hφ : (φ₀ w).val = e (φ w).val := rfl
  have hw₀ : (φ₀ w).val ∈ e '' N := hφ.symm ▸ mem_image_of_mem e hw
  change e.symm (p₀ w) = _
  rw [hfix₀ w hw₀, hφ, e.symm_apply_apply]

end GraphMinor.GM12
