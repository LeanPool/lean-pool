/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Composition on the actual maximal partial-operator domain

Mathlib's `LinearPMap.comp` preserves the entire domain of its right operand
and asks for a range-containment proof. The definition here first restricts
to precisely the vectors whose image belongs to the left operand's domain.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {E F G : Type*} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]

/-- Actual domain of a composition, before restricting either operator. -/
def partialCompDomain (g : F →ₗ.[ℂ] G) (f : E →ₗ.[ℂ] F) : Submodule ℂ E where
  carrier := {x | ∃ hx : x ∈ f.domain, f ⟨x, hx⟩ ∈ g.domain}
  zero_mem' := by
    refine ⟨f.domain.zero_mem, ?_⟩
    change f 0 ∈ g.domain
    rw [LinearPMap.map_zero]
    exact g.domain.zero_mem
  add_mem' := by
    rintro x y ⟨hx, hfx⟩ ⟨hy, hfy⟩
    refine ⟨f.domain.add_mem hx hy, ?_⟩
    change f (⟨x, hx⟩ + ⟨y, hy⟩) ∈ g.domain
    rw [LinearPMap.map_add]
    exact g.domain.add_mem hfx hfy
  smul_mem' := by
    rintro c x ⟨hx, hfx⟩
    refine ⟨f.domain.smul_mem c hx, ?_⟩
    change f (c • ⟨x, hx⟩) ∈ g.domain
    rw [LinearPMap.map_smul]
    exact g.domain.smul_mem c hfx

theorem partialCompDomain_le (g : F →ₗ.[ℂ] G) (f : E →ₗ.[ℂ] F) :
    partialCompDomain g f ≤ f.domain := fun _ hx => hx.choose

/-- Linear map for the partial comp, of type `E →ₗ.[ℂ] G`. -/
noncomputable def partialComp (g : F →ₗ.[ℂ] G) (f : E →ₗ.[ℂ] F) : E →ₗ.[ℂ] G :=
  g.comp (f.domRestrict (partialCompDomain g f)) fun x => by
    obtain ⟨hx, hfx⟩ := x.property.1
    change f ⟨(x : E), x.property.2⟩ ∈ g.domain
    exact hfx

theorem partialComp_domain (g : F →ₗ.[ℂ] G) (f : E →ₗ.[ℂ] F) :
    (partialComp g f).domain = partialCompDomain g f := by
  change partialCompDomain g f ⊓ f.domain = partialCompDomain g f
  exact inf_eq_left.mpr (partialCompDomain_le g f)

/-- Evaluation uses the literal original operators on the actual domain witnesses. -/
theorem partialComp_apply (g : F →ₗ.[ℂ] G) (f : E →ₗ.[ℂ] F)
    (x : (partialComp g f).domain) (hx : (x : E) ∈ f.domain)
    (hfx : f ⟨x, hx⟩ ∈ g.domain) :
    partialComp g f x = g ⟨f ⟨x, hx⟩, hfx⟩ := rfl

end VacuumBellSeparation
