/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.RatioRegularizerIndependence

/-!
# Full-domain unitary transport of partial operators

Transport uses the actual inverse-image domain. The universal resolvent
equation is invariant under this construction, hence it identifies both
the domain and values of the transported operator.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Linear map for the unitary partial transport, of type `F →ₗ.[ℂ] F`. -/
noncomputable def unitaryPartialTransport (V : E ≃ₗᵢ[ℂ] F) (T : E →ₗ.[ℂ] E) : F →ₗ.[ℂ] F :=
  V.toLinearEquiv.toLinearMap.compPMap
    (T.comp (V.symm.toLinearEquiv.toLinearMap.toPMap
      (T.domain.comap V.symm.toLinearEquiv.toLinearMap)) (fun x => x.property))

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem unitaryPartialTransport_domain (V : E ≃ₗᵢ[ℂ] F) (T : E →ₗ.[ℂ] E) :
    (unitaryPartialTransport V T).domain = T.domain.comap V.symm.toLinearEquiv.toLinearMap := rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem unitaryPartialTransport_apply (V : E ≃ₗᵢ[ℂ] F) (T : E →ₗ.[ℂ] E)
    (x : (unitaryPartialTransport V T).domain) :
    unitaryPartialTransport V T x = V (T ⟨V.symm x, x.property⟩) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem unitaryPartialTransport_resolvent (V : E ≃ₗᵢ[ℂ] F) (T : E →ₗ.[ℂ] E)
    (R : E →L[ℂ] E)
    (hR : ∀ x y : E, (∃ hy : y ∈ T.domain, y + T ⟨y, hy⟩ = x) ↔ R x = y)
    (x y : F) :
    (∃ hy : y ∈ (unitaryPartialTransport V T).domain,
      y + unitaryPartialTransport V T ⟨y, hy⟩ = x) ↔
        V (R (V.symm x)) = y := by
  constructor
  · rintro ⟨hy, hh⟩
    have heq : V.symm y + T ⟨V.symm y, hy⟩ = V.symm x := by
      apply V.injective
      simpa only [map_add, LinearIsometryEquiv.apply_symm_apply,
        unitaryPartialTransport_apply] using hh
    rw [(hR (V.symm x) (V.symm y)).mp ⟨hy, heq⟩,
      LinearIsometryEquiv.apply_symm_apply]
  · intro hh
    have heq : R (V.symm x) = V.symm y := by
      apply V.injective
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hh
    obtain ⟨hy, ht⟩ := (hR (V.symm x) (V.symm y)).mpr heq
    refine ⟨hy, ?_⟩
    simpa only [map_add, LinearIsometryEquiv.apply_symm_apply,
      unitaryPartialTransport_apply] using congrArg V ht

end VacuumBellSeparation
