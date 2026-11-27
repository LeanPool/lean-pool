/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioGraph

/-!
# Selfadjointness under full-domain unitary transport

The adjoint graph is characterized against every pair of the original
graph. Transport preserves those pairings and the complete domain, hence
preserves selfadjointness without a bounded-operator assumption.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem unitaryPartialTransport_dense_domain (V : E ≃ₗᵢ[ℂ] F) (T : E →ₗ.[ℂ] E)
    (hT : Dense (T.domain : Set E)) :
    Dense ((unitaryPartialTransport V T).domain : Set F) := by
  have he : ((unitaryPartialTransport V T).domain : Set F) =
      Set.range (fun x : T.domain => V (x : E)) := by
    ext y
    constructor
    · intro hy
      exact ⟨⟨V.symm y, hy⟩, V.apply_symm_apply y⟩
    · rintro ⟨x, rfl⟩
      change V.symm (V (x : E)) ∈ T.domain
      rw [V.symm_apply_apply]
      exact x.property
  rw [he]
  exact V.surjective.denseRange.comp hT.denseRange_val V.continuous

theorem unitaryPartialTransport_isSelfAdjoint (V : E ≃ₗᵢ[ℂ] F) (T : E →ₗ.[ℂ] E)
    (hT : IsSelfAdjoint T) : IsSelfAdjoint (unitaryPartialTransport V T) := by
  have hd := hT.dense_domain
  have hD := unitaryPartialTransport_dense_domain V T hd
  have hTeq : T.adjoint = T := hT
  change (unitaryPartialTransport V T).adjoint = unitaryPartialTransport V T
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hD]
  ext p
  rcases p with ⟨x, y⟩
  rw [Submodule.mem_adjoint_iff, unitaryPartialTransport_mem_graph]
  constructor
  · intro hxy
    have hp : (V.symm x, V.symm y) ∈ T.graph.adjoint := by
      rw [Submodule.mem_adjoint_iff]
      intro a b hab
      have hab' : (V a, V b) ∈ (unitaryPartialTransport V T).graph := by
        rw [unitaryPartialTransport_mem_graph, V.symm_apply_apply, V.symm_apply_apply]
        exact hab
      have h := hxy (V a) (V b) hab'
      have hx : inner ℂ b (V.symm x) = inner ℂ (V b) x := by
        simpa only [LinearIsometryEquiv.apply_symm_apply] using
          (V.inner_map_map b (V.symm x)).symm
      have hy : inner ℂ a (V.symm y) = inner ℂ (V a) y := by
        simpa only [LinearIsometryEquiv.apply_symm_apply] using
          (V.inner_map_map a (V.symm y)).symm
      simpa only [hx, hy] using h
    rwa [← LinearPMap.adjoint_graph_eq_graph_adjoint hd, hTeq] at hp
  · intro hxy a b hab
    have hp : (V.symm x, V.symm y) ∈ T.graph.adjoint := by
      rw [← LinearPMap.adjoint_graph_eq_graph_adjoint hd, hTeq]
      exact hxy
    have hab' := (unitaryPartialTransport_mem_graph V T a b).mp hab
    have h := (Submodule.mem_adjoint_iff _ _).mp hp (V.symm a) (V.symm b) hab'
    simpa only [LinearIsometryEquiv.inner_map_map] using h

omit [CompleteSpace E] [CompleteSpace F] in
theorem unitaryPartialTransport_inner_nonneg (V : E ≃ₗᵢ[ℂ] F) (T : E →ₗ.[ℂ] E)
    (hT : ∀ x y : E, (x, y) ∈ T.graph → 0 ≤ (inner ℂ x y).re)
    (x y : F) (hxy : (x, y) ∈ (unitaryPartialTransport V T).graph) :
    0 ≤ (inner ℂ x y).re := by
  have h := hT (V.symm x) (V.symm y) ((unitaryPartialTransport_mem_graph V T x y).mp hxy)
  simpa only [LinearIsometryEquiv.inner_map_map] using h

end VacuumBellSeparation
