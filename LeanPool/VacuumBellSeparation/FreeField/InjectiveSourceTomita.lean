/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceTomitaTestCore
public import LeanPool.VacuumBellSeparation.FreeField.WedgeSourceStandardness

/-!
# Source Tomita operators under actual complex injectivity

The construction uses precisely complex injectivity, so the separately
proved halfspace case is admissible. The full graph and its compact smooth
core are the same literal graph sets used for bounded regions.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Gaussian.HilbertComplexification

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
  (hκ : Function.Injective (complexSourceMap hm U))

/-- Injective source range equivalence of type `ComplexSourceHilbert hm U ≃ₗ[ℂ] (complexSourceMap
hm U).range`. -/
noncomputable def injectiveSourceRangeEquiv :
    ComplexSourceHilbert hm U ≃ₗ[ℂ] (complexSourceMap hm U).range :=
  LinearEquiv.ofInjective (complexSourceMap hm U).toLinearMap hκ

/-- Injective source Tomita. -/
noncomputable def injectiveSourceTomita :
    Lp ℂ 2 (oneParticleMeasure m) →ₛₗ.[starRingEnd ℂ] Lp ℂ 2 (oneParticleMeasure m) where
  domain := (complexSourceMap hm U).range
  toFun := (complexSourceMap hm U).toLinearMap.comp
    (conjugation.toLinearEquiv.toLinearMap.comp (injectiveSourceRangeEquiv hm U
      hκ).symm.toLinearMap)

theorem injectiveSourceTomita_source (z : ComplexSourceHilbert hm U) :
    injectiveSourceTomita hm U hκ (injectiveSourceRangeEquiv hm U hκ z) =
      complexSourceMap hm U (conjugation z) := by
  change complexSourceMap hm U (conjugation
    ((injectiveSourceRangeEquiv hm U hκ).symm (injectiveSourceRangeEquiv hm U hκ z))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem injectiveSourceTomita_graph (x y : Lp ℂ 2 (oneParticleMeasure m)) :
    (x, y) ∈ sourceTomitaGraph hm U ↔
      ∃ hx : x ∈ (injectiveSourceTomita hm U hκ).domain,
        injectiveSourceTomita hm U hκ ⟨x, hx⟩ = y := by
  constructor
  · rintro ⟨z, rfl, hy⟩
    exact ⟨⟨z, rfl⟩, (injectiveSourceTomita_source hm U hκ z).trans hy⟩
  · rintro ⟨hx, hy⟩
    refine ⟨(injectiveSourceRangeEquiv hm U hκ).symm ⟨x, hx⟩, ?_, hy⟩
    exact LinearEquiv.ofInjective_symm_apply _ _

theorem injectiveSourceTomita_dense_domain (hU : IsOpen U) (hne : U.Nonempty) :
    Dense ((injectiveSourceTomita hm U hκ).domain : Set (Lp ℂ 2 (oneParticleMeasure m))) :=
  complexSourceMap_denseRange_of_open hm U hU hne

theorem injectiveSourceTomita_closed_graph :
    IsClosed {p : Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m) |
      ∃ hp : p.1 ∈ (injectiveSourceTomita hm U hκ).domain,
        injectiveSourceTomita hm U hκ ⟨p.1, hp⟩ = p.2} := by
  have he : {p : Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m) |
      ∃ hp : p.1 ∈ (injectiveSourceTomita hm U hκ).domain,
        injectiveSourceTomita hm U hκ ⟨p.1, hp⟩ = p.2} = sourceTomitaGraph hm U := by
    ext p
    exact (injectiveSourceTomita_graph hm U hκ p.1 p.2).symm
  rw [he]
  exact sourceTomitaGraph_isClosed hm U

/-- The actual halfspace Tomita operator; injectivity has already been proved. -/
noncomputable def leftWedgeSourceTomita (ℓ : ℝ) :
    Lp ℂ 2 (oneParticleMeasure m) →ₛₗ.[starRingEnd ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  injectiveSourceTomita hm (leftWedgeTimeZero ℓ) (complexSourceMap_injective_leftWedgeTimeZero hm ℓ)

theorem leftWedgeSourceTomita_core (ℓ : ℝ) :
    closure (sourceTomitaTestGraph hm (leftWedgeTimeZero ℓ)) =
      {p : Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m) |
        ∃ hp : p.1 ∈ (leftWedgeSourceTomita hm ℓ).domain,
          leftWedgeSourceTomita hm ℓ ⟨p.1, hp⟩ = p.2} := by
  rw [closure_sourceTomitaTestGraph]
  ext p
  exact injectiveSourceTomita_graph hm (leftWedgeTimeZero ℓ) _ p.1 p.2

end VacuumBellSeparation
