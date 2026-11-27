/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeModularPowers
public import LeanPool.VacuumBellSeparation.FreeField.ModularWeightInclusion

/-!
# The genuine containing-left-wedge estimate on original completed sources

The bounded Gram compression estimate and the proved full wedge modular
identification yield an actual graph vector, with its norm bounded by the
smaller region's source weight. The region and source may be arbitrary;
the only localization premise is literal containment in the halfspace.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

variable {m : ℝ} (hm : 0 < m)

theorem physicalRapidityExponential_containing_leftWedge
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : U ⊆ leftWedgeTimeZero 0)
    {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) (z : ComplexSourceHilbert hm U) :
    ∃ χ : Lp ℂ 2 (oneParticleMeasure m),
      (complexSourceMap hm U z, χ) ∈ (physicalRapidityExponential hm c).graph ∧
        ‖χ‖ ≤ ‖sourceModularWeight hm U c z‖ := by
  refine ⟨leftWedgeSourcePolarUnitary hm 0
    (sourceModularWeight hm (leftWedgeTimeZero 0) c (complexSourceInclusion hm hU z)), ?_, ?_⟩
  · have h := physicalRapidityExponential_source_graph hm hc.le hc2 (complexSourceInclusion hm hU z)
    have he : complexSourceMap hm (leftWedgeTimeZero 0) (complexSourceInclusion hm hU z) =
        complexSourceMap hm U z :=
      DFunLike.congr_fun (complexSourceMap_comp_inclusion hm hU) z
    simpa only [he] using h
  · rw [LinearIsometryEquiv.norm_map]
    exact sourceModularWeight_inclusion_norm hm hU hc hc2 z

end VacuumBellSeparation
