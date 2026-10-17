/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ShellSumLayerFlip

/-!
# ShellSumLayerZeroEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The layer-zero term of the shell decomposition is the (J4) constant

ABK26, `a.j.nondeg` and `e.perturb.assumption`.

`ShellSumLayerFlip.lean` reduces the shell-sum corrector energy to the diagonal
sum `Σ_{k ∈ (n,m]} ‖P 𝐟_k‖²` on the layer carrier.  This module evaluates the
`k = 0` term:

`‖P 𝐟_0‖² = c⋆ (log 3)`  at a unit direction,

by transporting to the single-shell path carrier along the equivariant
coordinate map `F ↦ F 0` and reading
`FreshShellCorrectorEnergy.integral_normSq_valuePathCorrectorRepr_eq`.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3 (ABKModel)

noncomputable section

variable {d : ℕ}

/-- **Reading layer zero pushes the layer law onto the fresh-shell path law.** -/
theorem measurePreserving_seqPathCoord_zero (M : ABKModel d) :
    MeasurePreserving (fun F : ℤ → C(Vec d, Mat d) => F 0) (seqPathLaw M.P).toMeasure
      (zeroShellValuePathLaw M.P).toMeasure := by
  refine ⟨measurable_pi_apply 0, ?_⟩
  rw [seqPathLaw_toMeasure, zeroShellValuePathLaw_toMeasure_eq_map_valuePath,
    Measure.map_map (measurable_pi_apply 0) measurable_seqValuePath,
    ShellField.zeroShellLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_map ShellField.measurable_valuePath
      ShellField.measurable_zeroShellMap]
  rfl

/-- The transported fresh-shell forcing is the layer-zero forcing. -/
theorem carrierTransport_valuePathForcingL2 (M : ABKModel d) {e : Vec d}
    (he : Book.Ch02.vecNorm e = 1) :
    carrierTransport (HilbertVec d) (measurePreserving_seqPathCoord_zero M)
        (valuePathForcingL2 M he)
      = layerForcingL2 M e 0 := by
  have hcomp := Lp.toLp_compMeasurePreserving (p := 2)
    (f := fun F : ℤ → C(Vec d, Mat d) => F 0) (memLp_two_valuePathForcing M he)
    (measurePreserving_seqPathCoord_zero M)
  refine hcomp.trans ?_
  exact (MemLp.toLp_eq_toLp_iff _ (memLp_two_layerForcing M e 0)).2
    (Filter.Eventually.of_forall fun _ => rfl)

/-- **The layer-zero corrector energy is the (J4) constant.**

The `k = 0` term of the layer decomposition of `e.perturb.assumption` equals
`c⋆ (log 3)` at a unit direction, `c⋆` the constant selected by `a.j.nondeg`. -/
theorem norm_sq_stationaryPotentialProjection_layerForcingL2_zero (M : ABKModel d)
    {e : Vec d} (he : Book.Ch02.vecNorm e = 1) :
    ‖stationaryPotentialProjection (μ := (seqPathLaw M.P).toMeasure)
        (layerForcingL2 M e 0)‖ ^ 2
      = Algsuperdiff.Section3.Disorder.cstar M * Real.log 3 := by
  have hnat := norm_stationaryPotentialProjection_carrierTransport
    (d := d) (measurePreserving_seqPathCoord_zero M)
    (fun (_ : Vec d) (_ : ℤ → C(Vec d, Mat d)) => rfl) (valuePathForcingL2 M he)
  rw [carrierTransport_valuePathForcingL2 M he] at hnat
  have hcorr : ‖stationaryPotentialProjection
      (μ := (zeroShellValuePathLaw M.P).toMeasure) (valuePathForcingL2 M he)‖
      = ‖valuePathPotentialCorrector M he‖ := by
    rw [valuePathPotentialCorrector, norm_neg]
  rw [hnat, hcorr, ← integral_normSq_valuePathCorrectorRepr_eq_norm_sq M he]
  exact integral_normSq_valuePathCorrectorRepr_eq M he

end

end Algsuperdiff.Section3.Provider.Corrector
