/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusChartC2Transfer

/-!
# The horizontal projection commutes with the output chart transport

The proof of `lem:parametrix-error` (§7.1) works at the two-component fibre `ℂ²`, while the
chart calculus of the library is set up at `ℂ³` and carried to `ℂ²` by conjugation with the
isometric zero extension `ι_⊥` and the horizontal projection `π_⊥`
(`Global/TorusChartC2Transfer.lean`).  This module proves the commutation lemma that the
conjugation needs on the output side,
`extendStateC2 ∘ π_⊥ = π_⊥ ∘ outLocL2` (`extendStateC2_wholePlaneHorizontalProjL2`): the chart
transport is a scalar multiplier followed by a measure-preserving substitution, so it acts
diagonally in the fibre.  `Global/TorusChartC2TransportedField.lean` uses it to bring the
three-component chart action bridge down to two components.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set

namespace TorusChartC2Transfer

open TorusChartL2
open LocalizedSummandAlgebra
open TorusSupportedH2Output
open WholePlaneHorizontalFibre

variable (p : WholePlane) (R : ℝ) (hR : 0 < R)

/-! ## The second fibre commutation lemma -/

/-- **The projection commutation lemma.**  Projecting after the three-component output
transport is the two-component output transport after projecting.  The chart transport is a
scalar multiplier followed by a measure-preserving substitution, so it acts diagonally in the
fibre. -/
theorem extendStateC2_wholePlaneHorizontalProjL2 (Y : WholePlaneC3L2) :
    extendStateC2 p R hR (wholePlaneHorizontalProjL2 Y) =
      horizontalProjL2 (wholePlaneOutputLocalizationL2 p R hR Y) := by
  rw [extendStateC2_apply]
  apply Lp.ext
  have hplane : ((wholePlaneVerticalZeroExtendL2 (wholePlaneHorizontalProjL2 Y) :
        WholePlaneC3L2) : WholePlane → C3) =ᵐ[volume]
      fun x ↦ verticalZeroExtendPoint
        (horizontalProjPoint ((Y : WholePlane → C3) x)) := by
    filter_upwards [wholePlaneVerticalZeroExtendL2_coe_ae (wholePlaneHorizontalProjL2 Y),
      wholePlaneHorizontalProjL2_coe_ae Y] with x h1 h2
    rw [h1, h2]
  have hrestrict :
      ((wholePlaneVerticalZeroExtendL2 (wholePlaneHorizontalProjL2 Y) : WholePlaneC3L2) :
          WholePlane → C3) =ᵐ[volume.restrict wholePlaneFundamentalBox]
        fun x ↦ verticalZeroExtendPoint
          (horizontalProjPoint ((Y : WholePlane → C3) x)) :=
    hplane.filter_mono (ae_mono Measure.restrict_le_self)
  have hpull : (fun q ↦ ((wholePlaneVerticalZeroExtendL2 (wholePlaneHorizontalProjL2 Y) :
        WholePlaneC3L2) : WholePlane → C3) (torusWholePlaneRepresentative q)) =ᵐ[
      transverseMeasure] fun q ↦ verticalZeroExtendPoint (horizontalProjPoint
        ((Y : WholePlane → C3) (torusWholePlaneRepresentative q))) :=
    measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae_eq_comp hrestrict
  filter_upwards [horizontalProjL2_coe_ae (wholePlaneOutputLocalizationL2 p R hR
      (wholePlaneVerticalZeroExtendL2 (wholePlaneHorizontalProjL2 Y))),
    wholePlaneOutputLocalizationL2_coe_ae p R hR
      (wholePlaneVerticalZeroExtendL2 (wholePlaneHorizontalProjL2 Y)),
    horizontalProjL2_coe_ae (wholePlaneOutputLocalizationL2 p R hR Y),
    wholePlaneOutputLocalizationL2_coe_ae p R hR Y, hpull] with q h1 h2 h3 h4 h5
  rw [h1, h2, h5, h3, h4, map_smul, map_smul, horizontalProjPoint_verticalZeroExtendPoint]

end TorusChartC2Transfer

end

end FastDynamo
