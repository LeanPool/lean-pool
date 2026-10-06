/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.GaugeFrameEccentricity
public import LeanPool.HighContrastHomogenization.Support.Geometry.Translation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.NegSobolevTranslation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.EnergyPrice.TranslatedCubeEnergyPrice

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Gate R1: the price on a translate of a triadic cube

At the frozen witness the gauge domain is a *translate by an arbitrary
real vector* of a triadic cube (`matImage_inv_affineImage`), and the
Chapter 3 cube carriers (`CoeffFamily`, `IsForcedEquation`,
`DirichletForcedCubeSolution`) are hard-indexed by genuine `TriadicCube`s, so
the estimate must be transported rather than restated.

This file supplies the transport for the two carriers the *price* uses — the
extended-real coefficient-energy average and the Euclidean fractional norm —
and assembles the translated-cube inhabitant of
`GaugePhysicalEnergyPriceAtWitness`.

`eVolumeAverage_translateSet` and its `lintegral` helper exist only as
`private` declarations elsewhere, so they are re-proved here.
-/

namespace HCPolySupport
namespace HighContrast
namespace EnergyPrice

open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Translation transport of the extended-real carriers -/

/-- Lower integrals transport along a translation. -/
theorem lintegral_translateSet (z : Vec d) (V : Set (Vec d))
    (g : Vec d → ℝ≥0∞) :
    ∫⁻ x in translateSet z V, g x ∂volume =
      ∫⁻ x in V, g (x + z) ∂volume := by
  have hmp := measurePreserving_addRight_restrict_translateSet z V
  have hemb : MeasurableEmbedding (fun x : Vec d => x + z) :=
    (MeasurableEquiv.addRight z).measurableEmbedding
  exact (hmp.lintegral_comp_emb hemb g).symm

/-- Volume averages transport along a translation. -/
theorem eVolumeAverage_translateSet (z : Vec d) (V : Set (Vec d))
    (g : Vec d → ℝ≥0∞) :
    eVolumeAverage (translateSet z V) g =
      eVolumeAverage V (fun x => g (x + z)) := by
  unfold eVolumeAverage
  rw [lintegral_translateSet, volume_translateSet_eq]

/-- **The energy average on a translated set.** -/
theorem eVolumeAverage_coefficientEnergyDensity_translateSet
    (z : Vec d) (V : Set (Vec d)) (b : CoeffField d) (F : Vec d → Vec d) :
    eVolumeAverage (translateSet z V) (fun x =>
        ENNReal.ofReal (coefficientEnergyDensity b F x)) =
      eVolumeAverage V (fun y =>
        ENNReal.ofReal
          (coefficientEnergyDensity (fun w => b (w + z))
            (fun w => F (w + z)) y)) := by
  rw [eVolumeAverage_translateSet]
  rfl

/-- **The fractional norm on a translated set**, in the `F (· + z)`
direction. -/
theorem hsNormSq_translateSet_add (z : Vec d) (V : Set (Vec d)) (s : ℝ)
    (F : Vec d → Vec d) :
    hsNormSq (translateSet z V) s F =
      hsNormSq V s (fun x => F (x + z)) := by
  have h := RowSupply.hsNormSq_translateSet z V s (fun x => F (x + z))
  have hfun : (fun x : Vec d => (fun y : Vec d => F (y + z)) (x - z)) = F := by
    funext x
    simp
  rwa [hfun] at h

/-! ## The translated-cube price -/

end

end EnergyPrice
end HighContrast
end HCPolySupport
