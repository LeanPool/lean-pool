/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffinePullbackCoeffSpace

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.RealTranslationCoeffSpace

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Real translations of qualitative coefficient samples

The stochastic action uses integer translations, but deterministic response
covariance also needs translation by an arbitrary vector.  This module
packages that deterministic operation without attaching any stationarity
claim to it.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Translation of a coefficient sample by an arbitrary vector. -/
@[expose]
def realTranslateCoeff (z : Vec d) (a : CoeffSpace d) : CoeffSpace d where
  val := a.1.compMeasurePreserving (fun x : Vec d => x + z)
    (measurePreserving_add_right (volume : Measure (Vec d)) z)
  property := by
    let hmp := measurePreserving_add_right (volume : Measure (Vec d)) z
    have hrep :
        (⇑(a.1.compMeasurePreserving (fun x : Vec d => x + z) hmp) :
            CoeffField d) =ᵐ[volume] fun x ↦ a.1 (x + z) :=
      AEEqFun.coeFn_compMeasurePreserving _ _
    exact (a.2.comp_add_right z).congr hrep.symm

/-- The real translation has the expected representative almost everywhere. -/
theorem realTranslateCoeff_ae (z : Vec d) (a : CoeffSpace d) :
    (⇑(realTranslateCoeff z a).1 : CoeffField d) =ᵐ[volume]
      fun x ↦ a.1 (x + z) := by
  change
    (⇑(a.1.compMeasurePreserving (fun x : Vec d => x + z)
      (measurePreserving_add_right (volume : Measure (Vec d)) z)) :
        CoeffField d) =ᵐ[volume] fun x ↦ a.1 (x + z)
  exact AEEqFun.coeFn_compMeasurePreserving _ _

/-- Affine pullback commutes with replacing a coefficient representative by
an almost-everywhere equal one. -/
theorem affineCoefficient_congr_ae_global
    (L : Mat d) (hL : IsUnit L.det) {a b : CoeffField d}
    (hab : a =ᵐ[volume] b) :
    affineCoefficient L hL a =ᵐ[volume] affineCoefficient L hL b :=
  affineCoefficient_congr_ae L hL hab

/-- Skew-centring, the affine gauge, and translation by a fixed vector all
respect replacing a coefficient representative by an almost-everywhere equal
one, on any set.  Every residual-frame provider performs exactly this
transport, so it is stated once here. -/
theorem affineTranslatedCenteredCoeff_congr_ae
    (L : Mat d) (hL : IsUnit L.det) (b : Mat d) {u v : CoeffField d}
    (huv : u =ᵐ[volume] v) (c : Vec d) (V : Set (Vec d)) :
    (fun y : Vec d ↦ affineCoefficient L hL (fun w ↦ u w - b) (y + c))
      =ᵐ[volumeMeasureOn V]
      fun y : Vec d ↦ affineCoefficient L hL (fun w ↦ v w - b) (y + c) := by
  have hcentered : (fun w ↦ u w - b) =ᵐ[volume] fun w ↦ v w - b := by
    filter_upwards [huv] with w hw
    rw [hw]
  exact ae_restrict_of_ae
    ((measurePreserving_add_right (volume : Measure (Vec d))
        c).quasiMeasurePreserving.tendsto_ae
      (affineCoefficient_congr_ae_global L hL hcentered))

end

end RowSupply
end HighContrast
end HCPolySupport
