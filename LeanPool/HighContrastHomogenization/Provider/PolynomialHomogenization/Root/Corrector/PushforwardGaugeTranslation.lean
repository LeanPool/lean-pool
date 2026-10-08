/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardTransport
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSkewLaw

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardGaugeTranslation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The real-vector gauge conjugation

An integer translation of the physical sample becomes, in the normalized
gauge, a translation by the **real** vector `L⁻¹ z`.  This is the identity the
translated-gradient identification engine has to be fed at, and it is the piece
that was not otherwise available: the integer conjugation requires the matrix
to carry `ℤ^d` into `ℤ^d`, which the normalized root does not.

The route is elementary once the pieces are separated: the recentring and the
rescaling commute with the *integer* translation (both already available), and
the affine change of variables converts a translation by `w` on the physical
side into a translation by `L⁻¹ w` on the normalized side, pointwise.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## Rescaling commutes with the integer translation -/

/-- Positive scalar multiplication commutes with integer translation. -/
theorem translateCoeff_positiveScale_comm (z : Fin d → ℤ) (a : CoeffSpace d)
    (c : ℝ) (hc : 0 < c) :
    translateCoeff z (a.positiveScale c hc) =
      (translateCoeff z a).positiveScale c hc := by
  have hshift :=
    (measurePreserving_add_right (volume : Measure (Vec d))
      (Source.AKL.intTranslation z)).quasiMeasurePreserving.tendsto_ae
        (CoeffSpace.positiveScale_ae c hc a)
  apply Subtype.ext
  apply AEEqFun.ext
  filter_upwards [Source.AKL.translateField_ae z (a.positiveScale c hc).1,
    hshift, CoeffSpace.positiveScale_ae c hc (translateCoeff z a),
    Source.AKL.translateField_ae z a.1] with x hleft hscale hright hraw
  change (Source.AKL.translateField z (a.positiveScale c hc).1) x =
    ((translateCoeff z a).positiveScale c hc).1 x
  change (a.positiveScale c hc).1 (x + Source.AKL.intTranslation z) =
    c • a.1 (x + Source.AKL.intTranslation z) at hscale
  change (translateCoeff z a).1 x =
    a.1 (x + Source.AKL.intTranslation z) at hraw
  rw [hleft, hscale, hright, ← hraw]

/-- The normalized recentring commutes with the integer translation. -/
theorem translateCoeff_normalizedCenteredCoeff [NeZero d] (a : CoeffSpace d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) (z : Fin d → ℤ) :
    normalizedCenteredCoeff (translateCoeff z a) abar hS =
      translateCoeff z (normalizedCenteredCoeff a abar hS) := by
  simp only [normalizedCenteredCoeff]
  rw [translateCoeff_positiveScale_comm]
  exact congrArg (CoeffSpace.positiveScale _ (normalizedRootScale_pos hS))
    (Quenched.translateCoeff_subSkew z a (matTranspose_skewPart abar)).symm

/-! ## The affine change of variables converts the translation -/

/-- **P3, pointwise.**  Translating the argument of a coefficient field by `w`
before the affine pullback is translating the pullback by `L⁻¹ w`. -/
theorem affineCoefficient_translate_apply [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (c : CoeffField d) (w y : Vec d) :
    affineCoefficient (gaugeRoot abar) (isUnit_det_gaugeRoot hS)
        (fun x ↦ c (x + w)) y =
      affineCoefficient (gaugeRoot abar) (isUnit_det_gaugeRoot hS) c
        (y + matVecMul (gaugeRoot abar)⁻¹ w) := by
  simp only [affineCoefficient_apply]
  rw [matVecMul_add, gaugeRoot_apply_inv hS]

/-! ## The gauge conjugation -/

/-- **The real-vector gauge conjugation.**  An integer translation of the
physical sample is, in the normalized gauge, the translation by
`matVecMul (gaugeRoot abar)⁻¹ (Source.AKL.intTranslation z)` — a real vector,
which is exactly what the identification engine's free translation binder
accepts. -/
theorem gaugeCoeff_translateCoeff_ae [NeZero d] (a : CoeffSpace d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) (z : Fin d → ℤ) :
    gaugeCoeff (translateCoeff z a) abar hS =ᵐ[volume]
      fun y ↦ gaugeCoeff a abar hS
        (y + matVecMul (gaugeRoot abar)⁻¹ (Source.AKL.intTranslation z)) := by
  have h2 : affineCoefficient (gaugeRoot abar) (isUnit_det_gaugeRoot hS)
        (fun x ↦ (⇑(normalizedCenteredCoeff a abar hS).1 : CoeffField d)
          (x + Source.AKL.intTranslation z)) =
      fun y ↦ gaugeCoeff a abar hS
        (y + matVecMul (gaugeRoot abar)⁻¹ (Source.AKL.intTranslation z)) := by
    funext y
    exact affineCoefficient_translate_apply hS _ _ _
  simp only [gaugeCoeff] at h2 ⊢
  rw [← h2, translateCoeff_normalizedCenteredCoeff]
  exact affineCoefficient_congr_ae _ _
    (Source.AKL.translateField_ae z (normalizedCenteredCoeff a abar hS).1)

end

end Root
end HighContrast
end HCPolySupport
