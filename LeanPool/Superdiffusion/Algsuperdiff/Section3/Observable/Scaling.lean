/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.Dilation

/-!
# Scaling

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Section 3 cube normalization

This file supplies the literal triadic change of variables used to feed a
coefficient restriction on the centered cube `square_m` into the already
frozen unit-cube observables.  The normalized coefficient is the pullback

`x ↦ a (3^m x)`

on `square_0`.  It is constructed by CoarseGraining's public `CoeffOn.dilate`;
hence its ellipticity constants are the same as those of the source restriction
and its representative agrees almost everywhere with the displayed pullback.

## References

* ABK26, the scale-invariant cube conventions preceding Section 2.5.
* ABK26, Section 3, where `square_m` denotes `originCube d m`.
-/

namespace Algsuperdiff.Section3.Observable

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

/-- Dilation by `3^(-m)` sends the centered cube `square_m` to the unit
centered cube `square_0`. -/
theorem dilateOriginCube_neg_scale (d : ℕ) (m : ℤ) :
    dilateCube (-m) (originCube d m) = originCube d 0 := by
  simp [dilateCube, originCube]

/-- The exact unit-cube pullback of a coefficient restriction on `square_m`.

The underlying representative is `x ↦ a (3^m x)` almost everywhere on
`square_0`.  There is no fallback branch and no finite-scale surrogate. -/
noncomputable def unitRescaledCoeffOn {d : ℕ} (m : ℤ)
    (a : CoeffOn (cubeDomain (originCube d m))) :
    CoeffOn (cubeDomain (originCube d 0)) :=
  let b := CoeffOn.dilate (-m) a
  { toCoeffField := b.toCoeffField
    lam := b.lam
    Lam := b.Lam
    lam_pos := b.lam_pos
    lam_le_Lam := b.lam_le_Lam
    aeStronglyMeasurable := by
      intro i j
      simpa [dilateOriginCube_neg_scale] using b.aeStronglyMeasurable i j
    aeElliptic := by
      simpa [dilateOriginCube_neg_scale] using b.aeElliptic }

/-- The representative of `unitRescaledCoeffOn` is exactly the pullback
`x ↦ a(3^m x)` almost everywhere on the unit cube. -/
theorem unitRescaledCoeffOn_toCoeffField_ae_eq {d : ℕ} (m : ℤ)
    (a : CoeffOn (cubeDomain (originCube d m))) :
    (unitRescaledCoeffOn m a).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d 0))]
        dilateCoeffField (-m) a.toCoeffField := by
  simpa [unitRescaledCoeffOn, dilateOriginCube_neg_scale] using
    (CoeffOn.dilate_isCubeDilation (-m) a).coeff_ae_eq

/-- A compatible coefficient family on `square_m`, dilated by `3^(-m)`,
agrees on `square_0` with `unitRescaledCoeffOn`.  This is the bridge used to
read every unit-cube observable as the corresponding literal cube-`m`
quantity. -/
theorem dilatedFamily_root_aeeq_unitRescaledCoeffOn {d : ℕ} (m : ℤ)
    (a : CoeffOn (cubeDomain (originCube d m))) (F : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d m)) a) :
    CoeffOn.AEEq
      ((TriadicCoeffFamily.dilate (-m) F).coeffOn (originCube d 0))
      (unitRescaledCoeffOn m a) := by
  have hfamily :
      ((TriadicCoeffFamily.dilate (-m) F).coeffOn (originCube d 0)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (originCube d 0))]
          dilateCoeffField (-m) (F.coeffOn (originCube d m)).toCoeffField := by
    have hDilation :=
      (TriadicCoeffFamily.isDilation_dilate (-m) F (originCube d m)).coeff_ae_eq
    rw [dilateOriginCube_neg_scale] at hDilation
    exact hDilation
  have hpull :
      dilateCoeffField (-m) (F.coeffOn (originCube d m)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (originCube d 0))]
          dilateCoeffField (-m) a.toCoeffField := by
    simpa [dilateCoeffField, dilateOriginCube_neg_scale] using!
      (eventuallyEq_comp_undilate_of_ae_eq (-m) hF)
  exact hfamily.trans
    (hpull.trans (unitRescaledCoeffOn_toCoeffField_ae_eq m a).symm)

end

end Algsuperdiff.Section3.Observable
