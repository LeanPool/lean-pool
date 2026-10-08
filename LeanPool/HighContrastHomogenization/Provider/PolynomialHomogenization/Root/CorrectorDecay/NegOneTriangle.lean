/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.FixedGapNegOneRestriction

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.CorrectorDecay.NegOneTriangle

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

private theorem memVectorL2_isLocalVecTest
    {d : ℕ} {V : Set (Vec d)} {psi : Vec d → Vec d}
    (hpsi : IsLocalVecTest V psi) : MemVectorL2 V psi := by
  have hglobal : MemLp psi 2 volume :=
    hpsi.contDiff.continuous.memLp_of_hasCompactSupport
      hpsi.hasCompactSupport
  simpa only [volumeMeasureOn] using
    hglobal.mono_measure (Measure.restrict_le_self)

/-- The fail-closed normalized negative-one norm is subadditive on local
square-integrable vector fields. -/
theorem negOneNorm_add_le_of_memVectorL2
    {d : ℕ} {V : Set (Vec d)} (F G : Vec d → Vec d)
    (hF : MemVectorL2 V F) (hG : MemVectorL2 V G) :
    negOneNorm V (fun x ↦ F x + G x) ≤
      negOneNorm V F + negOneNorm V G := by
  unfold negOneNorm
  apply iSup_le
  intro test
  have htestL2 : MemVectorL2 V test.1 :=
    memVectorL2_isLocalVecTest test.2.1
  have hFint : IntegrableOn (fun x ↦ vecDot (F x) (test.1 x)) V volume :=
    integrableOn_vecDot_of_memVectorL2 hF htestL2
  have hGint : IntegrableOn (fun x ↦ vecDot (G x) (test.1 x)) V volume :=
    integrableOn_vecDot_of_memVectorL2 hG htestL2
  have hAddInt : IntegrableOn
      (fun x ↦ vecDot (F x + G x) (test.1 x)) V volume := by
    simpa only [vecDot_add_left] using! hFint.add hGint
  calc
    dualPairing V (fun x ↦ F x + G x) test.1 =
        ENNReal.ofReal
          (volumeAverage V (fun x ↦
            vecDot (F x + G x) (test.1 x))) :=
      dualPairing_eq_ofReal V _ _ hAddInt
    _ = ENNReal.ofReal
          (volumeAverage V (fun x ↦ vecDot (F x) (test.1 x)) +
            volumeAverage V (fun x ↦ vecDot (G x) (test.1 x))) := by
      congr 1
      simpa only [vecDot_add_left] using! volumeAverage_add hFint hGint
    _ ≤ ENNReal.ofReal
          (volumeAverage V (fun x ↦ vecDot (F x) (test.1 x))) +
        ENNReal.ofReal
          (volumeAverage V (fun x ↦ vecDot (G x) (test.1 x))) :=
      ENNReal.ofReal_add_le
    _ = dualPairing V F test.1 + dualPairing V G test.1 := by
      rw [dualPairing_eq_ofReal V F test.1 hFint,
        dualPairing_eq_ofReal V G test.1 hGint]
    _ ≤ (⨆ psi : {psi : Vec d → Vec d //
          IsLocalVecTest V psi ∧ h1NormSq V psi ≤ 1},
            dualPairing V F psi.1) +
        (⨆ psi : {psi : Vec d → Vec d //
          IsLocalVecTest V psi ∧ h1NormSq V psi ≤ 1},
            dualPairing V G psi.1) :=
      add_le_add (le_iSup (fun psi : {psi : Vec d → Vec d //
        IsLocalVecTest V psi ∧ h1NormSq V psi ≤ 1} ↦
          dualPairing V F psi.1) test)
        (le_iSup (fun psi : {psi : Vec d → Vec d //
          IsLocalVecTest V psi ∧ h1NormSq V psi ≤ 1} ↦
          dualPairing V G psi.1) test)

/-- Subadditivity descends to the quotient-safe local Hilbert-vector class. -/
theorem localNegOneNorm_add_le
    {d : ℕ} {V : Set (Vec d)} (F G : HilbertVectorL2 V) :
    localNegOneNorm V (F + G) ≤
      localNegOneNorm V F + localNegOneNorm V G := by
  let f : Vec d → Vec d := fun x ↦ (F x).toVec
  let g : Vec d → Vec d := fun x ↦ (G x).toVec
  have hF : MemVectorL2 V f := by
    exact MemLp.ae_eq
      (coeFn_hilbertVectorL2ToVectorL2 (U := V) F)
      (Lp.memLp (hilbertVectorL2ToVectorL2 (U := V) F))
  have hG : MemVectorL2 V g := by
    exact MemLp.ae_eq
      (coeFn_hilbertVectorL2ToVectorL2 (U := V) G)
      (Lp.memLp (hilbertVectorL2ToVectorL2 (U := V) G))
  have hadd :
      (fun x ↦ ((F + G) x).toVec) =ᵐ[volumeMeasureOn V]
        fun x ↦ f x + g x := by
    filter_upwards [Lp.coeFn_add F G] with x hx
    rw [hx]
    rfl
  calc
    localNegOneNorm V (F + G) =
        negOneNorm V (fun x ↦ f x + g x) := by
      unfold localNegOneNorm
      exact negOneNorm_eq_of_ae_eq_on hadd
    _ ≤ negOneNorm V f + negOneNorm V g :=
      negOneNorm_add_le_of_memVectorL2 f g hF hG
    _ = localNegOneNorm V F + localNegOneNorm V G := rfl

/-- The inverse-side-length normalized negative-one norm is subadditive. -/
theorem triadicScaledNegOneNorm_add_le
    {d : ℕ} (n : ℤ)
    (F G : HilbertVectorL2 (openCubeSet (originCube d n))) :
    triadicScaledNegOneNorm n (F + G) ≤
      triadicScaledNegOneNorm n F + triadicScaledNegOneNorm n G := by
  unfold triadicScaledNegOneNorm
  calc
    ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
          localNegOneNorm (openCubeSet (originCube d n)) (F + G) ≤
        ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
          (localNegOneNorm (openCubeSet (originCube d n)) F +
            localNegOneNorm (openCubeSet (originCube d n)) G) :=
      mul_le_mul_right (localNegOneNorm_add_le F G) _
    _ = ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
          localNegOneNorm (openCubeSet (originCube d n)) F +
        ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
          localNegOneNorm (openCubeSet (originCube d n)) G := by
      rw [mul_add]

end

end HighContrast
end HCPolySupport
