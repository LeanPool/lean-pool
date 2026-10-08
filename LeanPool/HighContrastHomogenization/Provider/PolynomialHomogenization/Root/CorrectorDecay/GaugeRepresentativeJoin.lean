/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.PhysicalClassBridge

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.GaugeRepresentativeJoin

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The raw exact-root family retained by the canonical physical corrector
and the sanitized identity-gauge response family are a.e. the same family. -/
theorem rawIdentityFamily_aeeq
    {d : ℕ} [NeZero d] {a : CoeffSpace d} {abar : Mat d}
    (geom : RoundedGenerationAnalyticGeometry d)
    (hS : (symmPart abar).PosDef)
    (aRaw : Book.Ch03.CoeffFamily d)
    (hRaw : ∀ Q : TriadicCube d,
      (aRaw.coeffOn Q).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ⇑(normalizedCenteredCoeff a abar hS).1)
    (hI : (symmPart (1 : Mat d)).PosDef)
    (aIdentity : Book.Ch03.CoeffFamily d)
    (hIdentity : ∀ Q : TriadicCube d,
      (aIdentity.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace (1 : Mat d) hI
          (exactGaugeCoeffSpace a abar hS)).1 : CoeffField d)) :
    Book.Ch02.TriadicCoeffFamily.AEEq aRaw aIdentity := by
  intro Q
  unfold Book.Ch02.CoeffOn.AEEq
  rw [hRaw Q, hIdentity Q]
  have hcentered := identityCenteredCoeffSpace_ae geom hI
    (exactGaugeCoeffSpace a abar hS)
  have hgauge := exactGaugeCoeffSpace_ae a abar hS
  exact ae_restrict_of_ae (hgauge.symm.trans hcentered.symm)

/-- On a fixed cube, the preceding two coefficient representatives agree
globally, not merely after restriction to the cube.  This stronger form is
what composes with the global affine pullback identities. -/
theorem rawIdentityCoeff_ae_global
    {d : ℕ} [NeZero d] {a : CoeffSpace d} {abar : Mat d}
    (geom : RoundedGenerationAnalyticGeometry d)
    (hS : (symmPart abar).PosDef)
    (aRaw : Book.Ch03.CoeffFamily d)
    (hRaw : ∀ Q : TriadicCube d,
      (aRaw.coeffOn Q).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ⇑(normalizedCenteredCoeff a abar hS).1)
    (hI : (symmPart (1 : Mat d)).PosDef)
    (aIdentity : Book.Ch03.CoeffFamily d)
    (hIdentity : ∀ Q : TriadicCube d,
      (aIdentity.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace (1 : Mat d) hI
          (exactGaugeCoeffSpace a abar hS)).1 : CoeffField d))
    (Q : TriadicCube d) :
    (aRaw.coeffOn Q).toCoeffField =ᵐ[volume]
      (aIdentity.coeffOn Q).toCoeffField := by
  rw [hRaw Q, hIdentity Q]
  have hcentered := identityCenteredCoeffSpace_ae geom hI
    (exactGaugeCoeffSpace a abar hS)
  have hgauge := exactGaugeCoeffSpace_ae a abar hS
  exact hgauge.symm.trans hcentered.symm

/-- Exact gauge transport, plus a.e.-invariance of the finite-corrector
limit, feeds the physical inverse-radius pair into the identity-gauge
quotient pair.
No equality of bundled coefficient-family records is assumed. -/
theorem physicalPair_le_identityGaugePair
    {d : ℕ} [NeZero d] {a : CoeffSpace d} {abar : Mat d}
    (geom : RoundedGenerationAnalyticGeometry d)
    (hS : (symmPart abar).PosDef)
    (aRaw : Book.Ch03.CoeffFamily d)
    (hRaw : ∀ Q : TriadicCube d,
      (aRaw.coeffOn Q).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ⇑(normalizedCenteredCoeff a abar hS).1)
    (hCauchy : FiniteAffineCorrectionLocalCauchy aRaw)
    (hRawJoint : IsFiniteAffineCorrectionJointLocalEquation aRaw
      (finiteAffineCorrectionJointLocalLimit aRaw hCauchy))
    (hI : (symmPart (1 : Mat d)).PosDef)
    (aIdentity : Book.Ch03.CoeffFamily d)
    (hIdentity : ∀ Q : TriadicCube d,
      (aIdentity.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace (1 : Mat d) hI
          (exactGaugeCoeffSpace a abar hS)).1 : CoeffField d))
    (PhiIdentity : Vec d → NormalizedLocalH1Carrier d)
    (hIdentityJoint : IsFiniteAffineCorrectionJointLocalEquation
      aIdentity PhiIdentity)
    (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d)
    (e : Vec d)
    (hpullback :
      (fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
        (e + gradPhi e a
          (matVecMul (Selection.normalizedRoot (symmPart abar)) y))) =ᵐ[volume]
        fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar)) e +
          (finiteAffineCorrectionJointLocalLimit aRaw hCauchy
            (matVecMul (Selection.normalizedRoot (symmPart abar))
              e)).globalGradientRepresentative y)
    {r : ℝ} (hr : 0 < r) (m : ℤ)
    (hm : m = outerTriadicGeneration (4 * r) (by positivity)) :
    ENNReal.ofReal r⁻¹ *
          negOneNorm (ellipsoid abar r)
            (fun x ↦ matVecMul (matSqrt (symmPart abar))
              (gradPhi e a x)) +
        ENNReal.ofReal r⁻¹ *
          negOneNorm (ellipsoid abar r)
            (fun x ↦ matVecMul (matSqrt (symmPart abar))⁻¹
              (matVecMul ((a.1 x : Mat d) - skewPart abar)
                  (e + gradPhi e a x) -
                matVecMul (symmPart abar) e)) ≤
      ENNReal.ofReal
          (Real.sqrt (h1AffineFactor
              (Selection.normalizedRoot (symmPart abar))) *
            closedBallScaledNegOneConstant d) *
        (triadicScaledNegOneNorm m
              (correctorGradientOnOriginCube PhiIdentity
                (matVecMul (matSqrt (symmPart abar)) e) m) +
          triadicScaledNegOneNorm m
              (scalarIdentityCorrectorFluxDefectOnOriginCube
                aIdentity PhiIdentity
                (matVecMul (matSqrt (symmPart abar)) e) m)) := by
  let PhiRaw : Vec d → NormalizedLocalH1Carrier d :=
    finiteAffineCorrectionJointLocalLimit aRaw hCauchy
  let eRef : Vec d := matVecMul (matSqrt (symmPart abar)) e
  let Q : TriadicCube d := originCube d m
  let F : Vec d → Vec d := (PhiIdentity eRef).globalGradientRepresentative
  let G : Vec d → Vec d := fun y ↦
    matVecMul ((aIdentity.coeffOn Q).toCoeffField y)
      (eRef + (PhiIdentity eRef).globalGradientRepresentative y) - eRef
  have hab := rawIdentityFamily_aeeq geom hS aRaw hRaw hI
    aIdentity hIdentity
  have hgradRawId : (PhiRaw eRef).globalGradientRepresentative =ᵐ[volume]
      (PhiIdentity eRef).globalGradientRepresentative :=
    jointGlobalGradient_ae_of_aeeq hab PhiRaw PhiIdentity
      hRawJoint hIdentityJoint eRef
  have hcoeffRawId : (aRaw.coeffOn Q).toCoeffField =ᵐ[volume]
      (aIdentity.coeffOn Q).toCoeffField :=
    rawIdentityCoeff_ae_global geom hS aRaw hRaw hI
      aIdentity hIdentity Q
  have h₁Raw := matSqrt_physicalGradient_pullback_ae hS aRaw
    hCauchy gradPhi e hpullback
  have h₁ : (fun y ↦ matVecMul (matSqrt (symmPart abar))
      (gradPhi e a (matVecMul (Selection.normalizedRoot (symmPart abar)) y)))
      =ᵐ[volume] F := by
    exact h₁Raw.trans (by simpa only [PhiRaw, eRef, F] using hgradRawId)
  have h₂Raw := physicalFlux_pullback_ae hS Q aRaw hRaw hCauchy
    gradPhi e hpullback
  have h₂Tail :
      (fun y ↦
        matVecMul ((aRaw.coeffOn Q).toCoeffField y)
            (eRef + (PhiRaw eRef).globalGradientRepresentative y) - eRef)
        =ᵐ[volume] G := by
    filter_upwards [hcoeffRawId, hgradRawId] with y hcoeffY hgradY
    simp only [G, eRef, PhiRaw]
    rw [hcoeffY, hgradY]
  have h₂ : (fun y ↦ matVecMul (matSqrt (symmPart abar))⁻¹
      (matVecMul
          ((a.1 (matVecMul (Selection.normalizedRoot (symmPart abar)) y) : Mat d) -
            skewPart abar)
          (e + gradPhi e a
            (matVecMul (Selection.normalizedRoot (symmPart abar)) y)) -
        matVecMul (symmPart abar) e)) =ᵐ[volume] G := by
    exact h₂Raw.trans (by simpa only [PhiRaw, eRef] using h₂Tail)
  have hF : MemVectorL2 (openCubeSet Q) F := by
    simpa only [Q, F] using
      memVectorL2_globalGradient_originCube (PhiIdentity eRef) m
  have hconst : MemVectorL2 (openCubeSet Q) (fun _ ↦ eRef) :=
    memVectorL2_const eRef
  have hfull : MemVectorL2 (openCubeSet Q)
      (fun y ↦ eRef + F y) := by
    simpa only [Pi.add_apply] using! hconst.add hF
  have hpublic : MemVectorL2 (openCubeSet Q) (fun y ↦
      matVecMul (Book.Ch03.publicCoeffField Q aIdentity y)
        (eRef + F y) - eRef) :=
    (memVectorL2_matVecMul_of_isEllipticFieldOn
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
        Q aIdentity) hfull).sub hconst
  have hrawPublic : G =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun y ↦ matVecMul (Book.Ch03.publicCoeffField Q aIdentity y)
        (eRef + F y) - eRef := by
    have hcoeff := (Book.Ch03.publicCoeffField_ae_eq_openCubeSet
      Q aIdentity).symm
    filter_upwards [hcoeff] with y hy
    simp only [G]
    rw [hy]
  have hG : MemVectorL2 (openCubeSet Q) G :=
    (memLp_congr_ae hrawPublic).mpr hpublic
  have hphysical := physicalScaledPair_le_gaugeOriginCube
    hS hr m hm
    (fun x ↦ matVecMul (matSqrt (symmPart abar)) (gradPhi e a x))
    (fun x ↦ matVecMul (matSqrt (symmPart abar))⁻¹
      (matVecMul ((a.1 x : Mat d) - skewPart abar)
          (e + gradPhi e a x) - matVecMul (symmPart abar) e))
    F G h₁ h₂ (by simpa only [Q] using hF)
      (by simpa only [Q] using hG)
  have hglobal := triadicScaledNegOne_pair_eq_global
    aIdentity PhiIdentity eRef m
  rw [hglobal]
  exact hphysical

end

end HighContrast
end HCPolySupport
