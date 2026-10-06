/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardRealTranslateLiouville
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLiouvilleForward
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalAffineH1sLoc

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardCovariance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Integer covariance of the normalized-gauge carrier, at a real translation

The identity-gauge covariance proof compares two integer phases of one
sample.  In the normalized gauge an integer
translation of the *physical* sample is a translation by the **real** vector
`L⁻¹ z`, so the same comparison has to run at a real translation.  Every step
of the identity proof carries over unchanged except the Liouville input, which
is supplied here by `engine_liouville_input`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- The affine-plus-corrector representative of a carrier with a correction-only
cube-growth row and a global corrector equation is in the Liouville class.
This is the `t = 0`, `c = 0` case of the available translated statement,
assembled from the two available untranslated rows. -/
theorem memLiouvilleClass_affineAdd_of_cubeGrowth [NeZero d]
    (Phi : NormalizedLocalH1Carrier d) {b : CoeffField d} (e : Vec d)
    (hEquation : IsWeakSolutionOn b Set.univ
      (fun x ↦ e + Phi.globalGradientRepresentative x))
    (q0 : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hcube : ∀ q : ℕ, q0 ≤ q →
      cubeLpNorm (originCube d (q : ℤ)) 2 Phi.globalValueRepresentative ≤
        C * (3 : ℝ) ^ q)
    {theta : ℝ} (htheta : 0 < theta)
    (hb : IsAELocallyUniformlyElliptic b) :
    MemLiouvilleClass b theta
      (fun x ↦ vecDot e x + Phi.globalValueRepresentative x)
      (fun x ↦ e + Phi.globalGradientRepresentative x) := by
  have hH1 := Phi.memH1sLoc_affineAdd_globalRepresentatives hb e 0
  have hgrowth := Phi.tendsto_affineAdd_normalizedL2Norm_sublinear_of_cubeGrowth
    q0 C hC hcube e 0 htheta
  simp only [add_zero] at hH1 hgrowth
  exact ⟨hH1, hEquation, hgrowth⟩

/-- **Covariance of the normalized-gauge carrier under a real translation.**

On the normalized-gauge event at a sample and at its integer translate, the
selected normalized carrier of the translated sample is the `L⁻¹ z`-translate
of the selected normalized carrier of the sample, at the pulled-back slope.

The Liouville input is `engine_liouville_input`; the identification is the same
`rootCorrectorIdentification_spec` engine the identity-gauge proof uses, whose
translation binder is an arbitrary real vector and whose boundary cost is the
source datum's weak gradient row. -/
theorem pushforwardCarrier_gradient_translate_ae [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef) (z : Fin d → ℤ) (e : Vec d)
    {a : CoeffSpace d}
    (hsrc : RootCorrectorEvent d (normalizedSample abar hS a))
    (htgt : RootCorrectorEvent d
      (normalizedSample abar hS (translateCoeff z a))) :
    (fun x ↦ (rootJointCarrier d (matVecMul (gaugeRoot abar) e)
        (normalizedSample abar hS a)).globalGradientRepresentative
          (x + matVecMul (gaugeRoot abar)⁻¹ (Source.AKL.intTranslation z)))
      =ᵐ[volume]
      NormalizedLocalH1Carrier.globalGradientRepresentative
        (rootJointCarrier d (matVecMul (gaugeRoot abar) e)
          (normalizedSample abar hS (translateCoeff z a))) := by
  set Le : Vec d := matVecMul (gaugeRoot abar) e with hLe
  set t : Vec d :=
    matVecMul (gaugeRoot abar)⁻¹ (Source.AKL.intTranslation z) with ht
  set aS : CoeffSpace d := normalizedSample abar hS a with haS
  set aT : CoeffSpace d :=
    normalizedSample abar hS (translateCoeff z a) with haT
  have hellT : IsAELocallyUniformlyElliptic (⇑aT.1 : CoeffField d) := aT.2
  have hellS : IsAELocallyUniformlyElliptic (⇑aS.1 : CoeffField d) := aS.2
  obtain ⟨qGrad, Nrow, _hNrow, hRowTail⟩ :=
    (selectedRootCorrectorData aS hsrc).gradientGrowth Le
  obtain ⟨qVal, C, hC, hValTail⟩ :=
    (selectedRootCorrectorData aS hsrc).valueGrowth Le
  set PhiSource : NormalizedLocalH1Carrier d :=
    finiteAffineCorrectionJointLocalLimit (selectedRootCorrectorData aS hsrc).aFin
      (selectedRootCorrectorData aS hsrc).hCauchy Le with hPhiSource
  set PhiTarget : Vec d → NormalizedLocalH1Carrier d :=
    finiteAffineCorrectionJointLocalLimit
      (selectedRootCorrectorData aT htgt).aFin
      (selectedRootCorrectorData aT htgt).hCauchy with hPhiTarget
  have hEquationSource : IsWeakSolutionOn (fun x ↦ aS.1 x) Set.univ
      (fun x ↦ Le + PhiSource.globalGradientRepresentative x) :=
    (finiteAffineCorrectionJointLocalLimit_isJointLocalEquation
      (selectedRootCorrectorData aS hsrc).aFin
      (selectedRootCorrectorData aS hsrc).hCauchy).isWeakSolutionOn_global
        (selectedRootCorrectorData aS hsrc).coeff Le
  have hLiouSample := memLiouvilleClass_affineAdd_of_cubeGrowth PhiSource Le
    hEquationSource qVal C hC hValTail rootCorrectorGrowth_pos hellS
  have hLiouGauge : MemLiouvilleClass (gaugeCoeff a abar hS) rootCorrectorGrowth
      (fun y ↦ vecDot Le y + PhiSource.globalValueRepresentative y)
      (fun y ↦ Le + PhiSource.globalGradientRepresentative y) :=
    (memLiouvilleClass_congr_coefficient (normalizedSample_ae abar hS a)
      hellS (isAELocallyUniformlyElliptic_gaugeCoeff a abar hS)).mp hLiouSample
  have hEngine := engine_liouville_input a abar hS PhiSource e
    rootCorrectorGrowth_pos hLiouGauge z
  have hLiouTarget : MemLiouvilleClass (fun y ↦ aT.1 y) rootCorrectorGrowth
      (fun y ↦ vecDot Le y + PhiSource.globalValueRepresentative (y + t))
      (fun y ↦ Le + PhiSource.globalGradientRepresentative (y + t)) :=
    (memLiouvilleClass_congr_coefficient
      (normalizedSample_ae abar hS (translateCoeff z a))
      hellT
      (isAELocallyUniformlyElliptic_gaugeCoeff (translateCoeff z a) abar hS)).mpr
      hEngine
  have hae := (rootCorrectorIdentification_spec d
      (selectedRootCorrectorData aT htgt).order
      (selectedRootCorrectorData aT htgt).order_pos
      (selectedRootCorrectorData aT htgt).order_lt).2
    (selectedRootCorrectorData aT htgt).aFin
    (selectedRootCorrectorData aT htgt).tolerance
    (selectedRootCorrectorData aT htgt).start
    (mem_identificationTolerance_of_mem
      (selectedRootCorrectorData aT htgt).tolerance_mem)
    (selectedRootCorrectorData aT htgt).goodTail
    PhiTarget
    (finiteAffineCorrectionJointLocalLimit_isJointLocalEquation
      (selectedRootCorrectorData aT htgt).aFin
      (selectedRootCorrectorData aT htgt).hCauchy)
    hellT (selectedRootCorrectorData aT htgt).coeff
    PhiSource Le t (selectedRootCorrectorData aS hsrc).order Nrow qGrad
    (selectedRootCorrectorData aS hsrc).order_pos
    (selectedRootCorrectorData aS hsrc).order_lt
    ((selectedRootCorrectorData aS hsrc).intrinsic Le)
    (selectedRootCorrectorData aT htgt).intrinsic
    hRowTail hLiouTarget
  rw [rootJointCarrier_of_event Le htgt, rootJointCarrier_of_event Le hsrc,
    ← hPhiSource, ← hPhiTarget]
  exact hae

end

end Root
end HighContrast
end HCPolySupport
