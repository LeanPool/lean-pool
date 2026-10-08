/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseDifferenceEnergy
public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseIdentification

/-!
# High-contrast homogenization: Provider.Response.AffineResponseEnergyIdentification

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical identification of affine difference energy

The affine reference family can be chosen samplewise from the physical
coefficient.  Stationarity transfers physical response integrability to every
aligned reference child.  Consequently the actual descendant-averaged
parent--child half-energy has expectation equal to the physical response
defect, for the primal and adjoint coefficients separately.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory Book.Ch02
open Book.Ch05.Section53.JUpperBoundWeakNorms

noncomputable section

variable {d : ℕ}

private theorem domain_eq_of_carrier_eq {U V : Book.Ch02.Domain d}
    (h : U.carrier = V.carrier) : U = V := by
  cases U
  cases V
  simp_all

private theorem integrable_affineResponseCell_of_covariance
    {P : Measure (CoeffSpace d)} (hP : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (w : Fin d → ℤ)
    (S : CoeffSpace d → CoeffSpace d)
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      ((S a).coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d)
    (hcov : ∃ z : Fin d → ℤ, ∀ a : CoeffSpace d,
      Book.Ch02.responseJ
          (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
          ((A a).coeffOn (translateCube w (originCube d k)))
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) =
        Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d k))
          ((A (translateCoeff z a)).coeffOn (originCube d k))
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r))
    (hbase : Integrable (fun a : CoeffSpace d ↦
      Book.Ch02.responseJ (adaptedDomain hq k)
        ((S a).coeffOn (adaptedDomain hq k)) p r) P) :
    Integrable (fun a : CoeffSpace d ↦ Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
      ((A a).coeffOn (translateCube w (originCube d k)))
      (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) P := by
  obtain ⟨z, hz⟩ := hcov
  let J₀ : CoeffSpace d → ℝ := fun a ↦
    Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d k))
      ((A a).coeffOn (originCube d k))
      (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
  have hzero : ∀ a : CoeffSpace d, J₀ a =
      Book.Ch02.responseJ (adaptedDomain hq k)
        ((S a).coeffOn (adaptedDomain hq k)) p r := by
    intro a
    have hcube : translateCube (0 : Fin d → ℤ) (originCube d k) =
        originCube d k := by
      apply congrArg (TriadicCube.mk k)
      funext i
      simp [originCube]
    have hdomain : adaptedDomainAt hq k 0 = adaptedDomain hq k :=
      domain_eq_of_carrier_eq (PortableHistory.adaptedCellAt_zero q k)
    have hcell := responseJ_affineResponseCell
      hq t k 0 (S a) (A a) (hA a) p r
    rw [hcube, hdomain] at hcell
    exact hcell
  have hJ₀ : Integrable J₀ P :=
    hbase.congr (Filter.Eventually.of_forall fun a ↦ (hzero a).symm)
  have hcomp : Integrable (fun a ↦ J₀ (translateCoeff z a)) P :=
    (Recurrence.measurePreserving_translateCoeff hP z).integrable_comp_of_integrable hJ₀
  exact hcomp.congr (Filter.Eventually.of_forall fun a ↦ (hz a).symm)

private theorem translated_originCube_eq (R : TriadicCube d) :
    translateCube R.index (originCube d R.scale) = R := by
  cases R with
  | mk scale index =>
      change TriadicCube.mk scale (fun i ↦ 0 + index i) =
        TriadicCube.mk scale index
      apply congrArg (TriadicCube.mk scale)
      funext i
      simp

/-! ## Actual energy identities -/

/-- There is a samplewise compatible primal affine family whose actual
descendant-averaged difference half-energy has expectation equal to the
physical primal response defect. -/
theorem exists_integral_affineSubSkewDifferenceEnergy_eq_profilePrimal
    {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} (hq : q.PosDef) {l s t : ℤ} (hqGrid : IsRoundedGrid l q)
    (hls : l ≤ s) (j : ℕ) (hscale : t - (j : ℤ) = s)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hs : Integrable (fun a ↦ Book.Ch02.responseJ (adaptedDomain hq s)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq s)) p r) P)
    (ht : Integrable (fun a ↦ Book.Ch02.responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r) P) :
    ∃ A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d,
      (∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
        ((a.subSkew g hg).coeffOn (adaptedDomain hq t)).toCoeffField) ∧
      (∀ R ∈ descendantsAtDepth (originCube d t) j,
        Integrable (fun a ↦ Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
          ((A a).coeffOn R) (matVecMul (matTranspose q) p)
            (matVecMul q⁻¹ r)) P) ∧
      Integrable (fun a ↦ Book.Ch02.responseJ
        (Book.Ch02.cubeDomain (originCube d s))
        ((A a).coeffOn (originCube d s)) (matVecMul (matTranspose q) p)
          (matVecMul q⁻¹ r)) P ∧
      (∫ a, descendantsAverage (originCube d t) j (fun R ↦ cubeAverage R
          (additivityDiffHalfEnergyDensityOnFamilyOnCube (A a)
            (originCube d t) R (matVecMul (matTranspose q) p)
              (matVecMul q⁻¹ r))) ∂P) =
        profilePrimalResponseDefect P hq g hg s t p r := by
  choose A hA using fun a : CoeffSpace d ↦
    exists_adaptedReferenceCoeffFamily hq t (a.subSkew g hg)
  have hchildInt : ∀ R ∈ descendantsAtDepth (originCube d t) j,
      Integrable (fun a ↦ Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        ((A a).coeffOn R) (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) P := by
    intro R hR
    have hRs : R.scale = s := by
      simpa [originCube, hscale] using scale_eq_sub_of_mem_descendantsAtDepth hR
    have hlR : l ≤ R.scale := by rw [hRs]; exact hls
    have hsR : Integrable (fun a ↦ Book.Ch02.responseJ
        (adaptedDomain hq R.scale)
        ((a.subSkew g hg).coeffOn (adaptedDomain hq R.scale)) p r) P :=
      hRs.symm ▸ hs
    have hcov := exists_translateCoeff_affineSubSkewResponseJ
      hq hqGrid hlR R.index g hg A hA p r
    have hInt := integrable_affineResponseCell_of_covariance hP hq R.index
      (fun a ↦ a.subSkew g hg) A hA p r hcov hsR
    rw [translated_originCube_eq R] at hInt
    exact hInt
  have hbaseCov := exists_translateCoeff_affineSubSkewResponseJ
    hq hqGrid hls 0 g hg A hA p r
  have hbaseInt := integrable_affineResponseCell_of_covariance hP hq 0
    (fun a ↦ a.subSkew g hg) A hA p r hbaseCov hs
  simp only [translateCube, originCube, Pi.zero_apply] at hbaseInt
  refine ⟨A, hA, hchildInt, hbaseInt, ?_⟩
  calc
    (∫ a, descendantsAverage (originCube d t) j (fun R ↦ cubeAverage R
        (additivityDiffHalfEnergyDensityOnFamilyOnCube (A a)
          (originCube d t) R (matVecMul (matTranspose q) p)
            (matVecMul q⁻¹ r))) ∂P) =
        ∫ a, responseJPartitionDefectOnFamilyAtDepth (A a)
          (originCube d t) j (matVecMul (matTranspose q) p)
            (matVecMul q⁻¹ r) ∂P := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun a ↦
        descendantsAverage_additivityDiffHalfEnergy_eq_responseJPartitionDefect_of_commonCoeff
          (A a) (originCube d t) j (matVecMul (matTranspose q) p)
            (matVecMul q⁻¹ r) (fun R _ ↦ by rw [hA a R, hA a (originCube d t)]))
    _ = profilePrimalResponseDefect P hq g hg s t p r :=
      integral_affineSubSkewResponseJPartitionDefect_eq_profilePrimal
        hP hq hqGrid hls j hscale g hg A hA p r hchildInt hs ht

/-- The independently chosen adjoint affine family satisfies the same actual
energy identity at the adjoint response defect. -/
theorem exists_integral_affineAdjointSubSkewDifferenceEnergy_eq_profileAdjoint
    {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} (hq : q.PosDef) {l s t : ℤ} (hqGrid : IsRoundedGrid l q)
    (hls : l ≤ s) (j : ℕ) (hscale : t - (j : ℤ) = s)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hs : Integrable (fun a ↦ Book.Ch02.responseJ (adaptedDomain hq s)
      (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq s)) p r) P)
    (ht : Integrable (fun a ↦ Book.Ch02.responseJ (adaptedDomain hq t)
      (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq t)) p r) P) :
    ∃ A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d,
      (∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
        (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq t)).toCoeffField) ∧
      (∀ R ∈ descendantsAtDepth (originCube d t) j,
        Integrable (fun a ↦ Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
          ((A a).coeffOn R) (matVecMul (matTranspose q) p)
            (matVecMul q⁻¹ r)) P) ∧
      Integrable (fun a ↦ Book.Ch02.responseJ
        (Book.Ch02.cubeDomain (originCube d s))
        ((A a).coeffOn (originCube d s)) (matVecMul (matTranspose q) p)
          (matVecMul q⁻¹ r)) P ∧
      (∫ a, descendantsAverage (originCube d t) j (fun R ↦ cubeAverage R
          (additivityDiffHalfEnergyDensityOnFamilyOnCube (A a)
            (originCube d t) R (matVecMul (matTranspose q) p)
              (matVecMul q⁻¹ r))) ∂P) =
        profileAdjointResponseDefect P hq g hg s t p r := by
  choose A hA using fun a : CoeffSpace d ↦
    exists_adaptedReferenceCoeffFamily hq t (a.subSkew g hg).transpose
  have hchildInt : ∀ R ∈ descendantsAtDepth (originCube d t) j,
      Integrable (fun a ↦ Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        ((A a).coeffOn R) (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) P := by
    intro R hR
    have hRs : R.scale = s := by
      simpa [originCube, hscale] using scale_eq_sub_of_mem_descendantsAtDepth hR
    have hlR : l ≤ R.scale := by rw [hRs]; exact hls
    have hsR : Integrable (fun a ↦ Book.Ch02.responseJ
        (adaptedDomain hq R.scale)
        (((a.subSkew g hg).transpose).coeffOn
          (adaptedDomain hq R.scale)) p r) P := hRs.symm ▸ hs
    have hcov := exists_translateCoeff_affineAdjointSubSkewResponseJ
      hq hqGrid hlR R.index g hg A hA p r
    have hInt := integrable_affineResponseCell_of_covariance hP hq R.index
      (fun a ↦ (a.subSkew g hg).transpose) A hA p r hcov hsR
    rw [translated_originCube_eq R] at hInt
    exact hInt
  have hbaseCov := exists_translateCoeff_affineAdjointSubSkewResponseJ
    hq hqGrid hls 0 g hg A hA p r
  have hbaseInt := integrable_affineResponseCell_of_covariance hP hq 0
    (fun a ↦ (a.subSkew g hg).transpose) A hA p r hbaseCov hs
  simp only [translateCube, originCube, Pi.zero_apply] at hbaseInt
  refine ⟨A, hA, hchildInt, hbaseInt, ?_⟩
  calc
    (∫ a, descendantsAverage (originCube d t) j (fun R ↦ cubeAverage R
        (additivityDiffHalfEnergyDensityOnFamilyOnCube (A a)
          (originCube d t) R (matVecMul (matTranspose q) p)
            (matVecMul q⁻¹ r))) ∂P) =
        ∫ a, responseJPartitionDefectOnFamilyAtDepth (A a)
          (originCube d t) j (matVecMul (matTranspose q) p)
            (matVecMul q⁻¹ r) ∂P := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun a ↦
        descendantsAverage_additivityDiffHalfEnergy_eq_responseJPartitionDefect_of_commonCoeff
          (A a) (originCube d t) j (matVecMul (matTranspose q) p)
            (matVecMul q⁻¹ r) (fun R _ ↦ by rw [hA a R, hA a (originCube d t)]))
    _ = profileAdjointResponseDefect P hq g hg s t p r :=
      integral_affineAdjointSubSkewResponseJPartitionDefect_eq_profileAdjoint
        hP hq hqGrid hls j hscale g hg A hA p r hchildInt hs ht

end

end HCPolySupport.HighContrast.Response
