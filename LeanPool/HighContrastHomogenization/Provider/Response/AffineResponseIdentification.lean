/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AffineAnnealedCutoffEnergy
public import LeanPool.HighContrastHomogenization.Provider.Response.AnnealedDefectIdentification

/-!
# High-contrast homogenization: Provider.Response.AffineResponseIdentification

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Annealed identifications for affine reference responses

The common affine family represents both the terminal response and every
aligned child response.  Integer-translation stationarity identifies each
child expectation with the centered physical response at the same scale.  The
reference partition defect therefore has exactly the physical response-defect
expectation.
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

private theorem integral_affineResponseCell_eq_physical_of_covariance
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
    (∫ a, Book.Ch02.responseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        ((A a).coeffOn (translateCube w (originCube d k)))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) ∂P) =
      ∫ a, Book.Ch02.responseJ (adaptedDomain hq k)
        ((S a).coeffOn (adaptedDomain hq k)) p r ∂P := by
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
    have hdomain : adaptedDomainAt hq k 0 = adaptedDomain hq k := by
      exact domain_eq_of_carrier_eq (PortableHistory.adaptedCellAt_zero q k)
    have hcell := responseJ_affineResponseCell
      hq t k 0 (S a) (A a) (hA a) p r
    rw [hcube, hdomain] at hcell
    exact hcell
  have hJ₀ : Integrable J₀ P :=
    hbase.congr (_root_.Filter.Eventually.of_forall fun a ↦ (hzero a).symm)
  calc
    (∫ a, Book.Ch02.responseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        ((A a).coeffOn (translateCube w (originCube d k)))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) ∂P) =
        ∫ a, J₀ (translateCoeff z a) ∂P := by
      exact integral_congr_ae (_root_.Filter.Eventually.of_forall hz)
    _ = ∫ a, J₀ a ∂P := integral_comp_translateCoeff hP z hJ₀
    _ = ∫ a, Book.Ch02.responseJ (adaptedDomain hq k)
        ((S a).coeffOn (adaptedDomain hq k)) p r ∂P := by
      exact integral_congr_ae (_root_.Filter.Eventually.of_forall hzero)

/-! ## Terminal and aligned-cell identifications -/

/-- The terminal response of the primal affine family is the physical
recentered response at the untransformed loads. -/
theorem integral_affineSubSkewResponseJ_eq_physical
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (g : Mat d) (hg : IsSkewMat g)
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d) :
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d t))
        ((A a).coeffOn (originCube d t))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) ∂P) =
      ∫ a, Book.Ch02.responseJ (adaptedDomain hq t)
        ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r ∂P := by
  exact integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦
    responseJ_affineResponse hq t (hA a (originCube d t)) p r)

/-- The terminal response identification for the independently transported
adjoint coefficient. -/
theorem integral_affineAdjointSubSkewResponseJ_eq_physical
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (g : Mat d) (hg : IsSkewMat g)
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d) :
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d t))
        ((A a).coeffOn (originCube d t))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) ∂P) =
      ∫ a, Book.Ch02.responseJ (adaptedDomain hq t)
        (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq t)) p r ∂P := by
  exact integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦
    responseJ_affineResponse hq t (hA a (originCube d t)) p r)

/-- Every aligned primal reference child has the expectation of the centered
physical response at its scale. -/
theorem integral_affineSubSkewCellResponseJ_eq_physical
    {P : Measure (CoeffSpace d)} (hP : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} (hq : q.PosDef) {l k t : ℤ} (hqGrid : IsRoundedGrid l q)
    (hlk : l ≤ k) (w : Fin d → ℤ) (g : Mat d) (hg : IsSkewMat g)
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d)
    (hbase : Integrable (fun a : CoeffSpace d ↦
      Book.Ch02.responseJ (adaptedDomain hq k)
        ((a.subSkew g hg).coeffOn (adaptedDomain hq k)) p r) P) :
    (∫ a, Book.Ch02.responseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        ((A a).coeffOn (translateCube w (originCube d k)))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) ∂P) =
      ∫ a, Book.Ch02.responseJ (adaptedDomain hq k)
        ((a.subSkew g hg).coeffOn (adaptedDomain hq k)) p r ∂P := by
  apply integral_affineResponseCell_eq_physical_of_covariance hP hq w
    (fun a ↦ a.subSkew g hg) A hA p r
  · exact exists_translateCoeff_affineSubSkewResponseJ
      hq hqGrid hlk w g hg A hA p r
  · exact hbase

/-- The aligned-cell expectation identity for the independent adjoint
response. -/
theorem integral_affineAdjointSubSkewCellResponseJ_eq_physical
    {P : Measure (CoeffSpace d)} (hP : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} (hq : q.PosDef) {l k t : ℤ} (hqGrid : IsRoundedGrid l q)
    (hlk : l ≤ k) (w : Fin d → ℤ) (g : Mat d) (hg : IsSkewMat g)
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d)
    (hbase : Integrable (fun a : CoeffSpace d ↦
      Book.Ch02.responseJ (adaptedDomain hq k)
        (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq k)) p r) P) :
    (∫ a, Book.Ch02.responseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        ((A a).coeffOn (translateCube w (originCube d k)))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) ∂P) =
      ∫ a, Book.Ch02.responseJ (adaptedDomain hq k)
        (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq k)) p r ∂P := by
  apply integral_affineResponseCell_eq_physical_of_covariance hP hq w
    (fun a ↦ (a.subSkew g hg).transpose) A hA p r
  · exact exists_translateCoeff_affineAdjointSubSkewResponseJ
      hq hqGrid hlk w g hg A hA p r
  · exact hbase

/-! ## The partition defect at the physical response defect -/

private theorem integral_responseJPartitionDefect_eq_sub_of_child_integrals
    {P : Measure (CoeffSpace d)}
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (Q : TriadicCube d) (j : ℕ) (p r : Vec d) {Js Jt : ℝ}
    (hchildInt : ∀ R ∈ descendantsAtDepth Q j, Integrable (fun a ↦
      Book.Ch02.responseJ (Book.Ch02.cubeDomain R) ((A a).coeffOn R) p r) P)
    (hparentInt : Integrable (fun a ↦ Book.Ch02.responseJ
      (Book.Ch02.cubeDomain Q) ((A a).coeffOn Q) p r) P)
    (hchild : ∀ R ∈ descendantsAtDepth Q j,
      (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        ((A a).coeffOn R) p r ∂P) = Js)
    (hparent : (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      ((A a).coeffOn Q) p r ∂P) = Jt) :
    (∫ a, responseJPartitionDefectOnFamilyAtDepth (A a) Q j p r ∂P) =
      Js - Jt := by
  let Child : TriadicCube d → CoeffSpace d → ℝ := fun R a ↦
    Book.Ch02.responseJ (Book.Ch02.cubeDomain R) ((A a).coeffOn R) p r
  have havgInt : Integrable (fun a ↦ descendantsAverage Q j
      (fun R ↦ Child R a)) P := by
    unfold descendantsAverage
    exact (integrable_finsetSum (descendantsAtDepth Q j)
      (fun R hR ↦ hchildInt R hR)).const_mul _
  have hswap : (∫ a, descendantsAverage Q j (fun R ↦ Child R a) ∂P) =
      descendantsAverage Q j (fun R ↦ ∫ a, Child R a ∂P) := by
    unfold descendantsAverage
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum _ (fun R hR ↦ hchildInt R hR)]
  rw [show (∫ a, responseJPartitionDefectOnFamilyAtDepth (A a) Q j p r ∂P) =
      (∫ a, descendantsAverage Q j (fun R ↦ Child R a) ∂P) -
        ∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
          ((A a).coeffOn Q) p r ∂P by
    unfold responseJPartitionDefectOnFamilyAtDepth
      childResponseJAverageOnFamilyAtDepth
    exact integral_sub havgInt hparentInt]
  rw [hswap, descendantsAverage_congr_of_eq_on_descendants Q j hchild,
    descendantsAverage_const, hparent]

/-- The primal affine reference partition defect has exactly the physical
primal response-defect expectation. -/
theorem integral_affineSubSkewResponseJPartitionDefect_eq_profilePrimal
    {P : Measure (CoeffSpace d)} (hP : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} (hq : q.PosDef) {l s t : ℤ} (hqGrid : IsRoundedGrid l q)
    (hls : l ≤ s) (j : ℕ) (hscale : t - (j : ℤ) = s)
    (g : Mat d) (hg : IsSkewMat g)
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d)
    (hchildInt : ∀ R ∈ descendantsAtDepth (originCube d t) j,
      Integrable (fun a ↦ Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        ((A a).coeffOn R) (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) P)
    (hs : Integrable (fun a ↦ Book.Ch02.responseJ (adaptedDomain hq s)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq s)) p r) P)
    (ht : Integrable (fun a ↦ Book.Ch02.responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r) P) :
    (∫ a, responseJPartitionDefectOnFamilyAtDepth (A a)
        (originCube d t) j (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) ∂P) =
      profilePrimalResponseDefect P hq g hg s t p r := by
  have hparentInt := ht.congr (_root_.Filter.Eventually.of_forall fun a ↦
    (responseJ_affineResponse hq t (hA a (originCube d t)) p r).symm)
  rw [profilePrimalResponseDefect_eq_sub_integral P hq g hg s t p r hs ht]
  apply integral_responseJPartitionDefect_eq_sub_of_child_integrals A
    (originCube d t) j (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
    hchildInt hparentInt
  · intro R hR
    have hRs : R.scale = s := by
      simpa [originCube, hscale] using scale_eq_sub_of_mem_descendantsAtDepth hR
    have hRform : translateCube R.index (originCube d R.scale) = R := by
      cases R with
      | mk scale index =>
          change TriadicCube.mk scale (fun i ↦ 0 + index i) =
            TriadicCube.mk scale index
          apply congrArg (TriadicCube.mk scale)
          funext i
          simp
    have hlR : l ≤ R.scale := by rw [hRs]; exact hls
    have hsR : Integrable (fun a ↦ Book.Ch02.responseJ
        (adaptedDomain hq R.scale)
        ((a.subSkew g hg).coeffOn (adaptedDomain hq R.scale)) p r) P := by
      exact hRs.symm ▸ hs
    have hcell := integral_affineSubSkewCellResponseJ_eq_physical
      (P := P) (l := l) (k := R.scale) (t := t)
      hP hq hqGrid hlR R.index g hg A hA p r hsR
    rw [hRform, hRs] at hcell
    exact hcell
  · exact integral_affineSubSkewResponseJ_eq_physical hq t g hg A hA p r

/-- The same partition-defect identification for the independently transported
adjoint response. -/
theorem integral_affineAdjointSubSkewResponseJPartitionDefect_eq_profileAdjoint
    {P : Measure (CoeffSpace d)} (hP : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} (hq : q.PosDef) {l s t : ℤ} (hqGrid : IsRoundedGrid l q)
    (hls : l ≤ s) (j : ℕ) (hscale : t - (j : ℤ) = s)
    (g : Mat d) (hg : IsSkewMat g)
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d)
    (hchildInt : ∀ R ∈ descendantsAtDepth (originCube d t) j,
      Integrable (fun a ↦ Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        ((A a).coeffOn R) (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) P)
    (hs : Integrable (fun a ↦ Book.Ch02.responseJ (adaptedDomain hq s)
      (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq s)) p r) P)
    (ht : Integrable (fun a ↦ Book.Ch02.responseJ (adaptedDomain hq t)
      (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq t)) p r) P) :
    (∫ a, responseJPartitionDefectOnFamilyAtDepth (A a)
        (originCube d t) j (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) ∂P) =
      profileAdjointResponseDefect P hq g hg s t p r := by
  have hparentInt := ht.congr (_root_.Filter.Eventually.of_forall fun a ↦
    (responseJ_affineResponse hq t (hA a (originCube d t)) p r).symm)
  rw [profileAdjointResponseDefect_eq_sub_integral P hq g hg s t p r hs ht]
  apply integral_responseJPartitionDefect_eq_sub_of_child_integrals A
    (originCube d t) j (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
    hchildInt hparentInt
  · intro R hR
    have hRs : R.scale = s := by
      simpa [originCube, hscale] using scale_eq_sub_of_mem_descendantsAtDepth hR
    have hRform : translateCube R.index (originCube d R.scale) = R := by
      cases R with
      | mk scale index =>
          change TriadicCube.mk scale (fun i ↦ 0 + index i) =
            TriadicCube.mk scale index
          apply congrArg (TriadicCube.mk scale)
          funext i
          simp
    have hlR : l ≤ R.scale := by rw [hRs]; exact hls
    have hsR : Integrable (fun a ↦ Book.Ch02.responseJ
        (adaptedDomain hq R.scale)
        (((a.subSkew g hg).transpose).coeffOn
          (adaptedDomain hq R.scale)) p r) P := by
      exact hRs.symm ▸ hs
    have hcell := integral_affineAdjointSubSkewCellResponseJ_eq_physical
      (P := P) (l := l) (k := R.scale) (t := t)
      hP hq hqGrid hlR R.index g hg A hA p r hsR
    rw [hRform, hRs] at hcell
    exact hcell
  · exact integral_affineAdjointSubSkewResponseJ_eq_physical hq t g hg A hA p r

end

end HCPolySupport.HighContrast.Response
