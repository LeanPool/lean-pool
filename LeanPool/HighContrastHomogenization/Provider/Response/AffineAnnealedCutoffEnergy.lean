/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseCell
public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseCongruence
public import LeanPool.HighContrastHomogenization.Provider.Response.AnnealedCutoffEnergy
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormState

/-!
# High-contrast homogenization: Provider.Response.AffineAnnealedCutoffEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Stationary cancellation for affine reference responses

An aligned reference child represents the response on its physical adapted
image.  Rounded-grid alignment makes that image an integer translate of the
cell at the origin, so stationarity cancels the cutoff-weighted child response
without placing a stationary law on the affine pullback family.  The argument
applies separately to the recentered coefficient and to its adjoint.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory Book.Ch05.Section53.JUpperBoundWeakNorms

noncomputable section

variable {d : ℕ}

private theorem translateCoeff_subSkew (z : Fin d → ℤ) (a : CoeffSpace d)
    (g : Mat d) (hg : IsSkewMat g) :
    translateCoeff z (a.subSkew g hg) = (translateCoeff z a).subSkew g hg := by
  have hshift :=
    (measurePreserving_add_right (volume : Measure (Vec d))
      (Source.AKL.intTranslation z)).quasiMeasurePreserving.tendsto_ae
        (CoeffSpace.subSkew_ae a g hg)
  apply Subtype.ext
  apply AEEqFun.ext
  filter_upwards [Source.AKL.translateField_ae z (a.subSkew g hg).1,
    hshift, CoeffSpace.subSkew_ae (translateCoeff z a) g hg,
    Source.AKL.translateField_ae z a.1] with x hleft hsub hright hraw
  change (Source.AKL.translateField z (a.subSkew g hg).1) x =
    ((translateCoeff z a).subSkew g hg).1 x
  change (a.subSkew g hg).1 (x + Source.AKL.intTranslation z) =
    a.1 (x + Source.AKL.intTranslation z) - g at hsub
  change (translateCoeff z a).1 x =
    a.1 (x + Source.AKL.intTranslation z) at hraw
  rw [hleft, hsub, hright, ← hraw]

private theorem translateCoeff_transpose (z : Fin d → ℤ) (a : CoeffSpace d) :
    translateCoeff z a.transpose = (translateCoeff z a).transpose := by
  have hshift :=
    (measurePreserving_add_right (volume : Measure (Vec d))
      (Source.AKL.intTranslation z)).quasiMeasurePreserving.tendsto_ae
        (CoeffSpace.transpose_ae a)
  apply Subtype.ext
  apply AEEqFun.ext
  filter_upwards [Source.AKL.translateField_ae z a.transpose.1,
    hshift, CoeffSpace.transpose_ae (translateCoeff z a),
    Source.AKL.translateField_ae z a.1] with x hleft htrans hright hraw
  change (Source.AKL.translateField z a.transpose.1) x =
    (translateCoeff z a).transpose.1 x
  change a.transpose.1 (x + Source.AKL.intTranslation z) =
    matTranspose (a.1 (x + Source.AKL.intTranslation z)) at htrans
  change (translateCoeff z a).1 x =
    a.1 (x + Source.AKL.intTranslation z) at hraw
  rw [hleft, htrans, hright, ← hraw]

private theorem translateCoeff_transpose_subSkew (z : Fin d → ℤ)
    (a : CoeffSpace d) (g : Mat d) (hg : IsSkewMat g) :
    translateCoeff z (a.subSkew g hg).transpose =
      ((translateCoeff z a).subSkew g hg).transpose := by
  rw [translateCoeff_transpose, translateCoeff_subSkew]

private theorem responseJ_adaptedDomainAt_translate_of_commutes
    {q : Mat d} (hq : q.PosDef) {k : ℤ} {w z : Fin d → ℤ}
    (hz : adaptedCellCenter q k w = fun i ↦ (z i : ℝ))
    (S : CoeffSpace d → CoeffSpace d)
    (hS : ∀ v a, translateCoeff v (S a) = S (translateCoeff v a))
    (a : CoeffSpace d) (p r : Vec d) :
    Book.Ch02.responseJ (adaptedDomainAt hq k w)
        ((S a).coeffOn (adaptedDomainAt hq k w)) p r =
      Book.Ch02.responseJ (adaptedDomainAt hq k 0)
        ((S (translateCoeff z a)).coeffOn (adaptedDomainAt hq k 0)) p r := by
  rw [Internal.Ch02.book_responseJ_eq_ResponseJ,
    Internal.Ch02.book_responseJ_eq_ResponseJ]
  simp only [CoeffSpace.coeffOn_toCoeffField, adaptedDomainAt_carrier]
  rw [Recurrence.adaptedCellAt_eq_translateSet_intVec hz,
    ResponseJ_translateSet_intTranslation, hS]
  rw [Recurrence.adaptedCellAt_eq_image, standardCell_zero]
  rfl

private theorem exists_translateCoeff_affineResponseJ_of_commutes
    {q : Mat d} (hq : q.PosDef) {l k t : ℤ} (hqGrid : IsRoundedGrid l q)
    (hlk : l ≤ k) (w : Fin d → ℤ)
    (S : CoeffSpace d → CoeffSpace d)
    (hS : ∀ z a, translateCoeff z (S a) = S (translateCoeff z a))
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      ((S a).coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d) :
    ∃ z : Fin d → ℤ, ∀ a : CoeffSpace d,
      Book.Ch02.responseJ
          (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
          ((A a).coeffOn (translateCube w (originCube d k)))
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) =
        Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d k))
          ((A (translateCoeff z a)).coeffOn (originCube d k))
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) := by
  obtain ⟨z, hz⟩ := Recurrence.exists_intVec_adaptedCellCenter hqGrid hlk w
  refine ⟨z, fun a ↦ ?_⟩
  calc
    Book.Ch02.responseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        ((A a).coeffOn (translateCube w (originCube d k)))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) =
      Book.Ch02.responseJ (adaptedDomainAt hq k w)
        ((S a).coeffOn (adaptedDomainAt hq k w)) p r :=
      responseJ_affineResponseCell hq t k w (S a) (A a) (hA a) p r
    _ = Book.Ch02.responseJ (adaptedDomainAt hq k 0)
        ((S (translateCoeff z a)).coeffOn (adaptedDomainAt hq k 0)) p r :=
      responseJ_adaptedDomainAt_translate_of_commutes hq hz S hS a p r
    _ = Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d k))
        ((A (translateCoeff z a)).coeffOn (originCube d k))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) :=
      (responseJ_affineResponseCell hq t k 0
        (S (translateCoeff z a)) (A (translateCoeff z a))
        (hA (translateCoeff z a)) p r).symm

/-! ## Literal primal and adjoint covariance -/

/-- A recentered affine reference child is the centered reference response of
the translated physical sample. -/
theorem exists_translateCoeff_affineSubSkewResponseJ
    {q : Mat d} (hq : q.PosDef) {l k t : ℤ} (hqGrid : IsRoundedGrid l q)
    (hlk : l ≤ k) (w : Fin d → ℤ) (g : Mat d) (hg : IsSkewMat g)
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d) :
    ∃ z : Fin d → ℤ, ∀ a : CoeffSpace d,
      Book.Ch02.responseJ
          (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
          ((A a).coeffOn (translateCube w (originCube d k)))
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) =
        Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d k))
          ((A (translateCoeff z a)).coeffOn (originCube d k))
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) :=
  exists_translateCoeff_affineResponseJ_of_commutes hq hqGrid hlk w
    (fun a ↦ a.subSkew g hg) (fun z a ↦ translateCoeff_subSkew z a g hg)
    A hA p r

/-- The adjoint recentered affine child obeys the same covariance, independently
of the primal response. -/
theorem exists_translateCoeff_affineAdjointSubSkewResponseJ
    {q : Mat d} (hq : q.PosDef) {l k t : ℤ} (hqGrid : IsRoundedGrid l q)
    (hlk : l ≤ k) (w : Fin d → ℤ) (g : Mat d) (hg : IsSkewMat g)
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d) :
    ∃ z : Fin d → ℤ, ∀ a : CoeffSpace d,
      Book.Ch02.responseJ
          (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
          ((A a).coeffOn (translateCube w (originCube d k)))
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) =
        Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d k))
          ((A (translateCoeff z a)).coeffOn (originCube d k))
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) :=
  exists_translateCoeff_affineResponseJ_of_commutes hq hqGrid hlk w
    (fun a ↦ (a.subSkew g hg).transpose)
    (fun z a ↦ translateCoeff_transpose_subSkew z a g hg) A hA p r

/-! ## Stationary cancellation -/

theorem subSkew_neg_subSkew
    (a : CoeffSpace d) (g : Mat d) (hg : IsSkewMat g) :
    (a.subSkew g hg).subSkew (-g) (isSkewMat_neg hg) = a := by
  apply Subtype.ext
  apply AEEqFun.ext
  filter_upwards [CoeffSpace.subSkew_ae (a.subSkew g hg) (-g)
      (isSkewMat_neg hg), CoeffSpace.subSkew_ae a g hg]
      with x hleft hright
  rw [hleft, hright]
  abel

@[expose]
public noncomputable def subSkewEquiv (g : Mat d) (hg : IsSkewMat g) :
    CoeffSpace d ≃ᵐ CoeffSpace d where
  toFun := fun a ↦ a.subSkew g hg
  invFun := fun a ↦ a.subSkew (-g) (isSkewMat_neg hg)
  left_inv := fun a ↦ subSkew_neg_subSkew a g hg
  right_inv := by
    intro a
    simpa only [neg_neg] using
      subSkew_neg_subSkew a (-g) (isSkewMat_neg hg)
  measurable_toFun := Selection.measurable_subSkew g hg
  measurable_invFun := Selection.measurable_subSkew (-g) (isSkewMat_neg hg)

@[expose]
public noncomputable def transposeEquiv : CoeffSpace d ≃ᵐ CoeffSpace d where
  toFun := CoeffSpace.transpose
  invFun := CoeffSpace.transpose
  left_inv := CoeffSpace.transpose_transpose
  right_inv := CoeffSpace.transpose_transpose
  measurable_toFun := Selection.measurable_transpose
  measurable_invFun := Selection.measurable_transpose

@[expose]
public noncomputable def adjointSubSkewEquiv (g : Mat d) (hg : IsSkewMat g) :
    CoeffSpace d ≃ᵐ CoeffSpace d :=
  (subSkewEquiv g hg).trans transposeEquiv

/-- Under the physical stationary law, the cutoff-weighted responses of one
compatible affine family for the recentered sample have mean zero. -/
theorem integral_cutoffWeighted_affineSubSkewResponseJ_eq_zero
    {P : Measure (CoeffSpace d)} (hP : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} (hq : q.PosDef) {l s t : ℤ} (hqGrid : IsRoundedGrid l q)
    (j : ℕ) (hscale : t - (j : ℤ) = s) (hls : l ≤ s)
    (g : Mat d) (hg : IsSkewMat g)
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d) {φ : Vec d → ℝ}
    (hint : ∀ R ∈ descendantsAtDepth (originCube d t) j,
      Integrable (fun a : CoeffSpace d ↦ Book.Ch02.responseJ
        (Book.Ch02.cubeDomain R) ((A a).coeffOn R)
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) P)
    (hbase : Integrable (fun a : CoeffSpace d ↦ Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d s))
      ((A a).coeffOn (originCube d s))
      (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) P)
    (hφ : IntegrableOn φ (cubeSet (originCube d t)) volume)
    (hmean : cubeAverage (originCube d t) φ = 1) :
    ∫ a, descendantsAverage (originCube d t) j (fun R ↦
        (1 - cubeAverage R φ) * Book.Ch02.responseJ
          (Book.Ch02.cubeDomain R) ((A a).coeffOn R)
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) ∂P = 0 := by
  apply integral_cutoffWeighted_affineResponseJ_eq_zero_of_stationarity
    hP hq hqGrid j hscale hls (subSkewEquiv g hg)
  · intro z a
    exact translateCoeff_subSkew z a g hg
  · exact hA
  · exact hint
  · exact hbase
  · exact hφ
  · exact hmean

/-- The same stationary cancellation for the independently transported adjoint
recentered coefficient family. -/
theorem integral_cutoffWeighted_affineAdjointSubSkewResponseJ_eq_zero
    {P : Measure (CoeffSpace d)} (hP : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} (hq : q.PosDef) {l s t : ℤ} (hqGrid : IsRoundedGrid l q)
    (j : ℕ) (hscale : t - (j : ℤ) = s) (hls : l ≤ s)
    (g : Mat d) (hg : IsSkewMat g)
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d) {φ : Vec d → ℝ}
    (hint : ∀ R ∈ descendantsAtDepth (originCube d t) j,
      Integrable (fun a : CoeffSpace d ↦ Book.Ch02.responseJ
        (Book.Ch02.cubeDomain R) ((A a).coeffOn R)
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) P)
    (hbase : Integrable (fun a : CoeffSpace d ↦ Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d s))
      ((A a).coeffOn (originCube d s))
      (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) P)
    (hφ : IntegrableOn φ (cubeSet (originCube d t)) volume)
    (hmean : cubeAverage (originCube d t) φ = 1) :
    ∫ a, descendantsAverage (originCube d t) j (fun R ↦
        (1 - cubeAverage R φ) * Book.Ch02.responseJ
          (Book.Ch02.cubeDomain R) ((A a).coeffOn R)
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) ∂P = 0 := by
  apply integral_cutoffWeighted_affineResponseJ_eq_zero_of_stationarity
    hP hq hqGrid j hscale hls (adjointSubSkewEquiv g hg)
  · intro z a
    exact translateCoeff_transpose_subSkew z a g hg
  · exact hA
  · exact hint
  · exact hbase
  · exact hφ
  · exact hmean

end

end HCPolySupport.HighContrast.Response
