/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.LocalDoubledResponseTranslation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.LocalHomogenizationErrorTranslation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local translation of the cube homogenization error

Root-cube identifications with one physical coefficient determine all
descendant responses.  The resulting theorem is the local, a.e. version of
the upstream translation API needed for independently constructed coefficient
families.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The physical translation represented by a lattice shift of a triadic
cube. -/
@[expose]
def cubeTranslationVector (z : Fin d → ℤ) (Q : TriadicCube d) : Vec d :=
  fun i ↦ (z i : ℝ) * cubeScaleFactor Q

private theorem openCubeSet_translateCube_descendant_eq_translateSet
    (z : Fin d → ℤ) (Q : TriadicCube d) (l : ℕ) (R : TriadicCube d)
    (hR : R ∈ descendantsAtScale Q (Q.scale - (l : ℤ))) :
    openCubeSet (translateCube (descendantTranslationShift l z) R) =
      translateSet (cubeTranslationVector z Q) (openCubeSet R) := by
  have hscale : R.scale = Q.scale - (l : ℤ) :=
    by
      have h := scale_eq_sub_of_mem_descendantsAtScale (by omega) hR
      simpa using h
  have hvec :
      (fun i ↦ ((descendantTranslationShift l z i : ℤ) : ℝ) *
        cubeScaleFactor R) = cubeTranslationVector z Q := by
    funext i
    simp only [descendantTranslationShift, cubeScaleFactor, hscale,
      cubeTranslationVector, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    field_simp [pow_ne_zero l (by norm_num : (3 : ℝ) ≠ 0)]
    rw [zpow_natCast]
    ac_rfl
  ext x
  rw [mem_openCubeSet_translateCube_iff, mem_translateSet_iff_sub_mem, hvec]

private theorem normalizedBlockResponseMax_translate_of_physical_ae
    (z : Fin d → ℤ) (Q : TriadicCube d) (l : ℕ)
    (R : TriadicCube d)
    (hR : R ∈ descendantsAtScale Q (Q.scale - (l : ℤ)))
    (aPhysical aCentered : Book.Ch02.TriadicCoeffFamily d)
    (f : CoeffField d)
    (hPhysical :
      (aPhysical.coeffOn (translateCube z Q)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (translateCube z Q))] f)
    (hCentered : (aCentered.coeffOn Q).toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)]
        translateCoeffField (cubeTranslationVector z Q) f)
    (a0 : Mat d) :
    Book.Ch02.normalizedBlockResponseMax
        (translateCube (descendantTranslationShift l z) R) aPhysical a0 =
      Book.Ch02.normalizedBlockResponseMax R aCentered a0 := by
  let T := translateCube (descendantTranslationShift l z) R
  let Z := cubeTranslationVector z Q
  have hTmem : T ∈ descendantsAtScale (translateCube z Q)
      ((translateCube z Q).scale - (l : ℤ)) := by
    rw [descendantsAtScale_translateCube z Q (by
      simp only [translateCube]
      omega)]
    refine Finset.mem_image.mpr ⟨R, hR, ?_⟩
    have hnat : (Q.scale - (Q.scale - (l : ℤ))).toNat = l := by simp
    simp only [T, translateCube, hnat]
  have hPhysicalT := coeffOn_descendant_ae_eq_of_root_ae_eq
    aPhysical (k := (translateCube z Q).scale - (l : ℤ))
      (by simp only [translateCube]; omega) hTmem hPhysical
  have hCenteredR := coeffOn_descendant_ae_eq_of_root_ae_eq
    aCentered (k := Q.scale - (l : ℤ)) (by omega) hR hCentered
  have hset : openCubeSet T = translateSet Z (openCubeSet R) := by
    simpa only [T, Z] using
      openCubeSet_translateCube_descendant_eq_translateSet z Q l R hR
  have hPhysicalComp :
      translateCoeffField Z (aPhysical.coeffOn T).toCoeffField =ᵐ[
        volumeMeasureOn (openCubeSet R)] translateCoeffField Z f := by
    have hPhysicalT' :
        (aPhysical.coeffOn T).toCoeffField =ᵐ[
          volumeMeasureOn (translateSet Z (openCubeSet R))] f := by
      rwa [← hset]
    let hmp :=
      measurePreserving_addRight_restrict_translateSet Z (openCubeSet R)
    have hcomp := hmp.quasiMeasurePreserving.tendsto_ae hPhysicalT'
    simpa only [Function.comp_apply, translateCoeffField] using! hcomp
  have hcoeff :
      translateCoeffField Z (aPhysical.coeffOn T).toCoeffField =ᵐ[
        volumeMeasureOn (openCubeSet R)]
          (aCentered.coeffOn R).toCoeffField :=
    hPhysicalComp.trans hCenteredR.symm
  unfold Book.Ch02.normalizedBlockResponseMax
    Book.Ch02.normalizedBlockResponseValueSet
  congr 1
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, he, ?_⟩
    exact doubledResponseJ_translate_of_aeeq Z
      (by simpa only [Book.Ch02.cubeDomain_coe] using hset)
      (aPhysical.coeffOn T) (aCentered.coeffOn R) hcoeff
      (ofFullBlockVec
        (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt a0) e))
      (ofFullBlockVec
        (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt a0) e))
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, he, ?_⟩
    exact (doubledResponseJ_translate_of_aeeq Z
      (by simpa only [Book.Ch02.cubeDomain_coe] using hset)
      (aPhysical.coeffOn T) (aCentered.coeffOn R) hcoeff
      (ofFullBlockVec
        (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt a0) e))
      (ofFullBlockVec
        (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt a0) e))).symm

/-- Two independently constructed coefficient families have identical
on-cube homogenization errors when their root representatives are the same
physical coefficient before and after the cube translation. -/
theorem homogenizationErrorOnCube_translate_of_physical_ae
    (z : Fin d → ℤ) (Q : TriadicCube d)
    (aPhysical aCentered : Book.Ch02.TriadicCoeffFamily d)
    (f : CoeffField d)
    (hPhysical :
      (aPhysical.coeffOn (translateCube z Q)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (translateCube z Q))] f)
    (hCentered : (aCentered.coeffOn Q).toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)]
        translateCoeffField (cubeTranslationVector z Q) f)
    (s : ℝ) (p q : Book.Ch02.MultiscaleExponent) (a0 : Mat d) :
    Book.Ch02.HomogenizationErrorOnCube (translateCube z Q) s p q
        aPhysical a0 =
      Book.Ch02.HomogenizationErrorOnCube Q s p q aCentered a0 := by
  apply Book.Ch02.HomogenizationErrorOnCube_translateCube_of_normalizedBlockResponseMax
  intro l R hR
  exact normalizedBlockResponseMax_translate_of_physical_ae
    z Q l R hR aPhysical aCentered f hPhysical hCentered a0

end

end RowSupply
end HighContrast
end HCPolySupport
