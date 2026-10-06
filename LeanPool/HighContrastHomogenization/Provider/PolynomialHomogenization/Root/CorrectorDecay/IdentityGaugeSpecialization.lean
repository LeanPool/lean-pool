/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBootstrapIdentityGrid
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationUniformRecurrence

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentityGaugeSpecialization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Exact identity specialization of the printed rounded recurrence

In the normalized gauge, the symmetric reference is literally the identity.
At an admissible rounded generation, rounding fixes that identity exactly.
The lemmas below isolate this specialization and its a.e.-invariance.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

private theorem symmPart_one {d : ℕ} :
    symmPart (1 : Mat d) = 1 := by
  exact symmPart_eq_of_isSymm Matrix.isSymm_one

private theorem skewPart_one {d : ℕ} :
    skewPart (1 : Mat d) = 0 := by
  ext i j
  change ((if i = j then 1 else 0) - (if j = i then 1 else 0)) / 2 = 0
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

private theorem specBound_one {d : ℕ} [NeZero d] :
    specBound (1 : Mat d) = 1 := by
  rw [specBound_eq_norm Matrix.PosSemidef.one, norm_one]

theorem roundedReferenceMatrixAtGeneration_one
    {d : ℕ} [NeZero d] {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    (hI : (symmPart (1 : Mat d)).PosDef) :
    roundedReferenceMatrixAtGeneration l (1 : Mat d) hI = 1 := by
  unfold roundedReferenceMatrixAtGeneration
  have hgrid : roundedGrid l (1 : Mat d) = 1 :=
    Quenched.roundedGrid_one_of_nonneg
      ((Int.natCast_nonneg (kZero d)).trans hl)
  rw [symmPart_one, hgrid, inv_one, specBound_one, one_smul]
  simp [matTranspose]

/-- The selected-generation centered coefficient at identity is pointwise the
input coefficient.  This is where the rounded construction becomes exact,
rather than merely close. -/
theorem roundedCenteredCoefficientAtGeneration_one
    {d : ℕ} [NeZero d] {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    (hI : (symmPart (1 : Mat d)).PosDef) (a : CoeffField d) :
    roundedCenteredCoefficientAtGeneration l hl (1 : Mat d) hI a = a := by
  funext x
  have hgrid : roundedGrid l (1 : Mat d) = 1 :=
    Quenched.roundedGrid_one_of_nonneg
      ((Int.natCast_nonneg (kZero d)).trans hl)
  rw [roundedCenteredCoefficientAtGeneration_apply,
    symmPart_one, hgrid, inv_one,
    specBound_one, one_smul, skewPart_one, sub_zero,
    matVecMul_one]
  simp [matTranspose]

/-- Re-rounding a gauge coefficient at the identity changes only its chosen
representative, not its a.e. class. -/
theorem identityCenteredCoeffSpace_ae
    {d : ℕ} [NeZero d] (geom : RoundedGenerationAnalyticGeometry d)
    (hI : (symmPart (1 : Mat d)).PosDef) (a : CoeffSpace d) :
    (⇑(geom.centeredCoeffSpace (1 : Mat d) hI a).1 : CoeffField d)
        =ᵐ[volume] (⇑a.1 : CoeffField d) := by
  have h := roundedCenteredCoeffSpaceAtGeneration_ae
    geom.generation geom.admissible (1 : Mat d) hI a
  exact h.trans (Filter.Eventually.of_forall fun x => by
    rw [roundedCenteredCoefficientAtGeneration_one geom.admissible hI a.1])

/-- A.e.-equivalent coefficient families have the same scalar-identity weak
error at every scale and order. -/
theorem scalarIdentityWeakError_eq_of_aeeq
    {d : ℕ} [NeZero d] {a b : Book.Ch02.TriadicCoeffFamily d}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b) (s : ℝ) (m : ℤ) :
    scalarIdentityWeakError a s m = scalarIdentityWeakError b s m := by
  unfold scalarIdentityWeakError
  exact Book.Ch02.HomogenizationErrorOnCube_eq_ofAEEq hab
    (originCube d m) s .infinity (.finite 2) (1 : Mat d)

theorem scalarIdentityPowerTail_of_aeeq
    {d : ℕ} [NeZero d] {a b : Book.Ch02.TriadicCoeffFamily d}
    {s amplitude kappa x : ℝ}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b)
    (h : ScalarIdentityPowerTail a s amplitude kappa x) :
    ScalarIdentityPowerTail b s amplitude kappa x := by
  intro m hxm
  rw [← scalarIdentityWeakError_eq_of_aeeq hab s m]
  exact h m hxm

/-- At identity, the selected-generation physical response row is exactly the
scalar-identity homogenization error of any family realizing the selected
coefficient space. -/
theorem roundedGenerationSpatialWeakError_one_eq
    {d : ℕ} [NeZero d] (geom : RoundedGenerationAnalyticGeometry d)
    (a : CoeffSpace d) (hI : (symmPart (1 : Mat d)).PosDef)
    (aIdentity : Book.Ch03.CoeffFamily d)
    (hIdentity : ∀ Q : TriadicCube d,
      (aIdentity.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace (1 : Mat d) hI a).1 : CoeffField d))
    (s : ℝ) (m : ℤ) :
    geom.spatialWeakError a (1 : Mat d) hI s m =
      scalarIdentityWeakError aIdentity s m := by
  have href : geom.referenceMatrix (1 : Mat d) hI = 1 := by
    exact roundedReferenceMatrixAtGeneration_one geom.admissible hI
  have hbridge := homogenizationErrorOnCube_eq_roundedGenerationSpatialWeakError
    (geom := geom) a (1 : Mat d) hI aIdentity hIdentity s m
  rw [← hbridge]
  unfold scalarIdentityWeakError
  rw [href]

/-- The exact gauge coefficient carried by a printed certificate. -/
@[expose]
def exactGaugeCoeffSpace
    {d : ℕ} [NeZero d] (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) : CoeffSpace d :=
  affinePullbackCoeffSpace (Selection.normalizedRoot (symmPart abar))
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (normalizedRoot_posDef_of_posDef hS).isUnit)
    (normalizedCenteredCoeff a abar hS)

theorem exactGaugeCoeffSpace_ae
    {d : ℕ} [NeZero d] (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    (⇑(exactGaugeCoeffSpace a abar hS).1 : CoeffField d) =ᵐ[volume]
      affineCoefficient (Selection.normalizedRoot (symmPart abar))
        ((Matrix.isUnit_iff_isUnit_det _).mp
          (normalizedRoot_posDef_of_posDef hS).isUnit)
        ⇑(normalizedCenteredCoeff a abar hS).1 := by
  exact affinePullbackCoeffSpace_ae _ _ _

/-- Package the certificate's exact family on the selected identity geometry.
The resulting family is a.e.-equivalent to the certificate family and retains
its complete quantitative power tail. -/
theorem exists_identityGaugeFamily
    {d : ℕ} [NeZero d] {g : ℝ} {a : CoeffSpace d} {abar : Mat d}
    {amplitude kappa x : ℝ}
    (hcert : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g amplitude kappa x a)
    (geom : RoundedGenerationAnalyticGeometry d) :
    ∃ (hS : (symmPart abar).PosDef)
      (hI : (symmPart (1 : Mat d)).PosDef)
      (aIdentity : Book.Ch03.CoeffFamily d),
      (∀ Q : TriadicCube d,
        (aIdentity.coeffOn Q).toCoeffField =
          (⇑(geom.centeredCoeffSpace (1 : Mat d) hI
            (exactGaugeCoeffSpace a abar hS)).1 : CoeffField d)) ∧
      ScalarIdentityPowerTail aIdentity (printCertificateOrder g)
        amplitude kappa x := by
  obtain ⟨hS, aRef, _hs, _hsHalf, _hAmplitude, _hKappa, _hx,
    haRef, htail⟩ := hcert
  have hI : (symmPart (1 : Mat d)).PosDef := by
    rw [symmPart_one]
    exact Matrix.PosDef.one
  let aGauge := exactGaugeCoeffSpace a abar hS
  obtain ⟨aIdentity, hIdentity⟩ :=
    exists_coeffFamily_of_coeffSpace
      (geom.centeredCoeffSpace (1 : Mat d) hI aGauge)
  have hcentered := identityCenteredCoeffSpace_ae geom hI aGauge
  have hgauge := exactGaugeCoeffSpace_ae a abar hS
  have hfamilies : Book.Ch02.TriadicCoeffFamily.AEEq aRef aIdentity := by
    intro Q
    unfold Book.Ch02.CoeffOn.AEEq
    rw [haRef Q, hIdentity Q]
    exact ae_restrict_of_ae (hgauge.symm.trans hcentered.symm)
  refine ⟨hS, hI, aIdentity, hIdentity, ?_⟩
  exact scalarIdentityPowerTail_of_aeeq hfamilies htail

end

end HighContrast
end HCPolySupport
