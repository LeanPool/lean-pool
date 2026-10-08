/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.SuccessorParent
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentityGaugeSpecialization
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationFiniteCaccioppoli

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentitySuccessorLocal

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Exact-identity response pricing and Caccioppoli control the successor on
the centered cube three scales inside its outer cube. -/
theorem exists_identityGaugeSuccessorLocalConstant
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (aGauge : CoeffSpace d) (hI : (symmPart (1 : Mat d)).PosDef)
        (aIdentity : Book.Ch03.CoeffFamily d),
        (∀ Q : TriadicCube d,
          (aIdentity.coeffOn Q).toCoeffField =
            (⇑(geom.centeredCoeffSpace (1 : Mat d) hI aGauge).1 :
              CoeffField d)) →
        ∀ (m : ℤ) (e : Vec d),
          scalarIdentityWeakError aIdentity
              (printCertificateOrder g) (m - 1) ≤ 1 →
          scalarIdentityWeakError aIdentity
              (printCertificateOrder g) m ≤ 1 →
          scalarIdentityWeakError aIdentity
              (printCertificateOrder g) (m + 1) ≤ 1 →
          Book.Ch03.h1EnergyNormOnCube (originCube d (m - 1 - 2))
              aIdentity (successorInnerRestriction aIdentity m e).toH1 ≤
            C * (scalarIdentityWeakError aIdentity
                  (printCertificateOrder g) m +
                scalarIdentityWeakError aIdentity
                  (printCertificateOrder g) (m + 1)) *
              euclideanNorm e := by
  obtain ⟨Cp, hCp, hparent⟩ :=
    exists_identitySuccessorParentL2Constant d g hg
  have hs : 0 < printCertificateOrder g := (printOrder_margins hg).1
  have hsHalf : printCertificateOrder g < (1 : ℝ) / 2 :=
    (printOrder_margins hg).2.1
  obtain ⟨Ccacc, hCcacc, hcacc⟩ :=
    exists_roundedGenerationFiniteLipschitzCaccioppoliAffineConstant
      d geom (printCertificateOrder g) hs hsHalf
  let C : ℝ := Ccacc * Cp
  have hC : 0 < C := mul_pos hCcacc hCp
  refine ⟨C, hC, ?_⟩
  intro aGauge hI aIdentity hIdentity m e herrPred herr0 herr1
  let s := printCertificateOrder g
  let E : ℤ → ℝ := scalarIdentityWeakError aIdentity s
  let N := euclideanNorm e
  let Wpred := cubeBesovScaleWeight 1 (originCube d (m - 1))
  let Ls := cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
    (finiteAffineSuccessorDifference aIdentity m e).toH1.toFun
  have hparent' : Wpred * Ls ≤ Cp * (E m + E (m + 1)) * N := by
    simpa only [Wpred, Ls, E, N, s] using
      hparent aIdentity m e herr0 herr1
  let uParent := finiteCubeSolutionRestriction aIdentity
    (by omega : m - 1 ≤ m) (finiteAffineSuccessorDifference aIdentity m e)
  let vInner := successorInnerRestriction aIdentity m e
  have hroundedPred : geom.spatialWeakError
      aGauge (1 : Mat d) hI s (m - 1) ≤ 1 := by
    rw [roundedGenerationSpatialWeakError_one_eq
      geom aGauge hI aIdentity hIdentity s (m - 1)]
    exact herrPred
  have hcaccRaw := hcacc aGauge (1 : Mat d) hI
    aIdentity hIdentity (m - 1) uParent 0 (0 : Vec d) hroundedPred
  have hcaccRaw' : Book.Ch03.h1EnergyNormOnCube
      (originCube d (m - 1 - 2)) aIdentity vInner.toH1 ≤
        Ccacc * (normalizedAffineCandidateError
          (originCube d (m - 1)) uParent.toH1.toFun 0 (0 : Vec d) +
          euclideanNorm (0 : Vec d)) := by
    simpa only [vInner, successorInnerRestriction, uParent] using hcaccRaw
  have hcandidate : normalizedAffineCandidateError
      (originCube d (m - 1)) uParent.toH1.toFun 0 (0 : Vec d) =
      Wpred * Ls := by
    unfold normalizedAffineCandidateError normalizedCubeL2Distance
    simp only [uParent, finiteCubeSolutionRestriction_toFun,
      vecDot_zero_left, add_zero, sub_zero, Wpred, Ls]
  calc
    Book.Ch03.h1EnergyNormOnCube (originCube d (m - 1 - 2))
        aIdentity vInner.toH1 ≤
      Ccacc * (normalizedAffineCandidateError
        (originCube d (m - 1)) uParent.toH1.toFun 0 (0 : Vec d) +
        euclideanNorm (0 : Vec d)) := hcaccRaw'
    _ = Ccacc * (Wpred * Ls) := by rw [hcandidate]; simp
    _ ≤ Ccacc * (Cp * (E m + E (m + 1)) * N) :=
      mul_le_mul_of_nonneg_left hparent' hCcacc.le
    _ = C * (scalarIdentityWeakError aIdentity s m +
        scalarIdentityWeakError aIdentity s (m + 1)) * euclideanNorm e := by
      dsimp only [C, E, N]
      ring

end

end HighContrast
end HCPolySupport
