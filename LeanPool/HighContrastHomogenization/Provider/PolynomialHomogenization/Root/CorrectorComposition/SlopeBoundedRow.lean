/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.C1SlopeBoundedDecay
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.PrintOrderGaugeRow

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.SlopeBoundedRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The undelayed exact-gauge row, with its slope norm and its good tail exported

`Root.exists_printOrderUndelayedExactGaugeRow` returns a slope `e` and the
simultaneous-slope estimate on the cubes `Finset.Icc n m`, and nothing else.
Two further data are needed, and the proof already has them in hand:

* **the slope norm** `euclideanNorm e ≤ Aslope * ‖Du‖_{Q_m}`, exported by
  `exists_scalarIdentityInfiniteCorrectorC1ConstantsWithSlope`;
* **the good tail** `ScalarIdentityGoodTail aIdentity (printCertificateOrder g)
  (c / 2) (triadicCeilingIndex x)` together with the local-Cauchy witness,
  which is what lets a consumer feed the existing
  `exists_scalarIdentityGoodTailJointWeightedGradientBoundConstant` and obtain
  `‖e + ∇Φ_e‖_{Q_q} ≤ B * euclideanNorm e` at every generation above the start.

Both are needed for the **near-terminal band** of the large-scale C¹ slope approximation's ball
terminal, where
the canonical outer cube of `r` overshoots every triadic cube contained in the
ball of radius `R`, so the cube row is silent and the estimate must be closed
by the corrector's own energy.

Nothing here is an estimate: the two statements below are the ones with
extra conjuncts that their own proofs already produce.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- **The printed-order C¹ smallness ceiling, with the slope norm.** -/
theorem exists_printOrderC1SmallnessCeilingWithSlope
    (d : ℕ) [NeZero d] (g eta : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hetaHalf : 1 / 2 ≤ eta) (heta1 : eta < 1) :
    ∃ (A Aslope cMax : ℝ), 0 < A ∧ 0 < Aslope ∧
      cMax ∈ Set.Ioo (0 : ℝ) 1 ∧
      cMax ≤ canonicalCorrectorSmallness d g hg ∧
      ∀ (aIdentity : Book.Ch03.CoeffFamily d) (delta : ℝ) (n0 : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) cMax →
        ScalarIdentityGoodTail aIdentity (printCertificateOrder g) delta n0 →
        FiniteAffineCorrectionLocalCauchy aIdentity ∧
        ∀ (Phi : Vec d → NormalizedLocalH1Carrier d),
          IsFiniteAffineCorrectionJointLocalEquation aIdentity Phi →
          ∀ (n m : ℕ), n0 ≤ (n : ℤ) → n + 2 ≤ m →
            ∀ u : Book.Ch03.CubeSolution (originCube d (m : ℤ)) aIdentity,
              ∃ e : Vec d,
                euclideanNorm e ≤ Aslope *
                  Book.Ch03.h1EnergyNormOnCube
                    (originCube d (m : ℤ)) aIdentity u.toH1 ∧
                ∀ q : ℕ, q ∈ Finset.Icc n m →
                  weightedGradNorm
                      (aIdentity.coeffOn (originCube d (q : ℤ))).toCoeffField
                      (openCubeSet (originCube d (q : ℤ)))
                      (fun y ↦ u.toH1.grad y -
                        (e + (Phi e).globalGradientRepresentative y)) ≤
                    ENNReal.ofReal
                        (A * Real.rpow 3 (-eta * ((m - q : ℕ) : ℝ))) *
                      weightedGradNorm
                        (aIdentity.coeffOn (originCube d (m : ℤ))).toCoeffField
                        (openCubeSet (originCube d (m : ℤ))) u.toH1.grad := by
  obtain ⟨A, Aslope, cC1, hA, hAslope, hcC1, hrow⟩ :=
    exists_scalarIdentityInfiniteCorrectorC1ConstantsWithSlope d
      (printCertificateOrder g) eta
      (printCertificateOrder_pos_of_mem_Ico hg)
      (printCertificateOrder_lt_half_of_mem_Ico hg) hetaHalf heta1
  obtain ⟨cCauchy, hcCauchy, hCauchy⟩ :=
    exists_finiteAffineCorrectionLocalCauchyThreshold d
      (printCertificateOrder g)
      (printCertificateOrder_pos_of_mem_Ico hg)
      (printCertificateOrder_lt_half_of_mem_Ico hg)
  have hc55 := canonicalCorrectorSmallness_mem d g hg
  refine ⟨A, Aslope,
    min (canonicalCorrectorSmallness d g hg) (min cC1 cCauchy),
    hA, hAslope, ⟨lt_min hc55.1 (lt_min hcC1.1 hcCauchy.1),
      (min_le_left _ _).trans_lt hc55.2⟩, min_le_left _ _, ?_⟩
  intro aIdentity delta n0 hdelta hgood
  have hdeltaC1 : delta ∈ Set.Ioc (0 : ℝ) cC1 :=
    ⟨hdelta.1, hdelta.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hdeltaCauchy : delta ∈ Set.Ioc (0 : ℝ) cCauchy :=
    ⟨hdelta.1, hdelta.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  refine ⟨hCauchy aIdentity delta n0 hdeltaCauchy hgood, ?_⟩
  intro Phi hPhi n m hn hnm u
  exact hrow aIdentity delta n0 hdeltaC1 hgood
    (hCauchy aIdentity delta n0 hdeltaCauchy hgood) Phi hPhi n m hn hnm u

/-- **The undelayed exact-gauge simultaneous-slope row, with the slope norm,
the local-Cauchy witness and the good tail exported.** -/
theorem exists_printOrderUndelayedExactGaugeRowWithSlope
    (d : ℕ) [NeZero d] (g eta : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hetaHalf : 1 / 2 ≤ eta) (heta1 : eta < 1) :
    ∃ (A Aslope cMax : ℝ), 0 < A ∧ 0 < Aslope ∧
      cMax ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (c kappa : ℝ), 0 < c → c ≤ cMax →
        ∀ (abar : Mat d) (a : CoeffSpace d) (x : ℝ),
          PrintOrderQuantitativeNormalizedReferenceCertificate abar g
              (correctorTargetAmplitude c kappa) kappa x a →
          ∃ (hS : (symmPart abar).PosDef)
              (hI : (symmPart (1 : Mat d)).PosDef)
              (aIdentity : Book.Ch03.CoeffFamily d)
              (Phi : Vec d → NormalizedLocalH1Carrier d)
              (_hCauchy : FiniteAffineCorrectionLocalCauchy aIdentity),
            (∀ Q : TriadicCube d,
              (aIdentity.coeffOn Q).toCoeffField =
                (⇑((canonicalIdentityGeometry d g hg).centeredCoeffSpace
                  (1 : Mat d) hI (exactGaugeCoeffSpace a abar hS)).1 :
                    CoeffField d)) ∧
            IsFiniteAffineCorrectionJointLocalEquation aIdentity Phi ∧
            ScalarIdentityGoodTail aIdentity (printCertificateOrder g)
              (c / 2) (Quenched.triadicCeilingIndex x : ℤ) ∧
            ∀ (n m : ℕ),
              (Quenched.triadicCeilingIndex x : ℤ) ≤ (n : ℤ) → n + 2 ≤ m →
                ∀ u : Book.Ch03.CubeSolution (originCube d (m : ℤ)) aIdentity,
                  ∃ e : Vec d,
                    euclideanNorm e ≤ Aslope *
                      Book.Ch03.h1EnergyNormOnCube
                        (originCube d (m : ℤ)) aIdentity u.toH1 ∧
                    ∀ q : ℕ, q ∈ Finset.Icc n m →
                      weightedGradNorm
                          (aIdentity.coeffOn
                            (originCube d (q : ℤ))).toCoeffField
                          (openCubeSet (originCube d (q : ℤ)))
                          (fun y ↦ u.toH1.grad y -
                            (e + (Phi e).globalGradientRepresentative y)) ≤
                        ENNReal.ofReal
                            (A * Real.rpow 3 (-eta * ((m - q : ℕ) : ℝ))) *
                          weightedGradNorm
                            (aIdentity.coeffOn
                              (originCube d (m : ℤ))).toCoeffField
                            (openCubeSet (originCube d (m : ℤ)))
                            u.toH1.grad := by
  obtain ⟨A, Aslope, cMax, hA, hAslope, hcMax, hcMax55, hceiling⟩ :=
    exists_printOrderC1SmallnessCeilingWithSlope d g eta hg hetaHalf heta1
  refine ⟨A, Aslope, cMax, hA, hAslope, hcMax, ?_⟩
  intro c kappa hc hccMax abar a x hcert
  have hcertData := hcert
  obtain ⟨_hSc, _aRefc, _hsc, _hsch, _hampc, hKappa, hxOne, _harefc, _htailc⟩ :=
    hcertData
  obtain ⟨hS, hI, aIdentity, hIdentity, hPower⟩ :=
    exists_canonicalIdentityGaugeFamily hg hcert
  have hAmplitudeNonneg : 0 ≤ correctorTargetAmplitude c kappa :=
    (correctorTargetAmplitude_pos hc hKappa).le
  have hgood : ScalarIdentityGoodTail aIdentity (printCertificateOrder g)
      (c / 2) (Quenched.triadicCeilingIndex x : ℤ) := by
    have hraw := hPower.goodTail hAmplitudeNonneg hKappa hxOne
    rwa [correctorTargetAmplitude_div hKappa] at hraw
  have hhalfCeiling : c / 2 ∈ Set.Ioc (0 : ℝ) cMax :=
    ⟨by linarith only [hc], by linarith only [hc, hccMax]⟩
  have hhalf55 : c / 2 ∈ Set.Ioc (0 : ℝ)
      (canonicalCorrectorSmallness d g hg) :=
    ⟨hhalfCeiling.1, hhalfCeiling.2.trans hcMax55⟩
  obtain ⟨hCauchy, hrow⟩ := hceiling aIdentity (c / 2)
    (Quenched.triadicCeilingIndex x : ℤ) hhalfCeiling hgood
  obtain ⟨Phi, hPhi, _htail⟩ :=
    exists_identityGaugeJointLimitWithTail d g
      (canonicalIdentityGeometry d g hg) hg
      (canonicalIdentityDualRegularity d g hg)
      (exactGaugeCoeffSpace a abar hS) hI aIdentity hIdentity
      (c / 2) (Quenched.triadicCeilingIndex x : ℤ) hhalf55 hgood
  exact ⟨hS, hI, aIdentity, Phi, hCauchy, hIdentity, hPhi, hgood,
    hrow Phi hPhi⟩

end

end Root
end HighContrast
end HCPolySupport
