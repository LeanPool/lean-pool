/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.BallTerminalBranchEstimates
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.RowCertificateRebase
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.CorrectorEnergyOnCube

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.ExactRootGaugeTerminalPieces

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Small pieces the large-scale C¹ slope approximation terminal assembly needs

Three facts, each one step:

* the joint local limit at slope `0` has vanishing gradient representative
  (`finiteAffineCorrectionJointLocalLimit_smul` at `c = 0`), which is what makes
  the **degenerate** case of the terminal — the one where the whole radius range
  sits in the near-terminal band — closable with `eRef := 0` and no triangle
  inequality at all;
* a triadic cube contained in the exact-root pullback ball has exact-root image
  inside the ellipsoid, so the terminal cube solution applies;
* the affine-coefficient field of the certificate's reference family is a.e.
  the identity-gauge family's, cube by cube — the bridge every energy
  comparison in the two branch estimates consumes.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The corrector at slope `0` is trivial.** -/
theorem jointLimit_zero_grad_ae [NeZero d]
    {aId : Book.Ch02.TriadicCoeffFamily d}
    (hCauchy : FiniteAffineCorrectionLocalCauchy aId)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation aId Phi) :
    (Phi 0).globalGradientRepresentative =ᵐ[volume] fun _ ↦ (0 : Vec d) := by
  have hPhiEq : Phi = finiteAffineCorrectionJointLocalLimit aId hCauchy :=
    (isFiniteAffineCorrectionJointLocalLimit_iff_eq aId hCauchy Phi).mp
      (by simpa only [IsFiniteAffineCorrectionJointLocalLimit] using hPhi.1)
  have hz : Phi 0 = NormalizedLocalH1Carrier.smulCarrier (0 : ℝ) (Phi 0) := by
    rw [hPhiEq]
    have h := finiteAffineCorrectionJointLocalLimit_smul aId hCauchy (0 : ℝ)
      (0 : Vec d)
    rwa [zero_smul] at h
  refine Filter.EventuallyEq.trans ?_
    (Filter.Eventually.of_forall fun y ↦
      zero_smul ℝ ((Phi 0).globalGradientRepresentative y))
  conv_lhs => rw [hz]
  exact Root.NormalizedLocalH1Carrier.globalGradientRepresentative_smulCarrier
    (0 : ℝ) (Phi 0)

/-- **The terminal cube solution's geometric premise.** -/
theorem matImage_subset_ellipsoid_of_subset_closedNormBall [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) {R : ℝ} {S : Set (Vec d)}
    (h : S ⊆ closedNormBall d R) :
    matImage (Selection.normalizedRoot (symmPart abar)) S ⊆ ellipsoid abar R := by
  have hq : IsUnit (Selection.normalizedRoot (symmPart abar)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (normalizedRoot_posDef_of_posDef hS).isUnit
  have heq : matImage (Selection.normalizedRoot (symmPart abar))⁻¹
      (ellipsoid abar R) = closedNormBall d R :=
    matImage_normalizedRoot_inv_ellipsoid_eq_closedNormBall hS R
  calc matImage (Selection.normalizedRoot (symmPart abar)) S
      ⊆ matImage (Selection.normalizedRoot (symmPart abar))
          (matImage (Selection.normalizedRoot (symmPart abar))⁻¹
            (ellipsoid abar R)) := by
        rw [heq]
        exact Set.image_mono h
    _ = ellipsoid abar R := matImage_matImage_inv hq (ellipsoid abar R)

/-- **The coefficient bridge.**  The exact-root affine coefficient is a.e. the
identity-gauge family's coefficient on every triadic cube. -/
theorem exactRootCoeff_ae_identityGauge [NeZero d]
    (geom : RoundedGenerationAnalyticGeometry d)
    {abar : Mat d} (hS : (symmPart abar).PosDef) {a : CoeffSpace d}
    (hI : (symmPart (1 : Mat d)).PosDef)
    (aIdentity : Book.Ch03.CoeffFamily d)
    (hIdentity : ∀ Q : TriadicCube d,
      (aIdentity.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace (1 : Mat d) hI
          (exactGaugeCoeffSpace a abar hS)).1 : CoeffField d))
    (Q : TriadicCube d) :
    affineCoefficient (Selection.normalizedRoot (symmPart abar))
        ((Matrix.isUnit_iff_isUnit_det _).mp
          (normalizedRoot_posDef_of_posDef hS).isUnit)
        (⇑(normalizedCenteredCoeff a abar hS).1) =ᵐ[volume]
      (aIdentity.coeffOn Q).toCoeffField := by
  obtain ⟨aRaw, hRawRaw⟩ := exists_normalizedReferenceCoeffFamily a abar hS 0
  have hRaw : ∀ Q' : TriadicCube d,
      (aRaw.coeffOn Q').toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          (⇑(normalizedCenteredCoeff a abar hS).1) := by
    intro Q'
    simpa using hRawRaw Q'
  have hglobal := rawIdentityCoeff_ae_global geom hS aRaw hRaw hI
    aIdentity hIdentity Q
  rwa [hRaw Q] at hglobal

end

end CorrectorComposition
end HighContrast
end HCPolySupport
