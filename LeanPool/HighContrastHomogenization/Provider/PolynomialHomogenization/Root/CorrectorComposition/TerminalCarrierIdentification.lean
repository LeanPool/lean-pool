/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.PushCorrectorFamilyDischarge
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.ClosedBallNearRatio
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.GaugeRepresentativeJoin

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.TerminalCarrierIdentification

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# the large-scale C¹ slope approximation clause residue (iii): the terminal's carrier **is** the
row's carrier

The large-scale C¹ slope approximation clause ball terminal must exhibit one family `PhiRef : Vec
d →
NormalizedLocalH1Carrier d` that simultaneously

* pulls the pushforward marker's slope family back to the gauge frame
  (`ExactRootGaugeTerminal`'s first clause), which forces
  `PhiRef v = Root.rootJointCarrier d v (normalizedSample abar hS a)`, and
* carries the cube row's decay, which forces `PhiRef` to be the row's own
  `Phi`, the joint local limit of the identity-gauge family `aIdentity`.

These two are the same object, and the identification
is "a rewrite, not an analytic step".  This module performs it.  The chain is

```
(selected datum).aFin  ≈ᵃᵉ  aRef   (RootCorrectorData.coeffAll + normalizedSample_ae)
aRef                   ≈ᵃᵉ  aIdentity   (rawIdentityCoeff_ae_global)
```

and `CorrectorComposition.jointLocalLimit_eq_of_aeeq` turns the composite a.e. equality into
a **literal** equality of joint local limits;
`isFiniteAffineCorrectionJointLocalLimit_iff_eq` pins the row's `Phi` to that
same limit.  No estimate, no measure theory beyond `ae_restrict_of_ae`.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- **The root joint carrier is the row's carrier.**  Every hypothesis is one
the undelayed row already returns. -/
theorem rootJointCarrier_eq_rowCarrier (d : ℕ) [NeZero d]
    (geom : RoundedGenerationAnalyticGeometry d)
    {abar : Mat d} (hS : (symmPart abar).PosDef) {a : CoeffSpace d}
    (hev : Root.RootCorrectorEvent d (Root.normalizedSample abar hS a))
    (hI : (symmPart (1 : Mat d)).PosDef)
    (aIdentity : Book.Ch03.CoeffFamily d)
    (hIdentity : ∀ Q : TriadicCube d,
      (aIdentity.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace (1 : Mat d) hI
          (exactGaugeCoeffSpace a abar hS)).1 : CoeffField d))
    (hCauchyId : FiniteAffineCorrectionLocalCauchy aIdentity)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation aIdentity Phi) :
    ∀ v : Vec d,
      Root.rootJointCarrier d v (Root.normalizedSample abar hS a) = Phi v := by
  obtain ⟨aRef, hRefRaw⟩ := exists_normalizedReferenceCoeffFamily a abar hS 0
  have hRef : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          (⇑(normalizedCenteredCoeff a abar hS).1) := by
    intro Q
    simpa using hRefRaw Q
  have hgauge : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField = Root.gaugeCoeff a abar hS :=
    fun Q ↦ hRef Q
  have haeq1 : Book.Ch02.TriadicCoeffFamily.AEEq
      (Root.selectedRootCorrectorData
        (Root.normalizedSample abar hS a) hev).aFin aRef := by
    intro Q
    refine ae_restrict_of_ae ?_
    rw [hgauge Q]
    exact ((Root.selectedRootCorrectorData
      (Root.normalizedSample abar hS a) hev).coeffAll Q).trans
        (Root.normalizedSample_ae abar hS a)
  have haeq2 : Book.Ch02.TriadicCoeffFamily.AEEq aRef aIdentity := by
    intro Q
    exact ae_restrict_of_ae
      (rawIdentityCoeff_ae_global geom hS aRef hRef hI aIdentity
        hIdentity Q)
  have haeq : Book.Ch02.TriadicCoeffFamily.AEEq
      (Root.selectedRootCorrectorData
        (Root.normalizedSample abar hS a) hev).aFin aIdentity :=
    fun Q ↦ (haeq1 Q).trans (haeq2 Q)
  have hlimit :
      finiteAffineCorrectionJointLocalLimit
          (Root.selectedRootCorrectorData
            (Root.normalizedSample abar hS a) hev).aFin
          (Root.selectedRootCorrectorData
            (Root.normalizedSample abar hS a) hev).hCauchy =
        finiteAffineCorrectionJointLocalLimit aIdentity hCauchyId :=
    jointLocalLimit_eq_of_aeeq haeq _ hCauchyId
  have hPhiEq : Phi = finiteAffineCorrectionJointLocalLimit aIdentity hCauchyId :=
    (isFiniteAffineCorrectionJointLocalLimit_iff_eq aIdentity hCauchyId Phi).mp
      (by simpa only [IsFiniteAffineCorrectionJointLocalLimit] using hPhi.1)
  intro v
  rw [Root.rootJointCarrier_of_event v hev, hlimit, hPhiEq]

/-- **The terminal's gauge-pullback clause, at the row's carrier.**  Under the
pushforward marker the clause is definitional: `pushforwardGradient_pullback_identity`
is a pointwise identity, and the carrier it names is the row's by
`rootJointCarrier_eq_rowCarrier`. -/
theorem pushforwardMarker_gaugePullback (d : ℕ) [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) {a : CoeffSpace d}
    (ha : a ∈ Root.pushforwardCore d abar hS)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (hcarrier : ∀ v : Vec d,
      Root.rootJointCarrier d v (Root.normalizedSample abar hS a) = Phi v)
    (e : Vec d) :
    (fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
        (e + Root.pushforwardPhysicalGradPhi d abar hS e a
          (matVecMul (Selection.normalizedRoot (symmPart abar)) y))) =ᵐ[volume]
      fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar)) e +
        (Phi (matVecMul (Selection.normalizedRoot (symmPart abar)) e)).globalGradientRepresentative
          y := by
  refine Filter.Eventually.of_forall fun y ↦ ?_
  have hcar : Root.rootJointCarrier d
      (matVecMul (Root.gaugeRoot abar) e)
      (Root.normalizedSample abar hS a) =
      Phi (matVecMul (Selection.normalizedRoot (symmPart abar)) e) :=
    hcarrier _
  rw [Root.pushforwardPhysicalGradPhi_of_mem ha e, hcar]
  exact Root.pushforwardGradient_pullback_identity hS _ e y

end

end CorrectorComposition
end HighContrast
end HCPolySupport
