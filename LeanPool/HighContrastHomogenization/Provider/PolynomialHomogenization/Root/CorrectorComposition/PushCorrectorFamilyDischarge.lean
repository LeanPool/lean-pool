/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.CertificateProjections
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.JointCarrierAEEq
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.SelectedReferenceResidue

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.PushCorrectorFamilyDischarge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The corrector-and-flux decay clause/the Liouville and C¹ clauses family corrector-family
hypothesis, discharged

The corrector-family half of the decay, Liouville and C¹ clauses reduces to a
single proposition,
`Root.SelectedReferenceCoeffExact d`: the *selected* corrector datum's
reference family must represent the normalized-root coefficient **pointwise**
on every triadic cube.  It is not provable, because the datum is chosen by
`Classical.choice` and the structure carried only an almost-everywhere,
origin-cube-only identity.

The repair is **one extra field** on `RootCorrectorData`
(`coeffAll`, an a.e. identity on *every* triadic cube), which the converter that
supplies the datum proves pointwise and previously discarded.  With it the
residue disappears entirely, and *without* indexing the datum by its exact
field:

* the selected family and the certificate's exact-gauge reference family
  `exists_normalizedReferenceCoeffFamily` are `Book.Ch02.TriadicCoeffFamily.AEEq`;
* along that a.e. equality the joint local limit is **literally the same carrier
  family** (`CorrectorComposition.jointLocalLimit_eq_of_aeeq`), the local Cauchy condition
  transfers, and so does the weak-error good tail
  (`Book.Ch02.HomogenizationErrorOnCube_eq_ofAEEq`);
* so `normalizedJoint` may be answered with the *certificate's* family, which
  carries the pointwise coefficient identity by construction, while the two
  pullback clauses stay definitional at the pushforward pair with additive
  constant `0`.

**`RootPushCanonicalFamily` is therefore a theorem, with the normalized supply
as its only input.**  the decay, Liouville and C¹ clauses's corrector-family hypothesis half are
unconditional.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## The good tail transfers -/

/-- The scalar identity weak-error row is an a.e.-representative invariant, so
the good tail transfers along an a.e. equality of coefficient families. -/
theorem scalarIdentityGoodTail_of_aeeq
    {a b : Book.Ch02.TriadicCoeffFamily d}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b) {s delta : ℝ} {n : ℤ}
    (h : ScalarIdentityGoodTail a s delta n) :
    ScalarIdentityGoodTail b s delta n := by
  have hsum : ∀ k : ℤ,
      scalarIdentityWeakError b s k = scalarIdentityWeakError a s k := by
    intro k
    exact (Book.Ch02.HomogenizationErrorOnCube_eq_ofAEEq hab (originCube d k) s
      Book.Ch02.MultiscaleExponent.infinity
      (Book.Ch02.MultiscaleExponent.finite 2) (1 : Mat d)).symm
  intro m hm
  have hrow := h m hm
  unfold ScalarIdentityGoodTailOnInterval at hrow ⊢
  simpa only [hsum] using hrow

/-! ## The corrector-family hypothesis -/

/-- **The pushforward canonical corrector-family hypothesis, from the normalized supply alone.** -/
theorem rootPushCanonicalFamily_of_normalizedSupply [NeZero d]
    {GoodScale : Mat d → CoeffSpace d → ℝ → Prop}
    (hsupply : Root.RootNormalizedSupply d GoodScale) :
    Root.RootPushCanonicalFamily d GoodScale := by
  intro abar hS
  refine ⟨?_, ?_⟩
  · intro a x hgood e
    exact (Root.pushforwardPhysical_equation d abar hS
      (mem_invariantTranslationCore_iff.mpr (hsupply abar hS a x hgood)) e).1
  · intro a x hgood
    have ha : a ∈ Root.pushforwardCore d abar hS :=
      mem_invariantTranslationCore_iff.mpr (hsupply abar hS a x hgood)
    have hev : Root.RootCorrectorEvent d (Root.normalizedSample abar hS a) :=
      Root.pushforwardEvent_of_mem_core_self ha
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
    have haeq : Book.Ch02.TriadicCoeffFamily.AEEq
        (Root.selectedRootCorrectorData
          (Root.normalizedSample abar hS a) hev).aFin aRef := by
      intro Q
      refine ae_restrict_of_ae ?_
      rw [hgauge Q]
      exact ((Root.selectedRootCorrectorData
        (Root.normalizedSample abar hS a) hev).coeffAll Q).trans
          (Root.normalizedSample_ae abar hS a)
    have hCauchyRef : FiniteAffineCorrectionLocalCauchy aRef :=
      finiteAffineCorrectionLocalCauchy_of_aeeq haeq
        (Root.selectedRootCorrectorData
          (Root.normalizedSample abar hS a) hev).hCauchy
    have hlimit :
        finiteAffineCorrectionJointLocalLimit
            (Root.selectedRootCorrectorData
              (Root.normalizedSample abar hS a) hev).aFin
            (Root.selectedRootCorrectorData
              (Root.normalizedSample abar hS a) hev).hCauchy =
          finiteAffineCorrectionJointLocalLimit aRef hCauchyRef :=
      jointLocalLimit_eq_of_aeeq haeq _ hCauchyRef
    obtain ⟨L, hL⟩ := Root.exists_natDelay_ge
      (Root.selectedRootCorrectorData
        (Root.normalizedSample abar hS a) hev).start
      (Quenched.triadicCeilingIndex x)
    refine ⟨hS,
      (Root.selectedRootCorrectorData
        (Root.normalizedSample abar hS a) hev).order,
      (Root.selectedRootCorrectorData
        (Root.normalizedSample abar hS a) hev).tolerance,
      aRef, L, hCauchyRef,
      (Root.selectedRootCorrectorData
        (Root.normalizedSample abar hS a) hev).order_pos,
      (Root.selectedRootCorrectorData
        (Root.normalizedSample abar hS a) hev).order_lt, hRef,
      scalarIdentityGoodTail_of_aeeq haeq
        ((Root.selectedRootCorrectorData
          (Root.normalizedSample abar hS a) hev).goodTail.mono_start hL),
      Root.finiteAffineCorrectionJointLocalLimit_isJointLocalEquation _ _, ?_⟩
    intro e
    have hcarrier : Root.rootJointCarrier d
        (matVecMul (Root.gaugeRoot abar) e)
        (Root.normalizedSample abar hS a) =
        finiteAffineCorrectionJointLocalLimit aRef hCauchyRef
          (matVecMul (Root.gaugeRoot abar) e) := by
      rw [Root.rootJointCarrier_of_event _ hev, hlimit]
    constructor
    · refine ⟨0, Filter.Eventually.of_forall fun y ↦ ?_⟩
      rw [Root.pushforwardPhysicalPhi_of_mem ha e, hcarrier]
      exact (Root.pushforwardValue_pullback_identity hS _ y).trans (add_zero _).symm
    · refine Filter.Eventually.of_forall fun y ↦ ?_
      rw [Root.pushforwardPhysicalGradPhi_of_mem ha e, hcarrier]
      exact Root.pushforwardGradient_pullback_identity hS _ e y

/-! ## The consequences -/

end

end CorrectorComposition
end HighContrast
end HCPolySupport
