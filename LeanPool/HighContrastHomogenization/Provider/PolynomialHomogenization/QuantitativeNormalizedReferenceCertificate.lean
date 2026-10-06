/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootGoodScaleProvider
public import LeanPool.HighContrastHomogenization.Provider.Regularity.QuantitativeGoodTail

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.QuantitativeNormalizedReferenceCertificate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# A rate-bearing normalized reference certificate

The deterministic regularity modules use one normalized coefficient family at
one real effective scale.  The certificate below retains the response order,
pointwise decay exponent, amplitude, and coefficient identification instead
of erasing them into a qualitative summable tail.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- A normalized reference family with a fixed small response order and a
fixed pointwise power tail above one common real effective scale.  The order,
amplitude, and exponent are parameters so they are selected before a sample. -/
@[expose]
def QuantitativeNormalizedReferenceCertificate [NeZero d] (abar : Mat d)
    (s amplitude kappa x : ℝ) (a : CoeffSpace d) : Prop :=
  ∃ (hS : (symmPart abar).PosDef) (aRef : Book.Ch03.CoeffFamily d),
    0 < s ∧ s < 1 / 4 ∧ 0 ≤ amplitude ∧ 0 < kappa ∧ 1 ≤ x ∧
    (∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ⇑(normalizedCenteredCoeff a abar hS).1) ∧
    ScalarIdentityPowerTail aRef s amplitude kappa x

/-- Deterministic enlargement preserves a quantitative normalized reference
certificate, with the exact rebased amplitude and no change of family. -/
theorem QuantitativeNormalizedReferenceCertificate.rebase
    [NeZero d] {abar : Mat d} {a : CoeffSpace d}
    {x y s amplitude kappa : ℝ}
    (h : QuantitativeNormalizedReferenceCertificate
      abar s amplitude kappa x a)
    (hy : 0 < y) (hxy : x ≤ y) :
    QuantitativeNormalizedReferenceCertificate abar s
      (amplitude * (y / x) ^ (-kappa)) kappa y a := by
  obtain ⟨hS, aRef, hs, hsLt, hAmplitude,
    hKappa, hx, haRef, htail⟩ := h
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  refine ⟨hS, aRef,
    hs, hsLt, ?_, hKappa, hx.trans hxy, haRef, ?_⟩
  · exact mul_nonneg hAmplitude
      (Real.rpow_nonneg (div_nonneg hy.le hxpos.le) _)
  · exact htail.rebase hxpos hy hxy

/-- Forgetting the retained pointwise rate gives the underlying qualitative
normalized-reference certificate at the same effective scale. -/
theorem QuantitativeNormalizedReferenceCertificate.to_normalizedReferenceGoodScale
    [NeZero d] {abar : Mat d} {a : CoeffSpace d}
    {x s amplitude kappa : ℝ}
    (h : QuantitativeNormalizedReferenceCertificate
      abar s amplitude kappa x a) :
    NormalizedReferenceGoodScale abar a x := by
  obtain ⟨hS, aRef, hs, hsLt, hAmplitude,
    hKappa, hx, haRef, htail⟩ := h
  have hsHalf : s < 1 / 2 := hsLt.trans (by norm_num)
  refine ⟨hS, s, amplitude / (1 - (3 : ℝ) ^ (-kappa)), aRef, 0,
    hs, hsHalf, haRef, ?_⟩
  simpa only [Nat.add_zero] using htail.goodTail hAmplitude hKappa hx

end

end HighContrast
end HCPolySupport
