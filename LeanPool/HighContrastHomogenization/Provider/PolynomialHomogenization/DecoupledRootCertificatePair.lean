/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRateBearingCommonAffineGoodScaleEvent

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.DecoupledRootCertificatePair

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Decoupled certificates at the polynomial-homogenization root

The deterministic regularity terminals use a privately selected small
fractional order.  The Dirichlet row uses the printed order selected after
the stochastic exponent.  Both certificates retain the same selected
contrast and rate parameters and the same exposed physical scale.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

noncomputable section

/-- The two certificates consumed at the root, with all stochastic and
calibration parameters retained in the type. -/
structure DecoupledRootGoodScale
    (d : ℕ) [NeZero d] (g c kappa : ℝ) (abar : Mat d)
    (a : CoeffSpace d) (x : ℝ) : Prop where
  privateOrder : NormalizedReferenceGoodScale abar a x
  printOrder :
    PrintOrderRateBearingCommonAffineGoodScale d g c kappa abar a x

/-- The printed-order certificate is available without changing the selected
root parameters. -/
theorem DecoupledRootGoodScale.to_printOrder
    {d : ℕ} [NeZero d] {g c kappa : ℝ} {abar : Mat d}
    {a : CoeffSpace d} {x : ℝ}
    (h : DecoupledRootGoodScale d g c kappa abar a x) :
    PrintOrderRateBearingCommonAffineGoodScale d g c kappa abar a x :=
  h.printOrder

/-- The printed quantitative field can be forgotten to the qualitative field
at the same exposed common scale. -/
theorem DecoupledRootGoodScale.of_printOrder
    {d : ℕ} [NeZero d] {g c kappa : ℝ} {abar : Mat d}
    {a : CoeffSpace d} {x : ℝ}
    (h : PrintOrderRateBearingCommonAffineGoodScale
      d g c kappa abar a x) :
    DecoupledRootGoodScale d g c kappa abar a x := by
  obtain ⟨sourceAmplitude, X, hCertificate, hx⟩ := h
  have hCertificateForRebase := hCertificate
  obtain ⟨_hS, _aRef, _hs, _hsLt, _hAmplitude,
    hkappa, hX, _haRef, _htail⟩ := hCertificate
  have hXx : X a ≤ x := by
    rw [hx]
    exact le_commonQuantitativeAffineScale hkappa (zero_le_one.trans hX)
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one (hX.trans hXx)
  refine ⟨?_, ⟨sourceAmplitude, X, hCertificateForRebase, hx⟩⟩
  exact
    PrintOrderQuantitativeNormalizedReferenceCertificate.to_normalizedReferenceGoodScale
      (PrintOrderQuantitativeNormalizedReferenceCertificate.rebase
        hCertificateForRebase hxpos hXx)

end

end Root
end HighContrast
end HCPolySupport
