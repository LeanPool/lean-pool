/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationResponseMax
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PrintOrderCertificateInhabitation

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedGenerationOuterResponse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Selected-generation rounded outer response at the printed order

The order-generic response maximum theorem applies directly at
`(1 + g) / 4` on every admissible rounded grid.  This interface keeps both
the selected generation and the resulting `g`-dependent geometric discount.
-/

namespace HCPolySupport
namespace HighContrast
open scoped BigOperators Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The full rounded spatial-response row inherits a power tail at the
printed order with the exact order-generic boundary-layer prefactor. -/
theorem exists_summable_roundedGenerationResponseMaxRow_le_printOrderPowerTail_sq
    [NeZero d] {generation : ℤ}
    (hl : (kZero d : ℤ) ≤ generation)
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (t : ℤ)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
    {g amplitude kappa x : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hAmplitude : 0 ≤ amplitude) (hKappa : 0 < kappa)
    (hTail : ScalarIdentityPowerTail aRef
      (printCertificateOrder g) amplitude kappa x)
    (hx : 0 < x) (M : ℤ) (hActive : x ≤ (3 : ℝ) ^ M) :
    ∃ G : ℕ, ∃ Z : ℕ → Finset (Fin d → ℤ),
      (3 : ℝ) ^ (G : ℤ) ≤
          1 + 3 *
            ((100 / 99 : ℝ) * witnessEccentricity (symmPart abar) *
              Real.sqrt d) ∧
      (∀ l : ℕ,
        ↑(Z l) =
          {w : Fin d → ℤ |
            adaptedCellCenter (roundedGrid generation (symmPart abar))
                (M - (l : ℤ)) w ∈
              adaptedCell (roundedGrid generation (symmPart abar)) M}) ∧
      (∀ l : ℕ, (Z l).card = 3 ^ (d * l)) ∧
      Summable (fun l : ℕ ↦
        Book.Ch02.geometricWeight (printCertificateOrder g) 2 l *
          Book.Ch02.finsetSupReal (Z l) (fun w ↦
            roundedNormalizedDoubledResponseMaxAtGeneration
              generation a abar hS (M - (l : ℤ)) w)) ∧
      (∑' l : ℕ,
          Book.Ch02.geometricWeight (printCertificateOrder g) 2 l *
            Book.Ch02.finsetSupReal (Z l) (fun w ↦
              roundedNormalizedDoubledResponseMaxAtGeneration
                generation a abar hS (M - (l : ℤ)) w)) ≤
        (max 1
            (6 * (d : ℝ) * Real.sqrt d *
              ((101 / 100 : ℝ) *
                witnessEccentricity (symmPart abar))) *
            (Book.Ch02.geometricDiscount
              (1 - 2 * printCertificateOrder g) 1)⁻¹) *
          Real.rpow (3 : ℝ)
            (2 * printCertificateOrder g * (G : ℝ)) *
          (amplitude * (((3 : ℝ) ^ M) / x) ^ (-kappa)) ^ 2 := by
  have hmargins := printOrder_margins hg
  obtain ⟨G, Z, hG, hZ, hcard, hsum, hresponse⟩ :=
    exists_summable_roundedGenerationResponseMaxRow_le_scalarIdentityWeakError_sq
      hl a abar hS t aRef haRef hmargins.1 hmargins.2.1 M
  refine ⟨G, Z, hG, hZ, hcard, hsum, ?_⟩
  let tail : ℝ := amplitude * (((3 : ℝ) ^ M) / x) ^ (-kappa)
  have hparentActive : x ≤ (3 : ℝ) ^ (M + (G : ℤ)) :=
    hActive.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have hparentWeak :
      scalarIdentityWeakError aRef (printCertificateOrder g)
          (M + (G : ℤ)) ≤ tail := by
    have hparent := hTail (M + (G : ℤ)) hparentActive
    have hpowOrder : (3 : ℝ) ^ M ≤ (3 : ℝ) ^ (M + (G : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hratioOrder :
        ((3 : ℝ) ^ M) / x ≤ ((3 : ℝ) ^ (M + (G : ℤ))) / x :=
      div_le_div_of_nonneg_right hpowOrder hx.le
    have hdecay :
        (((3 : ℝ) ^ (M + (G : ℤ))) / x) ^ (-kappa) ≤
          (((3 : ℝ) ^ M) / x) ^ (-kappa) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hratioOrder
        (neg_nonpos.mpr hKappa.le)
    exact hparent.trans (by
      simpa only [tail] using
        mul_le_mul_of_nonneg_left hdecay hAmplitude)
  have hparentSq :
      scalarIdentityWeakError aRef (printCertificateOrder g)
          (M + (G : ℤ)) ^ 2 ≤ tail ^ 2 :=
    pow_le_pow_left₀
      (scalarIdentityWeakError_nonneg aRef
        (printCertificateOrder g) (M + (G : ℤ)))
      hparentWeak 2
  have hboundary0 : 0 ≤ max 1
      (6 * (d : ℝ) * Real.sqrt d *
        ((101 / 100 : ℝ) * witnessEccentricity (symmPart abar))) :=
    zero_le_one.trans (le_max_left _ _)
  have hdiscount0 := printOrder_outerGeometricDiscount_inv_nonneg hg
  have hgeometry0 : 0 ≤
      (max 1
          (6 * (d : ℝ) * Real.sqrt d *
            ((101 / 100 : ℝ) * witnessEccentricity (symmPart abar))) *
          (Book.Ch02.geometricDiscount
            (1 - 2 * printCertificateOrder g) 1)⁻¹) *
        Real.rpow (3 : ℝ)
          (2 * printCertificateOrder g * (G : ℝ)) :=
    mul_nonneg (mul_nonneg hboundary0 hdiscount0)
      (Real.rpow_nonneg (by norm_num) _)
  calc
    (∑' l : ℕ,
        Book.Ch02.geometricWeight (printCertificateOrder g) 2 l *
          Book.Ch02.finsetSupReal (Z l) (fun w ↦
            roundedNormalizedDoubledResponseMaxAtGeneration
              generation a abar hS (M - (l : ℤ)) w)) ≤
        (max 1
            (6 * (d : ℝ) * Real.sqrt d *
              ((101 / 100 : ℝ) * witnessEccentricity (symmPart abar))) *
            (Book.Ch02.geometricDiscount
              (1 - 2 * printCertificateOrder g) 1)⁻¹) *
          Real.rpow (3 : ℝ)
            (2 * printCertificateOrder g * (G : ℝ)) *
          scalarIdentityWeakError aRef (printCertificateOrder g)
            (M + (G : ℤ)) ^ 2 := hresponse
    _ ≤ (max 1
            (6 * (d : ℝ) * Real.sqrt d *
              ((101 / 100 : ℝ) * witnessEccentricity (symmPart abar))) *
            (Book.Ch02.geometricDiscount
              (1 - 2 * printCertificateOrder g) 1)⁻¹) *
          Real.rpow (3 : ℝ)
            (2 * printCertificateOrder g * (G : ℝ)) * tail ^ 2 :=
      mul_le_mul_of_nonneg_left hparentSq hgeometry0
    _ = (max 1
            (6 * (d : ℝ) * Real.sqrt d *
              ((101 / 100 : ℝ) * witnessEccentricity (symmPart abar))) *
            (Book.Ch02.geometricDiscount
              (1 - 2 * printCertificateOrder g) 1)⁻¹) *
          Real.rpow (3 : ℝ)
            (2 * printCertificateOrder g * (G : ℝ)) *
          (amplitude * (((3 : ℝ) ^ M) / x) ^ (-kappa)) ^ 2 := rfl

end

end HighContrast
end HCPolySupport
