/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.HarmonicReplacement
public import LeanPool.HighContrastHomogenization.Provider.Regularity.ResponseExponentGap

/-!
# High-contrast homogenization: Provider.Regularity.HarmonicReplacementNegativeBesovAtErrorOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Harmonic replacement at a prescribed response-error order

The two-exponent comparison theorem permits the negative Besov output order to
be chosen independently of the response-error order.  A positive gap larger
than a factor of two is sufficient for the identity-harmonic replacement.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

private theorem coarseGrainingHomogenizationErrorAtDepth_zero_at_error_order
    {d : ℕ} (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Book.Ch03.ConstantCoeffMatrix d) (r : ℝ) :
    Book.Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 r 0 =
      Book.Ch02.HomogenizationErrorOnCube Q r .infinity (.finite 1) a
        a0.matrix := by
  simp [Book.Ch03.coarseGrainingHomogenizationErrorAtDepth,
    descendantsAtDepth_zero, Book.Ch02.finsetSupReal]

/-- At every output order strictly larger than twice the response-error order,
the chosen identity-harmonic replacement is controlled by that response
error. -/
theorem exists_identityHarmonicReplacementNegativeBesovEstimateConstant_at_error_order
    (d : ℕ) [NeZero d] (sOut b : ℝ)
    (hb : 0 < b) (h2b : 2 * b < sOut) (hsOut_lt : sOut < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch03.CoeffFamily d) (m : ℤ)
        (u : H1Function
          (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
        (hu : IsWeakSolutionOn (a.coeffOn (originCube d m)).toCoeffField
          (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) u.grad),
        Book.Ch03.homogenizationComparisonNegativeBesovLHS
            (originCube d m) a (identityConstantCoeffMatrix d) sOut
            (identityHarmonicReplacementDatum a m u hu).u
            (identityHarmonicReplacementDatum a m u hu).v ≤
          C * scalarIdentityWeakError a b m *
            Book.Ch03.h1EnergyNormOnCube (originCube d m) a u := by
  have hsOut : 0 < sOut :=
    (mul_pos (by norm_num : (0 : ℝ) < 2) hb).trans h2b
  have hb_half : b < sOut / 2 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    simpa only [mul_comm] using h2b
  let r : ℝ := (b + sOut / 2) / 2
  have hbr : b < r := by
    dsimp [r]
    linarith only [hb_half]
  have hrs : r < sOut / 2 := by
    dsimp [r]
    linarith only [hb_half]
  have hr : 0 < r := hb.trans hbr
  have hr_lt_half : r < 1 / 2 :=
    hrs.trans (div_lt_div_of_pos_right hsOut_lt (by norm_num))
  rcases exists_normalizedCubeNegativeBesovComparisonConstant d with
    ⟨Ccomparison, hCcomparison, hcomparison⟩
  let M : ℝ :=
    Book.Ch03.constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d)
  let Cbase : ℝ :=
    sOut⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
      Ccomparison * r⁻¹ * M
  let K : ℝ :=
    Book.Ch02.geometricDiscount r 1 *
      (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
      (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹
  let C : ℝ := Cbase * K
  have hmatrix_pos :
      0 < Book.Ch02.matrixNorm (identityConstantCoeffMatrix d).matrix := by
    simpa using
      (lt_of_lt_of_le zero_lt_one (Book.Ch02.one_le_matrixNorm_one (d := d)))
  have hM : 0 < M := Real.rpow_pos_of_pos hmatrix_pos _
  have hCbase : 0 < Cbase := by
    dsimp [Cbase]
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos
            (mul_pos (inv_pos.mpr hsOut) (pow_pos (inv_pos.mpr hr) _))
            (inv_pos.mpr (sub_pos.mpr hr_lt_half)))
          hCcomparison)
        (inv_pos.mpr hr))
      hM
  have hdisc_r_pos : 0 < Book.Ch02.geometricDiscount r 1 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos (by simpa only [mul_one] using hr)
  have hdisc_gap_pos : 0 < Book.Ch02.geometricDiscount (r - b) 2 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos
        (mul_pos (sub_pos.mpr hbr) (by norm_num : (0 : ℝ) < 2))
  have hdisc_b_pos : 0 < Book.Ch02.geometricDiscount b 2 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos (mul_pos hb (by norm_num : (0 : ℝ) < 2))
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos
      (mul_pos hdisc_r_pos (inv_pos.mpr (Real.sqrt_pos.2 hdisc_gap_pos)))
      (inv_pos.mpr (Real.sqrt_pos.2 hdisc_b_pos))
  have hC : 0 < C := mul_pos hCbase hK
  refine ⟨C, hC, ?_⟩
  intro a m u hu
  let Q := originCube d m
  let W := identityHarmonicReplacementDatum a m u hu
  let E := scalarIdentityWeakError a b m
  let H :=
    Book.Ch02.HomogenizationErrorOnCube Q r .infinity (.finite 1) a
      (1 : Mat d)
  let A := Book.Ch03.h1EnergyNormOnCube Q a u
  have hcomparisonBase :=
    hcomparison (j := 0) (r₂ := r) W hsOut hr hrs hsOut_lt le_rfl
      (forceBesovRegularity_zero Q r)
  have hdepth :
      Book.Ch03.coarseGrainingHomogenizationErrorAtDepth Q a
          (identityConstantCoeffMatrix d) r 0 = H := by
    simpa [Q, H] using
      coarseGrainingHomogenizationErrorAtDepth_zero_at_error_order Q a
        (identityConstantCoeffMatrix d) r
  have hcomparison' :
      Book.Ch03.homogenizationComparisonNegativeBesovLHS Q a
          (identityConstantCoeffMatrix d) sOut W.u W.v ≤ Cbase * H * A := by
    calc
      Book.Ch03.homogenizationComparisonNegativeBesovLHS Q a
          (identityConstantCoeffMatrix d) sOut W.u W.v ≤
          Book.Ch03.generalCoarseGrainingL2TwoExponentRHS Ccomparison Q a
            (identityConstantCoeffMatrix d) sOut r r 0
            (0 : Vec d → Vec d) W.u := hcomparisonBase
      _ = Cbase * H * A := by
        rw [show W.u = u by
          exact identityHarmonicReplacementDatum_u a m u hu]
        simp [Book.Ch03.generalCoarseGrainingL2TwoExponentRHS,
          Book.Ch03.generalCoarseGrainingL2TwoExponentFluxDefectRHS, hdepth,
          Cbase, M, A]
        ring
  have hHE : H ≤ K * E := by
    simpa [Q, H, K, E, scalarIdentityWeakError] using
      homogenizationErrorOnCube_infinity_one_le_gap_mul_infinity_two
        Q a (1 : Mat d) hb hbr
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, Book.Ch03.h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  calc
    Book.Ch03.homogenizationComparisonNegativeBesovLHS
        (originCube d m) a (identityConstantCoeffMatrix d) sOut
        (identityHarmonicReplacementDatum a m u hu).u
        (identityHarmonicReplacementDatum a m u hu).v =
        Book.Ch03.homogenizationComparisonNegativeBesovLHS Q a
          (identityConstantCoeffMatrix d) sOut W.u W.v := rfl
    _ ≤ Cbase * H * A := hcomparison'
    _ ≤ Cbase * (K * E) * A :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hHE hCbase.le) hA_nonneg
    _ = C * scalarIdentityWeakError a b m *
        Book.Ch03.h1EnergyNormOnCube (originCube d m) a u := by
      dsimp [C, E, A, Q]
      ring

end

end HighContrast
end HCPolySupport
