/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Initialization.Boundary
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CommonQuantitativeAffineScale
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedResponseScale
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationOuterResponse

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedGenerationResponseScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Selected-generation rounded response scale at the printed fractional order

The boundary-layer discount and affine multiplier already used by the
canonical response row apply uniformly to every admissible rounded generation.
-/

namespace HCPolySupport
namespace HighContrast
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The outer response row is controlled by the printed-order affine loss. -/
theorem exists_summable_roundedGenerationResponseMaxRow_le_printOrderAffineTail_sq
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
            (Response.adaptedDomain
              (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
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
        (printOrderRoundedResponseAffineConstant d g *
            witnessEccentricity (symmPart abar) *
          (amplitude * (((3 : ℝ) ^ M) / x) ^ (-kappa))) ^ 2 := by
  classical
  obtain ⟨G, Z, hG, hZ, hcard, hsum, hresponse⟩ :=
    exists_summable_roundedGenerationResponseMaxRow_le_printOrderPowerTail_sq
      hl a abar hS t aRef haRef hg hAmplitude hKappa hTail hx M hActive
  refine ⟨G, Z, hG, hZ, hcard, hsum, ?_⟩
  let ecc : ℝ := witnessEccentricity (symmPart abar)
  let boundaryDim : ℝ :=
    6 * (d : ℝ) * Real.sqrt d * (101 / 100 : ℝ)
  let enclosureDim : ℝ :=
    1 + 3 * ((100 / 99 : ℝ) * Real.sqrt d)
  let boundary : ℝ := max 1 (boundaryDim * ecc)
  let enclosure : ℝ :=
    1 + 3 * ((100 / 99 : ℝ) * ecc * Real.sqrt d)
  let discount : ℝ := (Book.Ch02.geometricDiscount
    (1 - 2 * printCertificateOrder g) 1)⁻¹
  let tail : ℝ := amplitude * (((3 : ℝ) ^ M) / x) ^ (-kappa)
  have hecc : 1 ≤ ecc := by
    simpa only [ecc] using Initialization.one_le_witnessEccentricity hS
  have hecc0 : 0 ≤ ecc := zero_le_one.trans hecc
  have hboundary0 : 0 ≤ boundary :=
    zero_le_one.trans (le_max_left _ _)
  have henclosureOne : 1 ≤ enclosure := by
    dsimp only [enclosure]
    exact le_add_of_nonneg_right (by positivity)
  have hG' : Real.rpow (3 : ℝ) (G : ℝ) ≤ enclosure := by
    calc
      Real.rpow (3 : ℝ) (G : ℝ) = (3 : ℝ) ^ G :=
        Real.rpow_natCast (3 : ℝ) G
      _ ≤ enclosure := by
        simpa only [ecc, enclosure, zpow_natCast] using hG
  have hshift : Real.rpow (3 : ℝ)
      (2 * printCertificateOrder g * (G : ℝ)) ≤ enclosure := by
    have hexponent0 : 0 ≤ 2 * printCertificateOrder g :=
      (mul_nonneg (by norm_num) (printOrder_margins hg).1.le)
    have hexponentOne : 2 * printCertificateOrder g ≤ 1 := by
      linarith only [(printOrder_margins hg).2.1]
    calc
      Real.rpow (3 : ℝ) (2 * printCertificateOrder g * (G : ℝ)) =
          Real.rpow (Real.rpow (3 : ℝ) (G : ℝ))
            (2 * printCertificateOrder g) := by
        rw [show 2 * printCertificateOrder g * (G : ℝ) =
            (G : ℝ) * (2 * printCertificateOrder g) by ring]
        exact Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _
      _ ≤ Real.rpow enclosure (2 * printCertificateOrder g) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hG' hexponent0
      _ ≤ Real.rpow enclosure 1 :=
        Real.rpow_le_rpow_of_exponent_le henclosureOne hexponentOne
      _ = enclosure := Real.rpow_one enclosure
  have hboundaryEcc : boundary ≤ max 1 boundaryDim * ecc := by
    dsimp only [boundary]
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) hecc
    · exact mul_le_mul_of_nonneg_right
        (le_max_right (1 : ℝ) boundaryDim) hecc0
  have hdiscount0 : 0 ≤ discount := by
    simpa only [discount] using printOrder_outerGeometricDiscount_inv_nonneg hg
  have hboundaryDiscount : boundary * discount ≤
      (max 1 boundaryDim * ecc) * discount :=
    mul_le_mul_of_nonneg_right hboundaryEcc hdiscount0
  have henclosureEcc : enclosure ≤ enclosureDim * ecc := by
    calc
      enclosure = 1 +
          (3 * ((100 / 99 : ℝ) * Real.sqrt d)) * ecc := by
        dsimp only [enclosure]
        ring
      _ ≤ ecc + (3 * ((100 / 99 : ℝ) * Real.sqrt d)) * ecc :=
        add_le_add hecc le_rfl
      _ = enclosureDim * ecc := by
        dsimp only [enclosureDim]
        ring
  have hgeometry :
      (boundary * discount) *
          Real.rpow (3 : ℝ)
            (2 * printCertificateOrder g * (G : ℝ)) ≤
        printOrderRoundedResponseAffineConstantSq d g * ecc ^ 2 := by
    calc
      (boundary * discount) * Real.rpow (3 : ℝ)
          (2 * printCertificateOrder g * (G : ℝ)) ≤
        ((max 1 boundaryDim * ecc) * discount) * enclosure :=
          mul_le_mul hboundaryDiscount hshift
            (Real.rpow_nonneg (by norm_num) _)
            (mul_nonneg
              (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hecc0)
              hdiscount0)
      _ ≤ ((max 1 boundaryDim * ecc) * discount) *
          (enclosureDim * ecc) :=
        mul_le_mul_of_nonneg_left henclosureEcc
          (mul_nonneg
            (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hecc0)
            hdiscount0)
      _ = printOrderRoundedResponseAffineConstantSq d g * ecc ^ 2 := by
        dsimp only [printOrderRoundedResponseAffineConstantSq, boundaryDim,
          enclosureDim, discount]
        ring
  have hconstantSq0 :
      0 ≤ printOrderRoundedResponseAffineConstantSq d g := by
    unfold printOrderRoundedResponseAffineConstantSq
    exact mul_nonneg
      (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hdiscount0)
      (by positivity)
  calc
    (∑' l : ℕ,
        Book.Ch02.geometricWeight (printCertificateOrder g) 2 l *
          Book.Ch02.finsetSupReal (Z l) (fun w ↦
            roundedNormalizedDoubledResponseMaxAtGeneration
              generation a abar hS (M - (l : ℤ)) w)) ≤
        (boundary * discount) *
          Real.rpow (3 : ℝ)
            (2 * printCertificateOrder g * (G : ℝ)) * tail ^ 2 := by
      simpa only [boundary, boundaryDim, ecc, discount, tail, mul_assoc] using
        hresponse
    _ ≤ (printOrderRoundedResponseAffineConstantSq d g * ecc ^ 2) *
          tail ^ 2 :=
      mul_le_mul_of_nonneg_right hgeometry (sq_nonneg tail)
    _ = (printOrderRoundedResponseAffineConstant d g * ecc * tail) ^ 2 := by
      rw [show printOrderRoundedResponseAffineConstantSq d g =
          printOrderRoundedResponseAffineConstant d g ^ 2 by
        exact (Real.sq_sqrt hconstantSq0).symm]
      ring
    _ = _ := rfl

private theorem multiplier_rpow_mul_ratio_eq_rpow_mul_scale
    {mult kappa x r : ℝ} (hmult : 0 < mult)
    (hx : 0 < x) (hr : 0 < r) :
    mult ^ kappa * (r / x) ^ (-kappa) =
      (r / (mult * x)) ^ (-kappa) := by
  have hratio : r / (mult * x) = (r / x) / mult := by
    field_simp [hmult.ne', hx.ne']
  rw [hratio, Real.div_rpow (div_nonneg hr.le hx.le) hmult.le,
    Real.rpow_neg hmult.le, div_inv_eq_mul, mul_comm]

/-- The printed-order affine scale absorbs the rounded response loss. -/
theorem
    exists_summable_roundedGenerationResponseMaxRow_le_printOrderEffectiveScale_powerTail_sq
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
            (Response.adaptedDomain
              (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
    {g amplitude kappa x : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hAmplitude : 0 ≤ amplitude) (hKappa : 0 < kappa)
    (hTail : ScalarIdentityPowerTail aRef
      (printCertificateOrder g) amplitude kappa x)
    (hx : 0 < x) (M : ℤ)
    (hActive : roundedAffineEffectiveScale
        (printOrderRoundedResponseAffineConstant d g)
        (specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
        kappa x ≤ (3 : ℝ) ^ M) :
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
        (amplitude * (((3 : ℝ) ^ M) /
          roundedAffineEffectiveScale
            (printOrderRoundedResponseAffineConstant d g)
            (specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
            kappa x) ^ (-kappa)) ^ 2 := by
  classical
  let Caff : ℝ := printOrderRoundedResponseAffineConstant d g
  let overlinePi : ℝ :=
    specBound (symmPart abar) * specBound (symmPart abar)⁻¹
  let mult : ℝ := roundedAffineMultiplier Caff overlinePi kappa
  let xEff : ℝ := roundedAffineEffectiveScale Caff overlinePi kappa x
  have hCaff : 0 < Caff := by
    simpa only [Caff] using printOrderRoundedResponseAffineConstant_pos d hg
  have hPi : 0 < overlinePi := by
    have hecc := Transport.zero_lt_witnessEccentricity hS
    simpa only [overlinePi, witnessEccentricity, Real.sqrt_pos] using hecc
  have hmult : 0 < mult := by
    simpa only [mult] using roundedAffineMultiplier_pos Caff overlinePi kappa
  have hxEff : 0 < xEff := by
    dsimp only [xEff, roundedAffineEffectiveScale, mult]
    exact mul_pos hmult hx
  have hxeq : xEff = mult * x := rfl
  have hxle : x ≤ xEff := by
    simpa only [Caff, overlinePi, xEff] using
      le_roundedAffineEffectiveScale Caff overlinePi kappa x hx.le
  have hActiveRaw : x ≤ (3 : ℝ) ^ M :=
    hxle.trans (by simpa only [Caff, overlinePi, xEff] using hActive)
  obtain ⟨G, Z, hG, hZ, hcard, hsum, hresponse⟩ :=
    exists_summable_roundedGenerationResponseMaxRow_le_printOrderAffineTail_sq
      hl a abar hS t aRef haRef hg hAmplitude hKappa hTail hx M hActiveRaw
  refine ⟨G, Z, hG, hZ, hcard, hsum, hresponse.trans ?_⟩
  let rate : ℝ := (((3 : ℝ) ^ M) / x) ^ (-kappa)
  let rateEff : ℝ := (((3 : ℝ) ^ M) / xEff) ^ (-kappa)
  have hrate0 : 0 ≤ rate := Real.rpow_nonneg (by positivity) _
  have hloss : roundedAffineLossAmplitude Caff overlinePi ≤ mult ^ kappa := by
    simpa only [mult] using
      roundedAffineLossAmplitude_le_multiplier_rpow hCaff hPi hKappa
  have hloss' : Caff * witnessEccentricity (symmPart abar) ≤
      mult ^ kappa := by
    simpa only [roundedAffineLossAmplitude, Caff, overlinePi,
      witnessEccentricity] using hloss
  have habsorb : mult ^ kappa * rate = rateEff := by
    simpa only [rate, rateEff, hxeq] using
      (multiplier_rpow_mul_ratio_eq_rpow_mul_scale hmult hx
        (by positivity : 0 < (3 : ℝ) ^ M))
  have hinside : Caff * witnessEccentricity (symmPart abar) *
      (amplitude * rate) ≤ amplitude * rateEff := by
    calc
      Caff * witnessEccentricity (symmPart abar) * (amplitude * rate) =
          amplitude *
            ((Caff * witnessEccentricity (symmPart abar)) * rate) := by
        ring
      _ ≤ amplitude * ((mult ^ kappa) * rate) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hloss' hrate0) hAmplitude
      _ = amplitude * rateEff := by rw [habsorb]
  have hinside0 : 0 ≤ Caff * witnessEccentricity (symmPart abar) *
      (amplitude * rate) :=
    mul_nonneg
      (mul_nonneg hCaff.le (Transport.zero_lt_witnessEccentricity hS).le)
      (mul_nonneg hAmplitude hrate0)
  have hsq := pow_le_pow_left₀ hinside0 hinside 2
  simpa only [Caff, overlinePi, xEff, rate, rateEff] using hsq

end

end HighContrast
end HCPolySupport
