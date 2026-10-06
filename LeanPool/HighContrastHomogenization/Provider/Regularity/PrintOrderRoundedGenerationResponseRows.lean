/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedResponseRows
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationResponseScale

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedGenerationResponseRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Selected-generation response rows at the printed-order common scale

The stochastic certificate controls every admissible rounded generation.
These definitions retain the selected generation in the physical weak-error
row and in the finite good-tail interfaces.
-/

namespace HCPolySupport
namespace HighContrast
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The full spatial weak error associated with one selected rounded grid. -/
@[expose]
noncomputable def roundedGenerationSpatialWeakError [NeZero d]
    (generation : ℤ) (a : CoeffSpace d) (abar : Mat d)
    (_hS : (symmPart abar).PosDef) (s : ℝ) (M : ℤ) : ℝ :=
  Real.sqrt (∑' u : ℕ,
    Book.Ch02.geometricWeight s 2 u *
      Book.Ch02.finsetSupReal
        (Response.alignedIndex (roundedGrid generation (symmPart abar))
          (M - (u : ℤ)) M)
        (fun w ↦ roundedNormalizedDoubledResponseMaxAtGeneration
          generation a abar _hS (M - (u : ℤ)) w))

/-- A selected-generation spatial weak error is nonnegative. -/
theorem roundedGenerationSpatialWeakError_nonneg [NeZero d]
    (generation : ℤ) (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (s : ℝ) (M : ℤ) :
    0 ≤ roundedGenerationSpatialWeakError generation a abar hS s M := by
  unfold roundedGenerationSpatialWeakError
  exact Real.sqrt_nonneg _

/-- The finite summable response row for a selected rounded generation. -/
@[expose]
def RoundedGenerationSpatialGoodTailOnInterval [NeZero d]
    (generation : ℤ) (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (s delta : ℝ) (n m : ℤ) : Prop :=
  (∑ k ∈ Finset.Icc n m,
    roundedGenerationSpatialWeakError generation a abar hS s k) ≤ delta

/-- The all-later summable response row for a selected rounded generation. -/
@[expose]
def RoundedGenerationSpatialGoodTail [NeZero d]
    (generation : ℤ) (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (s delta : ℝ) (n : ℤ) : Prop :=
  ∀ m : ℤ, n ≤ m →
    RoundedGenerationSpatialGoodTailOnInterval
      generation a abar hS s delta n m

/-- The finite pointwise response row for a selected rounded generation. -/
@[expose]
def RoundedGenerationSpatialGoodMaxOnInterval [NeZero d]
    (generation : ℤ) (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (s delta : ℝ) (n m : ℤ) : Prop :=
  ∀ k ∈ Finset.Icc n m,
    roundedGenerationSpatialWeakError generation a abar hS s k ≤ delta

/-- A summable selected-generation row controls its pointwise maximum. -/
theorem RoundedGenerationSpatialGoodTail.goodMaxOnInterval [NeZero d]
    {generation : ℤ} {a : CoeffSpace d} {abar : Mat d}
    {hS : (symmPart abar).PosDef} {s delta : ℝ} {n m : ℤ}
    (h : RoundedGenerationSpatialGoodTail
      generation a abar hS s delta n) (hnm : n ≤ m) :
    RoundedGenerationSpatialGoodMaxOnInterval
      generation a abar hS s delta n m := by
  intro k hk
  have hsingle :
      roundedGenerationSpatialWeakError generation a abar hS s k ≤
        ∑ j ∈ Finset.Icc n m,
          roundedGenerationSpatialWeakError generation a abar hS s j := by
    exact Finset.single_le_sum
      (fun j _ ↦ roundedGenerationSpatialWeakError_nonneg
        generation a abar hS s j) hk
  exact hsingle.trans (h m hnm)

/-- The printed certificate controls the rounded weak error at its corrected
common scale. -/
theorem
    PrintOrderQuantitativeNormalizedReferenceCertificate.exists_roundedGenerationSpatialWeakError_le_powerTail
    [NeZero d] {a : CoeffSpace d} {abar : Mat d}
    {g sourceAmplitude target kappa : ℝ} {X : CoeffSpace d → ℝ}
    (h : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g sourceAmplitude kappa (X a) a)
    {generation : ℤ} (hl : (kZero d : ℤ) ≤ generation)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hTarget : 0 < target) :
    ∃ hS : (symmPart abar).PosDef, ∀ M : ℤ,
      printOrderCommonQuantitativeAffineScale
          d g sourceAmplitude target kappa abar X a ≤ (3 : ℝ) ^ M →
      roundedGenerationSpatialWeakError generation
          a abar hS (printCertificateOrder g) M ≤
        target * (((3 : ℝ) ^ M) /
          printOrderCommonQuantitativeAffineScale
            d g sourceAmplitude target kappa abar X a) ^ (-kappa) := by
  classical
  obtain ⟨hS, aRef, _hs, _hsHalf, _, hKappa, hX, haRef, hTail⟩ :=
    h.exists_targetedRoundedReferenceCoeffFamily hTarget 0
  refine ⟨hS, ?_⟩
  intro M hActive
  have hxTarget : 0 < targetedQuantitativeEffectiveScale
      sourceAmplitude target kappa X a := by
    apply zero_lt_one.trans_le
    simpa only [targetedQuantitativeEffectiveScale] using
      (one_le_powerLossRandomScale
        (one_le_amplitudeReductionFactor sourceAmplitude target)
        hKappa hX)
  obtain ⟨G, Z, _hG, hZ, _hcard, _hSummable, hResponse⟩ :=
    exists_summable_roundedGenerationResponseMaxRow_le_printOrderEffectiveScale_powerTail_sq
      hl a abar hS 0 aRef haRef hg hTarget.le hKappa hTail hxTarget M
      (by simpa only [printOrderCommonQuantitativeAffineScale,
          commonQuantitativeAffineScale] using hActive)
  have hZeq : ∀ u : ℕ,
      Z u = Response.alignedIndex (roundedGrid generation (symmPart abar))
        (M - (u : ℤ)) M := by
    intro u
    apply Finset.ext
    intro w
    have hZmem :
        w ∈ Z u ↔
          adaptedCellCenter (roundedGrid generation (symmPart abar))
              (M - (u : ℤ)) w ∈
            adaptedCell (roundedGrid generation (symmPart abar)) M := by
      have hSet := congrArg (fun U : Set (Fin d → ℤ) ↦ w ∈ U) (hZ u)
      simpa only [Finset.mem_coe, Set.mem_ofPred_eq] using iff_of_eq hSet
    exact hZmem.trans
      (Response.mem_alignedIndex_iff (Recurrence.posDef_roundedGrid hl hS)
        (by omega)).symm
  have hCanonical :
      (∑' u : ℕ,
          Book.Ch02.geometricWeight (printCertificateOrder g) 2 u *
            Book.Ch02.finsetSupReal
              (Response.alignedIndex (roundedGrid generation (symmPart abar))
                (M - (u : ℤ)) M)
              (fun w ↦
                roundedNormalizedDoubledResponseMaxAtGeneration
                  generation a abar hS (M - (u : ℤ)) w)) ≤
        (target * (((3 : ℝ) ^ M) /
          printOrderCommonQuantitativeAffineScale
            d g sourceAmplitude target kappa abar X a) ^ (-kappa)) ^ 2 := by
    simpa only [hZeq, printOrderCommonQuantitativeAffineScale,
      commonQuantitativeAffineScale] using hResponse
  have hCommonOne : 1 ≤ printOrderCommonQuantitativeAffineScale
      d g sourceAmplitude target kappa abar X a := by
    unfold printOrderCommonQuantitativeAffineScale
    exact one_le_commonQuantitativeAffineScale hKappa hX
  have hRightNonneg : 0 ≤ target * (((3 : ℝ) ^ M) /
      printOrderCommonQuantitativeAffineScale
        d g sourceAmplitude target kappa abar X a) ^ (-kappa) :=
    mul_nonneg hTarget.le
      (Real.rpow_nonneg
        (div_nonneg (by positivity) (zero_le_one.trans hCommonOne)) _)
  unfold roundedGenerationSpatialWeakError
  calc
    Real.sqrt (∑' u : ℕ,
        Book.Ch02.geometricWeight (printCertificateOrder g) 2 u *
          Book.Ch02.finsetSupReal
            (Response.alignedIndex (roundedGrid generation (symmPart abar))
              (M - (u : ℤ)) M)
            (fun w ↦
              roundedNormalizedDoubledResponseMaxAtGeneration
                generation a abar hS (M - (u : ℤ)) w)) ≤
      Real.sqrt ((target * (((3 : ℝ) ^ M) /
        printOrderCommonQuantitativeAffineScale
          d g sourceAmplitude target kappa abar X a) ^ (-kappa)) ^ 2) :=
        Real.sqrt_le_sqrt hCanonical
    _ = target * (((3 : ℝ) ^ M) /
        printOrderCommonQuantitativeAffineScale
          d g sourceAmplitude target kappa abar X a) ^ (-kappa) :=
      Real.sqrt_sq hRightNonneg

private theorem physical_ratio_rpow_le_geometric_gap
    {x kappa : ℝ} {n k : ℤ} (hx : 0 < x)
    (hxn : x ≤ (3 : ℝ) ^ n) (hkappa : 0 < kappa) :
    (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤
      (3 : ℝ) ^ (-kappa * ((k : ℝ) - (n : ℝ))) := by
  have hkpow : 0 < (3 : ℝ) ^ k := by positivity
  have hratio : 0 < ((3 : ℝ) ^ k) / x := div_pos hkpow hx
  have hgap : 0 < (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) := by positivity
  have hbase : (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) ≤ ((3 : ℝ) ^ k) / x := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3),
      Real.rpow_intCast, Real.rpow_intCast]
    exact div_le_div_of_nonneg_left hkpow.le hx hxn
  calc
    (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤
        ((3 : ℝ) ^ ((k : ℝ) - (n : ℝ))) ^ (-kappa) :=
      (Real.rpow_le_rpow_iff_of_neg hratio hgap
        (neg_neg_of_pos hkappa)).2 hbase
    _ = (3 : ℝ) ^ (((k : ℝ) - (n : ℝ)) * (-kappa)) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
    _ = (3 : ℝ) ^ (-kappa * ((k : ℝ) - (n : ℝ))) := by
      congr 1
      ring

/-- The printed-order weak errors have a summable all-later tail. -/
theorem
    PrintOrderQuantitativeNormalizedReferenceCertificate.exists_roundedGenerationSpatialGoodTail
    [NeZero d] {a : CoeffSpace d} {abar : Mat d}
    {g sourceAmplitude target kappa : ℝ} {X : CoeffSpace d → ℝ}
    (h : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g sourceAmplitude kappa (X a) a)
    {generation : ℤ} (hl : (kZero d : ℤ) ≤ generation)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hTarget : 0 < target) :
    ∃ hS : (symmPart abar).PosDef,
      RoundedGenerationSpatialGoodTail generation a abar hS
        (printCertificateOrder g)
        (target / (1 - (3 : ℝ) ^ (-kappa)))
        (Quenched.triadicCeilingIndex
          (printOrderCommonQuantitativeAffineScale
            d g sourceAmplitude target kappa abar X a) : ℤ) := by
  obtain ⟨hS, hPower⟩ :=
    PrintOrderQuantitativeNormalizedReferenceCertificate.exists_roundedGenerationSpatialWeakError_le_powerTail
      h hl hg hTarget
  obtain ⟨_, _, _, _, _, hKappa, hX, _, _⟩ := h
  let xEff : ℝ := printOrderCommonQuantitativeAffineScale
    d g sourceAmplitude target kappa abar X a
  let N : ℕ := Quenched.triadicCeilingIndex xEff
  have hEffOne : 1 ≤ xEff := by
    simpa only [xEff, printOrderCommonQuantitativeAffineScale] using
      (one_le_commonQuantitativeAffineScale hKappa hX
        (Caff := printOrderRoundedResponseAffineConstant d g)
        (overlinePi :=
          specBound (symmPart abar) * specBound (symmPart abar)⁻¹))
  have hEffPos : 0 < xEff := zero_lt_one.trans_le hEffOne
  have hceilNat : xEff ≤ (3 : ℝ) ^ N := by
    simpa only [N] using Quenched.le_pow_triadicCeilingIndex hEffOne
  have hceil : xEff ≤ (3 : ℝ) ^ (N : ℤ) := by
    simpa only [zpow_natCast] using hceilNat
  have hweak : ∀ k : ℤ, (N : ℤ) ≤ k →
      roundedGenerationSpatialWeakError generation
          a abar hS (printCertificateOrder g) k ≤
        target * (3 : ℝ) ^ (-kappa * ((k : ℝ) - (N : ℝ))) := by
    intro k hNk
    have hEffPow : xEff ≤ (3 : ℝ) ^ k :=
      hceil.trans (zpow_le_zpow_right₀ (by norm_num) hNk)
    have hRate := hPower k (by simpa only [xEff] using hEffPow)
    have hRatio := physical_ratio_rpow_le_geometric_gap
      (k := k) hEffPos hceil hKappa
    exact hRate.trans
      (mul_le_mul_of_nonneg_left hRatio hTarget.le)
  refine ⟨hS, ?_⟩
  change ∀ m : ℤ, (N : ℤ) ≤ m →
    (∑ k ∈ Finset.Icc (N : ℤ) m,
      roundedGenerationSpatialWeakError generation
        a abar hS (printCertificateOrder g) k) ≤
      target / (1 - (3 : ℝ) ^ (-kappa))
  intro m _hNm
  have hgeom := Transport.sum_geom_above_le (c := kappa) hKappa
    (N : ℤ) (Finset.Icc (N : ℤ) m)
    (fun k hk ↦ (Finset.mem_Icc.mp hk).1)
  calc
    ∑ k ∈ Finset.Icc (N : ℤ) m,
        roundedGenerationSpatialWeakError generation
          a abar hS (printCertificateOrder g) k ≤
      ∑ k ∈ Finset.Icc (N : ℤ) m,
        target * (3 : ℝ) ^ (-kappa * ((k : ℝ) - (N : ℝ))) :=
      Finset.sum_le_sum fun k hk ↦ hweak k (Finset.mem_Icc.mp hk).1
    _ = target * ∑ k ∈ Finset.Icc (N : ℤ) m,
        (3 : ℝ) ^ (-kappa * ((k : ℝ) - (N : ℝ))) := by
      rw [Finset.mul_sum]
    _ ≤ target * (1 / (1 - (3 : ℝ) ^ (-kappa))) :=
      mul_le_mul_of_nonneg_left hgeom hTarget.le
    _ = target / (1 - (3 : ℝ) ^ (-kappa)) := by
      simp only [div_eq_mul_inv, one_mul]

end

end HighContrast
end HCPolySupport
