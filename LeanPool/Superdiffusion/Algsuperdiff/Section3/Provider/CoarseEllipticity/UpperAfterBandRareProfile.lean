/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperHsepResidualScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedAfterBandOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle

/-!
# UpperAfterBandRareProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Rare after-band Whitney-layer profile

This module prices and sums the explicit rare witness from
`SharpFramedAfterBandOrlicz` at one strict descendant.  It keeps the literal
exceptional exponent `Gamma_((1 - sigma) / 3)`, first bounds the complete
`gammaProductConst * residualScale * baseScale` amplitude, and then applies
the countable Orlicz triangle inequality over the Whitney-layer index.

The output still precedes multiplication by `probeMeanGoodWaveConst M *
vecNormSq p`, the triadic grid/depth maximum, and the coarse-scale weights.
The separate root row and every other wave/base/collar lane are absent.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-- A dimension-only coefficient for the exponentially small rare
after-band layer.  The leading `1` makes positivity unconditional. -/
def probeSharpAfterBandRareLayerConst (d : ℕ) : ℝ :=
  1 + 32 * upperHsepResidualConst *
    probeSharpAfterBandOrdinaryLayerConst d

/-- The dimension-only coefficient after the Whitney-layer sum. -/
def probeSharpAfterBandRareSumConst (d : ℕ) : ℝ :=
  probeSharpAfterBandRareLayerConst d /
    (1 - whitneyDecayRatio) ^ 2

/-- A summable deterministic majorant for one exact rare-lane scale. -/
def probeSharpAfterBandRareGoodMassLayerBound
    (M : ABKModel d) (E : ℝ) (k n : ℕ) : ℝ :=
  probeSharpAfterBandRareLayerConst d *
    (((n + 1 : ℕ) : ℝ) * whitneyDecayRatio ^ n) *
    (min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
      (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))) *
    Real.exp (-(upperHsepResidualRate * (E⁻¹ ^ 2 * M.gamma⁻¹)))

private theorem upperProfileHsepTau_one_fifth_le_for_product {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    (1 : ℝ) / 5 ≤ upperProfileHsepTau sigma := by
  have hden : 0 < 8 + 3 * sigma + sigma ^ 2 := by positivity
  have hsigmaSq : sigma ^ 2 ≤ (1 : ℝ) / 4 := by nlinarith
  rw [upperProfileHsepTau]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) hden]
  nlinarith

/-- The additional product of the hsep residual with a `Gamma_1` factor has
a universal product constant on the full terminal sigma window. -/
theorem gammaProductConst_upperProfileHsepTau_one_le_sixty_four
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    HCPolySupport.Book.Ch04.gammaProductConst
        (upperProfileHsepTau sigma) 1 ≤ 64 := by
  have hT : 0 < upperProfileHsepTau sigma :=
    upperProfileHsepTau_pos hsigma0 hsigma
  have hTlower : (1 : ℝ) / 5 ≤ upperProfileHsepTau sigma :=
    upperProfileHsepTau_one_fifth_le_for_product hsigma0 hsigma
  have hinv : (upperProfileHsepTau sigma)⁻¹ ≤ (5 : ℝ) :=
    (inv_le_iff_one_le_mul₀ hT).2 (by nlinarith)
  have hexponent :
      ((upperProfileHsepTau sigma * 1 /
        (upperProfileHsepTau sigma + 1))⁻¹) =
        (upperProfileHsepTau sigma)⁻¹ + 1 := by
    field_simp [hT.ne']
    ring
  change (2 : ℝ) ^
      ((upperProfileHsepTau sigma * 1 /
        (upperProfileHsepTau sigma + 1))⁻¹) ≤ 64
  rw [hexponent]
  calc
    (2 : ℝ) ^ ((upperProfileHsepTau sigma)⁻¹ + 1) ≤
        (2 : ℝ) ^ (6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 64 := by norm_num

theorem probeSharpAfterBandRareLayerConst_pos (d : ℕ) :
    0 < probeSharpAfterBandRareLayerConst d := by
  rw [probeSharpAfterBandRareLayerConst]
  have hresidual : 0 ≤ upperHsepResidualConst :=
    upperHsepResidualConst_pos.le
  have hlayer : 0 ≤ probeSharpAfterBandOrdinaryLayerConst d :=
    probeSharpAfterBandOrdinaryLayerConst_nonneg d
  positivity

theorem probeSharpAfterBandRareSumConst_pos (d : ℕ) :
    0 < probeSharpAfterBandRareSumConst d := by
  rw [probeSharpAfterBandRareSumConst]
  exact div_pos (probeSharpAfterBandRareLayerConst_pos d)
    (sq_pos_of_pos (sub_pos.mpr whitneyDecayRatio_lt_one))

theorem probeSharpAfterBandRareGoodMassLayerBound_pos
    (M : ABKModel d) (E : ℝ) (k n : ℕ) :
    0 < probeSharpAfterBandRareGoodMassLayerBound M E k n := by
  have hgap : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hmin : 0 < min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) :=
    lt_min one_pos (mul_pos M.shellPrefix.gamma_pos hgap)
  rw [probeSharpAfterBandRareGoodMassLayerBound]
  have hratio : 0 < whitneyDecayRatio := by
    rw [whitneyDecayRatio]
    positivity
  exact mul_pos
    (mul_pos
      (mul_pos (probeSharpAfterBandRareLayerConst_pos d)
        (mul_pos (by positivity) (pow_pos hratio n)))
      (mul_pos hmin (Real.rpow_pos_of_pos (by norm_num) _)))
    (Real.exp_pos _)

/-- The complete exact rare scale of one strict-descendant Whitney layer is bounded
by the fixed geometric layer profile times the verified exponential residual. -/
theorem probeSharpAfterBandRareGoodMassScale_le_layerBound
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E sigma : ℝ} (hE : 1 ≤ E)
    (hgamma20 : M.gamma ≤ 1 / 20)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (n : ℕ) :
    probeSharpAfterBandRareGoodMassScale
        M R.scale m E sigma k n ≤
      probeSharpAfterBandRareGoodMassLayerBound M E k n := by
  let G : ℝ := HCPolySupport.Book.Ch04.gammaProductConst
    (upperProfileHsepTau sigma) 1
  let AR : ℝ := upperHsepResidualScale sigma M.gamma
  let AX : ℝ :=
    probeSharpAfterBandBaseGoodMassScale M R.scale m E k n
  let O : ℝ := probeSharpAfterBandOrdinaryGoodMassLayer M E k n
  let W : ℝ := ((n + 1 : ℕ) : ℝ) * whitneyDecayRatio ^ n
  let T : ℝ := min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
    (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))
  let Z : ℝ :=
    Real.exp (-(upperHsepResidualRate * (E⁻¹ ^ 2 * M.gamma⁻¹)))
  have hG : G ≤ 64 :=
    gammaProductConst_upperProfileHsepTau_one_le_sixty_four hsigma0 hsigma
  have hAR : AR ≤ upperHsepResidualConst * Z := by
    exact upperHsepResidualScale_le_exp hsigma0 hsigma hE
      M.shellPrefix.gamma_pos
  have hAR0 : 0 ≤ AR := by
    exact (upperHsepResidualScale_pos sigma M.gamma).le
  have hAX0 : 0 ≤ AX := by
    exact probeSharpAfterBandBaseGoodMassScale_nonneg M R.scale m E k n
  have hresidual0 : 0 ≤ upperHsepResidualConst * Z := by
    exact mul_nonneg upperHsepResidualConst_pos.le (by
      dsimp only [Z]
      exact (Real.exp_pos _).le)
  have hGA : G * AR ≤ 64 * (upperHsepResidualConst * Z) :=
    mul_le_mul hG hAR hAR0 (by norm_num)
  have hAXeq : AX = (1 / 2 : ℝ) * O := by
    calc
      AX = (1 / 2 : ℝ) * (2 * AX) := by ring
      _ = (1 / 2 : ℝ) * O := by
        rw [two_mul_probeSharpAfterBandBaseGoodMassScale_eq_ordinary M hR]
  have hO : O ≤ probeSharpAfterBandOrdinaryLayerConst d * W * T := by
    exact probeSharpAfterBandOrdinaryGoodMassLayer_le M hE hgamma20 k n
  have hAX : AX ≤ (1 / 2 : ℝ) *
      (probeSharpAfterBandOrdinaryLayerConst d * W * T) := by
    rw [hAXeq]
    exact mul_le_mul_of_nonneg_left hO (by norm_num)
  have hproduct : G * AR * AX ≤
      (64 * (upperHsepResidualConst * Z)) *
        ((1 / 2 : ℝ) *
          (probeSharpAfterBandOrdinaryLayerConst d * W * T)) :=
    mul_le_mul hGA hAX hAX0
      (mul_nonneg (by norm_num) hresidual0)
  have hcoef0 : 0 ≤ 32 * upperHsepResidualConst *
      probeSharpAfterBandOrdinaryLayerConst d := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) upperHsepResidualConst_pos.le)
      (probeSharpAfterBandOrdinaryLayerConst_nonneg d)
  have hcoef : 32 * upperHsepResidualConst *
        probeSharpAfterBandOrdinaryLayerConst d ≤
      probeSharpAfterBandRareLayerConst d := by
    rw [probeSharpAfterBandRareLayerConst]
    linarith
  change G * AR * AX ≤
    probeSharpAfterBandRareLayerConst d * W * T * Z
  calc
    G * AR * AX ≤
        (64 * (upperHsepResidualConst * Z)) *
          ((1 / 2 : ℝ) *
            (probeSharpAfterBandOrdinaryLayerConst d * W * T)) := hproduct
    _ = (32 * upperHsepResidualConst *
          probeSharpAfterBandOrdinaryLayerConst d) * W * T * Z := by ring
    _ ≤ probeSharpAfterBandRareLayerConst d * W * T * Z := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (by
            dsimp only [W]
            exact mul_nonneg (by positivity)
              (pow_nonneg whitneyDecayRatio_nonneg n))) (by
            dsimp only [T]
            exact mul_nonneg
              (le_min zero_le_one
                (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity)))
              (Real.rpow_nonneg (by norm_num) _)))
        (Real.exp_pos _).le

theorem summable_probeSharpAfterBandRareGoodMassLayerBound
    (M : ABKModel d) (E : ℝ) (k : ℕ) :
    Summable (fun n : ℕ =>
      probeSharpAfterBandRareGoodMassLayerBound M E k n) := by
  simpa only [probeSharpAfterBandRareGoodMassLayerBound] using
    ((summable_succ_mul_whitneyDecayRatio.mul_left
      (probeSharpAfterBandRareLayerConst d)).mul_right
        (min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
          (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ)))).mul_right
      (Real.exp (-(upperHsepResidualRate * (E⁻¹ ^ 2 * M.gamma⁻¹))))

/-- Exact evaluation of the summed deterministic rare-layer majorant. -/
theorem tsum_probeSharpAfterBandRareGoodMassLayerBound_eq
    (M : ABKModel d) (E : ℝ) (k : ℕ) :
    ∑' n : ℕ, probeSharpAfterBandRareGoodMassLayerBound M E k n =
      probeSharpAfterBandRareSumConst d *
        (min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
          (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))) *
        Real.exp (-(upperHsepResidualRate *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  simp only [probeSharpAfterBandRareGoodMassLayerBound]
  rw [tsum_mul_right, tsum_mul_right, tsum_mul_left,
    hasSum_succ_mul_whitneyDecayRatio.tsum_eq,
    probeSharpAfterBandRareSumConst]
  ring


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
