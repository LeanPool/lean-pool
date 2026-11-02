/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.LowerSmallScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerInfinity

/-!
# SuperposedFluxLowerAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Assembly of the sharp lower coarse-ellipticity lane

One explicit dimension-only constant below dominates the auxiliary profile,
all three deterministic branch constants, and all three rare-event budgets.
The finite subquadratic, finite superquadratic, and infinity payloads are then
combined and converted to the literal lower-family carrier.  The final theorem
has exactly the lower conjunct's exported binders; all scalar gate choices and
the small/large scale split remain inside its proof.

This is a proved lower-leg declaration only.  It does not assert status for
the frozen two-sided coarse-ellipticity theorem or for any source node.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- A single dimension-only output constant for the sharp lower lane.  The
`max 0` wrappers make positivity unconditional in the ambient natural-number
dimension; an actual `ABKModel d` later supplies its standing `2 ≤ d`. -/
def superposedFluxLowerConst (d : ℕ) : ℝ :=
  8 + max 0 (profileAuxiliaryConst d) +
    max 0 (16 * superposedFluxSharpDetConst d) +
    max 0 ((superposedFluxTwoLeBudgetConst d + 6) /
      superposedFluxBfaRate d) +
    max 0 ((superposedFluxLtTwoBudgetConst d + 6) /
      (superposedFluxBfaRate d / 2)) +
    max 0 ((superposedFluxInfinityBudgetConst d + 6) /
      superposedFluxBfaRate d)

/-- The assembled lower-profile budget includes the fixed margin eight. -/
theorem eight_le_superposedFluxLowerConst (d : ℕ) :
    8 ≤ superposedFluxLowerConst d := by
  unfold superposedFluxLowerConst
  have h1 : 0 ≤ max 0 (profileAuxiliaryConst d) := le_max_left _ _
  have h2 : 0 ≤ max 0 (16 * superposedFluxSharpDetConst d) := le_max_left _ _
  have h3 : 0 ≤ max 0 ((superposedFluxTwoLeBudgetConst d + 6) /
      superposedFluxBfaRate d) := le_max_left _ _
  have h4 : 0 ≤ max 0 ((superposedFluxLtTwoBudgetConst d + 6) /
      (superposedFluxBfaRate d / 2)) := le_max_left _ _
  have h5 : 0 ≤ max 0 ((superposedFluxInfinityBudgetConst d + 6) /
      superposedFluxBfaRate d) := le_max_left _ _
  linarith
theorem superposedFluxLowerConst_pos (d : ℕ) :
    0 < superposedFluxLowerConst d := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (eight_le_superposedFluxLowerConst d)

private theorem profileAuxiliaryConst_le_superposedFluxLowerConst (d : ℕ) :
    profileAuxiliaryConst d ≤ superposedFluxLowerConst d := by
  unfold superposedFluxLowerConst
  have h0 : profileAuxiliaryConst d ≤ max 0 (profileAuxiliaryConst d) :=
    le_max_right _ _
  have h2 : 0 ≤ max 0 (16 * superposedFluxSharpDetConst d) := le_max_left _ _
  have h3 : 0 ≤ max 0 ((superposedFluxTwoLeBudgetConst d + 6) /
      superposedFluxBfaRate d) := le_max_left _ _
  have h4 : 0 ≤ max 0 ((superposedFluxLtTwoBudgetConst d + 6) /
      (superposedFluxBfaRate d / 2)) := le_max_left _ _
  have h5 : 0 ≤ max 0 ((superposedFluxInfinityBudgetConst d + 6) /
      superposedFluxBfaRate d) := le_max_left _ _
  linarith

private theorem sharpDet_le_superposedFluxLowerConst (d : ℕ) :
    16 * superposedFluxSharpDetConst d ≤ superposedFluxLowerConst d := by
  unfold superposedFluxLowerConst
  have h1 : 0 ≤ max 0 (profileAuxiliaryConst d) := le_max_left _ _
  have h0 : 16 * superposedFluxSharpDetConst d ≤
      max 0 (16 * superposedFluxSharpDetConst d) := le_max_right _ _
  have h3 : 0 ≤ max 0 ((superposedFluxTwoLeBudgetConst d + 6) /
      superposedFluxBfaRate d) := le_max_left _ _
  have h4 : 0 ≤ max 0 ((superposedFluxLtTwoBudgetConst d + 6) /
      (superposedFluxBfaRate d / 2)) := le_max_left _ _
  have h5 : 0 ≤ max 0 ((superposedFluxInfinityBudgetConst d + 6) /
      superposedFluxBfaRate d) := le_max_left _ _
  linarith

private theorem twoLeBudgetChoice_superposedFluxLowerConst (d : ℕ) :
    superposedFluxTwoLeBudgetConst d + 6 ≤
      superposedFluxBfaRate d * superposedFluxLowerConst d := by
  have hquot : (superposedFluxTwoLeBudgetConst d + 6) /
      superposedFluxBfaRate d ≤ superposedFluxLowerConst d := by
    unfold superposedFluxLowerConst
    have h1 : 0 ≤ max 0 (profileAuxiliaryConst d) := le_max_left _ _
    have h2 : 0 ≤ max 0 (16 * superposedFluxSharpDetConst d) := le_max_left _ _
    have h0 : (superposedFluxTwoLeBudgetConst d + 6) /
        superposedFluxBfaRate d ≤
          max 0 ((superposedFluxTwoLeBudgetConst d + 6) /
            superposedFluxBfaRate d) := le_max_right _ _
    have h4 : 0 ≤ max 0 ((superposedFluxLtTwoBudgetConst d + 6) /
        (superposedFluxBfaRate d / 2)) := le_max_left _ _
    have h5 : 0 ≤ max 0 ((superposedFluxInfinityBudgetConst d + 6) /
        superposedFluxBfaRate d) := le_max_left _ _
    linarith
  calc
    superposedFluxTwoLeBudgetConst d + 6 = superposedFluxBfaRate d *
        ((superposedFluxTwoLeBudgetConst d + 6) / superposedFluxBfaRate d) := by
      field_simp [ne_of_gt (superposedFluxBfaRate_pos d)]
    _ ≤ superposedFluxBfaRate d * superposedFluxLowerConst d :=
      mul_le_mul_of_nonneg_left hquot (superposedFluxBfaRate_pos d).le

private theorem ltTwoBudgetChoice_superposedFluxLowerConst (d : ℕ) :
    superposedFluxLtTwoBudgetConst d + 6 ≤
      (superposedFluxBfaRate d / 2) * superposedFluxLowerConst d := by
  have hrate : 0 < superposedFluxBfaRate d / 2 :=
    div_pos (superposedFluxBfaRate_pos d) (by norm_num)
  have hquot : (superposedFluxLtTwoBudgetConst d + 6) /
      (superposedFluxBfaRate d / 2) ≤ superposedFluxLowerConst d := by
    unfold superposedFluxLowerConst
    have h1 : 0 ≤ max 0 (profileAuxiliaryConst d) := le_max_left _ _
    have h2 : 0 ≤ max 0 (16 * superposedFluxSharpDetConst d) := le_max_left _ _
    have h3 : 0 ≤ max 0 ((superposedFluxTwoLeBudgetConst d + 6) /
        superposedFluxBfaRate d) := le_max_left _ _
    have h0 : (superposedFluxLtTwoBudgetConst d + 6) /
        (superposedFluxBfaRate d / 2) ≤
          max 0 ((superposedFluxLtTwoBudgetConst d + 6) /
            (superposedFluxBfaRate d / 2)) := le_max_right _ _
    have h5 : 0 ≤ max 0 ((superposedFluxInfinityBudgetConst d + 6) /
        superposedFluxBfaRate d) := le_max_left _ _
    linarith
  calc
    superposedFluxLtTwoBudgetConst d + 6 = (superposedFluxBfaRate d / 2) *
        ((superposedFluxLtTwoBudgetConst d + 6) /
          (superposedFluxBfaRate d / 2)) := by
      field_simp [ne_of_gt hrate, ne_of_gt (superposedFluxBfaRate_pos d)]
    _ ≤ (superposedFluxBfaRate d / 2) * superposedFluxLowerConst d :=
      mul_le_mul_of_nonneg_left hquot hrate.le

private theorem infinityBudgetChoice_superposedFluxLowerConst (d : ℕ) :
    superposedFluxInfinityBudgetConst d + 6 ≤
      superposedFluxBfaRate d * superposedFluxLowerConst d := by
  have hquot : (superposedFluxInfinityBudgetConst d + 6) /
      superposedFluxBfaRate d ≤ superposedFluxLowerConst d := by
    unfold superposedFluxLowerConst
    have h1 : 0 ≤ max 0 (profileAuxiliaryConst d) := le_max_left _ _
    have h2 : 0 ≤ max 0 (16 * superposedFluxSharpDetConst d) := le_max_left _ _
    have h3 : 0 ≤ max 0 ((superposedFluxTwoLeBudgetConst d + 6) /
        superposedFluxBfaRate d) := le_max_left _ _
    have h4 : 0 ≤ max 0 ((superposedFluxLtTwoBudgetConst d + 6) /
        (superposedFluxBfaRate d / 2)) := le_max_left _ _
    have h0 : (superposedFluxInfinityBudgetConst d + 6) /
        superposedFluxBfaRate d ≤
          max 0 ((superposedFluxInfinityBudgetConst d + 6) /
            superposedFluxBfaRate d) := le_max_right _ _
    linarith
  calc
    superposedFluxInfinityBudgetConst d + 6 = superposedFluxBfaRate d *
        ((superposedFluxInfinityBudgetConst d + 6) / superposedFluxBfaRate d) := by
      field_simp [ne_of_gt (superposedFluxBfaRate_pos d)]
    _ ≤ superposedFluxBfaRate d * superposedFluxLowerConst d :=
      mul_le_mul_of_nonneg_left hquot (superposedFluxBfaRate_pos d).le

/-- The exact frozen lower-family carrier in the internal large-scale branch.
The branch condition is a splice input and does not occur in the conclusion. -/
theorem superposedFlux_coarse_ellipticity_lower_large_scale
    (M : ABKModel d) (m : ℤ) (_hm : mStar M < m)
    (E : {E : ℝ // 1 ≤ E})
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc 0 (1 / 2))
    (hE1 : max (Real.exp (superposedFluxLowerConst d / sigma))
      (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hE2 : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (q : CoarseEllipticityExponent) (s : ℝ)
    (hsWindow : s ∈ Set.Icc
      (M.gamma / 2 + Real.exp
        (-((superposedFluxLowerConst d)⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
          M.gamma⁻¹))) 1) :
    Probability.IsLowerIntegerFamilyOrlicz
      (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 2))
      (fun L : ℤ => fun omega =>
        Observable.cutoffLowerEllipticityInv M m L s
          (by
            exact (add_pos
              (div_pos M.shellPrefix.gamma_pos (by norm_num))
              (Real.exp_pos
                (-((superposedFluxLowerConst d)⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                  M.gamma⁻¹)))).trans_le hsWindow.1)
          q omega * (Annealed.sigmaBar M (m - 1) : ℝ))
      (m - 1)
      (lowerEllipticityProfile (superposedFluxLowerConst d) M.gamma s q)
      (Real.exp
        (-((superposedFluxLowerConst d)⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
          M.gamma⁻¹))) := by
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let : NeZero d := ⟨by omega⟩
  have hdet16 := sharpDet_le_superposedFluxLowerConst d
  have hdet8 : 8 * superposedFluxSharpDetConst d ≤
      superposedFluxLowerConst d := by
    have hdet0 := (superposedFluxSharpDetConst_pos hd).le
    linarith
  have hdet2 : 2 * superposedFluxSharpDetConst d ≤
      superposedFluxLowerConst d := by
    have hdet0 := (superposedFluxSharpDetConst_pos hd).le
    linarith
  have hpayload := coarse_ellipticity_lower_payload_of_branchPayloads d
    (superposedFlux_lower_branchPayload_lt_two hd
      (superposedFluxLowerConst_pos d)
      (profileAuxiliaryConst_le_superposedFluxLowerConst d) hdet16
      (ltTwoBudgetChoice_superposedFluxLowerConst d))
    (superposedFlux_lower_branchPayload_two_le hd
      (superposedFluxLowerConst_pos d)
      (profileAuxiliaryConst_le_superposedFluxLowerConst d) hdet8
      (twoLeBudgetChoice_superposedFluxLowerConst d))
    (superposedFlux_lower_branchPayload_infinity hd
      (superposedFluxLowerConst_pos d)
      (profileAuxiliaryConst_le_superposedFluxLowerConst d) hdet2
      (infinityBudgetChoice_superposedFluxLowerConst d))
  exact coarse_ellipticity_lower_leg_body_of_familySplitPayload d hpayload
    M m E hstate sigma hsigma hE1 hE2 q s hsWindow

/-- Literal lower-conjunct theorem for the sharp lower lane.  The only
exported data are those of the frozen lower-family statement; the scale split
and every scalar adequacy inequality are discharged internally. -/
theorem superposedFlux_coarse_ellipticity_lower_leg (d : ℕ) :
    ∃ Clow : ℝ, 0 < Clow ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ q : CoarseEllipticityExponent,
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 + Real.exp
                  (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              Probability.IsLowerIntegerFamilyOrlicz
                (cutoffSampleLaw M).toMeasure
                (gammaSigma ((1 - sigma) / 2))
                (fun L : ℤ => fun omega =>
                  Observable.cutoffLowerEllipticityInv M m L s
                    (by
                      exact (add_pos
                        (div_pos M.shellPrefix.gamma_pos (by norm_num))
                        (Real.exp_pos
                          (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                            M.gamma⁻¹)))).trans_le hsWindow.1)
                    q omega * (Annealed.sigmaBar M (m - 1) : ℝ))
                (m - 1)
                (lowerEllipticityProfile Clow M.gamma s q)
                (Real.exp
                  (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  refine ⟨superposedFluxLowerConst d, superposedFluxLowerConst_pos d, ?_⟩
  intro M m E hstate sigma hsigma hE1 hE2 q s hsWindow
  by_cases hm : m ≤ mStar M
  · exact coarse_ellipticity_lower_of_le_mStar_of_eight_le M m hm
      (eight_le_superposedFluxLowerConst d) E sigma hsigma q s hsWindow
  · exact superposedFlux_coarse_ellipticity_lower_large_scale M m
      (lt_of_not_ge hm) E hstate sigma hsigma hE1 hE2 q s hsWindow

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
