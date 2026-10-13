/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.JointGridDepthMaximum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperPolyProfile

/-!
# UpperOrdinaryBlockProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The source-indexed ordinary upper block profile

This file proves a local deterministic profile result used by the conditional A
in `UpperCommonEnvelopeAE.lean`.  At descendant depth `k`, the source gap is

`m - n = k + 1`.

For the adopted deep-band mean split, a future analytic producer must establish
the following target per-cube scale for the centred ordinary part of the
corrected `b_L` estimate:

`C * cstar⁻¹ * gamma * (k + 1) * 3^(gamma * (k + 1))`.

The joint spatial-and-depth maximum contributes one further factor
`triadicJointDepthEntropyConst d * (k + 1)`.  The resulting expression is
*exactly* `upperPolyProfile` with head constant

`triadicJointDepthEntropyConst d * C * cstar⁻¹ * gamma * 3^gamma`.

On the standing range `gamma ≤ 1`, the harmless factor `3^gamma` is at most
`3`.  A second head constant below therefore has exactly the final parameter
dependence `C(d) * cstar⁻¹ * gamma`.

This is only deterministic source-index arithmetic.  It does not define the
centred per-cube random observable, prove its marginal `Gamma_1` estimate, or
claim the Step-3 `b_L` assembly.  Those are analytic producer obligations.

## Source

* ABK26, `p.bfA.multiscalebound`, read at `L = m`, followed by the descendant
  maximum.
* `cstar⁻¹` remains explicit, and the `E⁻²` deep-band mean must not be
  discarded.  The split adopted here assigns it to the target deterministic
  shift; an analytic producer must still construct the centred ordinary lane
  and establish the target scale described here.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

/-- The target centred ordinary `Gamma_1` scale that an analytic producer must
establish for one descendant block at depth `k`. -/
def upperOrdinaryPerCubeAmplitude
    (C cstar gamma : ℝ) (k : ℕ) : ℝ :=
  C * cstar⁻¹ * gamma * ((k : ℝ) + 1) *
    (3 : ℝ) ^ (gamma * ((k : ℝ) + 1))

/-- The head constant obtained after paying jointly for the triadic spatial
row and for all depths. -/
def upperOrdinaryJointProfileConst
    (d : ℕ) (C cstar gamma : ℝ) : ℝ :=
  triadicJointDepthEntropyConst d * C * cstar⁻¹ * gamma *
    (3 : ℝ) ^ gamma

/-- A dimensionally enlarged profile head with the final parameter dependence
`C(d) * cstar⁻¹ * gamma`, valid on the standing range `gamma ≤ 1`. -/
def upperOrdinaryJointProfileBound
    (d : ℕ) (C cstar gamma : ℝ) : ℝ :=
  3 * triadicJointDepthEntropyConst d * C * cstar⁻¹ * gamma


theorem upperOrdinaryJointProfileBound_nonneg
    (d : ℕ) {C cstar gamma : ℝ} (hC : 0 ≤ C)
    (hcstar : 0 ≤ cstar⁻¹) (hgamma : 0 ≤ gamma) :
    0 ≤ upperOrdinaryJointProfileBound d C cstar gamma := by
  unfold upperOrdinaryJointProfileBound
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (triadicJointDepthEntropyConst_pos d).le)
        hC)
      hcstar)
    hgamma

theorem upperOrdinaryJointProfileConst_le_bound
    (d : ℕ) {C cstar gamma : ℝ} (hC : 0 ≤ C)
    (hcstar : 0 ≤ cstar⁻¹) (hgamma : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) :
    upperOrdinaryJointProfileConst d C cstar gamma ≤
      upperOrdinaryJointProfileBound d C cstar gamma := by
  have hpow : (3 : ℝ) ^ gamma ≤ 3 := by
    calc
      (3 : ℝ) ^ gamma ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hgamma1
      _ = 3 := Real.rpow_one 3
  have hcoef : 0 ≤ triadicJointDepthEntropyConst d * C * cstar⁻¹ * gamma := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (triadicJointDepthEntropyConst_pos d).le hC) hcstar)
      hgamma
  rw [upperOrdinaryJointProfileConst, upperOrdinaryJointProfileBound]
  calc
    triadicJointDepthEntropyConst d * C * cstar⁻¹ * gamma *
          (3 : ℝ) ^ gamma
        ≤ triadicJointDepthEntropyConst d * C * cstar⁻¹ * gamma * 3 :=
      mul_le_mul_of_nonneg_left hpow hcoef
    _ = 3 * triadicJointDepthEntropyConst d * C * cstar⁻¹ * gamma := by
      ring

/-- The joint maximum's deterministic row price is exactly the quadratic
upper profile.  This is the `hprofile` argument required by
`exists_ae_isBigOWith_gammaSigma_one_gridSupAbs_aggregate_majorant` at the
source ordinary per-cube amplitude. -/
theorem triadicJointDepthEntropyConst_mul_upperOrdinaryPerCubeAmplitude_eq
    (d : ℕ) (C cstar gamma : ℝ) (k : ℕ) :
    triadicJointDepthEntropyConst d * ((k : ℝ) + 1) *
        upperOrdinaryPerCubeAmplitude C cstar gamma k =
      upperPolyProfile (upperOrdinaryJointProfileConst d C cstar gamma)
        gamma k := by
  rw [upperOrdinaryPerCubeAmplitude, upperOrdinaryJointProfileConst,
    upperPolyProfile]
  rw [show gamma * ((k : ℝ) + 1) = gamma + gamma * (k : ℝ) by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  ring


/-- The profile comparison with the harmless `3^gamma` factor absorbed into a
dimension-only head.  Its assumptions are sign data and the standing
small-`gamma` range only. -/
theorem triadicJointDepthEntropyConst_mul_upperOrdinaryPerCubeAmplitude_le_bound
    (d : ℕ) {C cstar gamma : ℝ} (hC : 0 ≤ C)
    (hcstar : 0 ≤ cstar⁻¹) (hgamma : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (k : ℕ) :
    triadicJointDepthEntropyConst d * ((k : ℝ) + 1) *
        upperOrdinaryPerCubeAmplitude C cstar gamma k ≤
      upperPolyProfile (upperOrdinaryJointProfileBound d C cstar gamma)
        gamma k := by
  rw [triadicJointDepthEntropyConst_mul_upperOrdinaryPerCubeAmplitude_eq]
  unfold upperPolyProfile
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
  exact mul_le_mul_of_nonneg_right
    (upperOrdinaryJointProfileConst_le_bound d hC hcstar hgamma hgamma1)
    (sq_nonneg _)

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
