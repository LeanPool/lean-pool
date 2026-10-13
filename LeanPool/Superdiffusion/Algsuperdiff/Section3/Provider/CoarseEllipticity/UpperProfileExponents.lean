/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib

/-!
# UpperProfileExponents

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
Exponent arithmetic for the Section 3.3 upper profile.

The percolation and wave-tail estimates are run at `sigma / 4`, while the
exceptional exponent in the frozen theorem is `Gamma_{(1-sigma)/3}`.  The
definitions below record the arithmetic buffer needed for the extra seam and
collar powers.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

def upperProfileSigma (sigma : ℝ) : ℝ := sigma / 4

def upperProfileBaseSigma (sigma : ℝ) : ℝ :=
  1 - upperProfileSigma sigma

def upperProfileTailSigma (sigma : ℝ) : ℝ :=
  1 / (1 + upperProfileSigma sigma)

def upperProfileTargetSigma (sigma : ℝ) : ℝ :=
  (1 - sigma) / 3

/-- The weakest hsep-factor exponent whose product with the profile tail
exponent equals the target exponent in the frozen theorem. -/
def upperProfileHsepTau (sigma : ℝ) : ℝ :=
  4 * (1 - sigma) / (8 + 3 * sigma + sigma ^ 2)

/-- Auxiliary exponent fed to the hsep indicator theorem. -/
def upperProfileHsepAuxSigma (sigma : ℝ) : ℝ :=
  upperProfileHsepTau sigma * upperProfileBaseSigma sigma /
    (upperProfileBaseSigma sigma - upperProfileHsepTau sigma)

theorem upperProfileBaseSigma_pos {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    0 < upperProfileBaseSigma sigma := by
  rw [upperProfileBaseSigma, upperProfileSigma]
  linarith

theorem upperProfileTailSigma_pos {sigma : ℝ}
    (hsigma0 : 0 < sigma) (_hsigma : sigma ≤ 1 / 2) :
    0 < upperProfileTailSigma sigma := by
  rw [upperProfileTailSigma, upperProfileSigma]
  positivity

theorem upperProfileTargetSigma_pos {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    0 < upperProfileTargetSigma sigma := by
  rw [upperProfileTargetSigma]
  exact div_pos (by linarith) (by norm_num)

theorem upperProfileHsepTau_pos {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    0 < upperProfileHsepTau sigma := by
  rw [upperProfileHsepTau]
  exact div_pos (mul_pos (by norm_num) (by linarith)) (by positivity)

theorem upperProfileHsepTau_lt_base {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    upperProfileHsepTau sigma < upperProfileBaseSigma sigma := by
  have hD : 0 < 8 + 3 * sigma + sigma ^ 2 := by positivity
  have hid :
      (4 - sigma) * (8 + 3 * sigma + sigma ^ 2) -
          (4 * (1 - sigma)) * 4 =
        16 + 20 * sigma + sigma ^ 2 - sigma ^ 3 := by ring
  have hsigmaSq : sigma ^ 2 ≤ 1 / 4 := by nlinarith
  have hcube : sigma ^ 3 ≤ sigma / 4 := by
    nlinarith [mul_nonneg hsigma0.le (sub_nonneg.mpr hsigmaSq)]
  rw [upperProfileHsepTau, upperProfileBaseSigma,
    upperProfileSigma]
  have hbaseeq : 1 - sigma / 4 = (4 - sigma) / 4 := by ring
  rw [hbaseeq]
  rw [div_lt_div_iff₀ hD (by norm_num : (0 : ℝ) < 4)]
  nlinarith

theorem upperProfileHsepAuxSigma_pos {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    0 < upperProfileHsepAuxSigma sigma := by
  rw [upperProfileHsepAuxSigma]
  exact div_pos
    (mul_pos (upperProfileHsepTau_pos hsigma0 hsigma)
      (upperProfileBaseSigma_pos hsigma0 hsigma))
    (sub_pos.mpr (upperProfileHsepTau_lt_base hsigma0 hsigma))

/-- The hsep indicator product theorem at the auxiliary exponent produces the
required hsep-factor exponent exactly. -/
theorem upperProfile_hsep_productSigma_eq {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    upperProfileBaseSigma sigma * upperProfileHsepAuxSigma sigma /
        (upperProfileBaseSigma sigma +
          upperProfileHsepAuxSigma sigma) =
      upperProfileHsepTau sigma := by
  let A := upperProfileBaseSigma sigma
  let T := upperProfileHsepTau sigma
  have hA : 0 < A := upperProfileBaseSigma_pos hsigma0 hsigma
  have hT : 0 < T := upperProfileHsepTau_pos hsigma0 hsigma
  have hTA : T < A := upperProfileHsepTau_lt_base hsigma0 hsigma
  have hsub : A - T ≠ 0 := ne_of_gt (sub_pos.mpr hTA)
  have hu : 0 < T * A / (A - T) :=
    div_pos (mul_pos hT hA) (sub_pos.mpr hTA)
  have hsum : A + T * A / (A - T) ≠ 0 := ne_of_gt (add_pos hA hu)
  change A * (T * A / (A - T)) /
      (A + T * A / (A - T)) = T
  field_simp [hsub, hsum, hA.ne']
  ring

/-- The required hsep exponent times the profile tail exponent equals the
exceptional exponent in the frozen theorem. -/
theorem upperProfile_hsep_mul_tailSigma_eq {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    upperProfileHsepTau sigma * upperProfileTailSigma sigma /
        (upperProfileHsepTau sigma +
          upperProfileTailSigma sigma) =
      upperProfileTargetSigma sigma := by
  have h1 : 4 + sigma ≠ 0 := by linarith
  have h2 : 8 + 3 * sigma + sigma ^ 2 ≠ 0 := by positivity
  rw [upperProfileHsepTau, upperProfileTailSigma,
    upperProfileSigma, upperProfileTargetSigma]
  field_simp
  ring

theorem upperProfileTargetSigma_le_hsep_mul_one {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    upperProfileTargetSigma sigma ≤
      upperProfileHsepTau sigma /
        (upperProfileHsepTau sigma + 1) := by
  have hD : 0 < 8 + 3 * sigma + sigma ^ 2 := by positivity
  have hden : 0 < 12 - sigma + sigma ^ 2 := by nlinarith [sq_nonneg sigma]
  have heq : upperProfileHsepTau sigma /
        (upperProfileHsepTau sigma + 1) =
      4 * (1 - sigma) / (12 - sigma + sigma ^ 2) := by
    apply (div_eq_iff
      (ne_of_gt (add_pos (upperProfileHsepTau_pos hsigma0 hsigma) one_pos))).2
    rw [upperProfileHsepTau]
    field_simp [hD.ne', hden.ne']
    ring
  rw [upperProfileTargetSigma, heq]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hden]
  nlinarith [mul_nonneg hsigma0.le (sq_nonneg (1 - sigma))]

/-- Harmonic-product exponents are monotone in their first input. -/
theorem productSigma_mono_left {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    a * r / (a + r) ≤ b * r / (b + r) := by
  have hb : 0 < b := ha.trans_le hab
  rw [div_le_div_iff₀ (add_pos ha hr) (add_pos hb hr)]
  nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hab)]

/-- The direct collar power `3^((2 gamma + 2b) hsep)` remains strong enough
when the frozen gate has paid `gamma ≤ b sigma`. -/
theorem upperProfileHsepTau_le_collarPowerSigma
    {sigma gamma b : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hgamma0 : 0 ≤ gamma) (hb : 0 < b)
    (hgamma : gamma ≤ b * sigma) :
    upperProfileHsepTau sigma ≤
      upperProfileBaseSigma sigma /
        ((2 * gamma + 2 * b) / b) := by
  have hp0 : 0 < (2 * gamma + 2 * b) / b := by positivity
  have hp : (2 * gamma + 2 * b) / b ≤ 2 + 2 * sigma := by
    rw [div_le_iff₀ hb]
    nlinarith
  have hsigma1 : sigma < 1 := by linarith
  have hupper : 0 < 2 + 2 * sigma := by positivity
  have hbase : 0 < upperProfileBaseSigma sigma :=
    upperProfileBaseSigma_pos hsigma0 hsigma
  calc
    upperProfileHsepTau sigma ≤
        upperProfileBaseSigma sigma / (2 + 2 * sigma) := by
      rw [upperProfileHsepTau, upperProfileBaseSigma,
        upperProfileSigma]
      rw [div_le_div_iff₀ (by positivity : 0 < 8 + 3 * sigma + sigma ^ 2)
        hupper]
      nlinarith [sq_nonneg sigma, mul_nonneg hsigma0.le (by linarith : 0 ≤ 1 - sigma)]
    _ ≤ upperProfileBaseSigma sigma /
          ((2 * gamma + 2 * b) / b) := by
      exact div_le_div_of_nonneg_left hbase.le hp0 hp

/-- Consequently the collar power times the profile tail still reaches the
exceptional exponent in the frozen theorem. -/
theorem upperProfileTargetSigma_le_collarPower_mul_tail
    {sigma gamma b : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hgamma0 : 0 ≤ gamma) (hb : 0 < b)
    (hgamma : gamma ≤ b * sigma) :
    upperProfileTargetSigma sigma ≤
      (upperProfileBaseSigma sigma / ((2 * gamma + 2 * b) / b)) *
          upperProfileTailSigma sigma /
        ((upperProfileBaseSigma sigma / ((2 * gamma + 2 * b) / b)) +
          upperProfileTailSigma sigma) := by
  rw [← upperProfile_hsep_mul_tailSigma_eq hsigma0 hsigma]
  exact productSigma_mono_left
    (upperProfileHsepTau_pos hsigma0 hsigma)
    (upperProfileHsepTau_le_collarPowerSigma hsigma0 hsigma hgamma0 hb hgamma)
    (upperProfileTailSigma_pos hsigma0 hsigma)

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
