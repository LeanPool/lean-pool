/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.IntrinsicScale
public import LeanPool.HighContrastHomogenization.Support.Ambient.Basic

/-!
# SuperdiffusiveBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Arithmetic assembly of the quenched displacement bounds

This file isolates the deterministic last step in the proof of ABK26,
Proposition `p.displacement.superdiffusive.bounds`.  The two results below are conditional
helpers whose hypotheses are the component process estimates.

For the directional second moment, the named inputs are precisely the stopped estimate, the
second-moment removal estimate, the comparison of the effective diffusivity with the intrinsic
scale, and the rare-exit estimate.  For the squared mean, the named inputs are the stopped
squared-mean estimate and the squared form of mean removal.  The conclusions retain every
numerical coefficient, so a later application can choose one common constant without hiding
arithmetic in an unnamed hypothesis.

The final section records the factor conversion used in the annealed estimate.  In particular,
the square of `sqrt p + sqrt |log gamma|` is bounded by the explicit factor
`2 * (p + |log gamma|)`; the two factors are not absorbed into an unspecified constant.

## References

* ABK26, Proposition `p.displacement.superdiffusive.bounds`, displays
  `e.second.moment.ThmA` and `e.displacement.squared.ThmA`.
-/

namespace Algsuperdiff.Section5.Provider

open HCPolySupport

noncomputable section

/-! ## 1. Small powers of the disorder parameter -/

private theorem pow_fifty_le_self {gamma : ℝ} (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) :
    gamma ^ (50 : ℕ) ≤ gamma := by
  rw [show (50 : ℕ) = 49 + 1 by norm_num, pow_succ]
  calc gamma ^ (49 : ℕ) * gamma ≤ 1 * gamma :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hgamma0 hgamma1) hgamma0
    _ = gamma := one_mul gamma

private theorem pow_hundred_le_pow_eighty {gamma : ℝ} (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) :
    gamma ^ (100 : ℕ) ≤ gamma ^ (80 : ℕ) := by
  rw [show (100 : ℕ) = 80 + 20 by norm_num, pow_add]
  exact mul_le_of_le_one_right (pow_nonneg hgamma0 80) (pow_le_one₀ hgamma0 hgamma1)

private theorem gamma_le_sqrt_mul_abs_log {gamma : ℝ} (hgamma : 0 < gamma)
    (hgamma4 : gamma ≤ 1 / 4) :
    gamma ≤ Real.sqrt gamma * |Real.log gamma| := by
  have hgamma1 : gamma ≤ 1 := by linarith only [hgamma4]
  have hsqrt1 : Real.sqrt gamma ≤ 1 := by
    calc Real.sqrt gamma ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hgamma1
      _ = 1 := Real.sqrt_one
  have hsqrtLog : Real.sqrt gamma ≤ |Real.log gamma| :=
    hsqrt1.trans (Algsuperdiff.Section5.Support.one_le_abs_log hgamma hgamma4)
  calc gamma = Real.sqrt gamma * Real.sqrt gamma :=
        (Real.mul_self_sqrt hgamma.le).symm
    _ ≤ Real.sqrt gamma * |Real.log gamma| :=
      mul_le_mul_of_nonneg_left hsqrtLog (Real.sqrt_nonneg gamma)

private theorem pow_fifty_le_sqrt_mul_abs_log {gamma : ℝ} (hgamma : 0 < gamma)
    (hgamma4 : gamma ≤ 1 / 4) :
    gamma ^ (50 : ℕ) ≤ Real.sqrt gamma * |Real.log gamma| := by
  have hgamma1 : gamma ≤ 1 := by linarith only [hgamma4]
  exact (pow_fifty_le_self hgamma.le hgamma1).trans
    (gamma_le_sqrt_mul_abs_log hgamma hgamma4)

private theorem pow_hundred_le_sqrt_mul_abs_log {gamma : ℝ} (hgamma : 0 < gamma)
    (hgamma4 : gamma ≤ 1 / 4) :
    gamma ^ (100 : ℕ) ≤ Real.sqrt gamma * |Real.log gamma| := by
  have hgamma1 : gamma ≤ 1 := by linarith only [hgamma4]
  have hpow : gamma ^ (100 : ℕ) ≤ gamma := by
    rw [show (100 : ℕ) = 99 + 1 by norm_num, pow_succ]
    calc gamma ^ (99 : ℕ) * gamma ≤ 1 * gamma :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hgamma.le hgamma1) hgamma.le
      _ = gamma := one_mul gamma
  exact hpow.trans (gamma_le_sqrt_mul_abs_log hgamma hgamma4)

/-! ## 2. The directional second moment -/

/-- The deterministic assembly of the stopped, removal, scale-comparison, and rare-exit
estimates.

Here `fullSecondMoment` is the directional second moment at time `t`,
`stoppedSecondMoment` is its stopped counterpart, `sigmaTime` is
`sigmaBar_m * t`, `intrinsicSq` is the square of the intrinsic scale, and `scaleSq` is
`3^(2m)`.  The four named hypotheses are exactly the four estimates combined in the printed
proof.  The conclusion is the printed first display, with all constants exposed. -/
theorem abs_fullSecondMoment_sub_two_mul_intrinsicSq_le_of_components
    {gamma fullSecondMoment stoppedSecondMoment sigmaTime intrinsicSq scaleSq EB
      Cstopped Cremove Cscale exitProbability : ℝ}
    (hgamma : 0 < gamma) (hgamma4 : gamma ≤ 1 / 4)
    (hscaleSq : 0 ≤ scaleSq) (hsigmaTime_le : sigmaTime ≤ scaleSq)
    (hCremove : 0 ≤ Cremove) (hexitProbability : 0 ≤ exitProbability)
    (hstoppedSecondMoment :
      |stoppedSecondMoment - 2 * sigmaTime| ≤
        Cstopped * scaleSq * EB + 2 * sigmaTime * exitProbability)
    (hsecondMomentRemoval :
      |fullSecondMoment - stoppedSecondMoment| ≤
        Cremove * gamma ^ (50 : ℕ) * scaleSq)
    (hintrinsicScale :
      |intrinsicSq - sigmaTime| ≤
        Cscale * Real.sqrt gamma * |Real.log gamma| * scaleSq)
    (hearlyExit : exitProbability ≤ gamma ^ (100 : ℕ)) :
    |fullSecondMoment - 2 * intrinsicSq| ≤
      (Cstopped * EB + (Cremove + 2 + 2 * Cscale) *
        (Real.sqrt gamma * |Real.log gamma|)) * scaleSq := by
  set A : ℝ := Real.sqrt gamma * |Real.log gamma| with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (Real.sqrt_nonneg gamma) (abs_nonneg (Real.log gamma))
  have hpow50 : gamma ^ (50 : ℕ) ≤ A := by
    rw [hA]
    exact pow_fifty_le_sqrt_mul_abs_log hgamma hgamma4
  have hpow100 : gamma ^ (100 : ℕ) ≤ A := by
    rw [hA]
    exact pow_hundred_le_sqrt_mul_abs_log hgamma hgamma4
  have hremove : |fullSecondMoment - stoppedSecondMoment| ≤
      Cremove * A * scaleSq :=
    hsecondMomentRemoval.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow50 hCremove) hscaleSq)
  have hexitA : exitProbability ≤ A := hearlyExit.trans hpow100
  have hsigmaExit : sigmaTime * exitProbability ≤ scaleSq * A := by
    calc sigmaTime * exitProbability ≤ scaleSq * exitProbability :=
          mul_le_mul_of_nonneg_right hsigmaTime_le hexitProbability
      _ ≤ scaleSq * A := mul_le_mul_of_nonneg_left hexitA hscaleSq
  have hscale : |sigmaTime - intrinsicSq| ≤ Cscale * A * scaleSq := by
    calc |sigmaTime - intrinsicSq| = |intrinsicSq - sigmaTime| := abs_sub_comm _ _
      _ ≤ Cscale * Real.sqrt gamma * |Real.log gamma| * scaleSq := hintrinsicScale
      _ = Cscale * A * scaleSq := by rw [hA]; ring
  have htwoscale : |2 * (sigmaTime - intrinsicSq)| ≤
      2 * (Cscale * A * scaleSq) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hscale (by norm_num)
  have htwoExit : 2 * sigmaTime * exitProbability ≤ 2 * (scaleSq * A) := by
    calc 2 * sigmaTime * exitProbability = 2 * (sigmaTime * exitProbability) := by ring
      _ ≤ 2 * (scaleSq * A) :=
        mul_le_mul_of_nonneg_left hsigmaExit (by norm_num)
  calc
    |fullSecondMoment - 2 * intrinsicSq| =
        |(fullSecondMoment - stoppedSecondMoment) +
          (stoppedSecondMoment - 2 * sigmaTime) +
          2 * (sigmaTime - intrinsicSq)| := by
            congr 1
            ring
    _ ≤ |fullSecondMoment - stoppedSecondMoment| +
          |stoppedSecondMoment - 2 * sigmaTime| +
          |2 * (sigmaTime - intrinsicSq)| := by
            exact (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Cremove * A * scaleSq +
          (Cstopped * scaleSq * EB + 2 * sigmaTime * exitProbability) +
          2 * (Cscale * A * scaleSq) := by
            exact add_le_add (add_le_add hremove hstoppedSecondMoment) htwoscale
    _ ≤ Cremove * A * scaleSq +
          (Cstopped * scaleSq * EB + 2 * (scaleSq * A)) +
          2 * (Cscale * A * scaleSq) := by
            exact add_le_add
              (add_le_add le_rfl (add_le_add le_rfl htwoExit)) le_rfl
    _ = (Cstopped * EB + (Cremove + 2 + 2 * Cscale) * A) * scaleSq := by ring

/-! ## 3. The squared mean -/

/-- The deterministic assembly of the stopped squared-mean estimate and the squared form of
the mean-removal estimate.

The vectors are the full and stopped means.  The conclusion displays separately the two
constants multiplying `EB^2` and `gamma^80`; a later application may replace both by one
common constant. -/
theorem vecNormSq_fullMean_le_of_stopped_and_removal {d : ℕ}
    {gamma scaleSq EB Cstopped Cremove : ℝ} {fullMean stoppedMean : Vec d}
    (hgamma : 0 < gamma) (hgamma4 : gamma ≤ 1 / 4) (hscaleSq : 0 ≤ scaleSq)
    (hCremove : 0 ≤ Cremove)
    (hstoppedMean : vecNormSq stoppedMean ≤ Cstopped * scaleSq * EB ^ (2 : ℕ))
    (hmeanRemovalSquared :
      vecNormSq (fullMean - stoppedMean) ≤
        Cremove * gamma ^ (100 : ℕ) * scaleSq) :
    vecNormSq fullMean ≤
      (2 * Cstopped * EB ^ (2 : ℕ) + 2 * Cremove * gamma ^ (80 : ℕ)) * scaleSq := by
  have hgamma1 : gamma ≤ 1 := by linarith only [hgamma4]
  have hpow := pow_hundred_le_pow_eighty hgamma.le hgamma1
  have hremove : vecNormSq (fullMean - stoppedMean) ≤
      Cremove * gamma ^ (80 : ℕ) * scaleSq :=
    hmeanRemovalSquared.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hCremove) hscaleSq)
  have hsplit : fullMean = stoppedMean + (fullMean - stoppedMean) := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hsplit]
  calc
    vecNormSq (stoppedMean + (fullMean - stoppedMean)) ≤
        2 * (vecNormSq stoppedMean + vecNormSq (fullMean - stoppedMean)) :=
      vecNormSq_add_le stoppedMean (fullMean - stoppedMean)
    _ ≤ 2 * (Cstopped * scaleSq * EB ^ (2 : ℕ) +
          Cremove * gamma ^ (80 : ℕ) * scaleSq) :=
      mul_le_mul_of_nonneg_left (add_le_add hstoppedMean hremove) (by norm_num)
    _ = (2 * Cstopped * EB ^ (2 : ℕ) +
          2 * Cremove * gamma ^ (80 : ℕ)) * scaleSq := by ring

/-! ## 4. The annealed moment factor -/

/-- Squaring the first annealed factor produces the second, up to the explicit coefficient
`2`. -/
theorem sq_sqrt_add_sqrt_abs_log_le_two_mul_add {p gamma : ℝ} (hp : 0 ≤ p) :
    (Real.sqrt p + Real.sqrt |Real.log gamma|) ^ (2 : ℕ) ≤
      2 * (p + |Real.log gamma|) := by
  have hlog0 : 0 ≤ |Real.log gamma| := abs_nonneg _
  have hpSq : (Real.sqrt p) ^ (2 : ℕ) = p := Real.sq_sqrt hp
  have hlogSq : (Real.sqrt |Real.log gamma|) ^ (2 : ℕ) = |Real.log gamma| :=
    Real.sq_sqrt hlog0
  have hdiff : 0 ≤ (Real.sqrt p - Real.sqrt |Real.log gamma|) ^ (2 : ℕ) :=
    sq_nonneg _
  nlinarith only [hpSq, hlogSq, hdiff]

end

end Algsuperdiff.Section5.Provider
