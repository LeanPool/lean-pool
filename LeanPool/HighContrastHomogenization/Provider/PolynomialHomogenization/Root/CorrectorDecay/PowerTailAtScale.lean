/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.CanonicalGaugeSpine

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.PowerTailAtScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open Set

noncomputable section

/-- A power tail can be restarted at any natural generation above its real
reference scale, retaining the exact power price at that generation. -/
theorem powerTail_goodTail_at_nat
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s amplitude kappa x : ℝ}
    (hPower : ScalarIdentityPowerTail a s amplitude kappa x)
    (hAmplitude : 0 ≤ amplitude) (hKappa : 0 < kappa)
    {q : ℕ} (hxq : x ≤ (3 : ℝ) ^ q) (hx : 0 < x) :
    ScalarIdentityGoodTail a s
      ((amplitude * (((3 : ℝ) ^ q) / x) ^ (-kappa)) /
        (1 - (3 : ℝ) ^ (-kappa))) (q : ℤ) := by
  have hy : 0 < (3 : ℝ) ^ q := by positivity
  have hyOne : 1 ≤ (3 : ℝ) ^ q := one_le_pow₀ (by norm_num)
  have hrebased := hPower.rebase hx hy hxq
  have hratioNonneg : 0 ≤ (((3 : ℝ) ^ q) / x) ^ (-kappa) :=
    Real.rpow_nonneg (div_nonneg hy.le hx.le) _
  have hgood := hrebased.goodTail
    (mul_nonneg hAmplitude hratioNonneg) hKappa hyOne
  have hceil : Quenched.triadicCeilingIndex ((3 : ℝ) ^ q) ≤ q :=
    Quenched.triadicCeilingIndex_le_of_le_pow hyOne le_rfl
  have hceilZ :
      (Quenched.triadicCeilingIndex ((3 : ℝ) ^ q) : ℤ) ≤ (q : ℤ) := by
    exact_mod_cast hceil
  exact hgood.mono_start hceilZ

/-- At the canonical target amplitude, the restarted tolerance is exactly
one half of the successor smallness times the physical power price. -/
theorem canonical_restarted_tolerance_eq
    {c kappa x : ℝ} {q : ℕ} (hKappa : 0 < kappa) :
    (correctorTargetAmplitude c kappa *
          (((3 : ℝ) ^ q) / x) ^ (-kappa)) /
        (1 - (3 : ℝ) ^ (-kappa)) =
      (c / 2) * (((3 : ℝ) ^ q) / x) ^ (-kappa) := by
  have hpow : (3 : ℝ) ^ (-kappa) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hKappa)
  unfold correctorTargetAmplitude
  field_simp [sub_ne_zero.mpr hpow.ne.symm]

end

end HighContrast
end HCPolySupport
