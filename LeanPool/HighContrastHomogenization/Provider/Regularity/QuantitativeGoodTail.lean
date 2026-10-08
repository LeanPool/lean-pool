/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.GoodTail
public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledMixingScaleDecay
public import LeanPool.HighContrastHomogenization.Provider.Transport.DiscreteConvolution

/-!
# High-contrast homogenization: Provider.Regularity.QuantitativeGoodTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quantitative weak-error tails

This file records the pointwise power decay retained by the normalized
reference certificate and proves its two basic operations: deterministic
rebasing of the reference scale and projection to a summable good tail.
-/

namespace HCPolySupport
namespace HighContrast

open scoped BigOperators

noncomputable section

/-- The scalar identity weak error decays with a fixed power above a real
reference scale. -/
@[expose]
def ScalarIdentityPowerTail {d : ℕ}
    (a : Book.Ch02.TriadicCoeffFamily d) (s amplitude kappa x : ℝ) : Prop :=
  ∀ k : ℤ, x ≤ (3 : ℝ) ^ k →
    scalarIdentityWeakError a s k ≤
      amplitude * (((3 : ℝ) ^ k) / x) ^ (-kappa)

/-- Increasing the amplitude preserves a quantitative weak-error tail. -/
theorem ScalarIdentityPowerTail.mono_amplitude
    {d : ℕ} {a : Book.Ch02.TriadicCoeffFamily d}
    {s amplitude amplitude' kappa x : ℝ}
    (h : ScalarIdentityPowerTail a s amplitude kappa x)
    (hAmplitude : amplitude ≤ amplitude') (hx : 0 < x) :
    ScalarIdentityPowerTail a s amplitude' kappa x := by
  intro k hxk
  have hpow : 0 < (3 : ℝ) ^ k := by positivity
  have hratio : 0 ≤ (((3 : ℝ) ^ k) / x) ^ (-kappa) :=
    Real.rpow_nonneg (div_nonneg hpow.le hx.le) _
  exact (h k hxk).trans (mul_le_mul_of_nonneg_right hAmplitude hratio)

/-- Rebasing to a larger positive scale divides the retained amplitude by the
corresponding power, without changing the exponent or coefficient family. -/
theorem ScalarIdentityPowerTail.rebase
    {d : ℕ} {a : Book.Ch02.TriadicCoeffFamily d}
    {s amplitude kappa x y : ℝ}
    (h : ScalarIdentityPowerTail a s amplitude kappa x)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) :
    ScalarIdentityPowerTail a s
      (amplitude * (y / x) ^ (-kappa)) kappa y := by
  intro k hyk
  have hxk : x ≤ (3 : ℝ) ^ k := hxy.trans hyk
  have hpow : 0 < (3 : ℝ) ^ k := by positivity
  have hyx : 0 ≤ y / x := (div_pos hy hx).le
  have hky : 0 ≤ (3 : ℝ) ^ k / y := (div_pos hpow hy).le
  have hfactor :
      (y / x) ^ (-kappa) * (((3 : ℝ) ^ k) / y) ^ (-kappa) =
        (((3 : ℝ) ^ k) / x) ^ (-kappa) := by
    rw [← Real.mul_rpow hyx hky]
    congr 1
    field_simp
  calc
    scalarIdentityWeakError a s k ≤
        amplitude * (((3 : ℝ) ^ k) / x) ^ (-kappa) := h k hxk
    _ = (amplitude * (y / x) ^ (-kappa)) *
        (((3 : ℝ) ^ k) / y) ^ (-kappa) := by
      rw [mul_assoc, hfactor]

private theorem physical_ratio_rpow_le_geometric_gap
    {x kappa : ℝ} {n k : ℤ} (hx : 0 < x)
    (hxn : x ≤ (3 : ℝ) ^ n) (hkappa : 0 < kappa) :
    (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤
      (3 : ℝ) ^ (-kappa * ((k : ℝ) - (n : ℝ))) := by
  have hkpow : 0 < (3 : ℝ) ^ k := by positivity
  have hratio : 0 < ((3 : ℝ) ^ k) / x := div_pos hkpow hx
  have hgap : 0 < (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) := by positivity
  have hbase :
      (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) ≤ ((3 : ℝ) ^ k) / x := by
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

/-- A positive quantitative power tail is summable from the first triadic
generation above its real reference scale. -/
theorem ScalarIdentityPowerTail.goodTail
    {d : ℕ} {a : Book.Ch02.TriadicCoeffFamily d}
    {s amplitude kappa x : ℝ}
    (h : ScalarIdentityPowerTail a s amplitude kappa x)
    (hAmplitude : 0 ≤ amplitude) (hKappa : 0 < kappa) (hx : 1 ≤ x) :
    ScalarIdentityGoodTail a s
      (amplitude / (1 - (3 : ℝ) ^ (-kappa)))
      (Quenched.triadicCeilingIndex x : ℤ) := by
  let N : ℕ := Quenched.triadicCeilingIndex x
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hceilNat : x ≤ (3 : ℝ) ^ N := by
    simpa only [N] using Quenched.le_pow_triadicCeilingIndex hx
  have hceil : x ≤ (3 : ℝ) ^ (N : ℤ) := by
    simpa only [zpow_natCast] using hceilNat
  have hweak : ∀ k : ℤ, (N : ℤ) ≤ k →
      scalarIdentityWeakError a s k ≤
        amplitude *
          (3 : ℝ) ^ (-kappa * ((k : ℝ) - (N : ℝ))) := by
    intro k hNk
    have hxk : x ≤ (3 : ℝ) ^ k :=
      hceil.trans (zpow_le_zpow_right₀ (by norm_num) hNk)
    have hratio := physical_ratio_rpow_le_geometric_gap
      hxpos hceil hKappa (k := k)
    exact (h k hxk).trans (mul_le_mul_of_nonneg_left hratio hAmplitude)
  intro m hNm
  unfold ScalarIdentityGoodTailOnInterval
  have hgeom := Transport.sum_geom_above_le (c := kappa) hKappa
    (N : ℤ) (Finset.Icc (N : ℤ) m)
    (fun k hk ↦ (Finset.mem_Icc.mp hk).1)
  calc
    ∑ k ∈ Finset.Icc (N : ℤ) m, scalarIdentityWeakError a s k ≤
        ∑ k ∈ Finset.Icc (N : ℤ) m,
          amplitude *
            (3 : ℝ) ^ (-kappa * ((k : ℝ) - (N : ℝ))) :=
      Finset.sum_le_sum fun k hk ↦ hweak k (Finset.mem_Icc.mp hk).1
    _ = amplitude *
        ∑ k ∈ Finset.Icc (N : ℤ) m,
          (3 : ℝ) ^ (-kappa * ((k : ℝ) - (N : ℝ))) := by
      rw [Finset.mul_sum]
    _ ≤ amplitude * (1 / (1 - (3 : ℝ) ^ (-kappa))) :=
      mul_le_mul_of_nonneg_left hgeom hAmplitude
    _ = amplitude / (1 - (3 : ℝ) ^ (-kappa)) := by
      simp only [div_eq_mul_inv, one_mul]

end

end HighContrast
end HCPolySupport
