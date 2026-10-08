/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.BadScaleTiles
public import LeanPool.HighContrastHomogenization.Annealed.SourceIntegrability
public import LeanPool.HighContrastHomogenization.Provider.Window.MultiplierMoment

/-!
# High-contrast homogenization: Provider.Window.BadScaleBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section


namespace HCPolySupport
namespace HighContrast
namespace Window
open MeasureTheory
open scoped ENNReal
noncomputable section

variable {d : ℕ}

private theorem one_le_momentMultiplier {Q K : ℝ} (hQ : 1 ≤ Q) :
    1 ≤ momentMultiplier Q (growthBar K) := by
  have hB : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hBpos : 0 < growthBar K := by linarith only [hB]
  have hz : 0 ≤ growthBar K ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) :=
    (zpow_pos hBpos _).le
  have hlog : 0 ≤ Real.log (growthBar K) :=
    Real.log_nonneg (by linarith only [hB])
  rw [momentMultiplier]
  apply Real.one_le_rpow
  · have hp : 0 ≤ 2 * Q * growthBar K ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) *
        (1 + Real.log (growthBar K)) := by positivity
    linarith only [hp]
  · exact inv_nonneg.mpr (by linarith only [hQ])

private theorem one_le_scaled_generation
    {Q K : ℝ} (hQ : 1 ≤ Q) {jStar M m : ℤ}
    (hw : IsCoupledWindow d Q K jStar M) (hm : M ≤ m) :
    1 ≤ (growthBar K ^ (4 * (d + 1)))⁻¹ *
      (3 : ℝ) ^ (m - (M - jStar)) := by
  let B : ℝ := growthBar K
  let r : ℕ := 4 * (d + 1)
  let C : ℝ := B ^ r
  let j : ℤ := m - (M - jStar)
  have hB : 0 < B := by
    dsimp only [B, growthBar]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hC : 0 < C := pow_pos hB _
  have hR : 1 ≤ momentMultiplier Q B := by
    simpa only [B] using one_le_momentMultiplier (K := K) hQ
  have hscale := sourceRemainderScale_mul_momentMultiplier_le_one
    (d := d) hQ hw
  have hA : C * (3 : ℝ) ^ ((2 : ℤ) - jStar) ≤ 1 := by
    calc
      C * (3 : ℝ) ^ ((2 : ℤ) - jStar)
          ≤ C * (3 : ℝ) ^ ((2 : ℤ) - jStar) * momentMultiplier Q B := by
            have hnonneg : 0 ≤ C * (3 : ℝ) ^ ((2 : ℤ) - jStar) := by positivity
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hR hnonneg
      _ ≤ 1 := by simpa only [C, B, r, sourceRemainderScale] using hscale
  have hJstar : 0 < (3 : ℝ) ^ jStar := by positivity
  have hsplit : (3 : ℝ) ^ ((2 : ℤ) - jStar) * (3 : ℝ) ^ jStar = 9 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hC9 : C * 9 ≤ (3 : ℝ) ^ jStar := by
    have hmul := mul_le_mul_of_nonneg_right hA hJstar.le
    rw [mul_assoc, hsplit, one_mul] at hmul
    exact hmul
  have h9 : (9 : ℝ) ≤ C⁻¹ * (3 : ℝ) ^ jStar := by
    have hdiv : (9 : ℝ) ≤ (3 : ℝ) ^ jStar / C :=
      (le_div_iff₀ hC).2 (by simpa only [mul_comm] using hC9)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  have hjstar : jStar ≤ j := by dsimp only [j]; omega
  have hJ : (3 : ℝ) ^ jStar ≤ (3 : ℝ) ^ j :=
    zpow_le_zpow_right₀ (by norm_num) hjstar
  have hx9 : (9 : ℝ) ≤ C⁻¹ * (3 : ℝ) ^ j :=
    h9.trans (mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hC.le))
  have : 1 ≤ C⁻¹ * (3 : ℝ) ^ j := (by norm_num : (1 : ℝ) ≤ 9).trans hx9
  simpa only [C, B, r, j] using this

private theorem tile_factor_le_scaled_generation
    {Q K : ℝ} {jStar M m : ℤ}
    (hw : IsCoupledWindow d Q K jStar M) (hm : M ≤ m) :
    (3 : ℝ) ^ (d * (M - jStar).toNat) ≤
      (3 : ℝ) ^ (-(m - (M - jStar))) *
        ((growthBar K ^ (4 * (d + 1)))⁻¹ *
          (3 : ℝ) ^ (m - (M - jStar))) ^ (4 * (d + 1)) := by
  let B : ℝ := growthBar K
  let r : ℕ := 4 * (d + 1)
  let C : ℝ := B ^ r
  let j : ℤ := m - (M - jStar)
  have hwindow := hw.2.1
  have hh0 : 0 ≤ M - jStar := by omega
  have hjStar : jStar ≤ j := by dsimp only [j]; omega
  have hB : 0 < B := by
    dsimp only [B, growthBar]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hC : 0 < C := pow_pos hB _
  have hr : 1 ≤ r := by dsimp only [r]; omega
  have hcoef : 0 ≤ 4 * (d : ℝ) + 3 := by positivity
  have hcoup :
      (d : ℝ) * ((M : ℝ) - (jStar : ℝ)) +
          16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 B ≤
        (4 * (d : ℝ) + 3) * (j : ℝ) := by
    refine hw.2.2.trans ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjStar) hcoef
  have hexp :
      ((d * (M - jStar).toNat : ℕ) : ℝ) +
          ((r * r : ℕ) : ℝ) * Real.logb 3 B ≤
        (((r - 1 : ℕ) : ℝ)) * (j : ℝ) := by
    have hcastR : ((M - jStar).toNat : ℝ) = ((M - jStar : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hh0
    calc
      ((d * (M - jStar).toNat : ℕ) : ℝ) +
            ((r * r : ℕ) : ℝ) * Real.logb 3 B =
          (d : ℝ) * ((M : ℝ) - (jStar : ℝ)) +
            16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 B := by
              norm_num only [Nat.cast_mul]
              rw [hcastR, Int.cast_sub]
              dsimp only [r]
              push_cast
              ring
      _ ≤ (4 * (d : ℝ) + 3) * (j : ℝ) := hcoup
      _ = (((r - 1 : ℕ) : ℝ)) * (j : ℝ) := by
        have hrm : r - 1 = 4 * d + 3 := by dsimp only [r]; omega
        rw [hrm]
        push_cast
        rfl
  have hBpow : (3 : ℝ) ^ Real.logb 3 B = B :=
    Real.rpow_logb (by norm_num) (by norm_num) hB
  have hlarge :
      (3 : ℝ) ^ (d * (M - jStar).toNat) * C ^ r ≤
        ((3 : ℝ) ^ j) ^ (r - 1) := by
    calc
      (3 : ℝ) ^ (d * (M - jStar).toNat) * C ^ r =
          (3 : ℝ) ^ (d * (M - jStar).toNat) * B ^ (r * r) := by
            change (3 : ℝ) ^ (d * (M - jStar).toNat) * (B ^ r) ^ r = _
            rw [← pow_mul]
      _ = (3 : ℝ) ^ (d * (M - jStar).toNat) *
          ((3 : ℝ) ^ Real.logb 3 B) ^ (r * r) := by rw [hBpow]
      _ = (3 : ℝ) ^
          (((d * (M - jStar).toNat : ℕ) : ℝ) +
            ((r * r : ℕ) : ℝ) * Real.logb 3 B) := by
              rw [← Real.rpow_natCast,
                ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3),
                mul_comm (Real.logb 3 B),
                ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ ≤ (3 : ℝ) ^ ((((r - 1 : ℕ) : ℝ)) * (j : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = ((3 : ℝ) ^ j) ^ (r - 1) := by
        rw [← Real.rpow_intCast, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
        congr 1
        ring
  have hCpow : 0 < C ^ r := pow_pos hC _
  have hJpow : ((3 : ℝ) ^ j) ^ r =
      ((3 : ℝ) ^ j) ^ (r - 1) * (3 : ℝ) ^ j := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
  have halgebra : ((3 : ℝ) ^ j) ^ (r - 1) / C ^ r =
      (3 : ℝ) ^ (-j) * (C⁻¹ * (3 : ℝ) ^ j) ^ r := by
    rw [zpow_neg, mul_pow, hJpow]
    field_simp [hC.ne', zpow_ne_zero]
    rw [← mul_pow, one_div, mul_inv_cancel₀ hC.ne', one_pow]
  have hfinal := (le_div_iff₀ hCpow).2 hlarge
  rw [halgebra] at hfinal
  simpa only [C, B, r, j] using hfinal

/-- Coupling absorbs the number of aligned tiles and leaves one geometric
factor at each generation. -/
theorem measureReal_badScaleEvent_le_geometric [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M m : ℤ} (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hm : M ≤ m) :
    P.real {a : CoeffSpace d | badScaleEvent g E (M - jStar) m a} ≤
      (3 : ℝ) ^ (-(m - (M - jStar))) *
        (Ψ ((growthBar K ^ (4 * (d + 1)))⁻¹ *
          (3 : ℝ) ^ (m - (M - jStar))))⁻¹ := by
  let x : ℝ := (growthBar K ^ (4 * (d + 1)))⁻¹ *
    (3 : ℝ) ^ (m - (M - jStar))
  let p : ℝ := (3 : ℝ) ^ (d * (M - jStar).toNat)
  let r : ℕ := 4 * (d + 1)
  have hwindow := hw.2.1
  have hh0 : 0 ≤ M - jStar := by omega
  have hk : (kZero d : ℤ) ≤ jStar := by
    exact (le_max_left _ _).trans hw.1
  have hj0 : 0 ≤ jStar := (Int.natCast_nonneg _).trans hk
  have hhM : M - jStar ≤ m := by omega
  have htile := measureReal_badScaleEvent_le_tiles hstat hdag hh0 hhM
  have hB : 1 ≤ growthBar K := (by
    rw [growthBar]
    exact le_trans (by norm_num) (le_max_left _ _))
  have hgrowth : IndependentSums.HasPsiGrowth Ψ (growthBar K) :=
    hasPsiGrowth_mono hdag.gauge_admissible
      (le_of_lt hdag.one_lt_growthWitness) (le_max_right _ _) hdag.gauge_growth
  have hx : 1 ≤ x := by
    exact one_le_scaled_generation hQ hw hm
  have harg : growthBar K ^ r * x = (3 : ℝ) ^ (m - (M - jStar)) := by
    dsimp only [x, r]
    field_simp [pow_ne_zero _ (by
      rw [growthBar]
      positivity : growthBar K ≠ 0)]
  have hgauge : x ^ r * Ψ x ≤ Ψ ((3 : ℝ) ^ (m - (M - jStar))) := by
    have h := IndependentSums.hasPsiGrowth_nat_polyAbsorption hB hgrowth
      hdag.gauge_admissible r hx
    rwa [harg] at h
  have hpoly : p ≤ (3 : ℝ) ^ (-(m - (M - jStar))) * x ^ r := by
    exact tile_factor_le_scaled_generation hw hm
  have hp0 : 0 ≤ p := by positivity
  have hxpow : 0 < x ^ r := pow_pos (lt_of_lt_of_le zero_lt_one hx) _
  have hPsiX : 0 < Ψ x := lt_of_lt_of_le zero_lt_one
    (hdag.gauge_admissible.2 (le_trans zero_le_one hx))
  have hPsiC : 0 < Ψ ((3 : ℝ) ^ (m - (M - jStar))) :=
    lt_of_lt_of_le zero_lt_one (hdag.gauge_admissible.2 (by positivity))
  calc
    P.real {a : CoeffSpace d | badScaleEvent g E (M - jStar) m a}
        ≤ p * (Ψ ((3 : ℝ) ^ (m - (M - jStar))))⁻¹ := by
          simpa only [p] using htile
    _ ≤ p * (x ^ r * Ψ x)⁻¹ :=
      mul_le_mul_of_nonneg_left
        ((inv_le_inv₀ hPsiC (mul_pos hxpow hPsiX)).2 hgauge) hp0
    _ = (p / x ^ r) * (Ψ x)⁻¹ := by field_simp
    _ ≤ (3 : ℝ) ^ (-(m - (M - jStar))) * (Ψ x)⁻¹ := by
      exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hxpow).2 hpoly)
        (inv_nonneg.mpr hPsiX.le)
    _ = (3 : ℝ) ^ (-(m - (M - jStar))) *
        (Ψ ((growthBar K ^ (4 * (d + 1)))⁻¹ *
          (3 : ℝ) ^ (m - (M - jStar))))⁻¹ := by rfl

end
end Window
end HighContrast
end HCPolySupport
