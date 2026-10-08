/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowTerminalNormalization

/-!
# High-contrast homogenization: Provider.Transport.WindowMomentBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The multiplier's moment is at most two

The coupled window on which the single source multiplier is built places its
alignment scale above the source burn `j_{\mathcal S}` of
`e.source.lower.scale`, and the third entry of that burn is chosen so that the
residual source parameter
`a_{j_*}^{\mathcal S} = \overline K_{\mathcal S}^{4(d+1)}3^{2-j_*}` cancels the
weak-Orlicz moment multiplier `\mathfrak M_Q(\overline K_{\mathcal S})`
furnished by the source tail gauge outright:

`j_*\geq 2+4(d+1)\log_3\overline K_{\mathcal S}
   +\log_3\mathfrak M_Q(\overline K_{\mathcal S})`
gives `3^{2-j_*}\leq\overline K_{\mathcal S}^{-4(d+1)}
  \mathfrak M_Q(\overline K_{\mathcal S})^{-1}`,

and hence `a_{j_*}^{\mathcal S}\mathfrak M_Q\leq1`.  The moment display of the
window multiplier then reads `‖Y_P‖_{L^Q}\leq1+a_{j_*}^{\mathcal S}\mathfrak M_Q
  \leq2`, which is the universal bound `\mathcal U = 2` the transport uses for
every cell of the window, and squaring it closes the terminal loss, the cost of
the source multiplier in the normalized moments.

The growth witness `\overline K_{\mathcal S} = \max\{2,K_{\Psi_{\mathcal S}}\}`
is at least two by construction, which is what makes both logarithms and the
moment multiplier positive.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The two positive scalar witnesses -/

/-- The growth witness `\overline K_{\mathcal S} = \max\{2,K_{\Psi_{\mathcal S}}\}`
is at least two. -/
theorem two_le_growthBar (K : ℝ) : (2 : ℝ) ≤ growthBar K :=
  le_max_left _ _

/-- The weak-Orlicz moment multiplier is positive: its base exceeds one, the
growth witness being at least two. -/
theorem zero_lt_momentMultiplier {Q K : ℝ} (hQ : 0 < Q) :
    (0 : ℝ) < momentMultiplier Q (growthBar K) := by
  have hKb2 : (2 : ℝ) ≤ growthBar K := two_le_growthBar K
  have hlog : (0 : ℝ) < Real.log (growthBar K) := Real.log_pos (by linarith only [hKb2])
  have hzp : (0 : ℝ) < growthBar K ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) :=
    zpow_pos (by linarith only [hKb2]) _
  rw [momentMultiplier]
  refine Real.rpow_pos_of_pos ?_ _
  have hp : (0 : ℝ) < 2 * Q * growthBar K ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) *
      (1 + Real.log (growthBar K)) := by
    refine mul_pos (mul_pos (by linarith only [hQ]) hzp) ?_
    linarith only [hlog]
  linarith only [hp]

/-! ## The burn cancels the moment multiplier -/

/-- **The source-remainder scale cancels the moment multiplier.**  This is what
the third entry of the source burn is for: at any alignment scale above the burn
the product is at most one. -/
theorem sourceRemainderScale_mul_momentMultiplier_le_one {Q K : ℝ} (hQ : 0 < Q)
    {jStar M : ℤ} (hw : IsCoupledWindow d Q K jStar M) :
    sourceRemainderScale d jStar K * momentMultiplier Q (growthBar K) ≤ 1 := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hKb2 : (2 : ℝ) ≤ growthBar K := two_le_growthBar K
  have hKb : (0 : ℝ) < growthBar K := by linarith only [hKb2]
  have hMpos : (0 : ℝ) < momentMultiplier Q (growthBar K) := zero_lt_momentMultiplier hQ
  have hb := hw.1
  rw [sourceBurn] at hb
  have hburn := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hb)
  have hreal : (2 : ℝ) + 4 * ((d : ℝ) + 1) * Real.logb 3 (growthBar K) +
      Real.logb 3 (momentMultiplier Q (growthBar K)) ≤ (jStar : ℝ) :=
    le_trans (Int.le_ceil _) (by exact_mod_cast hburn)
  set L : ℝ := Real.logb 3 (growthBar K) with hL
  set N : ℝ := Real.logb 3 (momentMultiplier Q (growthBar K)) with hN
  have hzpow : (3 : ℝ) ^ ((2 : ℤ) - jStar) = (3 : ℝ) ^ ((2 : ℝ) - (jStar : ℝ)) := by
    rw [← Real.rpow_intCast]
    push_cast
    ring_nf
  have hmono : (3 : ℝ) ^ ((2 : ℝ) - (jStar : ℝ)) ≤
      (3 : ℝ) ^ (-(4 * ((d : ℝ) + 1)) * L + -N) := by
    refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).mpr ?_
    linarith only [hreal]
  have hsplit : (3 : ℝ) ^ (-(4 * ((d : ℝ) + 1)) * L + -N) =
      growthBar K ^ (-(4 * ((d : ℝ) + 1))) * (momentMultiplier Q (growthBar K))⁻¹ := by
    rw [Real.rpow_add h3]
    congr 1
    · rw [mul_comm (-(4 * ((d : ℝ) + 1))) L, Real.rpow_mul h3.le, hL,
        Real.rpow_logb h3 (by norm_num) hKb]
    · rw [Real.rpow_neg h3.le, hN, Real.rpow_logb h3 (by norm_num) hMpos]
  have hKpow : growthBar K ^ (4 * (d + 1)) * growthBar K ^ (-(4 * ((d : ℝ) + 1))) = 1 := by
    rw [← Real.rpow_natCast (growthBar K) (4 * (d + 1)), ← Real.rpow_add hKb,
      show ((4 * (d + 1) : ℕ) : ℝ) + -(4 * ((d : ℝ) + 1)) = 0 by push_cast; ring,
      Real.rpow_zero]
  have hnn : (0 : ℝ) ≤ growthBar K ^ (4 * (d + 1)) := by positivity
  have hstep : (3 : ℝ) ^ ((2 : ℤ) - jStar) ≤
      growthBar K ^ (-(4 * ((d : ℝ) + 1))) * (momentMultiplier Q (growthBar K))⁻¹ := by
    rw [hzpow, ← hsplit]
    exact hmono
  calc sourceRemainderScale d jStar K * momentMultiplier Q (growthBar K)
      = growthBar K ^ (4 * (d + 1)) * (3 : ℝ) ^ ((2 : ℤ) - jStar) *
          momentMultiplier Q (growthBar K) := by rw [sourceRemainderScale]
    _ ≤ growthBar K ^ (4 * (d + 1)) *
          (growthBar K ^ (-(4 * ((d : ℝ) + 1))) *
            (momentMultiplier Q (growthBar K))⁻¹) *
          momentMultiplier Q (growthBar K) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hnn) hMpos.le
    _ = 1 := by
        rw [show growthBar K ^ (4 * (d + 1)) *
              (growthBar K ^ (-(4 * ((d : ℝ) + 1))) *
                (momentMultiplier Q (growthBar K))⁻¹) *
              momentMultiplier Q (growthBar K) =
            growthBar K ^ (4 * (d + 1)) * growthBar K ^ (-(4 * ((d : ℝ) + 1))) *
              ((momentMultiplier Q (growthBar K))⁻¹ *
                momentMultiplier Q (growthBar K)) by ring,
          hKpow, inv_mul_cancel₀ hMpos.ne', mul_one]

/-! ## The universal moment bound and the terminal loss -/

variable {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
  {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-- **The universal moment bound `‖Y_P‖_{L^Q}\leq\mathcal U = 2`.**  The window
multiplier's own moment display, with the source burn absorbing the remainder
scale. -/
theorem lqNorm_le_two {Q : ℝ} (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) : lqNorm P Q Y ≤ 2 := by
  refine le_trans (hY.lp_moment Q hQ) ?_
  have hle : 1 + sourceRemainderScale d jStar K * momentMultiplier Q (growthBar K) ≤ 2 := by
    linarith only [sourceRemainderScale_mul_momentMultiplier_le_one
      (lt_of_lt_of_le zero_lt_one hQ) hw]
  calc ENNReal.ofReal
        (1 + sourceRemainderScale d jStar K * momentMultiplier Q (growthBar K))
      ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hle
    _ = 2 := by norm_num

/-- An L^Q upper bound by two converts an ofReal bound for a multiplier's
mean into the corresponding real upper bound. -/
theorem integral_le_two {P : Measure (CoeffSpace d)} {Q : ℝ}
    {Y : CoeffSpace d → ℝ}
    (hnorm : ENNReal.ofReal (∫ a, Y a ∂P) ≤ lqNorm P Q Y)
    (htwo : lqNorm P Q Y ≤ 2) :
    (∫ a, Y a ∂P) ≤ 2 := by
  have h : ENNReal.ofReal (∫ a, Y a ∂P) ≤ ENNReal.ofReal 2 :=
    hnorm.trans (by simpa using htwo)
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h

/-- The source-remainder scale is positive. -/
theorem zero_lt_sourceRemainderScale (d : ℕ) (jStar : ℤ) (K : ℝ) :
    0 < sourceRemainderScale d jStar K := by
  have hKb : (0 : ℝ) < growthBar K := lt_of_lt_of_le (by norm_num) (two_le_growthBar K)
  rw [sourceRemainderScale]
  positivity

/-- **The squared moment bound `‖Y_P‖_{L^Q}^2\leq4`**, the last inequality in
the cost of the source multiplier in the normalized moments. -/
theorem lqNorm_sq_le_four {Q : ℝ} (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) : lqNorm P Q Y ^ 2 ≤ 4 := by
  have h := lqNorm_le_two hQ hw hY
  rw [pow_two]
  calc lqNorm P Q Y * lqNorm P Q Y ≤ 2 * 2 := mul_le_mul' h h
    _ = 4 := by norm_num

end

end Transport
end HighContrast
end HCPolySupport
