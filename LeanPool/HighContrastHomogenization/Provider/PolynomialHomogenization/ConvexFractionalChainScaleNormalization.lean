/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexFractionalChainBallVolumeScaling

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.ConvexFractionalChainScaleNormalization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Dyadic scale normalization of fractional chain jumps
-/

namespace HCPolySupport
namespace HighContrast

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The scale-free coefficient in the consecutive fractional-chain jump. -/
@[expose]
def convexFractionalChainJumpConstant (d : ℕ) (rho Rad s : ℝ) : ℝ≥0∞ :=
  convexFractionalChainLowerCoefficient d rho Rad s 0

private theorem ofReal_mul_scale_rpow
    {t a p q : ℝ} (ht : 0 < t) (ha : 0 < a) :
    ENNReal.ofReal ((t * a) ^ p) ^ q =
      ENNReal.ofReal (a ^ p) ^ q * ENNReal.ofReal (t ^ (p * q)) := by
  rw [Real.mul_rpow ht.le ha.le,
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le p),
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht p),
    ← Real.rpow_mul ht.le]
  ac_rfl

private theorem lowerCoefficient_eq_constant_mul_scale
    (hd : 1 ≤ d) {rho Rad s t : ℝ}
    (hrho : 0 < rho) (hRad : 0 ≤ Rad) (ht : 0 < t) :
    let vE := convexHardyBallVolumeLower d (t * rho)
    let vF := convexHardyBallVolumeLower d ((1 / 2 : ℝ) * t * rho)
    let K := ENNReal.ofReal
      (((3 / 2 : ℝ) * t * (Rad + rho)) ^ ((d : ℝ) + 2 * s))
    (vF⁻¹) ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) * vE⁻¹ =
      convexFractionalChainJumpConstant d rho Rad s *
        ENNReal.ofReal (t ^ (s - (d : ℝ))) := by
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hA : 0 < 2 * rho / Real.sqrt d := div_pos (mul_pos (by norm_num) hrho) hsqrt
  have hB : 0 < rho / Real.sqrt d := div_pos hrho hsqrt
  have hQ : 0 < (3 / 2 : ℝ) * (Rad + rho) :=
    mul_pos (by norm_num) (add_pos_of_nonneg_of_pos hRad hrho)
  have hVE : convexHardyBallVolumeLower d (t * rho) =
      ENNReal.ofReal ((t * (2 * rho / Real.sqrt d)) ^ (d : ℝ)) := by
    rw [convexHardyBallVolumeLower, ← Real.rpow_natCast]
    apply congrArg ENNReal.ofReal
    congr 1
    field_simp [hsqrt.ne']
  have hVF : convexHardyBallVolumeLower d ((1 / 2 : ℝ) * t * rho) =
      ENNReal.ofReal ((t * (rho / Real.sqrt d)) ^ (d : ℝ)) := by
    rw [convexHardyBallVolumeLower, ← Real.rpow_natCast]
    apply congrArg ENNReal.ofReal
    congr 1
    field_simp [hsqrt.ne']
  have hK : ENNReal.ofReal
      (((3 / 2 : ℝ) * t * (Rad + rho)) ^ ((d : ℝ) + 2 * s)) =
      ENNReal.ofReal ((t * ((3 / 2 : ℝ) * (Rad + rho))) ^
        ((d : ℝ) + 2 * s)) := by
    apply congrArg ENNReal.ofReal
    congr 1
    ring
  have hInvHalf (z : ℝ≥0∞) : (z⁻¹) ^ (1 / 2 : ℝ) = z ^ (-(1 / 2 : ℝ)) := by
    rw [ENNReal.inv_rpow, ENNReal.rpow_neg]
  have hInv (z : ℝ≥0∞) : z⁻¹ = z ^ (-1 : ℝ) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_one]
  dsimp only
  rw [hVE, hVF, hK, hInvHalf, hInv]
  rw [ofReal_mul_scale_rpow ht hB,
    ofReal_mul_scale_rpow ht hQ,
    ofReal_mul_scale_rpow ht hA]
  rw [convexFractionalChainJumpConstant,
    convexFractionalChainLowerCoefficient]
  simp only [convexFractionalChainScale, pow_zero, one_mul, mul_one]
  rw [show convexHardyBallVolumeLower d rho =
      ENNReal.ofReal ((2 * rho / Real.sqrt d) ^ (d : ℝ)) by
    rw [convexHardyBallVolumeLower, ← Real.rpow_natCast]
    apply congrArg ENNReal.ofReal
    congr 1
    field_simp [hsqrt.ne'],
    show convexHardyBallVolumeLower d ((1 / 2 : ℝ) * rho) =
      ENNReal.ofReal ((rho / Real.sqrt d) ^ (d : ℝ)) by
        rw [convexHardyBallVolumeLower, ← Real.rpow_natCast]
        apply congrArg ENNReal.ofReal
        congr 1
        field_simp [hsqrt.ne']
        ,
    hInvHalf, hInv]
  have hexp :
      (d : ℝ) * (-(1 / 2 : ℝ)) +
          ((d : ℝ) + 2 * s) * (1 / 2 : ℝ) + (d : ℝ) * (-1 : ℝ) =
        s - (d : ℝ) := by ring
  have htcombine :
      ENNReal.ofReal (t ^ ((d : ℝ) * (-(1 / 2 : ℝ)))) *
          ENNReal.ofReal (t ^ (((d : ℝ) + 2 * s) * (1 / 2 : ℝ))) *
          ENNReal.ofReal (t ^ ((d : ℝ) * (-1 : ℝ))) =
        ENNReal.ofReal (t ^ (s - (d : ℝ))) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      ← ENNReal.ofReal_mul
        (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg ht.le _)),
      ← Real.rpow_add ht, ← Real.rpow_add ht, hexp]
  calc
    _ = (ENNReal.ofReal ((rho / Real.sqrt d) ^ (d : ℝ)) ^
          (-(1 / 2 : ℝ)) *
        ENNReal.ofReal (((3 / 2 : ℝ) * (Rad + rho)) ^
          ((d : ℝ) + 2 * s)) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((2 * rho / Real.sqrt d) ^ (d : ℝ)) ^ (-1 : ℝ)) *
        (ENNReal.ofReal (t ^ ((d : ℝ) * (-(1 / 2 : ℝ)))) *
          ENNReal.ofReal (t ^ (((d : ℝ) + 2 * s) * (1 / 2 : ℝ))) *
          ENNReal.ofReal (t ^ ((d : ℝ) * (-1 : ℝ)))) := by ac_rfl
    _ = (ENNReal.ofReal ((rho / Real.sqrt d) ^ (d : ℝ)) ^
          (-(1 / 2 : ℝ)) *
        ENNReal.ofReal (((3 / 2 : ℝ) * (Rad + rho)) ^
          ((d : ℝ) + 2 * s)) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((2 * rho / Real.sqrt d) ^ (d : ℝ)) ^ (-1 : ℝ)) *
        ENNReal.ofReal (t ^ (s - (d : ℝ))) := by rw [htcombine]
    _ = _ := by ac_rfl

/-- The lower-volume-normalized chain coefficient has exactly the dyadic
homogeneity `scale^(s-d)`. -/
theorem convexFractionalChainLowerCoefficient_eq
    (hd : 1 ≤ d) {rho Rad s : ℝ} (hrho : 0 < rho) (hRad : 0 ≤ Rad)
    (n : ℕ) :
    convexFractionalChainLowerCoefficient d rho Rad s n =
      convexFractionalChainJumpConstant d rho Rad s *
        ENNReal.ofReal (convexFractionalChainScale n ^ (s - (d : ℝ))) := by
  exact lowerCoefficient_eq_constant_mul_scale hd hrho hRad
    (convexFractionalChainScale_pos n)

/-- The exact consecutive-ball coefficient is bounded by the scale-free
structural constant times `scale^(s-d)`. -/
theorem convexFractionalChainExactCoefficient_le_scale
    (hd : 1 ≤ d) (c x : Vec d) {rho Rad s : ℝ}
    (hrho : 0 < rho) (hRad : 0 ≤ Rad) (n : ℕ) :
    convexFractionalChainExactCoefficient c x rho Rad s n ≤
      convexFractionalChainJumpConstant d rho Rad s *
        ENNReal.ofReal (convexFractionalChainScale n ^ (s - (d : ℝ))) := by
  rw [← convexFractionalChainLowerCoefficient_eq hd hrho hRad n]
  exact convexFractionalChainExactCoefficient_le_lowerCoefficient
    hd c x hrho n

end

end HighContrast
end HCPolySupport
