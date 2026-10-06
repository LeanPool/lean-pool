/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.RenormalizedDaggerCore
public import LeanPool.HighContrastHomogenization.Provider.Quenched.BlockScaleGeometry
public import LeanPool.HighContrastHomogenization.Provider.Entry.EuclideanAdapter

/-!
# High-contrast homogenization: Provider.Quenched.RenormalizationParameterArithmetic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Arithmetic for the one-time renormalization

The parameter choices below are made before the probability law.  They turn a
single triadic bracket for the polynomial base into the window, inner-scale,
and radius-buffer inequalities used by the renormalized dagger.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

noncomputable section

private theorem one_add_mul_le_rpow_nat {nu : Real} (hnu : 0 <= nu) (j : Nat) :
    1 + (j : Real) * ((3 : Real) ^ nu - 1) <=
      (3 : Real) ^ (nu * (j : Real)) := by
  have hpow : (3 : Real) ^ (nu * (j : Real)) = ((3 : Real) ^ nu) ^ j := by
    rw [Real.rpow_mul (by norm_num : (0 : Real) <= 3), Real.rpow_natCast]
  have hone : (1 : Real) <= (3 : Real) ^ nu := by
    simpa only [← Real.rpow_zero (3 : Real)] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hnu
  have hbern := one_add_mul_le_pow (a := (3 : Real) ^ nu - 1)
    (by linarith only [hone]) j
  have hbaseeq : 1 + ((3 : Real) ^ nu - 1) = (3 : Real) ^ nu := by ring
  rw [hbaseeq] at hbern
  rw [hpow]
  exact hbern

private theorem log_renormCellCount_le (d A q : Nat) (hA : 1 <= A)
    (hq : 1 <= q) :
    Real.log (2 * renormCellCount d (A * q)) <=
      (2 * (A : Real) + (d : Real) * (A : Real) * Real.log 3) * (q : Real) := by
  have hApos : 0 < A := lt_of_lt_of_le Nat.zero_lt_one hA
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have htwoAq : (0 : Real) < 2 * ((A * q : Nat) : Real) := by positivity
  have hpow : (0 : Real) < (3 : Real) ^ (d * (A * q)) := by positivity
  rw [renormCellCount]
  rw [show 2 * (((A * q : Nat) : Real) * (3 : Real) ^ (d * (A * q))) =
      (2 * ((A * q : Nat) : Real)) * (3 : Real) ^ (d * (A * q)) by ring]
  rw [Real.log_mul (ne_of_gt htwoAq) (ne_of_gt hpow),
    Real.log_pow]
  have hlog := Real.log_le_sub_one_of_pos htwoAq
  have hcast : ((d * (A * q) : Nat) : Real) =
      (d : Real) * (A : Real) * (q : Real) := by push_cast; ring
  rw [hcast]
  have hqreal : (1 : Real) <= (q : Real) := by exact_mod_cast hq
  have hbound : 2 * ((A * q : Nat) : Real) - 1 <=
      2 * (A : Real) * (q : Real) := by
    push_cast
    linarith only [hqreal]
  calc
    Real.log (2 * ((A * q : Nat) : Real)) +
        (d : Real) * (A : Real) * (q : Real) * Real.log 3
      <= 2 * (A : Real) * (q : Real) +
        (d : Real) * (A : Real) * (q : Real) * Real.log 3 := by
          linarith only [hlog, hbound]
    _ = (2 * (A : Real) + (d : Real) * (A : Real) * Real.log 3) *
        (q : Real) := by ring

/-- A fixed multiple of the base index absorbs the radius union-bound
prefactor uniformly in that index. -/
theorem renorm_buffer_of_multiplier {d A B q : Nat} {mu : Real}
    (hmu : 0 < mu) (hA : 1 <= A) (hq : 1 <= q)
    (hB :
      (2 * (A : Real) + (d : Real) * (A : Real) * Real.log 3) /
          frGaugeConst d + 1 <=
        (3 : Real) ^ (2 * mu * (B : Real))) :
    Real.log (2 * renormCellCount d (A * q)) <=
      frGaugeConst d *
        ((3 : Real) ^ (2 * mu * ((B * q : Nat) : Real)) - 1) := by
  have hc : 0 < frGaugeConst d := frGaugeConst_pos d
  let C : Real := 2 * (A : Real) + (d : Real) * (A : Real) * Real.log 3
  have hC0 : 0 <= C := by
    have hlog3 : 0 <= Real.log 3 := Real.log_nonneg (by norm_num)
    dsimp only [C]
    positivity
  have hbase : C <= frGaugeConst d *
      ((3 : Real) ^ (2 * mu * (B : Real)) - 1) := by
    change C / frGaugeConst d + 1 <=
      (3 : Real) ^ (2 * mu * (B : Real)) at hB
    have := mul_le_mul_of_nonneg_left hB hc.le
    rw [mul_add, mul_div_cancel₀ _ hc.ne', mul_one] at this
    linarith only [this]
  have hnu : 0 <= 2 * mu * (B : Real) := by positivity
  have hbern := one_add_mul_le_rpow_nat hnu q
  have hq0 : 0 <= (q : Real) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hbase hq0
  have hlinear : C * (q : Real) <= frGaugeConst d *
      ((3 : Real) ^ (2 * mu * ((B * q : Nat) : Real)) - 1) := by
    have hcast : 2 * mu * ((B * q : Nat) : Real) =
        (2 * mu * (B : Real)) * (q : Real) := by push_cast; ring
    rw [hcast]
    calc
      C * (q : Real)
          <= (frGaugeConst d * ((3 : Real) ^ (2 * mu * (B : Real)) - 1)) *
            (q : Real) := hmul
      _ = frGaugeConst d *
          ((q : Real) * ((3 : Real) ^ (2 * mu * (B : Real)) - 1)) := by ring
      _ <= frGaugeConst d *
          ((3 : Real) ^ ((2 * mu * (B : Real)) * (q : Real)) - 1) := by
            apply mul_le_mul_of_nonneg_left _ hc.le
            linarith only [hbern]
  exact (log_renormCellCount_le d A q hA hq).trans hlinear

/-- A fixed exponent multiplier propagates a one-index triadic bound to every
positive index. -/
theorem mul_base_le_rpow_mul_index {C a : Real} {A q : Nat}
    (ha : 0 < a) (hq : 1 <= q)
    (hcoef : 0 <= a * (A : Real) - a - 1)
    (hbase : C <= (3 : Real) ^ (a * (A : Real) - a - 1))
    {base : Real} (hbase0 : 0 <= base)
    (hbase3 : base <= (3 : Real) ^ q) :
    C * base <= (3 : Real) ^ (a * ((A * q : Nat) : Real) - a) := by
  have hqreal : (1 : Real) <= (q : Real) := by exact_mod_cast hq
  have hbase3' : base <= (3 : Real) ^ (q : Real) := by
    rwa [Real.rpow_natCast]
  have hpowmul : C * base <=
      (3 : Real) ^ (a * (A : Real) - a - 1) * (3 : Real) ^ (q : Real) :=
    (mul_le_mul_of_nonneg_right hbase hbase0).trans <|
      mul_le_mul_of_nonneg_left hbase3' (Real.rpow_nonneg (by norm_num) _)
  have hexp : (a * (A : Real) - a - 1) + (q : Real) <=
      a * ((A * q : Nat) : Real) - a := by
    push_cast
    have hcoef' : 0 <= a * (A : Real) - 1 := by linarith only [hcoef, ha]
    have hmul := mul_nonneg hcoef' (sub_nonneg.mpr hqreal)
    calc
      a * (A : Real) - a - 1 + (q : Real)
          <= a * (A : Real) * (q : Real) - a := by
            nlinarith only [hmul]
      _ = a * ((A : Real) * (q : Real)) - a := by ring
  calc
    C * base <= (3 : Real) ^ (a * (A : Real) - a - 1) *
        (3 : Real) ^ (q : Real) := hpowmul
    _ = (3 : Real) ^ ((a * (A : Real) - a - 1) + (q : Real)) := by
      rw [Real.rpow_add (by norm_num)]
    _ <= (3 : Real) ^ (a * ((A * q : Nat) : Real) - a) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- Fixed parameters, chosen before the law, that absorb all dimensional
constants in the one-time renormalization. -/
theorem exists_renormalization_parameters (d : Nat)
    {g rho mu delta G0 : Real} (hdiff : 0 < rho - g) (hmu : 0 < mu)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) (hG0 : 0 < G0) :
    exists (T : Real) (A D B : Nat),
      1 <= T ∧
      Real.log 2 <= frGaugeConst d * T ^ 2 *
        ((3 : Real) ^ (2 * mu) - 1) ∧
      1 <= A ∧
      0 <= (rho - g) * (A : Real) - 1 ∧
      12 / (1 + delta) <=
        (3 : Real) ^ ((rho - g) * (A : Real) - 1) ∧
      1 <= D ∧
      0 <= mu * (D : Real) - mu - 1 ∧
      G0 * T / delta <= (3 : Real) ^ (mu * (D : Real) - mu - 1) ∧
      1 <= B ∧
      (2 * (A : Real) + (d : Real) * (A : Real) * Real.log 3) /
          frGaugeConst d + 1 <= (3 : Real) ^ (2 * mu * (B : Real)) := by
  have hc : 0 < frGaugeConst d := frGaugeConst_pos d
  have hgap : 0 < (3 : Real) ^ (2 * mu) - 1 := by
    have hone : (1 : Real) < (3 : Real) ^ (2 * mu) :=
      Real.one_lt_rpow (by norm_num) (by linarith only [hmu])
    linarith only [hone]
  let Cthr : Real := Real.log 2 / (frGaugeConst d *
    ((3 : Real) ^ (2 * mu) - 1)) + 1
  have hCthr : 0 < Cthr := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hden : 0 < frGaugeConst d * ((3 : Real) ^ (2 * mu) - 1) :=
      mul_pos hc hgap
    dsimp only [Cthr]
    positivity
  obtain ⟨R, hR⟩ := exists_shift_of_pos (mu := 2 * mu)
    (by linarith only [hmu]) hCthr
  let T : Real := (3 : Real) ^ (mu * (R : Real))
  have hT1 : 1 <= T := by
    dsimp only [T]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hTthr : Real.log 2 <= frGaugeConst d * T ^ 2 *
      ((3 : Real) ^ (2 * mu) - 1) := by
    have hden : 0 < frGaugeConst d * ((3 : Real) ^ (2 * mu) - 1) :=
      mul_pos hc hgap
    have hmain : Real.log 2 / (frGaugeConst d *
        ((3 : Real) ^ (2 * mu) - 1)) <= T ^ 2 := by
      have hpow : T ^ 2 = (3 : Real) ^ (2 * mu * (R : Real)) := by
        dsimp only [T]
        rw [← Real.rpow_natCast ((3 : Real) ^ (mu * (R : Real))) 2,
          ← Real.rpow_mul (by norm_num : (0 : Real) <= 3)]
        congr 1
        ring
      rw [hpow]
      linarith only [hR]
    have hmul := mul_le_mul_of_nonneg_left hmain hden.le
    rw [mul_div_cancel₀ _ hden.ne'] at hmul
    nlinarith only [hmul]
  let Cburn : Real := 12 / (1 + delta)
  have hCburn : 0 < Cburn := by
    dsimp only [Cburn]
    positivity
  obtain ⟨A0, hA0⟩ := exists_shift_of_pos (mu := rho - g) hdiff
    (mul_pos hCburn (by norm_num : (0 : Real) < 3))
  let A : Nat := max A0 1
  have hA : 1 <= A := le_max_right _ _
  have hA0A : (A0 : Real) <= (A : Real) := by
    exact_mod_cast Nat.le_max_left A0 1
  have hburnExp : Cburn <= (3 : Real) ^ ((rho - g) * (A : Real) - 1) := by
    have hmono : (3 : Real) ^ ((rho - g) * (A0 : Real)) <=
        (3 : Real) ^ ((rho - g) * (A : Real)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left hA0A hdiff.le)
    have hscaled := hA0.trans hmono
    have hthree : (3 : Real) ^ ((rho - g) * (A : Real)) =
        3 * (3 : Real) ^ ((rho - g) * (A : Real) - 1) := by
      rw [show (rho - g) * (A : Real) = 1 +
        ((rho - g) * (A : Real) - 1) by ring, Real.rpow_add (by norm_num)]
      norm_num
    rw [hthree] at hscaled
    nlinarith only [hscaled]
  have hburnNonneg : 0 <= (rho - g) * (A : Real) - 1 := by
    have hgt1 : 1 < Cburn := by
      have hden : 1 + delta < 2 := by linarith only [hdelta1]
      have hdenpos : 0 < 1 + delta := by linarith only [hdelta]
      rw [one_lt_div hdenpos]
      linarith only [hden]
    by_contra hneg
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : Real) < 3)
      (lt_of_not_ge hneg)
    exact (not_lt_of_ge (le_of_lt (hgt1.trans_le hburnExp))) hlt
  let Cd : Real := G0 * T / delta
  have hCd : 0 < Cd := by dsimp only [Cd]; positivity
  let Cdp : Real := max 1 Cd
  have hCdp : 0 < Cdp := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hshift : 0 < (3 : Real) ^ (mu + 1) := by positivity
  obtain ⟨D0, hD0⟩ := exists_shift_of_pos (mu := mu) hmu
    (mul_pos hCdp hshift)
  let D : Nat := max D0 1
  have hD : 1 <= D := le_max_right _ _
  have hD0D : (D0 : Real) <= (D : Real) := by
    exact_mod_cast Nat.le_max_left D0 1
  have hDexp' : Cdp <= (3 : Real) ^ (mu * (D : Real) - mu - 1) := by
    have hmono : (3 : Real) ^ (mu * (D0 : Real)) <=
        (3 : Real) ^ (mu * (D : Real)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left hD0D hmu.le)
    have hscaled := hD0.trans hmono
    have hsplit : (3 : Real) ^ (mu * (D : Real)) =
        (3 : Real) ^ (mu + 1) *
          (3 : Real) ^ (mu * (D : Real) - mu - 1) := by
      rw [← Real.rpow_add (by norm_num : (0 : Real) < 3)]
      congr 1
      ring
    rw [hsplit] at hscaled
    exact le_of_mul_le_mul_left (by simpa only [mul_comm] using hscaled) hshift
  have hDexp : Cd <= (3 : Real) ^ (mu * (D : Real) - mu - 1) :=
    (le_max_right _ _).trans hDexp'
  have hDnonneg : 0 <= mu * (D : Real) - mu - 1 := by
    have hCd1 : 1 <= Cdp := le_max_left _ _
    by_contra hneg
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : Real) < 3)
      (lt_of_not_ge hneg)
    exact (not_lt_of_ge (hCd1.trans hDexp')) hlt
  let Cbuf : Real :=
    (2 * (A : Real) + (d : Real) * (A : Real) * Real.log 3) /
      frGaugeConst d + 1
  have hCbuf : 0 < Cbuf := by
    have hlog : 0 <= Real.log 3 := Real.log_nonneg (by norm_num)
    dsimp only [Cbuf]
    positivity
  obtain ⟨B0, hB0⟩ := exists_shift_of_pos (mu := 2 * mu)
    (by linarith only [hmu]) hCbuf
  let B : Nat := max B0 1
  have hB : 1 <= B := le_max_right _ _
  have hB0B : (B0 : Real) <= (B : Real) := by
    exact_mod_cast Nat.le_max_left B0 1
  have hBexp : Cbuf <= (3 : Real) ^ (2 * mu * (B : Real)) :=
    hB0.trans <| Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hB0B (by linarith only [hmu]))
  refine ⟨T, A, D, B, hT1, hTthr, hA, hburnNonneg, ?_, hD,
    hDnonneg, ?_, hB, ?_⟩
  · simpa only [Cburn] using hburnExp
  · simpa only [Cd] using hDexp
  · simpa only [Cbuf] using hBexp

end

end Quenched
end HighContrast
end HCPolySupport
