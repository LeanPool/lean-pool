/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeRenormalizedScale

/-!
# High-contrast homogenization: Provider.Quenched.RenormalizedRadiusFamilyVarying

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Generation-dependent renormalized-radius tails

For a growing window the union-bound cardinality is absorbed jointly by the
window's renormalization base and the fixed tail buffer.  This retains the
base factor that the fixed-window interface may harmlessly discard.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem buffer_absorb_with_renormBase
    {mu Cnt B : ℝ} (hmu : 0 < mu) (hCnt : 0 < Cnt) (hB : 1 ≤ B)
    {b q : ℕ}
    (hbuf : Real.log Cnt ≤ frGaugeConst d *
      (B ^ 2 * (3 : ℝ) ^ (2 * mu * (b : ℝ)) - 1)) :
    Cnt * Real.exp (-(frGaugeConst d * B ^ 2 *
        (3 : ℝ) ^ (2 * mu * ((q : ℝ) + (b : ℝ))))) ≤
      Real.exp (-(frGaugeConst d * (3 : ℝ) ^ (2 * mu * (q : ℝ)))) := by
  have hmu2 : 0 < 2 * mu := by linarith only [hmu]
  have hcfr : 0 < frGaugeConst d := frGaugeConst_pos d
  let Q : ℝ := (3 : ℝ) ^ (2 * mu * (q : ℝ))
  let Bb : ℝ := (3 : ℝ) ^ (2 * mu * (b : ℝ))
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    exact Real.one_le_rpow (by norm_num) (mul_nonneg hmu2.le (Nat.cast_nonneg q))
  have hBb : 1 ≤ Bb := by
    dsimp only [Bb]
    exact Real.one_le_rpow (by norm_num) (mul_nonneg hmu2.le (Nat.cast_nonneg b))
  have hBsq : 1 ≤ B ^ 2 := by nlinarith only [hB]
  have hgain : 0 ≤ frGaugeConst d * (B ^ 2 * Bb - 1) := by
    exact mul_nonneg hcfr.le (by nlinarith only [hBsq, hBb])
  have hlog : Real.log Cnt ≤
      Q * (frGaugeConst d * (B ^ 2 * Bb - 1)) :=
    hbuf.trans (by
      calc
        frGaugeConst d * (B ^ 2 * Bb - 1) =
            1 * (frGaugeConst d * (B ^ 2 * Bb - 1)) := by ring
        _ ≤ Q * (frGaugeConst d * (B ^ 2 * Bb - 1)) :=
          mul_le_mul_of_nonneg_right hQ hgain)
  have hsplit : (3 : ℝ) ^ (2 * mu * ((q : ℝ) + (b : ℝ))) = Q * Bb := by
    dsimp only [Q, Bb]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hexp : Real.log Cnt - frGaugeConst d * B ^ 2 * (Q * Bb) ≤
      -(frGaugeConst d * Q) := by
    nlinarith only [hlog]
  have hrw : Cnt * Real.exp (-(frGaugeConst d * B ^ 2 * (Q * Bb))) =
      Real.exp (Real.log Cnt - frGaugeConst d * B ^ 2 * (Q * Bb)) := by
    rw [Real.exp_sub, Real.exp_log hCnt]
    rw [div_eq_mul_inv, ← Real.exp_neg]
  rw [hsplit, hrw]
  exact Real.exp_le_exp.2 hexp

/-- The shifted tail of a single member of a generation-dependent
renormalized-radius family. -/
theorem measureReal_renormRadius_gt_le_varying
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P]
    {S : CoeffSpace d → ℝ} {Ahat : BlockMat d}
    {gamma nu mu rho delta Gain : ℝ} {n l0 h b : ℕ}
    (hAhat : Book.Ch02.BlockPosDef Ahat) (hGain : 0 < Gain)
    (hdelta : 0 ≤ delta) (hmu : mu = nu - gamma) (hmupos : 0 < mu)
    (hgn : gamma ≤ nu) (hrg : gamma ≤ rho)
    (hl0 : 1 ≤ renormBase gamma nu mu delta Gain l0 h)
    (hthr : Real.log 2 ≤ frGaugeConst d *
      renormBase gamma nu mu delta Gain l0 h ^ 2 *
        ((3 : ℝ) ^ (2 * mu) - 1))
    (hcell : HasCellRenormalization P S Ahat gamma nu Gain n l0 h)
    (hb1 : 1 ≤ b) (hh1 : 1 ≤ h)
    (hbuf : Real.log (2 * renormCellCount d h) ≤ frGaugeConst d *
      (renormBase gamma nu mu delta Gain l0 h ^ 2 *
        (3 : ℝ) ^ (2 * mu * (b : ℝ)) - 1)) (q : ℕ) :
    P.real {a : CoeffSpace d |
        (3 : ℝ) ^ (n + q + b) < renormRadius S Ahat delta rho h n a} ≤
      Real.exp (-(frGaugeConst d * (3 : ℝ) ^ (2 * mu * (q : ℝ)))) := by
  set N : ℤ := ((n + q + b : ℕ) : ℤ) - 1 with hNdef
  have hnN : (n : ℤ) ≤ N := by omega
  have hpowsplit : (3 : ℝ) ^ (n + q + b) = 3 * (3 : ℝ) ^ N := by
    rw [hNdef, ← zpow_natCast (3 : ℝ) (n + q + b),
      show ((n + q + b : ℕ) : ℤ) = 1 + (((n + q + b : ℕ) : ℤ) - 1) by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring_nf
  have hNone : (1 : ℝ) ≤ (3 : ℝ) ^ N := by
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℤ) := by norm_num
      _ ≤ (3 : ℝ) ^ N := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hsub : {a : CoeffSpace d |
      (3 : ℝ) ^ (n + q + b) < renormRadius S Ahat delta rho h n a} ⊆
      {a : CoeffSpace d | ENNReal.ofReal ((3 : ℝ) ^ N) <
        renormScale S Ahat delta rho h n a} := by
    intro a ha
    simp only [Set.mem_ofPred_eq, renormRadius, hpowsplit] at ha
    have hmax : (3 : ℝ) ^ N <
        max 1 (renormScale S Ahat delta rho h n a).toReal := by
      linarith only [ha]
    have htoReal : (3 : ℝ) ^ N <
        (renormScale S Ahat delta rho h n a).toReal := by
      rcases max_cases 1 (renormScale S Ahat delta rho h n a).toReal with
        ⟨heq, -⟩ | ⟨heq, -⟩
      · rw [heq] at hmax
        linarith only [hmax, hNone]
      · rwa [heq] at hmax
    simp only [Set.mem_ofPred_eq]
    by_cases htop : renormScale S Ahat delta rho h n a = ⊤
    · rw [htop]
      exact ENNReal.ofReal_lt_top
    · exact (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) htop).2 htoReal
  have htail := measureReal_renormScale_gt_le (rho := rho) hAhat hGain hdelta
    hmu hmupos hgn hrg hl0 hthr hcell hnN
  have hshiftEq : (3 : ℝ) ^ (2 * mu * ((N : ℝ) + 1 - (n : ℝ))) =
      (3 : ℝ) ^ (2 * mu * ((q : ℝ) + (b : ℝ))) := by
    congr 1
    have hcast : (N : ℝ) = (n : ℝ) + (q : ℝ) + (b : ℝ) - 1 := by
      rw [hNdef]
      push_cast
      ring
    rw [hcast]
    ring
  have hcntpos : 0 < (2 : ℝ) * renormCellCount d h := by
    rw [renormCellCount]
    have hh : 0 < (h : ℝ) := by exact_mod_cast hh1
    positivity
  calc
    P.real {a : CoeffSpace d |
        (3 : ℝ) ^ (n + q + b) < renormRadius S Ahat delta rho h n a}
        ≤ P.real {a : CoeffSpace d | ENNReal.ofReal ((3 : ℝ) ^ N) <
          renormScale S Ahat delta rho h n a} := measureReal_mono hsub
    _ ≤ renormCellCount d h * (2 * Real.exp (-(frGaugeConst d *
          renormBase gamma nu mu delta Gain l0 h ^ 2 *
          (3 : ℝ) ^ (2 * mu * ((N : ℝ) + 1 - (n : ℝ)))))) := htail
    _ = 2 * renormCellCount d h * Real.exp (-(frGaugeConst d *
          renormBase gamma nu mu delta Gain l0 h ^ 2 *
          (3 : ℝ) ^ (2 * mu * ((q : ℝ) + (b : ℝ))))) := by
      rw [hshiftEq]
      ring
    _ ≤ Real.exp (-(frGaugeConst d *
          (3 : ℝ) ^ (2 * mu * (q : ℝ)))) :=
      buffer_absorb_with_renormBase hmupos hcntpos hl0 hbuf

end

end HCPolySupport.HighContrast.Quenched
