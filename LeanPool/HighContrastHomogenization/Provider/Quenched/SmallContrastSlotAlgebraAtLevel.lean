/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotAlgebra

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSlotAlgebraAtLevel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The summed three-group split at a released threshold pair

The summed split with the bad-event majorant read at a free threshold pair.
The pinned form is this at `(1 / 2, 1)`, definitionally.  As in the unsummed
split the majorant is an opaque summand of both the hypothesis and the base,
so the proof is the pinned one term for term.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The summed three-group split at a released threshold pair.** -/
theorem weakValueSharpMajorant_le_three_group_summed_at_level
    {M L rho : ℝ} {Hw : ℕ} {V : ℕ → ℝ} {V0 : ℝ} {Dr : ℕ → ℝ} {Vmean : ℝ}
    {F : ℕ → ℝ} {n jb : ℕ}
    {vsum cVsum vmsrc cVm bsrc cD delta alpha bmaj beta lev : ℝ}
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    (hM0 : 0 ≤ M) (hrho1 : rho < 1)
    (halpha0 : 0 < alpha) (halphaHalf : alpha ≤ 1 / 2)
    (hrhoAlpha : 1 / 2 - rho / 2 = alpha)
    (hHw : Hw + 1 ≤ n) (hcD0 : 0 ≤ cD) (hdelta0 : 0 ≤ delta)
    (hVsum : (∑ j ∈ Finset.range (Hw + 1),
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0)) ≤
      vsum + cVsum * F jb)
    (hVmean : Vmean ≤ vmsrc + cVm * F jb)
    (hDr0 : ∀ j, 0 ≤ Dr j)
    (hDrdelta : ∀ j ∈ Finset.range (Hw + 1), Dr j ≤ delta)
    (hDr : ∀ j ∈ Finset.range (Hw + 1), Dr j ≤ cD * (F (n - j) - F n))
    (hbad : Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 bmaj beta lev +
        Real.sqrt 2 * (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) *
          Real.sqrt (L + 1) ≤ bsrc) :
    ∃ w : ℝ, 0 ≤ w ∧
      (16 * M * Real.sqrt L *
            ((∑ j ∈ Finset.range (Hw + 1),
                (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j)) +
              ∑ j ∈ Finset.range (Hw + 1),
                (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
                  Real.sqrt (2 * d * Dr j)) +
          16 * M / (2 * ((1 - rho) / 2)) *
            (Real.sqrt 2 * Real.sqrt (L + 1) *
                Response.profileBadMajorantAt 4 bmaj beta lev +
              Real.sqrt 2 * (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) *
                Real.sqrt (L + 1)) +
          Response.constantSeminormCoefficient * (M * Real.sqrt 7 * Vmean) ≤
        weakSourceGroupSummed M L rho vsum vmsrc bsrc +
          weakBaseCoefficientSummed M L cVsum cVm * F jb + w) ∧
      w ^ 2 ≤ weakDropConstant (d := d) M L alpha cD delta *
        iterationDropSum ((3 : ℝ) ^ (-alpha)) F n := by
  classical
  have h3 : (0 : ℝ) < 3 := by norm_num
  set w1 : ℕ → ℝ := fun j => (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) with hw1
  set w2 : ℕ → ℝ := fun j => (3 : ℝ) ^ (-alpha * (j : ℝ)) with hw2
  have hw1nn : ∀ j, 0 ≤ w1 j := fun j => Real.rpow_nonneg (le_of_lt h3) _
  have hw2nn : ∀ j, 0 ≤ w2 j := fun j => Real.rpow_nonneg (le_of_lt h3) _
  set SD1 : ℝ := ∑ j ∈ Finset.range (Hw + 1), w1 j * Dr j with hSD1
  set SD2 : ℝ := ∑ j ∈ Finset.range (Hw + 1), w2 j * Real.sqrt (2 * d * Dr j)
    with hSD2
  have hSD1nn : 0 ≤ SD1 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw1nn j) (hDr0 j)
  have hSD2nn : 0 ≤ SD2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw2nn j) (Real.sqrt_nonneg _)
  have hfac0 : 0 ≤ 16 * M * Real.sqrt L :=
    mul_nonneg (by linarith only [hM0]) (Real.sqrt_nonneg _)
  refine ⟨16 * M * Real.sqrt L * (SD1 + SD2),
    mul_nonneg hfac0 (by linarith only [hSD1nn, hSD2nn]), ?_, ?_⟩
  · -- the base bound
    have hS1 : (∑ j ∈ Finset.range (Hw + 1),
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j)) ≤
        (vsum + cVsum * F jb) + SD1 := by
      have hsplit : ∀ j ∈ Finset.range (Hw + 1),
          w1 j * (V j + V0 + Dr j) = w1 j * (V j + V0) + w1 j * Dr j := by
        intro j _
        ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← hSD1]
      linarith only [hVsum]
    have hS2 : (∑ j ∈ Finset.range (Hw + 1),
        (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
          Real.sqrt (2 * d * Dr j)) = SD2 := by
      rw [hSD2, hw2]
      exact Finset.sum_congr rfl fun j _ => by rw [hrhoAlpha]
    have hcs : (0 : ℝ) ≤ Response.constantSeminormCoefficient := by
      rw [Response.constantSeminormCoefficient_eq]
      have hlt : (3 : ℝ) ^ (-(1 : ℝ) / 2) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
      have : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 2) := by linarith only [hlt]
      positivity
    have hcoefVm : 0 ≤ Response.constantSeminormCoefficient * M * Real.sqrt 7 :=
      mul_nonneg (mul_nonneg hcs hM0) (Real.sqrt_nonneg _)
    have hVm : Response.constantSeminormCoefficient * (M * Real.sqrt 7 * Vmean) ≤
        Response.constantSeminormCoefficient * M * Real.sqrt 7 *
          (vmsrc + cVm * F jb) := by
      have := mul_le_mul_of_nonneg_left hVmean hcoefVm
      linarith only [this]
    have hcoef0 : (0 : ℝ) ≤ 16 * M / (2 * ((1 - rho) / 2)) := by
      have hden : (0 : ℝ) < 2 * ((1 - rho) / 2) := by linarith only [hrho1]
      exact div_nonneg (by linarith only [hM0]) hden.le
    have hbadmul := mul_le_mul_of_nonneg_left hbad hcoef0
    have hfirst : 16 * M * Real.sqrt L *
        ((∑ j ∈ Finset.range (Hw + 1),
            (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j)) +
          ∑ j ∈ Finset.range (Hw + 1),
            (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
              Real.sqrt (2 * d * Dr j)) ≤
        16 * M * Real.sqrt L *
          ((vsum + cVsum * F jb) + SD1 + SD2) := by
      refine mul_le_mul_of_nonneg_left ?_ hfac0
      rw [hS2]
      linarith only [hS1]
    rw [weakSourceGroupSummed, weakBaseCoefficientSummed]
    calc
      _ ≤ 16 * M * Real.sqrt L *
            ((vsum + cVsum * F jb) + SD1 + SD2) +
          16 * M / (2 * ((1 - rho) / 2)) * bsrc +
          Response.constantSeminormCoefficient * M * Real.sqrt 7 *
            (vmsrc + cVm * F jb) :=
        add_le_add (add_le_add hfirst hbadmul) hVm
      _ = _ := by ring
  · -- the drop group, exactly as in the uniform split
    have hsq : (16 * M * Real.sqrt L * (SD1 + SD2)) ^ 2 ≤
        2 * (16 * M * Real.sqrt L) ^ 2 * (SD1 ^ 2 + SD2 ^ 2) := by
      have hp : (SD1 + SD2) ^ 2 ≤ 2 * (SD1 ^ 2 + SD2 ^ 2) := by
        nlinarith only [sq_nonneg (SD1 - SD2)]
      have := mul_le_mul_of_nonneg_left hp (sq_nonneg (16 * M * Real.sqrt L))
      calc
        (16 * M * Real.sqrt L * (SD1 + SD2)) ^ 2 =
            (16 * M * Real.sqrt L) ^ 2 * (SD1 + SD2) ^ 2 := by ring
        _ ≤ (16 * M * Real.sqrt L) ^ 2 *
            (2 * (SD1 ^ 2 + SD2 ^ 2)) := this
        _ = 2 * (16 * M * Real.sqrt L) ^ 2 * (SD1 ^ 2 + SD2 ^ 2) := by ring
    have hlin : SD1 ≤ cD * ((1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ *
        iterationDropSum ((3 : ℝ) ^ (-(1 / 2 : ℝ))) F n) := by
      rw [hSD1, hw1]
      exact weak_drop_sum_le_iteration hFmono (mu := (1 / 2 : ℝ))
        (by norm_num) hHw hcD0 hDr
    have hgeoW : ∑ j ∈ Finset.range (Hw + 1), w1 j ≤ halfGeom := by
      have hrw : ∀ j ∈ Finset.range (Hw + 1),
          w1 j = ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ j := fun j _ =>
        rpow_weight_eq_pow (mu := (1 / 2 : ℝ)) j
      rw [Finset.sum_congr rfl hrw]
      exact geom_sum_le_inv_one_sub
        (le_of_lt (Real.rpow_pos_of_pos h3 _))
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)) _
    have hSD1sq : SD1 ^ 2 ≤ (delta * halfGeom) * SD1 := by
      refine le_trans (sq_sum_le_of_le (Finset.range (Hw + 1)) w1 Dr
        (fun j _ => hw1nn j) (fun j _ => hDr0 j) hDrdelta) ?_
      have := mul_le_mul_of_nonneg_left hgeoW hdelta0
      exact mul_le_mul_of_nonneg_right (by linarith only [this]) hSD1nn
    have hT12 : iterationDropSum ((3 : ℝ) ^ (-(1 / 2 : ℝ))) F n ≤
        iterationDropSum ((3 : ℝ) ^ (-alpha)) F n := by
      refine iterationDropSum_mono_r hFmono
        (le_of_lt (Real.rpow_pos_of_pos h3 _)) ?_ n
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by linarith only [halphaHalf])
    have hSD1T : SD1 ≤ cD * (halfGeom *
        iterationDropSum ((3 : ℝ) ^ (-alpha)) F n) := by
      refine le_trans hlin ?_
      refine mul_le_mul_of_nonneg_left ?_ hcD0
      rw [halfGeom]
      refine mul_le_mul_of_nonneg_left hT12 (le_of_lt (inv_pos.mpr ?_))
      have hlt : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
      linarith only [hlt]
    have hroot : SD2 ^ 2 ≤ (1 - (3 : ℝ) ^ (-alpha))⁻¹ *
        (2 * (d : ℝ) * (cD * ((1 - (3 : ℝ) ^ (-alpha))⁻¹ *
          iterationDropSum ((3 : ℝ) ^ (-alpha)) F n))) := by
      rw [hSD2, hw2]
      exact weak_rooted_drop_sum_sq_le hFmono (nu := alpha) halpha0 hHw
        (by positivity) hcD0 hDr0 hDr
    have hT0 : 0 ≤ iterationDropSum ((3 : ℝ) ^ (-alpha)) F n :=
      iterationDropSum_nonneg hFmono (le_of_lt (Real.rpow_pos_of_pos h3 _)) n
    have hSD1final : SD1 ^ 2 ≤ (delta * halfGeom) *
        (cD * (halfGeom * iterationDropSum ((3 : ℝ) ^ (-alpha)) F n)) := by
      refine le_trans hSD1sq ?_
      refine mul_le_mul_of_nonneg_left hSD1T ?_
      exact mul_nonneg hdelta0 halfGeom_pos.le
    rw [weakDropConstant]
    have hinside : SD1 ^ 2 + SD2 ^ 2 ≤
        (delta * halfGeom * (cD * halfGeom) +
          (1 - (3 : ℝ) ^ (-alpha))⁻¹ *
            (2 * (d : ℝ) * (cD * (1 - (3 : ℝ) ^ (-alpha))⁻¹))) *
          iterationDropSum ((3 : ℝ) ^ (-alpha)) F n := by
      calc
        SD1 ^ 2 + SD2 ^ 2 ≤
            (delta * halfGeom) *
                (cD * (halfGeom * iterationDropSum ((3 : ℝ) ^ (-alpha)) F n)) +
              (1 - (3 : ℝ) ^ (-alpha))⁻¹ *
                (2 * (d : ℝ) * (cD * ((1 - (3 : ℝ) ^ (-alpha))⁻¹ *
                  iterationDropSum ((3 : ℝ) ^ (-alpha)) F n))) :=
          add_le_add hSD1final hroot
        _ = _ := by ring
    have hcoeff0 : 0 ≤ 2 * (16 * M * Real.sqrt L) ^ 2 := by positivity
    calc
      (16 * M * Real.sqrt L * (SD1 + SD2)) ^ 2 ≤
          2 * (16 * M * Real.sqrt L) ^ 2 * (SD1 ^ 2 + SD2 ^ 2) := hsq
      _ ≤ 2 * (16 * M * Real.sqrt L) ^ 2 *
          ((delta * halfGeom * (cD * halfGeom) +
            (1 - (3 : ℝ) ^ (-alpha))⁻¹ *
              (2 * (d : ℝ) * (cD * (1 - (3 : ℝ) ^ (-alpha))⁻¹))) *
            iterationDropSum ((3 : ℝ) ^ (-alpha)) F n) :=
        mul_le_mul_of_nonneg_left hinside hcoeff0
      _ = _ := by ring

end

end HCPolySupport.HighContrast.Quenched
