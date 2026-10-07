/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Cauchy Schwarz Energy

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory
open CKN


noncomputable section

namespace CIV

/-- The Cauchy-Schwarz inequality for the Bochner integral on `Vec m`, in the square-root form
the comparison energy estimate consumes. -/
theorem integral_abs_mul_abs_le_sqrt_mul_sqrt {m : ℕ} (F c : Vec m → ℝ)
    (hF : MemLp F 2 volume) (hc : MemLp c 2 volume) :
    ∫ x, |F x| * |c x| ≤ Real.sqrt (∫ x, F x ^ 2) * Real.sqrt (∫ x, c x ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; rfl
  have hFabs : MemLp (fun x => |F x|) (ENNReal.ofReal (2 : ℝ)) volume := by
    rw [h2]; exact hF.abs
  have hcabs : MemLp (fun x => |c x|) (ENNReal.ofReal (2 : ℝ)) volume := by
    rw [h2]; exact hc.abs
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure (Vec m))) hpq
    (f := fun x => |F x|) (g := fun x => |c x|)
    (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (Filter.Eventually.of_forall fun x => abs_nonneg _) hFabs hcabs
  have hrw : ∀ g : Vec m → ℝ, (∫ x, |g x| ^ (2 : ℝ)) = ∫ x, g x ^ 2 := by
    intro g
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change |g x| ^ (2 : ℝ) = g x ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [hrw F, hrw c] at key
  rwa [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at key

/-- The pointwise bound feeding the Cauchy-Schwarz step: a factor in `[0, 1]` and a cutoff in
`[0, 1]` can both be discarded, at the cost of absolute values. -/
theorem two_mul_mul_le_two_mul_abs_mul_abs {m : ℕ} (Phi c chi dfac : Vec m → ℝ) (x : Vec m)
    (hd0 : 0 ≤ dfac x) (hd1 : dfac x ≤ 1) (hchi0 : 0 ≤ chi x) (hchi1 : chi x ≤ 1) :
    2 * Phi x * dfac x * c x * chi x ^ 2 ≤ 2 * |Phi x * chi x| * |c x| := by
  have hPhi : Phi x ≤ |Phi x| := le_abs_self _
  have hPhi' : -|Phi x| ≤ Phi x := neg_abs_le _
  have hc : c x ≤ |c x| := le_abs_self _
  have hc' : -|c x| ≤ c x := neg_abs_le _
  have habsP : 0 ≤ |Phi x| := abs_nonneg _
  have habsc : 0 ≤ |c x| := abs_nonneg _
  have hprod : |Phi x * chi x| = |Phi x| * chi x := by
    rw [abs_mul, abs_of_nonneg hchi0]
  have hsq : chi x ^ 2 ≤ chi x := by nlinarith only [hchi0, hchi1]
  have h1d : (0 : ℝ) ≤ 1 - dfac x := by linarith only [hd1]
  have hmul : Phi x * c x ≤ |Phi x| * |c x| := by
    nlinarith only [hPhi, hPhi', hc, hc', habsP, habsc]
  have hgap : (0 : ℝ) ≤ |Phi x| * |c x| - Phi x * c x := by linarith only [hmul]
  have habs : 2 * Phi x * dfac x * c x * chi x ^ 2
      ≤ 2 * |Phi x| * dfac x * |c x| * chi x ^ 2 := by
    nlinarith only [mul_nonneg (mul_nonneg hd0 (sq_nonneg (chi x))) hgap]
  have hstep2 : 2 * |Phi x| * dfac x * |c x| * chi x ^ 2
      ≤ 2 * |Phi x| * |c x| * chi x ^ 2 := by
    nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg habsP habsc) (sq_nonneg (chi x))) h1d]
  have hstep3 : 2 * |Phi x| * |c x| * chi x ^ 2 ≤ 2 * (|Phi x| * chi x) * |c x| := by
    nlinarith only [mul_nonneg (mul_nonneg habsP habsc) (sub_nonneg.mpr hsq)]
  rw [hprod]
  linarith only [habs, hstep2, hstep3]

end CIV
