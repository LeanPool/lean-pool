/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/TwoPointLSI.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.FiniteEntropyTensorization
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Two point LSI

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `uniformFiniteLSI_bool`.
-/

@[expose] public section

namespace GinibrePoincare
noncomputable section

private def logRatioDeficit (t : ℝ) : ℝ :=
  1 / t - 1 - Real.log (1 + t ^ 2) + Real.log 2 + 2 * Real.log t

private theorem logRatioDeficit_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt logRatioDeficit (-((t - 1) ^ 2) / (t ^ 2 * (1 + t ^ 2))) t := by
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have h := (((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht.ne').sub_const 1).sub
    (((hasDerivAt_id t).pow 2).const_add 1 |>.log hpos.ne')
  have hh := (h.add_const (Real.log 2)).add ((Real.hasDerivAt_log ht.ne').const_mul 2)
  convert! hh using 1
  simp only [id_eq, Pi.pow_apply, Nat.reduceSub, pow_one, mul_one, zero_mul, zero_sub]
  field_simp [ht.ne', hpos.ne']
  ring

/-- A logarithmic inequality giving the sharp two-point constant. -/
theorem log_two_point_ratio_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.log (1 + t ^ 2) - Real.log 2 - 2 * Real.log t ≤ 1 / t - 1 := by
  have hc : ContinuousOn logRatioDeficit (Set.Icc t 1) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ht hx.1
    exact (logRatioDeficit_deriv hxpos).continuousAt.continuousWithinAt
  have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t 1) hc
    (fun x hx => (logRatioDeficit_deriv (lt_of_lt_of_le ht
      (Set.mem_Icc.mp (interior_subset hx)).1)).hasDerivWithinAt)
    (fun x hx => div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      (by positivity))
  have he := hm (by exact ⟨le_rfl, ht1⟩) (by exact ⟨ht1, le_rfl⟩) ht1
  norm_num [logRatioDeficit, one_div] at he
  rw [one_div]
  linarith

private def twoPointDeficit (t : ℝ) : ℝ :=
  (1 - t) ^ 2 - entropyPhi (t ^ 2) + entropyPhi (1 + t ^ 2) -
    (1 + t ^ 2) * Real.log 2

private theorem twoPointDeficit_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt twoPointDeficit
      (2 * (t - 1) + 2 * t * (Real.log (1 + t ^ 2) - Real.log 2 - 2 * Real.log t)) t := by
  have hs := (hasDerivAt_id t).pow 2
  have hp : 0 < 1 + t ^ 2 := by positivity
  have hsq : t ^ 2 ≠ 0 := pow_ne_zero _ ht.ne'
  have h := (((hasDerivAt_id t).const_sub 1).pow 2).sub
    (hs.mul (hs.log hsq))
  have hh := (h.add ((hs.const_add 1).mul ((hs.const_add 1).log hp.ne'))).sub
    ((hs.const_add 1).mul_const (Real.log 2))
  convert! hh using 1
  simp only [id_eq, Pi.pow_apply, Nat.reduceSub, pow_one, mul_one, Real.log_pow]
  field_simp [ht.ne', hp.ne']
  ring

/-- The sharp two-point entropy inequality in normalized scalar form. -/
theorem two_point_deficit_nonneg {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (1 - t) ^ 2 - entropyPhi (t ^ 2) + entropyPhi (1 + t ^ 2) -
      (1 + t ^ 2) * Real.log 2 := by
  by_cases hz : t = 0
  · subst t
    simp only [sub_zero, one_pow, zero_pow (by decide : 2 ≠ 0), add_zero,
      entropyPhi, Real.log_zero, Real.log_one, mul_zero, sub_zero, one_mul]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
  have hc : ContinuousOn twoPointDeficit (Set.Icc t 1) := by
    intro x hx
    exact (twoPointDeficit_deriv (lt_of_lt_of_le htpos hx.1)).continuousAt.continuousWithinAt
  have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t 1) hc
    (fun x hx => (twoPointDeficit_deriv (lt_of_lt_of_le htpos
      (Set.mem_Icc.mp (interior_subset hx)).1)).hasDerivWithinAt)
    (fun x hx => by
      have hxmem := Set.mem_Icc.mp (interior_subset hx)
      have hxpos := lt_of_lt_of_le htpos hxmem.1
      have hl := mul_le_mul_of_nonneg_left (log_two_point_ratio_le hxpos hxmem.2)
        (by positivity : 0 ≤ 2 * x)
      have he : 2 * x * (1 / x - 1) = 2 * (1 - x) := by
        field_simp
      rw [he] at hl
      linarith)
  have he := hm (by exact ⟨le_rfl, ht1⟩) (by exact ⟨ht1, le_rfl⟩) ht1
  norm_num [twoPointDeficit, entropyPhi] at he
  norm_num only [entropyPhi, Real.log_pow, Nat.cast_ofNat]
  linarith

/-- Square entropy for the fair two-point law. -/
def twoPointSquareEntropy (a b : ℝ) : ℝ :=
  (entropyPhi (a ^ 2) + entropyPhi (b ^ 2) - entropyPhi (a ^ 2 + b ^ 2) +
    (a ^ 2 + b ^ 2) * Real.log 2) / 2

private theorem entropyPhi_mul (c u : ℝ) (hc : c ≠ 0) :
    entropyPhi (c * u) = c * entropyPhi u + c * u * Real.log c := by
  by_cases hu : u = 0
  · simp [hu, entropyPhi]
  · simp only [entropyPhi, Real.log_mul hc hu]
    ring

private theorem two_point_lsi_ordered {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    twoPointSquareEntropy a b ≤ (a - b) ^ 2 / 2 := by
  have ha : 0 ≤ a := hb.trans hba
  by_cases hz : a = 0
  · have hbz : b = 0 := by linarith
    simp [hz, hbz, twoPointSquareEntropy, entropyPhi]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
  let t := b / a
  have ht : 0 ≤ t := div_nonneg hb ha
  have ht1 : t ≤ 1 := (div_le_one hap).mpr hba
  have hd := two_point_deficit_nonneg ht ht1
  have hac : a ^ 2 ≠ 0 := pow_ne_zero _ hz
  have hb2 : b ^ 2 = a ^ 2 * t ^ 2 := by dsimp [t]; field_simp
  have hab : a ^ 2 + b ^ 2 = a ^ 2 * (1 + t ^ 2) := by rw [hb2]; ring
  have had : (a - b) ^ 2 = a ^ 2 * (1 - t) ^ 2 := by dsimp [t]; field_simp
  unfold twoPointSquareEntropy
  rw [hab, hb2, had, entropyPhi_mul _ _ hac, entropyPhi_mul _ _ hac]
  have hphi : entropyPhi (a ^ 2) = a ^ 2 * Real.log (a ^ 2) := rfl
  rw [hphi]
  nlinarith [mul_nonneg (sq_nonneg a) hd]

/-- Sharp LSI on the fair two-point space, including arbitrary signed values. -/
theorem two_point_lsi (a b : ℝ) :
    twoPointSquareEntropy a b ≤ (a - b) ^ 2 / 2 := by
  have he : twoPointSquareEntropy a b = twoPointSquareEntropy |a| |b| := by
    simp [twoPointSquareEntropy, sq_abs]
  rw [he]
  have h : twoPointSquareEntropy |a| |b| ≤ (|a| - |b|) ^ 2 / 2 := by
    rcases le_total |b| |a| with hab |hab
    · exact two_point_lsi_ordered (abs_nonneg b) hab
    · have h := two_point_lsi_ordered (abs_nonneg a) hab
      have he : twoPointSquareEntropy |b| |a| = twoPointSquareEntropy |a| |b| := by
        unfold twoPointSquareEntropy
        rw [add_comm (entropyPhi (|b| ^ 2)), add_comm (|b| ^ 2)]
      rw [he] at h
      nlinarith
  refine h.trans ?_
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have hab : a * b ≤ |a| * |b| := (le_abs_self (a * b)).trans_eq (abs_mul a b)
  nlinarith [sq_abs a, sq_abs b]

/-- The scalar two-point formula is the uniform-law entropy used by tensorization. -/
theorem uniformFiniteEntropy_bool (f : Bool → ℝ) :
    uniformFiniteEntropy (fun x => (f x) ^ 2) =
      twoPointSquareEntropy (f true) (f false) := by
  simp [uniformFiniteEntropy, twoPointSquareEntropy]

/-- Sharp two-point LSI in the form needed by product tensorization. -/
theorem uniformFiniteLSI_bool (f : Bool → ℝ) :
    uniformFiniteEntropy (fun x => (f x) ^ 2) ≤ (f true - f false) ^ 2 / 2 := by
  rw [uniformFiniteEntropy_bool]
  exact two_point_lsi _ _

end
end GinibrePoincare
