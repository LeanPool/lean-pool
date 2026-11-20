/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryVolterraContraction.lean.
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

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The Bielecki estimate for the actual globally Lipschitz Volterra operator.
This is a finite-horizon integral estimate, not an assumed existence theorem. -/

@[expose] public section

open MeasureTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem bakryEmeryVolterra_weighted_contraction (g : E → E) {K : ℝ≥0}
    (hg : LipschitzWith K g) (L : ℝ) (hL : 0 < L) (t : ℝ) (ht : 0 ≤ t)
    (N X Y : ℝ → E) (C : ℝ) (hC : 0 ≤ C)
    (hXY : ∀ s ∈ Icc 0 t, ‖X s - Y s‖ ≤ C) :
    ‖Real.exp (-L*t) • ∫ s in (0 : ℝ)..t,
      (g (Real.exp (L*s) • X s + N s) - g (Real.exp (L*s) • Y s + N s))‖ ≤
      ((K : ℝ)/L)*C := by
  have hd (s : ℝ) : HasDerivAt (fun r => Real.exp (L*r)/L) (Real.exp (L*s)) s := by
    convert (((hasDerivAt_id s).const_mul L).exp.div_const L) using 1 <;> simp [hL.ne']
  have hi : IntervalIntegrable (fun s => Real.exp (L*s)) volume 0 t :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi
  have hbound := intervalIntegral.norm_integral_le_of_norm_le ht
    (g := fun s => (K : ℝ)*Real.exp (L*s)*C)
    (ae_of_all _ (fun s hs => by
      have hh := hg.norm_sub_le (Real.exp (L*s) • X s + N s)
        (Real.exp (L*s) • Y s + N s)
      rw [add_sub_add_right_eq_sub, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hh
      apply hh.trans
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (hXY s ⟨hs.1.le, hs.2⟩)
        (mul_nonneg K.coe_nonneg (Real.exp_nonneg (L*s)))))
    ((hi.const_mul (K : ℝ)).mul_const C)
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, he] at hbound
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg (-L*t))
  have hcancel : Real.exp (-L*t)*Real.exp (L*t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1; ring_nf
  have hpos := Real.exp_pos (-L*t)
  have hK : 0 ≤ (K : ℝ) := K.coe_nonneg
  simp only [mul_zero, Real.exp_zero] at hmul
  apply hmul.trans
  apply (mul_le_mul_iff_right₀ hL).mp
  field_simp
  have hn : 0 ≤ Real.exp (-L*t)*(K : ℝ)*C := by positivity
  have heq : Real.exp (-(L*t))*(K : ℝ)*(Real.exp (L*t)-1)*C =
      (K : ℝ)*C-Real.exp (-(L*t))*(K : ℝ)*C := by
    calc
      _ = (K : ℝ)*C*(Real.exp (-(L*t))*Real.exp (L*t))-
        Real.exp (-(L*t))*(K : ℝ)*C := by ring
      _ = _ := by rw [show Real.exp (-(L*t))*Real.exp (L*t)=1 by
                    simpa only [neg_mul] using hcancel]; ring
  rw [heq]
  simpa only [neg_mul] using sub_le_self ((K : ℝ)*C) hn

end
end GinibrePoincare
