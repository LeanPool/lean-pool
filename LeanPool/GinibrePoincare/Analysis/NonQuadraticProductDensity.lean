/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticProductDensity.lean.
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

public import Mathlib.MeasureTheory.Integral.Pi

/-! # Finite product densities without an integrability assumption
Tonelli's theorem applies to arbitrary measurable nonnegative weights, before
normalization or finiteness of their masses has been established.
-/

@[expose] public section
open MeasureTheory
open scoped ENNReal BigOperators
namespace GinibrePoincare
noncomputable section

/-- The extended nonnegative integral of a separable finite product factors,
including infinite values. -/
theorem lintegral_fin_prod_eq_prod {n : ℕ} {E : Type*} [MeasurableSpace E]
    {μ : Fin n → Measure E} [∀ i, SigmaFinite (μ i)]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp [Measure.pi_empty_univ]
  | succ n ih =>
    calc
      _ = ∫⁻ x : E × (Fin n → E),
          f 0 x.1 * ∏ i, f (Fin.succ i) (x.2 i)
          ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
        have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
        rw [← hmp.lintegral_comp
          (by exact Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i))]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Fin.zero_succAbove]
        rfl
      _ = (∫⁻ x, f 0 x ∂μ 0) *
          ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂μ i.succ := by
        rw [lintegral_prod_mul (f := f 0) (g := fun x : Fin n → E => ∏ i, f i.succ (x i)) (hf
            0).aemeasurable
          (by exact (Finset.measurable_prod _ fun i _ =>
            (hf i.succ).comp (measurable_pi_apply i)).aemeasurable), ih]
        exact fun i => hf i.succ
      _ = _ := by rw [Fin.prod_univ_succ]

/-- Finite products of finite-valued densities preserve product structure,
with no separate coordinate integrability premise. -/
theorem pi_withDensity_ofReal_eq_unconditional {n : ℕ} {E : Type*} [MeasurableSpace E]
    (μ : Fin n → Measure E) [∀ i, SigmaFinite (μ i)]
    (w : Fin n → E → ℝ) (hw : ∀ i, Measurable (w i))
    (hp : ∀ i x, 0 ≤ w i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (w i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, w i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  simp_rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hp i _)]
  rw [lintegral_fin_prod_eq_prod (fun i x => ENNReal.ofReal (w i x)) (fun i => (hw
      i).ennreal_ofReal)]
  · congr 1
    funext i
    rw [withDensity_apply _ (hs i)]

end
end GinibrePoincare
