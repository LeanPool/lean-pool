/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/EntropyLimitStability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEntropy
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Entropy Limit Stability
-/


@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- A nonnegative shift of the logarithmic square moment, suitable for Fatou. -/
def shiftedSquareLog (x : ℝ) : ℝ := x ^ 2 * Real.log (x ^ 2) + 1

theorem shiftedSquareLog_nonneg (x : ℝ) : 0 ≤ shiftedSquareLog x := by
  have h := Real.negMulLog_le_one_sub_self (sq_nonneg x)
  rw [Real.negMulLog_eq_neg] at h
  unfold shiftedSquareLog
  nlinarith [sq_nonneg x]

theorem continuous_shiftedSquareLog : Continuous shiftedSquareLog := by
  exact (continuous_square_mul_log continuous_id).add continuous_const

/-- Entropy bounds survive almost-everywhere convergence, convergence of square
moments and convergence of energy. Fatou also proves finiteness of the limiting
logarithmic moment, so no integrability certificate for that moment is assumed. -/
theorem squareEntropy_le_of_ae_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ℕ → α → ℝ) (g : α → ℝ) (E : ℕ → ℝ) (e : ℝ)
    (hf : ∀ m, AEStronglyMeasurable (f m) μ)
    (hg : AEStronglyMeasurable g μ)
    (hlog : ∀ m, Integrable (fun x => f m x ^ 2 * Real.log (f m x ^ 2)) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun m => f m x) atTop (𝓝 (g x)))
    (hmass : Tendsto (fun m => ∫ x, f m x ^ 2 ∂μ) atTop (𝓝 (∫ x, g x ^ 2 ∂μ)))
    (hE : Tendsto E atTop (𝓝 e))
    (hineq : ∀ m, squareEntropy μ (f m) ≤ E m) :
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) μ ∧ squareEntropy μ g ≤ e := by
  let L : ℝ := e + (∫ x, g x ^ 2 ∂μ) * Real.log (∫ x, g x ^ 2 ∂μ) + 1
  let B : ℕ → ℝ := fun m => E m +
    (∫ x, f m x ^ 2 ∂μ) * Real.log (∫ x, f m x ^ 2 ∂μ) + 1
  have hB : Tendsto B atTop (𝓝 L) := by
    exact (hE.add (Real.continuous_mul_log.continuousAt.tendsto.comp hmass)).add tendsto_const_nhds
  have hbound : ∀ m, (∫⁻ x, ENNReal.ofReal (shiftedSquareLog (f m x)) ∂μ) ≤ ENNReal.ofReal (B m)
    := by
    intro m
    have hsm : Integrable (fun x => shiftedSquareLog (f m x)) μ := (hlog m).fun_add
      (integrable_const 1)
    rw [← ofReal_integral_eq_lintegral_ofReal hsm
      (ae_of_all _ (fun x => shiftedSquareLog_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    change (∫ x, f m x ^ 2 * Real.log (f m x ^ 2) + 1 ∂μ) ≤ _
    rw [integral_add (hlog m) (integrable_const 1)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hi := hineq m
    unfold squareEntropy at hi
    dsimp [B]
    linarith
  have hfatou : (∫⁻ x, ENNReal.ofReal (shiftedSquareLog (g x)) ∂μ) ≤ ENNReal.ofReal L := by
    calc
      _ = ∫⁻ x, liminf (fun m => ENNReal.ofReal (shiftedSquareLog (f m x))) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact ((ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (continuous_shiftedSquareLog.continuousAt.tendsto.comp hx)).liminf_eq).symm
      _ ≤ liminf (fun m => ∫⁻ x, ENNReal.ofReal (shiftedSquareLog (f m x)) ∂μ) atTop :=
        lintegral_liminf_le' (fun m => ENNReal.measurable_ofReal.aemeasurable.comp_aemeasurable
          (continuous_shiftedSquareLog.measurable.comp_aemeasurable (hf m).aemeasurable))
      _ ≤ liminf (fun m => ENNReal.ofReal (B m)) atTop := liminf_le_liminf (Eventually.of_forall
        hbound)
      _ = _ := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hB).liminf_eq
  have hshift : Integrable (fun x => shiftedSquareLog (g x)) μ := by
    refine ⟨continuous_shiftedSquareLog.comp_aestronglyMeasurable hg, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => shiftedSquareLog_nonneg _))]
    exact hfatou.trans_lt ENNReal.ofReal_lt_top
  have hglog : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) μ := by
    have hi := hshift.sub (integrable_const (1 : ℝ))
    change Integrable (fun x => shiftedSquareLog (g x) - 1) μ at hi
    simpa only [shiftedSquareLog, add_sub_cancel_right] using hi
  refine ⟨hglog, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hshift
    (ae_of_all _ (fun x => shiftedSquareLog_nonneg _))] at hfatou
  have hnonneg : 0 ≤ ∫ x, shiftedSquareLog (g x) ∂μ :=
    integral_nonneg (fun x => shiftedSquareLog_nonneg _)
  have hLn : 0 ≤ L := by
    apply ge_of_tendsto hB
    apply Eventually.of_forall
    intro m
    have hsm : Integrable (fun x => shiftedSquareLog (f m x)) μ := (hlog m).fun_add
      (integrable_const 1)
    have hnon : 0 ≤ ∫ x, shiftedSquareLog (f m x) ∂μ :=
      integral_nonneg (fun x => shiftedSquareLog_nonneg (f m x))
    unfold shiftedSquareLog at hnon
    rw [integral_add (hlog m) (integrable_const 1)] at hnon
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hnon
    have hi := hineq m
    unfold squareEntropy at hi
    dsimp [B]
    linarith
  have hreal : (∫ x, shiftedSquareLog (g x) ∂μ) ≤ L := by
    exact (ENNReal.ofReal_le_ofReal_iff hLn).mp hfatou
  unfold shiftedSquareLog at hreal
  rw [integral_add hglog (integrable_const 1)] at hreal
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hreal
  unfold squareEntropy
  dsimp [L] at hreal
  linarith

end
end GinibrePoincare
