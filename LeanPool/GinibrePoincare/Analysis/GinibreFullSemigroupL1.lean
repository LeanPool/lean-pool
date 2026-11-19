/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupL1.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupMarkov

/-! # Full diffusion domination and L¹ contractivity -/

@[expose] public section
open MeasureTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Actual Lipschitz composition preserves the complete symmetric real L² space. -/
def ginibreFullSymmetricCompose (n : ℕ) (φ : ℝ → ℝ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hzero : φ 0 = 0) (x : ginibreFullSymmetricValues n) :
    ginibreFullSymmetricValues n := by
  let y := hφ.compLp hzero x.val
  refine ⟨y, ?_⟩
  intro σ
  apply Lp.ext
  have hya := hφ.coeFn_compLp hzero x.val
  have hyp := (ginibre_measurePreserving_permute
      σ).quasiMeasurePreserving.ae_eq_comp hya
  have hxp := ginibreRealPermutationL2_ae σ x.val
  rw [x.property σ] at hxp
  filter_upwards [ginibreRealPermutationL2_ae σ y, hyp, hya, hxp] with z hp hq hy hx
  simp only [Function.comp_apply] at hq
  rw [hp, hq, hy, ← hx]
  rfl

/-- The actual pointwise absolute-value observable, still in symmetric L². -/
def ginibreFullRealAbs (n : ℕ) (x : ginibreFullSymmetricValues n) : ginibreFullSymmetricValues n :=
  ginibreFullSymmetricCompose n (fun r : ℝ => ‖r‖) lipschitzWith_one_norm norm_zero x

theorem ginibreFullRealAbs_ae (n : ℕ) (x : ginibreFullSymmetricValues n) :
    ((ginibreFullRealAbs n x).val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => ‖x.val z‖ := lipschitzWith_one_norm.coeFn_compLp norm_zero x.val

/-- Conservation of the actual real equilibrium integral. -/
theorem ginibreFullRealEvolution_integral (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (x : ginibreFullSymmetricValues n) :
    (∫ z, (ginibreFullRealEvolution n hn t x).val z ∂ginibreMeasure n) =
      ∫ z, x.val z ∂ginibreMeasure n := by
  have hi (y : ginibreFullSymmetricValues n) :
      (∫ z, (ginibreFullSymmetricOfReal n y).val z ∂ginibreMeasure n) =
        (((∫ z, y.val z ∂ginibreMeasure n) : ℝ) : ℂ) := by
    calc
      _ = ∫ z, ((y.val z : ℝ) : ℂ) ∂ginibreMeasure n :=
        integral_congr_ae (ginibreFullComplexOfReal_ae n y.val)
      _ = _ := integral_complex_ofReal
  have h := ginibreFullEvolution_integral n hn t (ginibreFullSymmetricOfReal n x)
  rw [ginibreFullEvolution_ofReal, hi, hi] at h
  exact_mod_cast h

/-- Markov domination by the evolution of the absolute value. -/
theorem ginibreFullRealEvolution_abs_domination (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (x : ginibreFullSymmetricValues n) :
    ∀ᵐ z ∂ginibreMeasure n, ‖(ginibreFullRealEvolution n hn t x).val z‖ ≤
      (ginibreFullRealEvolution n hn t (ginibreFullRealAbs n x)).val z := by
  have ha := ginibreFullRealAbs_ae n x
  have hp := ginibreFullRealEvolution_mono n hn t x (ginibreFullRealAbs n x) (by
    filter_upwards [ha] with z hz
    rw [hz]
    exact le_abs_self _)
  have hm := ginibreFullRealEvolution_mono n hn t (-x) (ginibreFullRealAbs n x) (by
    filter_upwards [ha, Lp.coeFn_neg x.val] with z hz hnz
    change (-x.val) z ≤ _
    rw [hz, hnz]
    exact neg_le_abs _)
  rw [map_neg] at hm
  filter_upwards [hp, hm, Lp.coeFn_neg (ginibreFullRealEvolution n hn t x).val] with z hz hz' he
  change (- (ginibreFullRealEvolution n hn t x).val) z ≤ _ at hz'
  rw [he] at hz'
  simp only [Pi.neg_apply] at hz'
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, hz⟩

/-- Full diffusion contracts the L¹ distance, on its actual entire L² domain. -/
theorem ginibreFullRealEvolution_integral_abs_le (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (x : ginibreFullSymmetricValues n) :
    (∫ z, ‖(ginibreFullRealEvolution n hn t x).val z‖ ∂ginibreMeasure n) ≤
      ∫ z, ‖x.val z‖ ∂ginibreMeasure n := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hT : Integrable (ginibreFullRealEvolution n hn t x).val (ginibreMeasure n) :=
    (Lp.memLp _).integrable (by norm_num)
  have hA : Integrable (ginibreFullRealEvolution n hn t (ginibreFullRealAbs n x)).val
      (ginibreMeasure n) :=
    (Lp.memLp _).integrable (by norm_num)
  calc
    _ ≤ ∫ z, (ginibreFullRealEvolution n hn t (ginibreFullRealAbs n x)).val z ∂ginibreMeasure n :=
      integral_mono_ae hT.norm hA (ginibreFullRealEvolution_abs_domination n hn t x)
    _ = ∫ z, (ginibreFullRealAbs n x).val z ∂ginibreMeasure n :=
      ginibreFullRealEvolution_integral n hn t _
    _ = _ := integral_congr_ae (ginibreFullRealAbs_ae n x)

end
end GinibrePoincare
