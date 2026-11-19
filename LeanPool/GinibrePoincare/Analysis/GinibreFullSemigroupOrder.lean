/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupOrder.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupOrderTest
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConstants
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakVariational

/-! # Actual positivity of the full weak Dirichlet resolvent -/

@[expose] public section
open MeasureTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Positivity follows from the actual weak equation at every positive step size. -/
theorem ginibreFullWeak_backward_nonneg (n : ℕ) (hn : 0 < n)
    (c : ℝ) (hc : 0 < c) (f u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hf : ∀ᵐ z ∂ginibreMeasure n, 0 ≤ f z)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g))
    (he : ∀ w : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n w h → IsGinibreSymmetricWeakPair (w, h) →
      inner ℝ u w + (c / (n : ℝ)) * inner ℝ g h = inner ℝ f w) :
    ∀ᵐ z ∂ginibreMeasure n, 0 ≤ u z := by
  obtain ⟨K, hK⟩ := ginibreNegativeTest_lipschitz
  let q := hK.compLp ginibreNegativeTest_zero u
  let r := ginibreFullChainGradient n ginibreNegativeTest ginibreNegativeTest_smooth K hK u g
  have hq := ginibreFullWeakSpace_smoothChain n hn ginibreNegativeTest ginibreNegativeTest_smooth
    ginibreNegativeTest_zero K hK u g hu hs
  have heq := he q r hq.1 hq.2
  have hqa : (q : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => ginibreNegativeTest (u z) := hK.coeFn_compLp ginibreNegativeTest_zero u
  have hra := ginibreFullChainGradient_ae n ginibreNegativeTest ginibreNegativeTest_smooth K hK u g
  have hvalue : ∀ᵐ z ∂ginibreMeasure n, inner ℝ (u z) (q z) ≤ 0 := by
    filter_upwards [hqa] with z hz
    rw [Real.inner_apply]
    rw [hz]
    exact ginibreNegativeTest_mul_nonpos _
  have huv : inner ℝ u q ≤ 0 := by
    rw [L2.inner_def]
    exact integral_nonpos_of_ae hvalue
  have hgrad : inner ℝ g r ≤ 0 := by
    rw [L2.inner_def]
    apply integral_nonpos_of_ae
    filter_upwards [hra] with z hz
    change inner ℝ (g z) (r z) ≤ 0
    rw [hz, real_inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_nonpos_of_nonpos_of_nonneg (ginibreNegativeTest_deriv_nonpos _) (sq_nonneg _)
  have hsource : 0 ≤ inner ℝ f q := by
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [hf, hqa] with z hz hqz
    simp only [Pi.zero_apply, Real.inner_apply]
    rw [hqz]
    exact mul_nonneg hz (ginibreNegativeTest_nonneg _)
  have henergy : (c / (n : ℝ)) * inner ℝ g r ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hgrad
  have hzero : inner ℝ u q = 0 := by linarith
  have hneg : ∀ᵐ z ∂ginibreMeasure n, 0 ≤ -inner ℝ (u z) (q z) := by
    filter_upwards [hvalue] with z hz
    linarith
  have hint := (L2.integrable_inner (𝕜 := ℝ) u q).neg
  have hiz : (∫ z, -inner ℝ (u z) (q z) ∂ginibreMeasure n) = 0 := by
    rw [integral_neg, ← L2.inner_def, hzero, neg_zero]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hneg hint).mp hiz
  change ∀ᵐ z ∂ginibreMeasure n, 0 ≤ u z
  filter_upwards [hae, hqa] with z hz hqz
  by_contra hu
  have hupos : u z < 0 := lt_of_not_ge hu
  simp only [Pi.zero_apply, Real.inner_apply] at hz
  rw [hqz] at hz
  have hprod := neg_eq_zero.mp hz
  exact (mul_ne_zero hupos.ne (ginibreNegativeTest_pos hupos).ne') hprod

/-- The concrete full weak resolvent preserves pointwise nonnegativity. -/
theorem ginibreFullValueResolvent_nonneg (n : ℕ) (hn : 0 < n)
    (f : GinibreFullValueL2 n) (hf : ∀ᵐ z ∂ginibreMeasure n, 0 ≤ f z) :
    ∀ᵐ z ∂ginibreMeasure n, 0 ≤ ginibreFullValueResolvent n hn f z := by
  let p := ginibreFullFormResolvent n hn f
  have hp := ginibreFullFormSpace_weak n hn p
  refine ginibreFullWeak_backward_nonneg n hn 1 one_pos f (ginibreFullFormValue n hn p)
    (ginibreFullFormGradient n hn p) hf hp.1 hp.2 fun w h hw hs => ?_
  have heq := ginibreFullFormResolvent_riesz n hn f
    (ginibreFullFormOfWeak n hn (⟨(w, h), ⟨hw, hs⟩⟩ : ginibreFullWeakSpace n hn))
  rw [ginibreFullFormSpace_inner, ginibreFullFormOfWeak_value,
    ginibreFullFormOfWeak_gradient] at heq
  exact heq

/-- Order preservation for actual almost-everywhere representatives. -/
theorem ginibreFullValueResolvent_mono (n : ℕ) (hn : 0 < n)
    (f h : GinibreFullValueL2 n) (hfh : ∀ᵐ z ∂ginibreMeasure n, f z ≤ h z) :
    ∀ᵐ z ∂ginibreMeasure n,
      ginibreFullValueResolvent n hn f z ≤ ginibreFullValueResolvent n hn h z := by
  have hd : ∀ᵐ z ∂ginibreMeasure n, 0 ≤ (h - f) z := by
    filter_upwards [hfh, Lp.coeFn_sub h f] with z hz he
    rw [he]
    exact sub_nonneg.mpr hz
  have hr := ginibreFullValueResolvent_nonneg n hn (h - f) hd
  rw [map_sub] at hr
  filter_upwards [hr, Lp.coeFn_sub (ginibreFullValueResolvent n hn h)
    (ginibreFullValueResolvent n hn f)] with z hz he
  rw [he] at hz
  exact sub_nonneg.mp hz

/-- The full resolvent preserves every actual bounded constant interval. -/
theorem ginibreFullValueResolvent_interval (n : ℕ) (hn : 0 < n)
    (f : GinibreFullValueL2 n) (a b : ℝ)
    (hf : ∀ᵐ z ∂ginibreMeasure n, f z ∈ Set.Icc a b) :
    ∀ᵐ z ∂ginibreMeasure n, ginibreFullValueResolvent n hn f z ∈ Set.Icc a b := by
  have hl := ginibreFullValueResolvent_mono n hn (ginibreRealConstantL2 n hn a) f (by
    filter_upwards [hf, ginibreRealConstantL2_ae n hn a] with z hz he
    rw [he]
    exact hz.1)
  have hu := ginibreFullValueResolvent_mono n hn f (ginibreRealConstantL2 n hn b) (by
    filter_upwards [hf, ginibreRealConstantL2_ae n hn b] with z hz he
    rw [he]
    exact hz.2)
  rw [ginibreFullValueResolvent_constant] at hl hu
  filter_upwards [hl, hu, ginibreRealConstantL2_ae n hn a,
    ginibreRealConstantL2_ae n hn b] with z hz hz' ha hb
  rw [ha] at hz
  rw [hb] at hz'
  exact ⟨hz, hz'⟩

end
end GinibrePoincare
