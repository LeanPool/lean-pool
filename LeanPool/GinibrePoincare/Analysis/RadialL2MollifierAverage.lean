/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialL2MollifierAverage.lean.
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

public import LeanPool.GinibrePoincare.Analysis.RadialMollifierKernels
public import LeanPool.GinibrePoincare.Analysis.LebesgueL2Mollification

/-! # Strong L² convergence of actual radial kernel averages

The normalized shrinking radial kernels act by Bochner averages of translations
on scalar and vector Lebesgue L² spaces. These actual averages converge strongly.
Identification with their pointwise convolutions is a separate step.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The Bochner integral `∫ y, K y • τ_y u` in Lebesgue `L²` of the translates `τ_y u` of `u`
weighted by the radial mollifier kernel `K = radialMollifierKernel n m`. -/
def radialL2MollifierAverage (n m : ℕ)
    (u : Lp V 2 (volume : Measure (Configuration n))) : Lp V 2 (volume : Measure (Configuration n))
        :=
  ∫ y, radialMollifierKernel n m y • lebesgueL2Translate n y u

omit [CompleteSpace V] in
/-- The actual radial average is a well-defined Bochner integral in L². -/
theorem integrable_radialL2MollifierIntegrand (n m : ℕ)
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    Integrable (fun y => radialMollifierKernel n m y • lebesgueL2Translate n y u) := by
  obtain ⟨hs, hc, _⟩ := radialMollifierKernel_properties n m
  exact (hs.continuous.smul (continuous_lebesgueL2Translate n u)).integrable_of_hasCompactSupport
    hc.smul_right

/-- Continuous linear test pairings commute with the actual L² bump average. -/
theorem radialL2MollifierAverage_pairing (n : ℕ) (m : ℕ)
    (u : Lp V 2 (volume : Measure (Configuration n)))
    (L : Lp V 2 (volume : Measure (Configuration n)) →L[ℝ] ℝ) :
    L (radialL2MollifierAverage n m u) =
      ∫ y, radialMollifierKernel n m y * L (lebesgueL2Translate n y u) := by
  unfold radialL2MollifierAverage
  rw [← L.integral_comp_comm (integrable_radialL2MollifierIntegrand n m u)]
  simp only [map_smul, smul_eq_mul]

/-- The Bochner L² average has the expected translated representative pairing
against every actual scalar L² test. -/
theorem radialL2MollifierAverage_test_pairing (n : ℕ) (m : ℕ)
    (u : Lp ℝ 2 (volume : Measure (Configuration n)))
    (w : Configuration n → ℝ) (hw : MemLp w 2 volume) :
    (∫ x, radialL2MollifierAverage n m u x * w x) =
      ∫ y, radialMollifierKernel n m y * (∫ x, u (x - y) * w x) := by
  let L : Lp ℝ 2 (volume : Measure (Configuration n)) →L[ℝ] ℝ :=
    innerSL ℝ (hw.toLp w)
  have hL (v : Lp ℝ 2 (volume : Measure (Configuration n))) :
      L v = ∫ x, v x * w x := by
    change inner ℝ (hw.toLp w) v = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp] with x hx
    simp [hx, mul_comm]
  rw [← hL]
  rw [radialL2MollifierAverage_pairing]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [hL]
  congr 1
  apply integral_congr_ae
  filter_upwards [lebesgueL2Translate_ae n y u] with x hx
  rw [hx]

/-- A bound on translations over the support bounds the radial averaged error. -/
theorem radialL2MollifierAverage_error_le (n m : ℕ)
    (u : Lp V 2 (volume : Measure (Configuration n))) (ε : ℝ)
    (he : ∀ y ∈ Function.support (radialMollifierKernel n m),
      ‖lebesgueL2Translate n y u - u‖ ≤ ε) :
    ‖radialL2MollifierAverage n m u - u‖ ≤ ε := by
  obtain ⟨_, _, hnonneg, hi, hmass⟩ := radialMollifierKernel_properties n m
  have hconst : Integrable (fun y => radialMollifierKernel n m y • u) := hi.smul_const u
  have hint := integrable_radialL2MollifierIntegrand n m u
  have heq : radialL2MollifierAverage n m u - u =
      ∫ y, radialMollifierKernel n m y • (lebesgueL2Translate n y u - u) := by
    unfold radialL2MollifierAverage
    calc
      _ = (∫ y, radialMollifierKernel n m y • lebesgueL2Translate n y u) -
          ∫ y, radialMollifierKernel n m y • u := by
        rw [integral_smul_const, hmass, one_smul]
      _ = ∫ y, (radialMollifierKernel n m y • lebesgueL2Translate n y u -
          radialMollifierKernel n m y • u) := (integral_sub hint hconst).symm
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun y => (smul_sub _ _ _).symm)
  rw [heq]
  have hb : ‖∫ y, radialMollifierKernel n m y • (lebesgueL2Translate n y u - u)‖ ≤
      ∫ y, radialMollifierKernel n m y * ε := by
    apply norm_integral_le_of_norm_le (hi.mul_const ε)
    exact Eventually.of_forall (fun y => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnonneg y)]
      by_cases hy : radialMollifierKernel n m y = 0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_left (he y hy) (hnonneg y))
  simpa only [integral_mul_const, hmass, one_mul] using hb

/-- Actual normalized radial kernel averages converge strongly in scalar or vector L². -/
theorem radialL2MollifierAverage_tendsto (n : ℕ)
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    Tendsto (fun m => radialL2MollifierAverage n m u) atTop (𝓝 u) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, ht⟩ := Metric.continuousAt_iff.mp
    (continuous_lebesgueL2Translate n u).continuousAt (ε / 2) (half_pos hε)
  have hr : Tendsto (fun m : ℕ => 2 / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    have hi : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
    simpa [div_eq_mul_inv] using hi.const_mul 2
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.mp hr).2 δ hδ)
  refine ⟨M, fun m hm => ?_⟩
  rw [dist_eq_norm]
  apply (radialL2MollifierAverage_error_le n m u (ε / 2) ?_).trans_lt (half_lt_self hε)
  intro y hy
  have hd : dist y 0 < δ := by
    rw [dist_zero_right]
    exact (radialMollifierKernel_support_bound n m y hy).trans_lt (hM m hm)
  simpa only [lebesgueL2Translate_zero, dist_eq_norm] using (ht hd).le

end
end GinibrePoincare
