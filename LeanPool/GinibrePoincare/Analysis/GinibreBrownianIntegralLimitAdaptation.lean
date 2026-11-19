/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralLimitAdaptation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralMartingaleLimit
public import LeanPool.GinibrePoincare.Analysis.BrownianNullAugmentationMeasurableCongr

/-! Genuine L² limits of past-measurable coefficients remain measurable in the completed past. -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem actualL2Limit_nullAugmentation_measurable {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] [P.IsComplete]
    (m : MeasurableSpace Ω) (hm : m ≤ mAmbient) (S : ℕ → Ω → ℝ)
    (hs : ∀ n, MemLp (S n) 2 P)
    (hS : ∀ n, @Measurable Ω ℝ (ginibreNullAugmentation (mAmbient := mAmbient) P m) _ (S n))
    (I : Lp ℝ 2 P) (hlim : Tendsto (fun n => (hs n).toLp (S n)) atTop (𝓝 I)) :
    @Measurable Ω ℝ (ginibreNullAugmentation (mAmbient := mAmbient) P m) _ (fun ω => I ω) := by
  let aug := ginibreNullAugmentation (mAmbient := mAmbient) P m
  have haug : aug ≤ mAmbient := ginibreNullAugmentation_le (mAmbient := mAmbient) P m hm
  let A := fun u : Lp ℝ 2 P => (condExpL2 ℝ ℝ haug u : Lp ℝ 2 P)
  have hA : Continuous A := continuous_subtype_val.comp (condExpL2 ℝ ℝ haug).continuous
  have he (n : ℕ) : A ((hs n).toLp (S n)) = (hs n).toLp (S n) := by
    apply Lp.ext
    have hc := (hs n).condExpL2_ae_eq_condExp (𝕜 := ℝ) haug
    have hfix := condExp_of_stronglyMeasurable haug (hS n).stronglyMeasurable ((hs n).integrable (by
        norm_num))
    filter_upwards [hc, (hs n).coeFn_toLp] with ω hω hsω
    simpa only [hfix, hsω] using hω
  have hleft := (hA.tendsto I).comp hlim
  have hright : Tendsto (fun n => A ((hs n).toLp (S n))) atTop (𝓝 I) := by
    simpa only [he] using hlim
  have hid : A I = I := tendsto_nhds_unique hleft hright
  have hc := (Lp.memLp I).condExpL2_ae_eq_condExp (𝕜 := ℝ) haug
  simp only [Lp.toLp_coeFn] at hc
  have hI : (fun ω => I ω) =ᵐ[P] P[(fun ω => I ω) | aug] := by
    change (fun ω => A I ω) =ᵐ[P] _ at hc
    rwa [hid] at hc
  apply ginibreNullAugmentation_measurable_congr (mAmbient := mAmbient) P m _ _ _ hI
  exact stronglyMeasurable_condExp.measurable

end
end GinibrePoincare
