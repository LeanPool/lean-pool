/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterZeroPositiveTime.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianRadialGenerator
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroOULaw
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUIndependent

/-! Exact positive-time Gaussian center distribution, including initial center
zero. Fixed-time nonvanishing is a measure-theoretic conclusion. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreOUVariance_pos {rate t : ℝ≥0} (hr : 0 < rate) (ht : 0 < t) :
    0 < ginibreOUVariance rate t := by
  have hrR : 0 < (rate : ℝ) := hr
  have htR : 0 < (t : ℝ) := ht
  have hd : ginibreOUDecay rate t < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hdp := ginibreOUDecay_nonneg rate t
  rw [← NNReal.coe_pos, ginibreOUVariance_coe]
  nlinarith

theorem ginibreBrownian_center_planar_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (t : ℝ≥0) :
    HasLaw (fun ω => ((coordinateSum (ginibreBrownianMaximalProcess n α z B t ω)).re,
      (coordinateSum (ginibreBrownianMaximalProcess n α z B t ω)).im))
      ((ginibreOUTransition (ginibreCenterOURate n α) t (coordinateSum z).re).prod
        (ginibreOUTransition (ginibreCenterOURate n α) t (coordinateSum z).im)) P := by
  let Br := ginibreNormalizedCenterBrownian n 0 B
  let Bi := ginibreNormalizedCenterBrownian n 1 B
  have hBr := ginibreNormalizedCenterBrownian_isBrownian hn 0 B P hB hind
  have hBi := ginibreNormalizedCenterBrownian_isBrownian hn 1 B P hB hind
  have hi := ginibreNormalizedCenterBrownian_real_imag_independent n B P hB hind
  have hl := (ginibreBrownianOU_independent Br Bi P hBr hBi hi
    (ginibreCenterOURate n α) (ginibreCenterOURate n α) t t
    (coordinateSum z).re (coordinateSum z).im).hasLaw_prod
      (ginibreBrownianOU_hasLaw Br P hBr _ t (coordinateSum z).re)
      (ginibreBrownianOU_hasLaw Bi P hBi _ t (coordinateSum z).im)
  apply hl.congr
  filter_upwards [ginibreBrownian_center_real_OU hn α z hz B P hB hind,
    ginibreBrownian_center_imag_OU hn α z hz B P hB hind] with ω hr hi
  exact Prod.ext (hr t) (hi t)

theorem ginibreBrownian_center_positive_time_nonzero
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B t ω) ≠ 0 := by
  have hl := ginibreBrownianOU_hasLaw (ginibreNormalizedCenterBrownian n 0 B) P
    (ginibreNormalizedCenterBrownian_isBrownian hn 0 B P hB hind)
    (ginibreCenterOURate n α) t (coordinateSum z).re
  have hr : 0 < ginibreCenterOURate n α := by
    apply NNReal.coe_pos.mp
    rw [ginibreCenterOURate_coe]
    exact div_pos (mul_pos (by norm_num) hα) (by exact_mod_cast hn)
  have hv := ginibreOUVariance_pos hr ht
  have hne : ginibreOUVariance (ginibreCenterOURate n α) t ≠ 0 := hv.ne'
  have : NullSingletonClass (ginibreOUTransition (ginibreCenterOURate n α) t (coordinateSum z).re)
      :=
    nullSingletonClass_gaussianReal hne
  have ha : ∀ᵐ x ∂ginibreOUTransition (ginibreCenterOURate n α) t (coordinateSum z).re, x ≠ 0 := by
    exact ae_iff.mpr (by simp)
  have hs := (hl.ae_iff (measurableSet_setOfPred.mp ((measurableSet_singleton (0 : ℝ)).compl))).mpr
      ha
  filter_upwards [hs, ginibreBrownian_center_real_OU hn α z hz B P hB hind] with ω hs he
  intro hzero
  have hz0 : coordinateSum (ginibreBrownianMaximalProcess n α z B t ω)=0 :=
    Complex.normSq_eq_zero.mp hzero
  apply hs
  rw [← he t, hz0]
  rfl

end
end GinibrePoincare
