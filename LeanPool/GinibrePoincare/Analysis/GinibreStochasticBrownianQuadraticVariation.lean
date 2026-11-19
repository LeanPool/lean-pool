/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticBrownianQuadraticVariation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianQuadraticSums
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOURiemann

/-! # Actual Brownian quadratic variation along uniform partitions in mean square -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace GinibrePoincare
noncomputable section

/-- The quadratic sum of `B` along the uniform partition of `[0, t]` into `n + 1` steps. -/
def ginibreBrownianUniformQuadraticSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (n : ℕ) : Ω → ℝ :=
  ginibreBrownianQuadraticSum B (n+1) (fun i => ginibreUniformBrownianTime t n i)

theorem ginibreBrownianUniformTime_increment_coe (t : ℝ≥0) (n i : ℕ) :
    ((ginibreUniformBrownianTime t n (i+1)-ginibreUniformBrownianTime t n i : ℝ≥0) : ℝ) =
      (t : ℝ)/((n : ℝ)+1) := by
  rw [NNReal.coe_sub (ginibreUniformBrownianTime_mono t n (Nat.le_succ i)),
    ginibreUniformBrownianTime_coe, ginibreUniformBrownianTime_coe,
    ginibreUniformTime_increment]

theorem ginibreBrownianUniformQuadraticSum_mean {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (n : ℕ) :
    (∫ ω, ginibreBrownianUniformQuadraticSum B t n ω ∂P) = (t : ℝ) := by
  have h := ginibreBrownianQuadraticSum_mean B P hB (n+1)
    (fun i => ginibreUniformBrownianTime t n i)
    ((ginibreUniformBrownianTime_mono t n).comp Fin.val_strictMono.monotone)
  change (∫ ω, ginibreBrownianUniformQuadraticSum B t n ω ∂P) = _ at h
  simp only [Fin.val_succ, Fin.val_castSucc, ginibreBrownianUniformTime_increment_coe,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        at h
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  simpa only [mul_div_cancel₀ _ hn] using h

theorem ginibreBrownianUniformQuadraticSum_variance {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (n : ℕ) :
    variance (ginibreBrownianUniformQuadraticSum B t n) P = 2*(t : ℝ)^2/((n : ℝ)+1) := by
  have h := ginibreBrownianQuadraticSum_variance B P hB (n+1)
    (fun i => ginibreUniformBrownianTime t n i)
    ((ginibreUniformBrownianTime_mono t n).comp Fin.val_strictMono.monotone)
  change variance (ginibreBrownianUniformQuadraticSum B t n) P = _ at h
  simp only [Fin.val_succ, Fin.val_castSucc, ginibreBrownianUniformTime_increment_coe,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        at h
  rw [h]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem ginibreBrownianUniformQuadraticSum_meanSquaredError {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (n : ℕ) :
    (∫ ω, (ginibreBrownianUniformQuadraticSum B t n ω-(t : ℝ))^2 ∂P) =
      2*(t : ℝ)^2/((n : ℝ)+1) := by
  have hm := ginibreBrownianQuadraticSum_memLp_two B P hB (n+1)
    (fun i => ginibreUniformBrownianTime t n i)
    ((ginibreUniformBrownianTime_mono t n).comp Fin.val_strictMono.monotone)
  have h := variance_eq_integral hm.aemeasurable
  change variance (ginibreBrownianUniformQuadraticSum B t n) P =
    (∫ ω, (ginibreBrownianUniformQuadraticSum B t n ω - ∫ x, ginibreBrownianUniformQuadraticSum B t
        n x ∂P)^2 ∂P) at h
  rw [ginibreBrownianUniformQuadraticSum_mean B P hB t n] at h
  exact h.symm.trans (ginibreBrownianUniformQuadraticSum_variance B P hB t n)

theorem ginibreBrownianUniformQuadraticSum_tendsto_meanSquare {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (ginibreBrownianUniformQuadraticSum B t n ω-(t : ℝ))^2 ∂P)
      atTop (nhds 0) := by
  simp_rw [ginibreBrownianUniformQuadraticSum_meanSquaredError B P hB t]
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*(t : ℝ)^2)
  simpa only [mul_zero, mul_one_div] using h

end
end GinibrePoincare
