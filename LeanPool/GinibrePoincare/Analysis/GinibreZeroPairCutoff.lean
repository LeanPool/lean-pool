/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreZeroPairCutoff.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibrePairRadius
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairIntegrability

/-! # Actual smooth cutoffs near two simultaneous coordinate zeroes -/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- The cutoff vanishes near two zero coordinates and equals one beyond a
shrinking neighbourhood. Its scale is the actual combined squared radius. -/
def ginibreZeroPairCutoff {n : ℕ} (m : ℕ) (i j : Fin n) (z : Configuration n) : ℝ :=
  1 - sobolevCutoffBump (((m : ℝ) + 1) * ginibrePairRadiusSq i j z)

theorem ginibreZeroPairCutoff_smooth {n : ℕ} (m : ℕ) (i j : Fin n) :
    ContDiff ℝ ∞ (ginibreZeroPairCutoff m i j) :=
  contDiff_const.sub (sobolevCutoffBump.contDiff.comp
    (contDiff_const.mul (contDiff_ginibrePairRadiusSq i j)))

theorem ginibreZeroPairCutoff_mem_unit {n : ℕ} (m : ℕ) (i j : Fin n) (z : Configuration n) :
    0 ≤ ginibreZeroPairCutoff m i j z ∧ ginibreZeroPairCutoff m i j z ≤ 1 := by
  have h0 := sobolevCutoffBump.nonneg (x := ((m : ℝ) + 1) * ginibrePairRadiusSq i j z)
  have h1 := sobolevCutoffBump.le_one (x := ((m : ℝ) + 1) * ginibrePairRadiusSq i j z)
  dsimp [ginibreZeroPairCutoff]
  constructor <;> linarith

/-- The topological support stays a positive distance from the pair zero set. -/
theorem ginibreZeroPairCutoff_support_bound {n : ℕ} (m : ℕ) (i j : Fin n) :
    tsupport (ginibreZeroPairCutoff m i j) ⊆
      {z | 1 / ((m : ℝ) + 1) ≤ ginibrePairRadiusSq i j z} := by
  apply closure_minimal ?_ (isClosed_le continuous_const (contDiff_ginibrePairRadiusSq i
    j).continuous)
  intro z hz
  by_contra hnot
  have hr : ginibrePairRadiusSq i j z < 1 / ((m : ℝ) + 1) := not_le.mp hnot
  have hp : 0 < (m : ℝ) + 1 := by positivity
  have hb : sobolevCutoffBump (((m : ℝ) + 1) * ginibrePairRadiusSq i j z) = 1 := by
    apply sobolevCutoffBump.one_of_mem_closedBall
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, sobolevCutoffBump]
    rw [abs_of_nonneg (mul_nonneg hp.le (ginibrePairRadiusSq_nonneg i j z))]
    exact (by nlinarith [(lt_div_iff₀ hp).mp hr])
  exact hz (by simp [ginibreZeroPairCutoff, hb])

/-- The cutoff's actual gradient is the scalar chain-rule multiple of the pair gradient. -/
theorem ginibreZeroPairCutoff_gradient {n : ℕ} (m : ℕ) (i j : Fin n) (z : Configuration n) :
    ginibreEuclideanGradient (ginibreZeroPairCutoff m i j) z =
      (-(deriv (sobolevCutoffBump : ℝ → ℝ)
        (((m : ℝ) + 1) * ginibrePairRadiusSq i j z) * ((m : ℝ) + 1))) •
        ginibreEuclideanGradient (ginibrePairRadiusSq i j) z := by
  have he := ((sobolevCutoffBump.contDiff (n := ⊤)).differentiable (by simp)
    (((m : ℝ) + 1) * ginibrePairRadiusSq i j z)).hasDerivAt.comp_hasFDerivAt z
      (((contDiff_ginibrePairRadiusSq i j).differentiable (by
        simp)).differentiableAt.hasFDerivAt.const_mul ((m : ℝ) + 1))
  have hc := (hasFDerivAt_const (1 : ℝ) z).sub he
  change HasFDerivAt (ginibreZeroPairCutoff m i j) _ z at hc
  ext k
  rw [ginibreEuclideanGradient_coordinate, hc.fderiv]
  simp [ginibreEuclideanGradient_coordinate]
  ring

theorem ginibreZeroPairCutoff_gradient_norm_sq {n : ℕ} (m : ℕ) (i j : Fin n) (hij : i ≠ j)
    (z : Configuration n) :
    ‖ginibreEuclideanGradient (ginibreZeroPairCutoff m i j) z‖ ^ 2 =
      (deriv (sobolevCutoffBump : ℝ → ℝ)
        (((m : ℝ) + 1) * ginibrePairRadiusSq i j z)) ^ 2 * ((m : ℝ) + 1) ^ 2 *
        (4 * ginibrePairRadiusSq i j z) := by
  rw [ginibreZeroPairCutoff_gradient, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, neg_sq, mul_pow, ginibrePairRadiusSq_gradient_norm_sq i j hij]

/-- An actual scale-independent inverse-radius bound for the cutoff energy. -/
theorem ginibreZeroPairCutoff_gradient_inverse_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n m (i j : Fin n), i ≠ j → ∀ z : Configuration n,
      ‖ginibreEuclideanGradient (ginibreZeroPairCutoff m i j) z‖ ^ 2 ≤
        C * (ginibrePairRadiusSq i j z)⁻¹ := by
  obtain ⟨M, hM0, hM⟩ := sobolevCutoff_deriv_bound
  have hd (x : ℝ) : |deriv (sobolevCutoffBump : ℝ → ℝ) x| ≤ M := by
    simpa [sobolevCutoff_deriv] using hM 0 x
  refine ⟨16 * M ^ 2, by positivity, ?_⟩
  intro n m i j hij z
  rw [ginibreZeroPairCutoff_gradient_norm_sq m i j hij]
  let r := ginibrePairRadiusSq i j z
  let p : ℝ := (m : ℝ) + 1
  have hr0 : 0 ≤ r := ginibrePairRadiusSq_nonneg i j z
  have hp : 0 < p := by dsimp [p]; positivity
  by_cases hr : r = 0
  · simp [r, hr]
  · have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    by_cases hs : p * r ∈ tsupport (sobolevCutoffBump : ℝ → ℝ)
    · have hpr : p * r ≤ 2 := by
        rw [sobolevCutoffBump.tsupport_eq] at hs
        have ha : |p * r| ≤ 2 := by
          simpa [Metric.mem_closedBall, Real.dist_eq, sobolevCutoffBump] using hs
        exact (le_abs_self _).trans ha
      have hdb : (deriv (sobolevCutoffBump : ℝ → ℝ) (p * r)) ^ 2 ≤ M ^ 2 := by
        have hb := hd (p * r)
        nlinarith [sq_abs (deriv (sobolevCutoffBump : ℝ → ℝ) (p * r)), abs_nonneg
          (deriv (sobolevCutoffBump : ℝ → ℝ) (p * r))]
      change (deriv (sobolevCutoffBump : ℝ → ℝ) (p * r)) ^ 2 * p ^ 2 * (4 * r) ≤
        16 * M ^ 2 * r⁻¹
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ hrp).mpr
      calc
        _ = 4 * (deriv (sobolevCutoffBump : ℝ → ℝ) (p * r)) ^ 2 * (p * r) ^ 2 := by ring
        _ ≤ 4 * M ^ 2 * 4 := by
          gcongr
          nlinarith [mul_nonneg hp.le hr0]
        _ = _ := by ring
    · have hz := deriv_of_notMem_tsupport hs
      change (deriv (sobolevCutoffBump : ℝ → ℝ) (p * r)) ^ 2 * p ^ 2 * (4 * r) ≤ _
      rw [hz]
      simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul]
      positivity

/-- At any point outside the pair zero set, the cutoff and its actual gradient
are eventually exactly one and zero, respectively. -/
theorem ginibreZeroPairCutoff_eventually_one_gradient_zero {n : ℕ} (i j : Fin n)
    (z : Configuration n) (hr : 0 < ginibrePairRadiusSq i j z) :
    ∀ᶠ m : ℕ in atTop, ginibreZeroPairCutoff m i j z = 1 ∧
      ginibreEuclideanGradient (ginibreZeroPairCutoff m i j) z = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ginibrePairRadiusSq i j z)
  filter_upwards [eventually_ge_atTop N] with m hm
  have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < (m : ℝ) + 1 := by positivity
  have hs : 2 < ((m : ℝ) + 1) * ginibrePairRadiusSq i j z := by
    have he := (div_lt_iff₀ hr).mp hN
    nlinarith
  have hb : sobolevCutoffBump (((m : ℝ) + 1) * ginibrePairRadiusSq i j z) = 0 := by
    apply sobolevCutoffBump.zero_of_le_dist
    simp only [sobolevCutoffBump, Real.dist_eq, sub_zero]
    rw [abs_of_pos (mul_pos hp hr)]
    exact hs.le
  have hn : ((m : ℝ) + 1) * ginibrePairRadiusSq i j z ∉
      tsupport (sobolevCutoffBump : ℝ → ℝ) := by
    rw [sobolevCutoffBump.tsupport_eq]
    simp only [Metric.mem_closedBall, Real.dist_eq, sobolevCutoffBump, sub_zero]
    rw [abs_of_pos (mul_pos hp hr)]
    exact not_le.mpr hs
  refine ⟨by simp [ginibreZeroPairCutoff, hb], ?_⟩
  rw [ginibreZeroPairCutoff_gradient, deriv_of_notMem_tsupport hn]
  simp

end
end GinibrePoincare
