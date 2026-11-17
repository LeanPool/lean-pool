/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreCollisionCutoff.lean.
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

public import LeanPool.GinibrePoincare.Analysis.ComplexSquaredGradient
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Concrete.Generator

/-! # Actual symmetric cutoff near the full collision locus -/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section

theorem contDiff_vandermondeWeight (n : ℕ) :
    ContDiff ℝ ∞ (vandermondeWeight : Configuration n → ℝ) := by
  have hr : ContDiff ℝ ∞ (fun z : Configuration n => (vandermonde z).re) :=
    Complex.reCLM.contDiff.comp (contDiff_vandermonde n)
  have hi : ContDiff ℝ ∞ (fun z : Configuration n => (vandermonde z).im) :=
    Complex.imCLM.contDiff.comp (contDiff_vandermonde n)
  change ContDiff ℝ ∞ (fun z => (vandermonde z).re * (vandermonde z).re +
    (vandermonde z).im * (vandermonde z).im)
  exact (hr.mul hr).add (hi.mul hi)

theorem vandermondeWeight_symmetric (n : ℕ) : IsSymmetric (vandermondeWeight : Configuration n →
  ℝ) := by
  intro σ z
  unfold vandermondeWeight
  rw [vandermonde_permute, map_mul]
  have hs : Complex.normSq (permutationSign σ) = 1 := by
    unfold permutationSign
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, one_mul]

def ginibreCollisionCutoff (n m : ℕ) (z : Configuration n) : ℝ :=
  1 - sobolevCutoffBump (((m : ℝ) + 1) * vandermondeWeight z)

theorem ginibreCollisionCutoff_smooth (n m : ℕ) : ContDiff ℝ ∞ (ginibreCollisionCutoff n m) :=
  contDiff_const.sub (sobolevCutoffBump.contDiff.comp
    (contDiff_const.mul (contDiff_vandermondeWeight n)))

theorem ginibreCollisionCutoff_symmetric (n m : ℕ) : IsSymmetric (ginibreCollisionCutoff n m) := by
  intro σ z
  simp only [ginibreCollisionCutoff, vandermondeWeight_symmetric n σ z]

theorem ginibreCollisionCutoff_mem_unit (n m : ℕ) (z : Configuration n) :
    0 ≤ ginibreCollisionCutoff n m z ∧ ginibreCollisionCutoff n m z ≤ 1 := by
  have h0 := sobolevCutoffBump.nonneg (x := ((m : ℝ) + 1) * vandermondeWeight z)
  have h1 := sobolevCutoffBump.le_one (x := ((m : ℝ) + 1) * vandermondeWeight z)
  dsimp [ginibreCollisionCutoff]
  constructor <;> linarith

theorem ginibreCollisionCutoff_support_collisionFree (n m : ℕ) :
    tsupport (ginibreCollisionCutoff n m) ⊆ {z | CollisionFree z} := by
  have hs : tsupport (ginibreCollisionCutoff n m) ⊆
      {z | 1 / ((m : ℝ) + 1) ≤ vandermondeWeight z} := by
    apply closure_minimal ?_ (isClosed_le continuous_const (contDiff_vandermondeWeight
      n).continuous)
    intro z hz
    by_contra hnot
    have hr : vandermondeWeight z < 1 / ((m : ℝ) + 1) := not_le.mp hnot
    have hp : 0 < (m : ℝ) + 1 := by positivity
    have hb : sobolevCutoffBump (((m : ℝ) + 1) * vandermondeWeight z) = 1 := by
      apply sobolevCutoffBump.one_of_mem_closedBall
      simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, sobolevCutoffBump]
      rw [abs_of_nonneg (mul_nonneg hp.le (vandermondeWeight_nonneg z))]
      nlinarith [(lt_div_iff₀ hp).mp hr]
    exact hz (by simp [ginibreCollisionCutoff, hb])
  intro z hz
  apply (vandermonde_ne_zero_iff z).mp
  intro hv
  have hw : vandermondeWeight z = 0 := by simp [vandermondeWeight, hv]
  have hp : 0 < 1 / ((m : ℝ) + 1) := by positivity
  have hh := hs hz
  change 1 / ((m : ℝ) + 1) ≤ vandermondeWeight z at hh
  rw [hw] at hh
  linarith

/-- Multiplying a smooth compact symmetric observable by the collision cutoff
produces an element of the Theorem 1.9 core. -/
theorem ginibreCollisionCutoff_mul_core (n m : ℕ)
    (f : Configuration n → ℝ) (hf : IsSmoothCompactSymmetric f) :
    IsTheoremOneNineCore (fun z => ginibreCollisionCutoff n m z * f z) := by
  refine ⟨(ginibreCollisionCutoff_smooth n m).mul hf.1, hf.2.1.mul_left, ?_, ?_⟩
  · have hs : tsupport (fun z => ginibreCollisionCutoff n m z * f z) ⊆
        {z | CollisionFree z} :=
      (tsupport_mul_subset_left (f := ginibreCollisionCutoff n m) (g := f)).trans
        (ginibreCollisionCutoff_support_collisionFree n m)
    change ∀ z, z ∈ tsupport (fun z => ginibreCollisionCutoff n m z * f z) →
      z ∉ collisionSet n
    intro z hz
    exact (collisionFree_iff_not_mem_collisionSet z).mp (hs hz)
  · intro σ z
    simp only [ginibreCollisionCutoff_symmetric n m σ z, hf.2.2 σ z]

theorem ginibreCollisionCutoff_gradient (n m : ℕ) (z : Configuration n) :
    ginibreEuclideanGradient (ginibreCollisionCutoff n m) z =
      (-(deriv (sobolevCutoffBump : ℝ → ℝ) (((m : ℝ) + 1) * vandermondeWeight z) * ((m : ℝ) + 1))) •
        ginibreEuclideanGradient (vandermondeWeight : Configuration n → ℝ) z := by
  have he := ((sobolevCutoffBump.contDiff (n := ⊤)).differentiable (by simp)
    (((m : ℝ) + 1) * vandermondeWeight z)).hasDerivAt.comp_hasFDerivAt z
      (((contDiff_vandermondeWeight n).differentiable (by
        simp)).differentiableAt.hasFDerivAt.const_mul ((m : ℝ) + 1))
  have hc := (hasFDerivAt_const (1 : ℝ) z).sub he
  change HasFDerivAt (ginibreCollisionCutoff n m) _ z at hc
  ext k
  rw [ginibreEuclideanGradient_coordinate, hc.fderiv]
  simp [ginibreEuclideanGradient_coordinate]
  ring

/-- The actual density factor absorbs the singular cutoff derivative. -/
theorem ginibreCollisionCutoff_weighted_gradient_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ n m (z : Configuration n),
      vandermondeWeight z * ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2 ≤
        C * complexDirectionalEnergy (vandermonde : Configuration n → ℂ) z := by
  obtain ⟨M, hM0, hM⟩ := sobolevCutoff_deriv_bound
  have hd (x : ℝ) : |deriv (sobolevCutoffBump : ℝ → ℝ) x| ≤ M := by
    simpa [sobolevCutoff_deriv] using hM 0 x
  refine ⟨16 * M ^ 2, by positivity,?_⟩
  intro n m z
  let r := vandermondeWeight z
  let p : ℝ := (m : ℝ) + 1
  let d := deriv (sobolevCutoffBump : ℝ → ℝ) (p * r)
  have hr0 : 0 ≤ r := vandermondeWeight_nonneg z
  have hp : 0 < p := by dsimp [p]; positivity
  have hE := ginibreEuclideanGradient_complex_normSq_bound (vandermonde : Configuration n → ℂ)
    (contDiff_vandermonde n) z
  change ‖ginibreEuclideanGradient (vandermondeWeight : Configuration n → ℝ) z‖ ^ 2 ≤
    4 * r * complexDirectionalEnergy vandermonde z at hE
  rw [ginibreCollisionCutoff_gradient, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, neg_sq,
    mul_pow]
  change r * (d ^ 2 * p ^ 2 * ‖ginibreEuclideanGradient (vandermondeWeight : Configuration n → ℝ)
    z‖ ^ 2) ≤ _
  by_cases hs : p * r ∈ tsupport (sobolevCutoffBump : ℝ → ℝ)
  · have hpr : p * r ≤ 2 := by
      rw [sobolevCutoffBump.tsupport_eq] at hs
      have ha : |p * r| ≤ 2 := by
        simpa [Metric.mem_closedBall, Real.dist_eq, sobolevCutoffBump] using hs
      exact (le_abs_self _).trans ha
    have hdb : d ^ 2 ≤ M ^ 2 := by
      have hh := hd (p * r)
      dsimp [d]
      nlinarith [sq_abs (deriv (sobolevCutoffBump : ℝ → ℝ) (p * r)), abs_nonneg (deriv
        (sobolevCutoffBump : ℝ → ℝ) (p * r))]
    calc
      _ ≤ r * (d ^ 2 * p ^ 2 * (4 * r * complexDirectionalEnergy vandermonde z)) := by gcongr
      _ = 4 * d ^ 2 * (p * r) ^ 2 * complexDirectionalEnergy vandermonde z := by ring
      _ ≤ 16 * M ^ 2 * complexDirectionalEnergy vandermonde z := by
        have hprsq : (p * r) ^ 2 ≤ 4 := by nlinarith [mul_nonneg hp.le hr0]
        have hb : 4 * d ^ 2 * (p * r) ^ 2 ≤ 16 * M ^ 2 := by
          nlinarith [mul_le_mul hdb hprsq (sq_nonneg _) (sq_nonneg M)]
        exact mul_le_mul_of_nonneg_right hb (complexDirectionalEnergy_nonneg _ z)
  · have hz : d = 0 := deriv_of_notMem_tsupport hs
    rw [hz]
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul]
    simp only [mul_zero, ge_iff_le]
    exact mul_nonneg (by positivity) (complexDirectionalEnergy_nonneg vandermonde z)

/-- Away from collisions the actual cutoff and gradient are eventually one and zero. -/
theorem ginibreCollisionCutoff_eventually_one_gradient_zero (n : ℕ) (z : Configuration n)
    (hz : CollisionFree z) : ∀ᶠ m in atTop,
    ginibreCollisionCutoff n m z = 1 ∧ ginibreEuclideanGradient (ginibreCollisionCutoff n m) z = 0
      := by
  have hr : 0 < vandermondeWeight z := Complex.normSq_pos.mpr ((vandermonde_ne_zero_iff z).mpr hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / vandermondeWeight z)
  filter_upwards [eventually_ge_atTop N] with m hm
  have hp : 2 < ((m : ℝ) + 1) * vandermondeWeight z := by
    have hnm : (N : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [(div_lt_iff₀ hr).mp hN]
  have hn : ((m : ℝ) + 1) * vandermondeWeight z ∉ tsupport (sobolevCutoffBump : ℝ → ℝ) := by
    rw [sobolevCutoffBump.tsupport_eq]
    simp only [Metric.mem_closedBall, Real.dist_eq, sobolevCutoffBump, sub_zero]
    rw [abs_of_pos (by positivity : 0 < ((m : ℝ) + 1) * vandermondeWeight z)]
    exact not_le.mpr hp
  refine ⟨by simp [ginibreCollisionCutoff, image_eq_zero_of_notMem_tsupport hn],?_⟩
  rw [ginibreCollisionCutoff_gradient, deriv_of_notMem_tsupport hn]
  simp
end
end GinibrePoincare
