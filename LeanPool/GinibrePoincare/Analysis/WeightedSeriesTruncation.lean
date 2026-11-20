/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/WeightedSeriesTruncation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteParsevalModes

/-! # Truncation of weighted real series -/


@[expose] public section


open Filter
open scoped BigOperators Topology

namespace GinibrePoincare

open MeasureTheory

theorem tendsto_weighted_partialSums {a : ℕ → ℝ}
    (ha : Summable (fun k : ℕ ↦ (k : ℝ) * a k)) :
    Tendsto (fun N ↦ ∑ k ∈ Finset.range N, (k : ℝ) * a k) atTop
      (𝓝 (∑' k : ℕ, (k : ℝ) * a k)) := by
  simpa only [Finset.sum_filter] using ha.hasSum.tendsto_sum_nat

theorem tendsto_weighted_tails_zero {a : ℕ → ℝ}
    (ha : Summable (fun k : ℕ ↦ (k : ℝ) * a k)) :
    Tendsto
      (fun N ↦ (∑' k : ℕ, (k : ℝ) * a k) -
        ∑ k ∈ Finset.range N, (k : ℝ) * a k)
      atTop (𝓝 0) := by
  convert tendsto_const_nhds.sub (tendsto_weighted_partialSums ha) using 1
  simp

theorem tendsto_summable_tails_zero {a : ℕ → ℝ} (ha : Summable a) :
    Tendsto (fun N ↦ (∑' k, a k) - ∑ k ∈ Finset.range N, a k)
      atTop (𝓝 0) := by
  convert tendsto_const_nhds.sub ha.hasSum.tendsto_sum_nat using 1
  simp

theorem tendsto_gaussianHermiteMode_partialSums {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    Tendsto (fun N ↦ ∑ d ∈ Finset.range N, gaussianHermiteMode hn d g)
      atTop (𝓝 g) := by
  simpa only [Finset.sum_filter] using
    (hasSum_gaussianHermiteMode hn g).tendsto_sum_nat

theorem tendsto_gaussianHermiteMode_weightedEnergy_tails_zero
    {n : ℕ} (hn : 0 < n) (g : Lp ℂ 2 (complexGaussianMeasure n))
    (hs : Summable (fun d : ℕ ↦
      (d : ℝ) * ‖gaussianHermiteMode hn d g‖ ^ 2)) :
    Tendsto
      (fun N ↦
        (∑' d : ℕ, (d : ℝ) * ‖gaussianHermiteMode hn d g‖ ^ 2) -
          ∑ d ∈ Finset.range N,
            (d : ℝ) * ‖gaussianHermiteMode hn d g‖ ^ 2)
      atTop (𝓝 0) :=
  tendsto_weighted_tails_zero hs

/-- Gaussian `L²` vectors with summable antiholomorphic-degree weighted
Hermite-mode mass. -/
def HermiteWeightedDomain {n : ℕ} (hn : 0 < n) :
    Set (Lp ℂ 2 (complexGaussianMeasure n)) :=
  {g | Summable (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) *
    positiveHermiteModeMass hn g k)}

/-- Finite truncation of the Hermite antiholomorphic-degree decomposition. -/
noncomputable def gaussianHermiteModePartialSum {n : ℕ} (hn : 0 < n) (N : ℕ)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  ∑ d ∈ Finset.range N, gaussianHermiteMode hn d g

@[simp] theorem gaussianHermiteMode_idempotent {n : ℕ} (hn : 0 < n)
    (d : ℕ) (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianHermiteMode hn d (gaussianHermiteMode hn d g) =
      gaussianHermiteMode hn d g := by
  rw [gaussianHermiteMode_eq_antiDegreeProjection]
  exact (Submodule.starProjection_eq_self_iff).2
    (gaussianHermiteMode_mem_closedSpan hn d g)

theorem gaussianHermiteMode_cross_eq_zero {n : ℕ} (hn : 0 < n)
    {d e : ℕ} (hde : d ≠ e)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianHermiteMode hn d (gaussianHermiteMode hn e g) = 0 := by
  let x := gaussianHermiteMode hn e g
  have he : gaussianHermiteMode hn e x = x :=
    gaussianHermiteMode_idempotent hn e g
  have horth := inner_gaussianHermiteMode_eq_zero hn hde x x
  rw [he] at horth
  have horth' : inner ℂ x (gaussianHermiteMode hn d x) = 0 := by
    rw [← inner_conj_symm, horth, map_zero]
  have hself := inner_gaussianHermiteMode_self_sum hn x d
  rw [horth'] at hself
  change gaussianHermiteMode hn d x = 0
  exact inner_self_eq_zero.mp hself.symm

theorem gaussianHermiteMode_partialSum_eq_zero_of_le {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) {N d : ℕ} (hNd : N ≤ d) :
    gaussianHermiteMode hn d (gaussianHermiteModePartialSum hn N g) = 0 := by
  rw [gaussianHermiteMode_eq_antiDegreeProjection]
  unfold gaussianHermiteModePartialSum
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro e he
  rw [← gaussianHermiteMode_eq_antiDegreeProjection]
  exact gaussianHermiteMode_cross_eq_zero hn (by
    have hed := Finset.mem_range.mp he
    omega) g

theorem gaussianHermiteModePartialSum_mem_weightedDomain {n : ℕ}
    (hn : 0 < n) (N : ℕ) (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianHermiteModePartialSum hn N g ∈ HermiteWeightedDomain hn := by
  unfold HermiteWeightedDomain positiveHermiteModeMass
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range N)).subset
  intro k hk
  by_contra hkrange
  have hNk : N ≤ k := by simpa using hkrange
  have hz : ((k + 1 : ℕ) : ℝ) * ‖gaussianHermiteMode hn (k + 1)
      (gaussianHermiteModePartialSum hn N g)‖ ^ 2 = 0 := by
    rw [gaussianHermiteMode_partialSum_eq_zero_of_le hn g
      (hNk.trans (Nat.le_succ k))]
    simp
  exact hk hz

theorem tendsto_gaussianHermiteModePartialSum {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    Tendsto (fun N ↦ gaussianHermiteModePartialSum hn N g) atTop (𝓝 g) :=
  tendsto_gaussianHermiteMode_partialSums hn g

theorem HermiteWeightedDomain.tendsto_weightedEnergy_tails_zero
    {n : ℕ} {hn : 0 < n} {g : Lp ℂ 2 (complexGaussianMeasure n)}
    (hg : g ∈ HermiteWeightedDomain hn) :
    Tendsto
      (fun N ↦
        (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * positiveHermiteModeMass hn g k) -
          ∑ k ∈ Finset.range N,
            ((k + 1 : ℕ) : ℝ) * positiveHermiteModeMass hn g k)
      atTop (𝓝 0) :=
  tendsto_summable_tails_zero hg

/-- Finite Hermite-mode truncations form an explicit form core: they
converge in Gaussian `L²`, and their omitted weighted energy tends to zero. -/
theorem HermiteWeightedDomain.finiteMode_formCore
    {n : ℕ} {hn : 0 < n} {g : Lp ℂ 2 (complexGaussianMeasure n)}
    (hg : g ∈ HermiteWeightedDomain hn) :
    Tendsto (fun N ↦ gaussianHermiteModePartialSum hn N g) atTop (𝓝 g) ∧
      Tendsto
        (fun N ↦
          (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * positiveHermiteModeMass hn g k) -
            ∑ k ∈ Finset.range N,
              ((k + 1 : ℕ) : ℝ) * positiveHermiteModeMass hn g k)
        atTop (𝓝 0) :=
  ⟨tendsto_gaussianHermiteModePartialSum hn g,
    HermiteWeightedDomain.tendsto_weightedEnergy_tails_zero hg⟩

end GinibrePoincare
