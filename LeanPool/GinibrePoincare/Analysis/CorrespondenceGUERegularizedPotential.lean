/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUERegularizedPotential.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEConvexity
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEBarrier
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryConvexGibbsLSI
/-!
# Correspondence GUE regularized potential

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueRegularizedPotential_contDiff`, `gueRegularizedPotential_strongConvexOn`,
`gueLogBarrier_exp_polynomial_bound`.
-/

@[expose] public section
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

/-- The regularized GUE potential
`(n / 2) * ‖x‖ ^ 2 + ∑_{i < j} 2 * gueLogBarrier ε (x j - x i)`. -/
def gueRegularizedPotential (n : ℕ) (ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (n : ℝ)/2*‖x‖^2 + ∑ p ∈ guePairs n, 2*gueLogBarrier ε (x p.2-x p.1)

theorem gueRegularizedPotential_contDiff (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (gueRegularizedPotential n ε) := by
  apply ContDiff.add
  · exact contDiff_const.mul (contDiff_norm_sq ℝ)
  · apply ContDiff.sum
    intro p hp
    have hd : ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) => x p.2-x p.1) := by
      convert ((PiLp.proj 2 (fun _ : Fin n => ℝ) p.2).contDiff (𝕜 := ℝ)).sub
        ((PiLp.proj 2 (fun _ : Fin n => ℝ) p.1).contDiff (𝕜 := ℝ)) using 1
      funext x
      rfl
    exact contDiff_const.mul ((gueLogBarrier_contDiff hε).comp hd)

/-- The regularization has the exact same n-strong convexity as the singular
ordered GUE potential. -/
theorem gueRegularizedPotential_strongConvexOn (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    StrongConvexOn univ (n : ℝ) (gueRegularizedPotential n ε) := by
  apply strongConvexOn_iff_convex.mpr
  have hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ p ∈ guePairs n, 2*gueLogBarrier ε (x p.2-x p.1)) := by
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hh := (gueLogBarrier_convex hε).2 (mem_univ (x p.2-x p.1))
      (mem_univ (y p.2-y p.1)) ha hb hab
    simp only [smul_eq_mul] at hh
    have he : (a • x+b • y) p.2-(a • x+b • y) p.1 = a*(x p.2-x p.1)+b*(y p.2-y p.1) := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [he]
    nlinarith
  convert hc using 1
  funext x
  simp [gueRegularizedPotential]

/-- In the truncated logarithm regime the Boltzmann pair factor is bounded
by ε², uniformly including negative and zero gaps. -/
theorem gueLogBarrier_exp_bound {ε u : ℝ} (hε : 0 < ε) (hu : u ≤ ε) :
    Real.exp (-2*gueLogBarrier ε u) ≤ ε^2 := by
  have hb : -Real.log ε ≤ gueLogBarrier ε u := by
    unfold gueLogBarrier
    rw [ite_eq_left hu]
    have hdiv : (u-ε)/ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) hε.le
    have hsq : 0 ≤ (u-ε)^2/(2*ε^2) := by positivity
    linarith
  calc
    _ ≤ Real.exp (2*Real.log ε) := Real.exp_le_exp.mpr (by linarith)
    _ = ε^2 := by rw [two_mul, Real.exp_add, Real.exp_log hε]; ring

/-- Every regularized pair factor is bounded by a fixed polynomial majorant. -/
theorem gueLogBarrier_exp_polynomial_bound {ε u : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.exp (-2*gueLogBarrier ε u) ≤ (1+|u|)^2 := by
  by_cases hu : u≤ε
  · have h := gueLogBarrier_exp_bound hε hu
    have he : ε^2≤1 := by nlinarith
    have hm : 1≤(1+|u|)^2 := by nlinarith [abs_nonneg u]
    exact h.trans (he.trans hm)
  · have hpos : 0<u := hε.trans (lt_of_not_ge hu)
    unfold gueLogBarrier
    rw [ite_eq_right hu]
    have he : -2 * -Real.log u = Real.log u+Real.log u := by ring
    rw [he, Real.exp_add, Real.exp_log hpos]
    rw [abs_of_pos hpos]
    nlinarith

end
end GinibrePoincare
