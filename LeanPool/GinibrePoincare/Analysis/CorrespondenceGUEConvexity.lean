/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEConvexity.lean.
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
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# Correspondence GUE convexity

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueEnergy_strongConvexOn`, `gueRawDensity_eq_exp_energy`.
-/

@[expose] public section
open Set
namespace GinibrePoincare
noncomputable section

/-- Strict ordered real chamber; its boundary has zero Vandermonde density. -/
def gueStrictChamber (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i j : Fin n, i<j → x i<x j}

/-- The ordered index pairs `(i, j)` with `i < j`. -/
def guePairs (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1<p.2)

/-- Negative logarithm of the unnormalized real GUE density, with the paper's
real Gaussian normalization n/2 rather than the complex normalization n. -/
def gueEnergy (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (n : ℝ)/2*‖x‖^2 + ∑ p ∈ guePairs n, -2*Real.log (x p.2-x p.1)

/-- The unnormalized GUE eigenvalue density
`exp (-(n / 2) * ∑ i, x i ^ 2) * ∏_{i < j} (x j - x i) ^ 2`. -/
def gueRawDensity (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-(n : ℝ)/2*∑ i, (x i)^2)*∏ p ∈ guePairs n, (x p.2-x p.1)^2

theorem gueStrictChamber_convex (n : ℕ) : Convex ℝ (gueStrictChamber n) := by
  intro x hx y hy a b ha hb hab i j hij
  have hax := mul_nonneg ha (sub_pos.mpr (hx i j hij)).le
  have hby := mul_nonneg hb (sub_pos.mpr (hy i j hij)).le
  have hpos : 0<a*(x j-x i)+b*(y j-y i) := by
    by_cases h : 0<a
    · exact add_pos_of_pos_of_nonneg (mul_pos h (sub_pos.mpr (hx i j hij))) hby
    · have hb' : 0<b := by linarith
      exact add_pos_of_nonneg_of_pos hax (mul_pos hb' (sub_pos.mpr (hy i j hij)))
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  linarith

/-- The ordered GUE density is n-strongly log-concave: subtracting the
quadratic n/2 confinement leaves a convex function on the strict chamber. -/
theorem gueEnergy_strong_convexity (n : ℕ) :
    ConvexOn ℝ (gueStrictChamber n) (fun x => gueEnergy n x-(n : ℝ)/2*‖x‖^2) := by
  have hc : ConvexOn ℝ (gueStrictChamber n)
      (fun x => ∑ p ∈ guePairs n, -2*Real.log (x p.2-x p.1)) := by
    refine ⟨gueStrictChamber_convex n,?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hij : p.1<p.2 := (Finset.mem_filter.mp hp).2
    have hlog := strictConcaveOn_log_Ioi.concaveOn.2
      (sub_pos.mpr (hx _ _ hij)) (sub_pos.mpr (hy _ _ hij)) ha hb hab
    simp only [smul_eq_mul] at hlog
    have he : (a • x+b • y) p.2-(a • x+b • y) p.1 =
        a*(x p.2-x p.1)+b*(y p.2-y p.1) := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [he]
    nlinarith
  convert hc using 1
  funext x
  simp [gueEnergy]

/-- Strong convexity in Mathlib's standard definition, with exact curvature n. -/
theorem gueEnergy_strongConvexOn (n : ℕ) :
    StrongConvexOn (gueStrictChamber n) (n : ℝ) (gueEnergy n) :=
  strongConvexOn_iff_convex.mpr (gueEnergy_strong_convexity n)

/-- Literal real GUE Boltzmann density on the ordered chamber. -/
theorem gueRawDensity_eq_exp_energy (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ gueStrictChamber n) : gueRawDensity n x = Real.exp (-gueEnergy n x) := by
  have hsum : -(∑ p ∈ guePairs n, -2*Real.log (x p.2-x p.1)) =
      ∑ p ∈ guePairs n, (Real.log (x p.2-x p.1)+Real.log (x p.2-x p.1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  unfold gueEnergy
  rw [neg_add, hsum, Real.exp_add, Real.exp_sum]
  unfold gueRawDensity
  rw [EuclideanSpace.real_norm_sq_eq]
  congr 1
  · congr 1
    ring
  · apply Finset.prod_congr rfl
    intro p hp
    have hpos := sub_pos.mpr (hx _ _ (Finset.mem_filter.mp hp).2)
    rw [Real.exp_add, Real.exp_log hpos]
    ring

end
end GinibrePoincare
