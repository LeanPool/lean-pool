/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupPaperSpeed.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupWeakHeat
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupL1
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupDecay
public import LeanPool.GinibrePoincare.Analysis.GinibreDynamicsGenerator

/-! # The full diffusion at the paper's arbitrary speed -/

@[expose] public section
open MeasureTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Exact paper time scale at inverse temperature n². -/
def ginibrePaperSpeedFactor (n : ℕ) (α : ℝ≥0) : ℝ≥0 := α / n

@[simp] theorem ginibrePaperSpeedFactor_coe (n : ℕ) (α : ℝ≥0) :
    (ginibrePaperSpeedFactor n α : ℝ) = (α : ℝ) / (n : ℝ) := by
  simp [ginibrePaperSpeedFactor]

/-- The actual full symmetric diffusion at arbitrary nonnegative paper speed. -/
def ginibreFullPaperEvolution (n : ℕ) (hn : 0 < n) (α t : ℝ≥0) :
    ginibreSymmetricL2 n →L[ℂ] ginibreSymmetricL2 n :=
  ginibreFullEvolution n hn (ginibrePaperSpeedFactor n α * t)

/-- Actual real paper-speed diffusion. -/
def ginibreFullRealPaperEvolution (n : ℕ) (hn : 0 < n) (α t : ℝ≥0) :
    ginibreFullSymmetricValues n →L[ℝ] ginibreFullSymmetricValues n :=
  ginibreFullRealEvolution n hn (ginibrePaperSpeedFactor n α * t)

@[simp] theorem ginibreFullPaperEvolution_zero (n : ℕ) (hn : 0 < n) (α : ℝ≥0) :
    ginibreFullPaperEvolution n hn α 0 = 1 := by simp [ginibreFullPaperEvolution]

theorem ginibreFullPaperEvolution_add (n : ℕ) (hn : 0 < n) (α s t : ℝ≥0) :
    ginibreFullPaperEvolution n hn α (s + t) =
      ginibreFullPaperEvolution n hn α s * ginibreFullPaperEvolution n hn α t := by
  unfold ginibreFullPaperEvolution
  rw [mul_add, ginibreFullEvolution_add]

theorem continuous_ginibreFullPaperEvolution (n : ℕ) (hn : 0 < n) (α : ℝ≥0)
    (x : ginibreSymmetricL2 n) : Continuous (fun t => ginibreFullPaperEvolution n hn α t x) :=
  (continuous_ginibreFullEvolution n hn x).comp (continuous_const.mul continuous_id)

theorem ginibreFullPaperEvolution_contracts (n : ℕ) (hn : 0 < n) (α t : ℝ≥0)
    (x : ginibreSymmetricL2 n) : ‖ginibreFullPaperEvolution n hn α t x‖ ≤ ‖x‖ :=
  ginibreFullEvolution_contracts n hn _ x

theorem ginibreFullPaperEvolution_integral (n : ℕ) (hn : 0 < n) (α t : ℝ≥0)
    (x : ginibreSymmetricL2 n) :
    (∫ z, (ginibreFullPaperEvolution n hn α t x).val z ∂ginibreMeasure n) =
      ∫ z, x.val z ∂ginibreMeasure n := ginibreFullEvolution_integral n hn _ x

theorem ginibreFullRealPaperEvolution_interval (n : ℕ) (hn : 0 < n) (α t : ℝ≥0)
    (x : ginibreFullSymmetricValues n) (a b : ℝ)
    (hx : ∀ᵐ z ∂ginibreMeasure n, x.val z ∈ Set.Icc a b) :
    ∀ᵐ z ∂ginibreMeasure n, (ginibreFullRealPaperEvolution n hn α t x).val z ∈ Set.Icc a b :=
  ginibreFullRealEvolution_interval n hn _ x a b hx

/-- The actual infinitesimal derivative has exactly the α/n paper multiplier. -/
theorem ginibreFullPaperEvolution_right_derivative (n : ℕ) (hn : 0 < n) (α : ℝ≥0)
    (u v : ginibreSymmetricL2 n) (hg : (u, v) ∈ (ginibreFullGenerator n hn).graph) :
    HasDerivWithinAt (fun s : ℝ => ginibreFullPaperEvolution n hn α (Real.toNNReal s) u)
      (((α : ℝ) / (n : ℝ)) • v) (Set.Ici 0) 0 := by
  let c : ℝ := ginibrePaperSpeedFactor n α
  have hc : 0 ≤ c := (ginibrePaperSpeedFactor n α).coe_nonneg
  have hd := (ginibreFullGenerator_graph_iff_right_derivative n hn u v).mp hg
  have hs : HasDerivWithinAt (fun s : ℝ => c * s) c (Set.Ici 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul c).hasDerivWithinAt
  have hcomp := hd.scomp_of_eq 0 hs (by
    intro s hs
    exact mul_nonneg hc hs) (by simp)
  have hcc : Real.toNNReal c = ginibrePaperSpeedFactor n α := Real.toNNReal_coe
  simp only [Function.comp_def, Real.toNNReal_mul hc, hcc] at hcomp
  simpa only [ginibreFullPaperEvolution, c, ginibrePaperSpeedFactor_coe] using hcomp

/-- The sharp full centered relaxation rate at the paper's exact speed. -/
theorem ginibreFullPaperEvolution_centered_decay (n : ℕ) (hn : 0 < n) (α t : ℝ≥0)
    (x : ginibreSymmetricL2 n) :
    ‖ginibreFullPaperEvolution n hn α t (ginibreFullComplexCenter n hn x)‖ ≤
      Real.exp (-2 * ((α : ℝ) / (n : ℝ)) * (t : ℝ)) * ‖ginibreFullComplexCenter n hn x‖ := by
  have h := ginibreFullEvolution_centered_decay n hn (ginibrePaperSpeedFactor n α * t) x
  simpa only [ginibreFullPaperEvolution, NNReal.coe_mul, ginibrePaperSpeedFactor_coe,
    mul_assoc] using h

end
end GinibrePoincare
