/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryConvexLift.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticRadialConfinement
public import Mathlib.Analysis.Normed.Module.Convex

/-! # The convex Euclidean lift in the primary proof of Theorem 1.14

This file proves the dimension-independent convexity step in the versioned
paper's proof. It does not assert the Bakry–Émery entropy theorem.
-/

@[expose] public section

open Set
namespace GinibrePoincare
noncomputable section

/-- The convex planar radial remainder restricted to its real axis. -/
def bakryEmeryRadialRemainder (ρ : ℝ) (V : Potential) (r : ℝ) : ℝ :=
  V (r : ℂ) - ρ / 2 * r ^ 2

/-- Restriction of the planar convexity hypothesis to the real axis. -/
theorem bakryEmeryRadialRemainder_convex (ρ : ℝ) {V : Potential}
    (hc : IsRhoConvexPotential ρ V) :
    ConvexOn ℝ univ (bakryEmeryRadialRemainder ρ V) := by
  have h := hc.comp_linearMap Complex.ofRealCLM.toLinearMap
  unfold bakryEmeryRadialRemainder
  simpa [bakryEmeryRadialRemainder, Function.comp_def, Complex.normSq_ofReal, pow_two] using h

/-- Rotation invariance supplies the evenness needed for increasing radial lifts. -/
theorem bakryEmeryRadialRemainder_even (ρ : ℝ) {V : Potential}
    (hrot : IsRotationalPotential V) (r : ℝ) :
    bakryEmeryRadialRemainder ρ V (-r) = bakryEmeryRadialRemainder ρ V r := by
  have h := hrot (-1) (r : ℂ) (by simp)
  simp only [bakryEmeryRadialRemainder, Complex.ofReal_neg, neg_sq]
  congr 1
  simpa using h

/-- Every even convex scalar function is increasing on positive radii. -/
theorem even_convex_monotoneOn_nonnegative (ψ : ℝ → ℝ)
    (hc : ConvexOn ℝ univ ψ) (he : ∀ r, ψ (-r) = ψ r) :
    MonotoneOn ψ (Ici 0) := by
  intro x hx y hy hxy
  by_cases hy0 : y = 0
  · have hx0 : x = 0 := by simp only [mem_Ici] at hx; linarith
    simp [hx0, hy0]
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  let a : ℝ := (y + x) / (2 * y)
  let b : ℝ := (y - x) / (2 * y)
  have ha : 0 ≤ a := div_nonneg (add_nonneg hy hx) (by positivity)
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hxy) (by positivity)
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have heq : a • y + b • (-y) = x := by
    simp only [smul_eq_mul]; dsimp [a, b]; field_simp; ring
  have h := hc.2 (mem_univ y) (mem_univ (-y)) ha hb hab
  rw [heq, he] at h
  simpa only [smul_eq_mul, ← add_mul, hab, one_mul] using h

/-- The Euclidean lift remainder is convex in every real normed space. This
is the geometric step preceding the paper's Bakry–Émery invocation. -/
theorem bakryEmeryEuclideanLift_remainder_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : ℝ) {V : Potential} (hrot : IsRotationalPotential V)
    (hc : IsRhoConvexPotential ρ V) :
    ConvexOn ℝ (univ : Set E) (fun x => V (‖x‖ : ℂ) - ρ / 2 * ‖x‖ ^ 2) := by
  have hψ := bakryEmeryRadialRemainder_convex ρ hc
  have hm := even_convex_monotoneOn_nonnegative _ hψ
    (bakryEmeryRadialRemainder_even ρ hrot)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hn := convexOn_univ_norm.2 hx hy ha hb hab
  have hp : 0 ≤ a • ‖x‖ + b • ‖y‖ := by
    simp only [smul_eq_mul]
    positivity
  exact (hm (norm_nonneg _) hp hn).trans
    (hψ.2 (mem_univ _) (mem_univ _) ha hb hab)

/-- The actual lift potential at inverse temperature `n`, in any Euclidean
block dimension, has strong-convexity parameter exactly `nρ`. -/
def bakryEmeryEuclideanLiftPotential
    {E : Type*} [NormedAddCommGroup E] (n : ℕ) (V : Potential) (x : E) : ℝ :=
  (n : ℝ) * V (‖x‖ : ℂ)

theorem bakryEmeryEuclideanLift_strongConvex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (ρ : ℝ) {V : Potential} (hrot : IsRotationalPotential V)
    (hc : IsRhoConvexPotential ρ V) :
    ConvexOn ℝ (univ : Set E)
      (fun x => bakryEmeryEuclideanLiftPotential n V x -
        ((n : ℝ) * ρ) / 2 * ‖x‖ ^ 2) := by
  have h := (bakryEmeryEuclideanLift_remainder_convex (E := E) ρ hrot hc).smul
    (c := (n : ℝ)) (Nat.cast_nonneg n)
  convert h using 1
  funext x
  simp only [bakryEmeryEuclideanLiftPotential, smul_eq_mul]
  ring

end
end GinibrePoincare
