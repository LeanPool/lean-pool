/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialSobolevClosure.lean and
GinibrePoincare/Analysis/EntropyL2Closure.lean, together with conjugation
identities from GinibreConjugationGeometry.lean and GinibreEqualityWeakHolomorphic.lean.
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

public import Mathlib.MeasureTheory.Function.L2Space

/-! # L² norm and conjugation identities -/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
open scoped BigOperators

/-- The actual square moment equals the Hilbert-space squared norm. -/
theorem integral_square_eq_L2_norm_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : Lp ℝ 2 μ) : (∫ x, f x ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem integral_norm_sq_eq_L2_norm_sq {α V : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (μ : Measure α) (v : Lp V 2 μ) :
    (∫ x, ‖v x‖ ^ 2 ∂μ) = ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- Conjugation distributes over addition in complex L². -/
theorem Lp_star_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u v : Lp ℂ 2 μ) : star (u + v) = star u + star v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (u + v), Lp.coeFn_star u, Lp.coeFn_star v,
    Lp.coeFn_add u v, Lp.coeFn_add (star u) (star v)] with z huv hu hv hadd hstaradd
  change (u + v) z = u z + v z at hadd
  change (star u + star v) z = star u z + star v z at hstaradd
  rw [huv, hstaradd]
  calc
    star ((u + v) z) = star (u z + v z) := congrArg star hadd
    _ = star (u z) + star (v z) := by simp
    _ = star u z + star v z := congrArg₂ (· + ·) hu.symm hv.symm

/-- Conjugation commutes with real scalar multiplication in complex L². -/
theorem Lp_star_real_smul {α : Type*} [MeasurableSpace α] {μ : Measure α} (r : ℝ)
    (u : Lp ℂ 2 μ) : star (r • u) = r • star u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (r • u), Lp.coeFn_star u,
    Lp.coeFn_smul r u, Lp.coeFn_smul r (star u)] with z hru hu hsmul hstarsmul
  change (r • u) z = r • u z at hsmul
  change (r • star u) z = r • star u z at hstarsmul
  rw [hru, hstarsmul]
  calc
    star ((r • u) z) = star (r • u z) := congrArg star hsmul
    _ = r • star (u z) := by simp
    _ = r • star u z := congrArg (r • ·) hu.symm

/-- Conjugation preserves the complex L² norm. -/
theorem Lp_norm_star {α : Type*} [MeasurableSpace α] {μ : Measure α} (u : Lp ℂ 2 μ) :
    ‖star u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  exact congrArg ENNReal.toReal AEEqFun.eLpNorm_star

end GinibrePoincare
