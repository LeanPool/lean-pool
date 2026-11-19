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

/-- The squared norm of a complex L² class with a real representative is its square integral. -/
theorem L2_norm_sq_eq_integral_sq_of_ae_ofReal {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (v : Lp ℂ 2 μ) (f : α → ℝ)
    (h : v =ᵐ[μ] fun x ↦ (f x : ℂ)) :
    ‖v‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← integral_norm_sq_eq_L2_norm_sq μ v]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]

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

/-- Conjugation is involutive on complex L². -/
theorem Lp_star_star {α : Type*} [MeasurableSpace α] {μ : Measure α} (u : Lp ℂ 2 μ) :
    star (star u) = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (star u), Lp.coeFn_star u] with z h1 h2
  simp only [Pi.star_apply] at h1 h2
  rw [h1, h2, star_star]

/-- Conjugation distributes over subtraction in complex L². -/
theorem Lp_star_sub {α : Type*} [MeasurableSpace α] {μ : Measure α} (u v : Lp ℂ 2 μ) :
    star (u - v) = star u - star v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (u - v), Lp.coeFn_sub u v,
    Lp.coeFn_sub (star u) (star v), Lp.coeFn_star u, Lp.coeFn_star v] with z h1 h2 h3 h4 h5
  simp only [Pi.star_apply, Pi.sub_apply] at h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5, star_sub]

/-- Conjugation fixes zero in complex L². -/
theorem Lp_star_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} :
    star (0 : Lp ℂ 2 μ) = 0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (0 : Lp ℂ 2 μ), Lp.coeFn_zero ℂ 2 μ] with z hs hz
  simp only [Pi.star_apply] at hs
  rw [hs, hz]
  simp

/-- Conjugation is conjugate-linear for complex scalars in complex L². -/
theorem Lp_star_complex_smul {α : Type*} [MeasurableSpace α] {μ : Measure α} (a : ℂ)
    (u : Lp ℂ 2 μ) : star (a • u) = star a • star u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (a • u), Lp.coeFn_smul a u,
    Lp.coeFn_smul (star a) (star u), Lp.coeFn_star u] with z h1 h2 h3 h4
  simp only [Pi.star_apply, Pi.smul_apply] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  simp [smul_eq_mul]

/-- Conjugation conjugates the complex L² inner product. -/
theorem Lp_inner_star_star {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u v : Lp ℂ 2 μ) : inner ℂ (star u) (star v) = star (inner ℂ u v) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  rw [integral_congr_ae (show
    (fun z ↦ inner ℂ ((star u) z) ((star v) z)) =ᵐ[μ]
      (fun z ↦ star (inner ℂ (u z) (v z))) by
    filter_upwards [Lp.coeFn_star u, Lp.coeFn_star v] with z hu hv
    rw [hu, hv]
    simp [RCLike.inner_apply])]
  exact integral_conj

/-- Pointwise conjugation on complex L², as a real-linear isometry. -/
def LpConjugationIsometry {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    Lp ℂ 2 μ →ₗᵢ[ℝ] Lp ℂ 2 μ where
  toLinearMap :=
    { toFun := star
      map_add' := Lp_star_add
      map_smul' := Lp_star_real_smul }
  norm_map' := Lp_norm_star

@[simp] theorem LpConjugationIsometry_apply {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (u : Lp ℂ 2 μ) : LpConjugationIsometry μ u = star u := rfl

end GinibrePoincare
