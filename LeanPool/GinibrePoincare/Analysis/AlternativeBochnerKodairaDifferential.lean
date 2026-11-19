/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBochnerKodairaDifferential.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianDbarDistributionalClosure
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Differential operators for the independent Bochner–Kodaira route

The operators below are actual real Fréchet derivatives, not coefficient
operators. The commutation relation is the differential ingredient of (6.8)
in arXiv:2608.19358v2.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The real directional derivative `fderiv ℝ f z v` of `f` at `z` in the direction `v`. -/
def bkDirectional {n : ℕ} (v : Configuration n) (f : Configuration n → ℂ)
    (z : Configuration n) : ℂ := fderiv ℝ f z v

/-- The holomorphic Wirtinger derivative `∂ f / ∂ z_j = (∂_{x_j} f - I ∂_{y_j} f) / 2` in the
`j`-th coordinate. -/
def bkPartial {n : ℕ} (f : Configuration n → ℂ) (j : Fin n)
    (z : Configuration n) : ℂ :=
  (1 / 2 : ℂ) * (bkDirectional (realCoordinateDirection j) f z -
    Complex.I * bkDirectional (imaginaryCoordinateDirection j) f z)

theorem bkDirectional_contDiff {n : ℕ} (v : Configuration n)
    {f : Configuration n → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (bkDirectional v f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem bkDbar_contDiff {n : ℕ} {f : Configuration n → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : Fin n) : ContDiff ℝ ∞ (dbarComponent f j) := by
  exact contDiff_const.mul ((bkDirectional_contDiff _ hf).add
    (contDiff_const.mul (bkDirectional_contDiff _ hf)))

theorem bkPartial_contDiff {n : ℕ} {f : Configuration n → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : Fin n) : ContDiff ℝ ∞ (bkPartial f j) := by
  exact contDiff_const.mul ((bkDirectional_contDiff _ hf).sub
    (contDiff_const.mul (bkDirectional_contDiff _ hf)))

theorem bkDirectional_second {n : ℕ} (u v : Configuration n)
    {f : Configuration n → ℂ} (hf : ContDiff ℝ ∞ f) (z : Configuration n) :
    bkDirectional v (bkDirectional u f) z = fderiv ℝ (fderiv ℝ f) z v u := by
  unfold bkDirectional
  rw [fderiv_clm_apply ((hf.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).differentiable (by simp) z)
    (differentiableAt_const u)]
  simp

theorem bkDirectional_comm {n : ℕ} (u v : Configuration n)
    {f : Configuration n → ℂ} (hf : ContDiff ℝ ∞ f) (z : Configuration n) :
    bkDirectional v (bkDirectional u f) z = bkDirectional u (bkDirectional v f) z := by
  rw [bkDirectional_second _ _ hf, bkDirectional_second _ _ hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp [])).eq v u

theorem bkDirectional_dbar {n : ℕ} (v : Configuration n)
    {f : Configuration n → ℂ} (hf : ContDiff ℝ ∞ f) (j : Fin n)
    (z : Configuration n) :
    bkDirectional v (dbarComponent f j) z =
      (1 / 2 : ℂ) * (bkDirectional v (bkDirectional (realCoordinateDirection j) f) z +
        Complex.I * bkDirectional v (bkDirectional (imaginaryCoordinateDirection j) f) z) := by
  have hx := ((bkDirectional_contDiff (realCoordinateDirection j) hf).differentiable (by simp)
      z).hasFDerivAt
  have hy := ((bkDirectional_contDiff (imaginaryCoordinateDirection j) hf).differentiable (by simp)
      z).hasFDerivAt
  have h := (hx.add (hy.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have he := congrArg (fun L : Configuration n →L[ℝ] ℂ => L v) h.fderiv
  exact he.trans (by simp [bkDirectional, smul_eq_mul]; ring)

theorem bkDirectional_partial {n : ℕ} (v : Configuration n)
    {f : Configuration n → ℂ} (hf : ContDiff ℝ ∞ f) (j : Fin n)
    (z : Configuration n) :
    bkDirectional v (bkPartial f j) z =
      (1 / 2 : ℂ) * (bkDirectional v (bkDirectional (realCoordinateDirection j) f) z -
        Complex.I * bkDirectional v (bkDirectional (imaginaryCoordinateDirection j) f) z) := by
  have hx := ((bkDirectional_contDiff (realCoordinateDirection j) hf).differentiable (by simp)
      z).hasFDerivAt
  have hy := ((bkDirectional_contDiff (imaginaryCoordinateDirection j) hf).differentiable (by simp)
      z).hasFDerivAt
  have h := (hx.sub (hy.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have he := congrArg (fun L : Configuration n →L[ℝ] ℂ => L v) h.fderiv
  exact he.trans (by simp [bkDirectional, smul_eq_mul])

theorem bkDbar_partial_comm {n : ℕ} {f : Configuration n → ℂ}
    (hf : ContDiff ℝ ∞ f) (j k : Fin n) (z : Configuration n) :
    dbarComponent (bkPartial f k) j z = bkPartial (dbarComponent f j) k z := by
  change (1 / 2 : ℂ) * (bkDirectional _ (bkPartial f k) z +
    Complex.I * bkDirectional _ (bkPartial f k) z) = _
  rw [bkDirectional_partial _ hf, bkDirectional_partial _ hf]
  unfold bkPartial
  rw [bkDirectional_dbar _ hf, bkDirectional_dbar _ hf]
  rw [bkDirectional_comm (realCoordinateDirection k) (realCoordinateDirection j) hf,
    bkDirectional_comm (imaginaryCoordinateDirection k) (realCoordinateDirection j) hf,
    bkDirectional_comm (realCoordinateDirection k) (imaginaryCoordinateDirection j) hf,
    bkDirectional_comm (imaginaryCoordinateDirection k) (imaginaryCoordinateDirection j) hf]
  ring

theorem bkDbar_comm {n : ℕ} {f : Configuration n → ℂ}
    (hf : ContDiff ℝ ∞ f) (j k : Fin n) (z : Configuration n) :
    dbarComponent (dbarComponent f k) j z = dbarComponent (dbarComponent f j) k z := by
  change (1 / 2 : ℂ) * (bkDirectional _ (dbarComponent f k) z +
    Complex.I * bkDirectional _ (dbarComponent f k) z) =
    (1 / 2 : ℂ) * (bkDirectional _ (dbarComponent f j) z +
    Complex.I * bkDirectional _ (dbarComponent f j) z)
  rw [bkDirectional_dbar _ hf, bkDirectional_dbar _ hf,
    bkDirectional_dbar _ hf, bkDirectional_dbar _ hf]
  rw [bkDirectional_comm (realCoordinateDirection k) (realCoordinateDirection j) hf,
    bkDirectional_comm (imaginaryCoordinateDirection k) (realCoordinateDirection j) hf,
    bkDirectional_comm (realCoordinateDirection k) (imaginaryCoordinateDirection j) hf,
    bkDirectional_comm (imaginaryCoordinateDirection k) (imaginaryCoordinateDirection j) hf]
  ring

theorem bkPartial_mul {n : ℕ} {f g : Configuration n → ℂ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin n) (z : Configuration n) :
    bkPartial (fun w => f w * g w) j z =
      bkPartial f j z * g z + f z * bkPartial g j z := by
  change bkPartial (f * g) j z = _
  unfold bkPartial bkDirectional
  rw [fderiv_mul (hf z) (hg z)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Conjugation exchanges the actual two Wirtinger operators. -/
theorem bkPartial_eq_conj_dbar {n : ℕ} {f : Configuration n → ℂ}
    (hf : Differentiable ℝ f) (j : Fin n) (z : Configuration n) :
    bkPartial f j z = conj (dbarComponent (fun w => conj (f w)) j z) := by
  have h := (Complex.conjCLE.hasFDerivAt.comp z (hf z).hasFDerivAt).fderiv
  change fderiv ℝ (fun w => conj (f w)) z = _ at h
  unfold bkPartial bkDirectional dbarComponent
  rw [h]
  change (1 / 2 : ℂ) * (fderiv ℝ f z (realCoordinateDirection j) -
    Complex.I * fderiv ℝ f z (imaginaryCoordinateDirection j)) =
    conj ((1 / 2 : ℂ) * (conj (fderiv ℝ f z (realCoordinateDirection j)) +
      Complex.I * conj (fderiv ℝ f z (imaginaryCoordinateDirection j))))
  simp only [map_mul, map_add, Complex.conj_I,
    starRingEnd_self_apply]
  rw [show conj (1 / 2 : ℂ) = 1 / 2 by apply Complex.ext <;> norm_num]
  ring

theorem bkAdjoint_eq {n : ℕ} {f : Configuration n → ℂ}
    (hf : Differentiable ℝ f) (j : Fin n) :
    gaussianDbarAdjointTest j f = fun z => (n : ℂ) * conj (z j) * f z - bkPartial f j z := by
  funext z
  rw [gaussianDbarAdjointTest, ← bkPartial_eq_conj_dbar hf]

/-- The Gaussian weighted adjoint preserves compact smooth tests. -/
theorem bkAdjoint_contDiff {n : ℕ} {f : Configuration n → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : Fin n) :
    ContDiff ℝ ∞ (gaussianDbarAdjointTest j f) := by
  rw [bkAdjoint_eq (hf.differentiable (by simp))]
  exact ((contDiff_const.mul (Complex.conjCLE.contDiff.comp ((ContinuousLinearMap.proj j :
      Configuration n →L[ℝ] ℂ).contDiff))).mul hf).sub
    (bkPartial_contDiff hf j)

theorem bkAdjoint_compact {n : ℕ} {f : Configuration n → ℂ}
    (hc : HasCompactSupport f) (j : Fin n) : HasCompactSupport (gaussianDbarAdjointTest j f) := by
  unfold gaussianDbarAdjointTest
  exact hc.mul_left.sub ((hasCompactSupport_dbarComponent
    (hc.comp_left (g := conj) (by simp)) j).comp_left (by simp))

/-- Antiholomorphic differentiation of a conjugate coordinate. -/
theorem bkDbar_conj_coordinate {n : ℕ} (j k : Fin n) (z : Configuration n) :
    dbarComponent (fun w => conj (w k)) j z = if j = k then 1 else 0 := by
  have h := (Complex.conjCLE.hasFDerivAt.comp z
    (ContinuousLinearMap.proj k : Configuration n →L[ℝ] ℂ).hasFDerivAt).fderiv
  change fderiv ℝ (fun w => conj (w k)) z = _ at h
  unfold dbarComponent
  rw [h]
  by_cases hjk : j = k
  · subst k
    simp [realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection,
      ContinuousLinearMap.proj_apply]
    norm_num
  · simp [realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection,
      ContinuousLinearMap.proj_apply, hjk, Ne.symm hjk]

/-- Canonical commutation relation, proved from Fréchet derivative symmetry. -/
theorem bkDbar_adjoint_comm {n : ℕ} {f : Configuration n → ℂ}
    (hf : ContDiff ℝ ∞ f) (j k : Fin n) (z : Configuration n) :
    dbarComponent (gaussianDbarAdjointTest k f) j z =
      gaussianDbarAdjointTest k (dbarComponent f j) z +
        if j = k then (n : ℂ) * f z else 0 := by
  rw [bkAdjoint_eq (hf.differentiable (by simp))]
  have hg : ContDiff ℝ ∞ (fun z : Configuration n => (n : ℂ) * conj (z k) * f z) :=
    (contDiff_const.mul (Complex.conjCLE.contDiff.comp ((ContinuousLinearMap.proj k : Configuration
        n →L[ℝ] ℂ).contDiff))).mul hf
  have hx := (hg.differentiable (by simp) z).hasFDerivAt
  have hy := ((bkPartial_contDiff hf k).differentiable (by simp) z).hasFDerivAt
  have hsub := (hx.sub hy).fderiv
  change fderiv ℝ (fun z => (n : ℂ) * conj (z k) * f z - bkPartial f k z) z = _ at hsub
  have hsplit : dbarComponent (fun z => (n : ℂ) * conj (z k) * f z - bkPartial f k z) j z =
      dbarComponent (fun z => (n : ℂ) * conj (z k) * f z) j z -
        dbarComponent (bkPartial f k) j z := by
    unfold dbarComponent
    rw [hsub]
    simp only [sub_apply]
    ring
  have hcoord : Differentiable ℝ (fun w : Configuration n => (n : ℂ) * conj (w k)) := by fun_prop
  rw [hsplit, dbarComponent_mul hcoord (hf.differentiable (by simp))]
  have hscale : dbarComponent (fun w : Configuration n => (n : ℂ) * conj (w k)) j z =
      (n : ℂ) * dbarComponent (fun w : Configuration n => conj (w k)) j z := by
    unfold dbarComponent
    rw [fderiv_const_mul
      (show DifferentiableAt ℝ (fun w : Configuration n => conj (w k)) z by fun_prop)]
    simp only [smul_apply, smul_eq_mul]
    ring
  rw [hscale, bkDbar_conj_coordinate, bkDbar_partial_comm hf,
    bkAdjoint_eq ((bkDbar_contDiff hf j).differentiable (by simp))]
  split_ifs <;> ring

end
end GinibrePoincare

