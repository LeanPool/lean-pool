/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreGradientPhaseNorm.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakGradientPhase

/-! # The phase pullback preserves the actual Euclidean gradient norm -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators
namespace GinibrePoincare
noncomputable section

/-- The transpose real rotation on the actual Euclidean gradient coordinates. -/
def ginibreGradientPhasePullback (n : ℕ) (a : Fin n → ℂ)
    (h : EuclideanSpace ℝ (Fin n × Fin 2)) : EuclideanSpace ℝ (Fin n × Fin 2) :=
  WithLp.toLp 2 (fun k => ∑ j : Fin n × Fin 2,
    ginibreDirectionCoefficient (coordinatePhase a (ginibreCoordinateDirection k)) j * h j)

/-- Real gradient coordinates transform by the corresponding two-dimensional rotation. -/
theorem ginibreGradientPhasePullback_real (n : ℕ) (a : Fin n → ℂ)
    (h : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n) :
    ginibreGradientPhasePullback n a h (i, 0) =
      (a i).re * h (i, 0) + (a i).im * h (i, 1) := by
  simp [ginibreGradientPhasePullback, Fintype.sum_prod_type, Fin.sum_univ_two,
    ginibreDirectionCoefficient, coordinatePhase, ginibreCoordinateDirection,
    realCoordinateDirection, coordinateDirection, Finset.sum_add_distrib, apply_ite, ite_mul]

/-- Imaginary gradient coordinates transform by the same real rotation. -/
theorem ginibreGradientPhasePullback_imag (n : ℕ) (a : Fin n → ℂ)
    (h : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n) :
    ginibreGradientPhasePullback n a h (i, 1) =
      -(a i).im * h (i, 0) + (a i).re * h (i, 1) := by
  simp [ginibreGradientPhasePullback, Fintype.sum_prod_type, Fin.sum_univ_two,
    ginibreDirectionCoefficient, coordinatePhase, ginibreCoordinateDirection,
    imaginaryCoordinateDirection, coordinateDirection, Finset.sum_add_distrib, apply_ite, ite_mul]

/-- Unit coordinate phases preserve the squared Euclidean gradient norm. -/
theorem ginibreGradientPhasePullback_norm_sq (n : ℕ) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ = 1) (h : EuclideanSpace ℝ (Fin n × Fin 2)) :
    ‖ginibreGradientPhasePullback n a h‖ ^ 2 = ‖h‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
    ginibreGradientPhasePullback_real, ginibreGradientPhasePullback_imag,
    Real.norm_eq_abs, sq_abs]
  apply Finset.sum_congr rfl
  intro i _
  have hu : (a i).re ^ 2 + (a i).im ^ 2 = 1 := by
    have he := ha i
    have hs : Complex.normSq (a i) = 1 := by rw [← Complex.sq_norm, he]; norm_num
    simpa only [Complex.normSq_apply, pow_two] using hs
  nlinarith

/-- The actual weak gradient norm of a radial value is phase invariant a.e. -/
theorem ginibre_radial_weak_gradient_norm_phase_ae (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ = 1) :
    ∀ᵐ z ∂(volume : Measure (Configuration n)), ‖g (coordinatePhase a z)‖ = ‖g z‖ := by
  filter_upwards [ginibre_radial_weak_gradient_phase_covariance n hn u g hg f hf hr a ha] with z hz
  have he : ginibreGradientPhasePullback n a (g (coordinatePhase a z)) = g z := by
    ext k
    exact (hz k).symm
  have hs := ginibreGradientPhasePullback_norm_sq n a ha (g (coordinatePhase a z))
  rw [he] at hs
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs.symm

end
end GinibrePoincare
