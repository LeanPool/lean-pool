/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianLSIReal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BernoulliBinomialBridge
public import LeanPool.GinibrePoincare.Analysis.GaussianSobolevApproximation

/-!
# Gaussian LSIReal
-/


@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators BoundedContinuousFunction
namespace GinibrePoincare
noncomputable section

private def compactTestBCF (f : ℝ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) : ℝ →ᵇ ℝ :=
  let C := Classical.choose (hf.bounded_above_of_compact_support hc)
  BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * C) (fun x y =>
    (dist_le_norm_add_norm _ _).trans (by
      change ‖f x‖ + ‖f y‖ ≤ 2 * C
      have hC := Classical.choose_spec (hf.bounded_above_of_compact_support hc)
      linarith [hC x, hC y]))

/-- The cube average identity also holds after any fixed scaling. -/
theorem bernoulliCubeAverage_scaled_eq_integral (n : ℕ) (c : ℝ) (F : ℝ →ᵇ ℝ) :
    bernoulliCubeAverage n (fun x => F (c * bernoulliCubeSum n x)) =
      ∫ ω, F (c * rademacherSum n ω) ∂rademacherProduct :=
  bernoulliCubeAverage_eq_rademacherSum_integral n
    (F.compContinuous ⟨fun x => c * x, by fun_prop⟩)

/-- The concrete finite cube has exactly the entropy used by the binomial CLT. -/
theorem bernoulliCube_entropy_eq (n : ℕ) (c : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    uniformFiniteEntropy (fun x => (f (c * bernoulliCubeSum n x)) ^ 2) =
      squareEntropy rademacherProduct (fun ω => f (c * rademacherSum n ω)) := by
  let F := compactTestBCF f hf hc
  let L := compactTestBCF (fun x => (f x) ^ 2 * Real.log ((f x) ^ 2))
    (continuous_square_mul_log hf) (compactSupport_square_mul_log hc)
  have hm := bernoulliCubeAverage_scaled_eq_integral n c (F ^ 2)
  have hl := bernoulliCubeAverage_scaled_eq_integral n c L
  change bernoulliCubeAverage n (fun x => (f (c * bernoulliCubeSum n x)) ^ 2) =
    (∫ ω, (f (c * rademacherSum n ω)) ^ 2 ∂rademacherProduct) at hm
  change bernoulliCubeAverage n (fun x => (f (c * bernoulliCubeSum n x)) ^ 2 *
    Real.log ((f (c * bernoulliCubeSum n x)) ^ 2)) =
    (∫ ω, (f (c * rademacherSum n ω)) ^ 2 *
      Real.log ((f (c * rademacherSum n ω)) ^ 2) ∂rademacherProduct) at hl
  rw [uniformFiniteEntropy_eq]
  change bernoulliCubeAverage n (fun x => (f (c * bernoulliCubeSum n x)) ^ 2 *
    Real.log ((f (c * bernoulliCubeSum n x)) ^ 2)) -
    entropyPhi (bernoulliCubeAverage n (fun x => (f (c * bernoulliCubeSum n x)) ^ 2)) = _
  rw [hm, hl]
  rfl

/-- The exact fiber energy is the proved finite-cube Dirichlet energy. -/
theorem bernoulliCube_energy_eq (n : ℕ) (f : ℝ → ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    bernoulliCubeEnergy (n + 1) (fun x => f (bernoulliMesh n * bernoulliCubeSum (n + 1) x)) =
      bernoulliTaylorEnergy n f := by
  let c := bernoulliMesh n
  let F := compactTestBCF f hf hc
  let J : ℝ →ᵇ ℝ := (F.compContinuous ⟨fun x => x + c, by fun_prop⟩ -
    F.compContinuous ⟨fun x => x - c, by fun_prop⟩) ^ 2
  have hj := bernoulliCubeAverage_scaled_eq_integral n c J
  change bernoulliCubeAverage n (fun x => (f (c * bernoulliCubeSum n x + c) -
    f (c * bernoulliCubeSum n x - c)) ^ 2) =
    (∫ ω, (f (c * rademacherSum n ω + c) - f (c * rademacherSum n ω - c)) ^ 2
      ∂rademacherProduct) at hj
  rw [bernoulliCubeEnergy_sum_test n (fun t => f (c * t)), bernoulliTaylorEnergy_eq_jump]
  have he : (fun x : BernoulliCube n =>
      (f (c * (bernoulliCubeSum n x + 1)) - f (c * (bernoulliCubeSum n x - 1))) ^ 2) =
    (fun x => (f (c * bernoulliCubeSum n x + c) - f (c * bernoulliCubeSum n x - c)) ^ 2) := by
    funext x
    congr 2 <;> ring
  change ((n : ℝ) + 1) / 2 * bernoulliCubeAverage n
    (fun x => (f (c * (bernoulliCubeSum n x + 1)) - f (c * (bernoulliCubeSum n x - 1))) ^ 2) = _
  rw [he, hj]
  rfl

/-- The previously open finite-binomial inequality follows from the actual cube LSI. -/
theorem binomial_fiber_lsi (n : ℕ) (f : ℝ → ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    squareEntropy rademacherProduct (fun ω => f (normalizedBernoulliSum (n + 1) ω)) ≤
      bernoulliTaylorEnergy n f := by
  have h := bernoulliCube_lsi (n + 1)
    (fun x => f (bernoulliMesh n * bernoulliCubeSum (n + 1) x))
  rw [bernoulliCube_entropy_eq _ _ f hf hc, bernoulliCube_energy_eq _ f hf hc] at h
  simpa [normalizedBernoulliSum, bernoulliMesh, rademacherSum, Nat.cast_add, Nat.cast_one] using h

/-- Sharp Gaussian log-Sobolev inequality on the actual compact C² core. -/
theorem gaussianReal_lsi_C2 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    squareEntropy (gaussianReal 0 1) f ≤ 2 * ∫ x, (deriv f x) ^ 2 ∂gaussianReal 0 1 :=
  gaussian_lsi_of_binomial_fiber_bounds f hf hc (fun n => binomial_fiber_lsi n f hf.continuous hc)

/-- The Gaussian H¹ completion inequality is now unconditional. -/
theorem gaussianReal_lsi_H1Completion :
    ∀ p ∈ gaussianH1Completion,
      Integrable (fun x => p.1 x ^ 2 * Real.log (p.1 x ^ 2)) (gaussianReal 0 1) ∧
        squareEntropy (gaussianReal 0 1) p.1 ≤ 2 * ‖p.2‖ ^ 2 :=
  gaussianH1Completion_lsi_of_C2 gaussianReal_lsi_C2

/-- Sharp Gaussian LSI for all actual C¹ finite-energy functions. -/
theorem gaussianReal_lsi_C1 (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hv : MemLp f 2 (gaussianReal 0 1)) (hd : MemLp (deriv f) 2 (gaussianReal 0 1)) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) (gaussianReal 0 1) ∧
      squareEntropy (gaussianReal 0 1) f ≤ 2 * ∫ x, (deriv f x) ^ 2 ∂gaussianReal 0 1 :=
  gaussian_lsi_C1_of_C2 gaussianReal_lsi_C2 f hf hv hd

end
end GinibrePoincare
