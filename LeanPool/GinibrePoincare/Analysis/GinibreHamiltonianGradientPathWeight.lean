/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianGradientPathWeight.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUReversalWeight
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGenerator

/-! Concrete Hamiltonian action weights at the original paper speed.
These are deterministic path identities; identification with a changed Brownian
law is a separate stochastic theorem. -/

@[expose] public section
open Set MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The energy term in the symmetric gradient-diffusion action. -/
def ginibreHamiltonianPathEnergy (n : ℕ) (α T : ℝ)
    (x : ℝ → Configuration n) : ℝ :=
  (α / (4 * (n : ℝ)^2)) *
    ∫ s in (0 : ℝ)..T, ginibreHamiltonianGradientNormSq n (x s)

/-- Literal endpoint and energy action with the paper's diffusivity `α/n²`. -/
def ginibreHamiltonianGradientPathWeight (n : ℕ) (α T : ℝ)
    (x : ℝ → Configuration n) : ℝ :=
  Real.exp (-(ginibreHamiltonian n (x 0) + ginibreHamiltonian n (x T))/2 +
    2*α*T - ginibreHamiltonianPathEnergy n α T x)

theorem ginibreHamiltonianPathEnergy_reverse (n : ℕ) (α T : ℝ)
    (x : ℝ → Configuration n) :
    ginibreHamiltonianPathEnergy n α T (fun s => x (T-s)) =
      ginibreHamiltonianPathEnergy n α T x := by
  unfold ginibreHamiltonianPathEnergy
  congr 1
  have h := intervalIntegral.integral_comp_sub_left
    (fun s => ginibreHamiltonianGradientNormSq n (x s)) (a := 0) (b := T) T
  simpa using h

theorem ginibreHamiltonianGradientPathWeight_reverse (n : ℕ) (α T : ℝ)
    (x : ℝ → Configuration n) :
    ginibreHamiltonianGradientPathWeight n α T (fun s => x (T-s)) =
      ginibreHamiltonianGradientPathWeight n α T x := by
  unfold ginibreHamiltonianGradientPathWeight
  rw [ginibreHamiltonianPathEnergy_reverse]
  simp only [sub_zero, sub_self]
  congr 1
  ring

theorem ginibreHamiltonianGradientPathWeight_pos (n : ℕ) (α T : ℝ)
    (x : ℝ → Configuration n) :
    0 < ginibreHamiltonianGradientPathWeight n α T x :=
  Real.exp_pos _

theorem ginibreHamiltonianPathEnergy_nonneg (n : ℕ) (α T : ℝ)
    (hα : 0 ≤ α) (hT : 0 ≤ T) (x : ℝ → Configuration n) :
    0 ≤ ginibreHamiltonianPathEnergy n α T x := by
  exact mul_nonneg (div_nonneg hα (mul_nonneg (by norm_num) (sq_nonneg _)))
    (intervalIntegral.integral_nonneg_of_forall hT
      (fun s => ginibreHamiltonianGradientNormSq_nonneg n (x s)))

/-- The endpoint density is the genuine Ginibre Gibbs weight, rather than an
abstract replacement potential. -/
theorem ginibreHamiltonianGradientPathWeight_sq (n : ℕ) (α T : ℝ)
    (x : ℝ → Configuration n) (h0 : CollisionFree (x 0))
    (hT : CollisionFree (x T)) :
    (ginibreHamiltonianGradientPathWeight n α T x)^2 =
      ginibreWeight n (x 0) * ginibreWeight n (x T) *
        Real.exp (4*α*T - 2*ginibreHamiltonianPathEnergy n α T x) := by
  rw [← ginibreHamiltonian_exp_neg (x 0) h0,
    ← ginibreHamiltonian_exp_neg (x T) hT]
  unfold ginibreHamiltonianGradientPathWeight
  rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The local action coefficient follows from the actual constant Hamiltonian
Laplacian, with no curvature certificate. -/
theorem ginibreHamiltonian_gradientAction_coefficient {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    (α / (2*(n : ℝ)^2)) * configurationLaplacian (ginibreHamiltonian n) z -
      (α / (4*(n : ℝ)^2)) * ginibreHamiltonianGradientNormSq n z =
    2*α - (α / (4*(n : ℝ)^2)) * ginibreHamiltonianGradientNormSq n z := by
  rw [ginibreHamiltonian_laplacian z hz]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnR]
  ring

theorem ginibreHamiltonianGradientPathWeight_le_endpoint (n : ℕ) (α T : ℝ)
    (hα : 0 ≤ α) (hT : 0 ≤ T) (x : ℝ → Configuration n) :
    ginibreHamiltonianGradientPathWeight n α T x ≤
      Real.exp (-(ginibreHamiltonian n (x 0) + ginibreHamiltonian n (x T))/2 +
        2*α*T) := by
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (ginibreHamiltonianPathEnergy_nonneg n α T hα hT x)

end
end GinibrePoincare
