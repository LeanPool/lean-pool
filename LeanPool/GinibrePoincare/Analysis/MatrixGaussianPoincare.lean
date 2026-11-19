/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixGaussianPoincare.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixGaussianH1Closure
public import LeanPool.GinibrePoincare.Analysis.SquareEntropyLinearization

/-! # Sharp Gaussian matrix Poincaré inequality

The actual Gaussian matrix LSI is linearized at constants, with the logarithmic
integrals differentiated internally. Closure gives the full matrix H¹ domain.
This argument does not use the Ginibre symmetric Poincaré inequality.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Sharp ordinary Gaussian matrix Poincaré inequality on the compact C¹ core. -/
theorem matrixGaussian_poincare_compactC1 (n : ℕ) (hn : 0 < n)
    (F : MatrixRealSpace n → ℝ) (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) :
    (∫ A, F A^2 ∂matrixGaussianMeasure n) - (∫ A, F A ∂matrixGaussianMeasure n)^2 ≤
      (1/(2*(n : ℝ))) * ∫ A, matrixRealGradientEnergy n F A ∂matrixGaussianMeasure n := by
  let μ : Measure (MatrixRealSpace n) := matrixGaussianMeasure n
  let : IsProbabilityMeasure μ := matrixGaussianMeasure_isProbability n
  have hv : MemLp F 2 μ := hF.continuous.memLp_of_hasCompactSupport hc
  have hd (i : MatrixRealIndex n) : MemLp
      (fun A => fderiv ℝ F A (matrixRealCoordinates n (Pi.single i 1))) 2 μ :=
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) _)
  obtain ⟨M, hM⟩ := hF.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hMb (A : MatrixRealSpace n) : |F A| ≤ M := by
    simpa [Real.norm_eq_abs] using hM (Set.mem_range_self A)
  have hM0 : 0 ≤ M := (abs_nonneg (F 0)).trans (hMb 0)
  have hlin := squareEntropy_affine_bound_variance μ F hF.continuous.measurable M hM0 hMb
    ((1/(n : ℝ))*∫ A, matrixRealGradientEnergy n F A ∂μ) (by
      intro t
      have hft : ContDiff ℝ 1 (fun A => 1+t*F A) := contDiff_const.add (contDiff_const.mul hF)
      have hvt : MemLp (fun A => 1+t*F A) 2 μ := (memLp_const (1 : ℝ)).add (hv.const_mul t)
      have hdt (A H : MatrixRealSpace n) :
          fderiv ℝ (fun A => 1+t*F A) A H = t * fderiv ℝ F A H := by
        rw [fderiv_const_add, fderiv_const_mul (hF.differentiable (by norm_num) A)]
        rfl
      have hdpt (i : MatrixRealIndex n) : MemLp
          (fun A => fderiv ℝ (fun A => 1+t*F A) A (matrixRealCoordinates n (Pi.single i 1))) 2
            μ := by
        simp_rw [hdt]
        exact (hd i).const_mul t
      have he (A : MatrixRealSpace n) : matrixRealGradientEnergy n (fun A => 1+t*F A) A =
          t^2 * matrixRealGradientEnergy n F A := by
        unfold matrixRealGradientEnergy directionalEnergy
        simp_rw [hdt, mul_pow]
        rw [Finset.mul_sum]
      have hh : squareEntropy μ (fun A => 1+t*F A) ≤
          (1 / (n : ℝ)) * ∫ A, matrixRealGradientEnergy n (fun A => 1+t*F A) A ∂μ :=
        matrixGaussian_lsi_C1_H1 n hn _ hft hvt hdpt
      simp_rw [he] at hh
      rw [integral_const_mul] at hh
      convert hh using 1
      ring)
  have h1 : (∫ A, F A ^ 2 ∂matrixGaussianMeasure n) = ∫ A, F A ^ 2 ∂μ := rfl
  have h2 : (∫ A, F A ∂matrixGaussianMeasure n) = ∫ A, F A ∂μ := rfl
  have h3 : (∫ A, matrixRealGradientEnergy n F A ∂matrixGaussianMeasure n) =
      ∫ A, matrixRealGradientEnergy n F A ∂μ := rfl
  rw [h1, h2, h3]
  convert hlin using 1
  ring

/-- The normalized constant in the actual matrix Gaussian L² space. -/
def matrixGaussianOneL2 (n : ℕ) : MatrixGaussianL2 n := by
  letI := matrixGaussianMeasure_isProbability n
  exact (memLp_const (1 : ℝ)).toLp (fun _ => 1)

theorem matrixGaussianOneL2_ae (n : ℕ) :
    (matrixGaussianOneL2 n : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n] fun _ => 1 := by
  let := matrixGaussianMeasure_isProbability n
  exact (memLp_const (1 : ℝ)).coeFn_toLp

/-- Actual matrix Gaussian variance as a continuous quadratic expression in L². -/
def matrixGaussianL2Variance (n : ℕ) (u : MatrixGaussianL2 n) : ℝ :=
  ‖u‖^2 - (inner ℝ (matrixGaussianOneL2 n) u)^2

theorem matrixGaussianL2Variance_integral (n : ℕ) (u : MatrixGaussianL2 n) :
    matrixGaussianL2Variance n u = (∫ A, u A^2 ∂matrixGaussianMeasure n) -
      (∫ A, u A ∂matrixGaussianMeasure n)^2 := by
  unfold matrixGaussianL2Variance
  rw [← integral_square_eq_L2_norm_sq, L2.inner_def]
  congr 2
  apply integral_congr_ae
  filter_upwards [matrixGaussianOneL2_ae n] with A hA
  simp [hA]

/-- The sharp Gaussian Poincaré inequality on the full actual matrix H¹ closure. -/
theorem matrixGaussianH1Completion_poincare (n : ℕ) (hn : 0 < n)
    (p : MatrixGaussianSobolevPair n) (hp : p ∈ matrixGaussianH1Completion n) :
    matrixGaussianL2Variance n p.1 ≤ (1/(2*(n : ℝ)))*matrixGaussianSobolevEnergy n p := by
  have hclosed : IsClosed {p : MatrixGaussianSobolevPair n |
      matrixGaussianL2Variance n p.1 ≤ (1/(2*(n : ℝ)))*matrixGaussianSobolevEnergy n p} := by
    apply isClosed_le
    · exact continuous_fst.norm.pow 2 |>.sub ((continuous_const.inner continuous_fst).pow 2)
    · exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp continuous_snd).norm.pow 2)
  apply closure_minimal ?_ hclosed hp
  intro q hq
  obtain ⟨F, hF, hc, hv, hd⟩ := hq
  have he : matrixGaussianSobolevEnergy n q =
      ∫ A, matrixRealGradientEnergy n F A ∂matrixGaussianMeasure n := by
    unfold matrixGaussianSobolevEnergy matrixRealGradientEnergy directionalEnergy
    simp_rw [← integral_square_eq_L2_norm_sq]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      apply integral_congr_ae
      filter_upwards [hd i] with A hA
      simp [hA]
    · intro i hi
      exact ((Lp.memLp (q.2 i)).ae_eq (hd i)).integrable_sq
  change matrixGaussianL2Variance n q.1 ≤ _
  rw [matrixGaussianL2Variance_integral, he]
  have hv2 : (fun A => q.1 A^2) =ᵐ[matrixGaussianMeasure n] (fun A => F A^2) :=
    hv.mono fun A hA => congrArg (fun v : ℝ => v^2) hA
  rw [integral_congr_ae hv, integral_congr_ae hv2]
  exact matrixGaussian_poincare_compactC1 n hn F hF hc

end
end GinibrePoincare
