/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixGaussianH1LSI.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpatialCutoff

/-!
# Matrix Gaussian H 1 LSI

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixGaussian_lsi_C1_H1`, `matrixSpatialTruncation_L2_errors`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff NNReal
namespace GinibrePoincare
noncomputable section

/-- The product `A ↦ matrixSpatialCutoff n k A * F A` of `F` with the `k`-th spatial cutoff. -/
def matrixSpatialTruncation (n k : ℕ) (F : MatrixRealSpace n → ℝ) : MatrixRealSpace n → ℝ :=
  fun A => matrixSpatialCutoff n k A * F A

theorem matrixSpatialTruncation_contDiff (n k : ℕ) (F : MatrixRealSpace n → ℝ)
    (hF : ContDiff ℝ 1 F) : ContDiff ℝ 1 (matrixSpatialTruncation n k F) :=
  ((matrixSpatialCutoff_smooth n k).of_le (by simp)).mul hF

theorem matrixSpatialTruncation_compact (n k : ℕ) (F : MatrixRealSpace n → ℝ) :
    HasCompactSupport (matrixSpatialTruncation n k F) :=
  (matrixSpatialCutoff_compact n k).mul_right

theorem matrixSpatialTruncation_fderiv (n k : ℕ) (F : MatrixRealSpace n → ℝ)
    (hF : ContDiff ℝ 1 F) (A H : MatrixRealSpace n) :
    fderiv ℝ (matrixSpatialTruncation n k F) A H =
      fderiv ℝ (matrixSpatialCutoff n k) A H * F A +
        matrixSpatialCutoff n k A * fderiv ℝ F A H := by
  have hd := ((matrixSpatialCutoff_smooth n k).differentiable (by simp) A).hasFDerivAt.mul
    (hF.differentiable (by norm_num) A).hasFDerivAt
  unfold matrixSpatialTruncation
  simpa [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, mul_comm, add_comm, Pi.mul_def] using
      congrArg (fun L : MatrixRealSpace n →L[ℝ] ℝ => L H) hd.fderiv

theorem matrixSpatialTruncation_limits (n : ℕ) (F : MatrixRealSpace n → ℝ)
    (hF : ContDiff ℝ 1 F) (A H : MatrixRealSpace n) :
    Tendsto (fun k => matrixSpatialTruncation n k F A) atTop (nhds (F A)) ∧
      Tendsto (fun k => fderiv ℝ (matrixSpatialTruncation n k F) A H)
        atTop (nhds (fderiv ℝ F A H)) := by
  constructor
  · simpa [matrixSpatialTruncation] using (matrixSpatialCutoff_tendsto n A).mul_const (F A)
  · simp_rw [matrixSpatialTruncation_fderiv n _ F hF A H]
    simpa using ((matrixSpatialCutoff_derivative_tendsto n A H).mul_const (F A)).add
      ((matrixSpatialCutoff_tendsto n A).mul_const (fderiv ℝ F A H))

theorem matrixSpatialTruncation_mass_tendsto (n : ℕ) (μ : Measure (MatrixRealSpace n))
    (F : MatrixRealSpace n → ℝ) (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ) :
    Tendsto (fun k => ∫ A, matrixSpatialTruncation n k F A ^ 2 ∂μ)
      atTop (nhds (∫ A, F A ^ 2 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun A => F A ^ 2)
    (fun k => ((matrixSpatialTruncation_contDiff n k F hF).continuous.pow 2).aestronglyMeasurable)
    hv.integrable_sq
  · intro k
    apply ae_of_all
    intro A
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨h0, h1⟩ := matrixSpatialCutoff_mem_unit n k A
    change (matrixSpatialCutoff n k A * F A) ^ 2 ≤ F A ^ 2
    have hc : matrixSpatialCutoff n k A ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (F A))]
  · exact ae_of_all _ fun A => ((matrixSpatialTruncation_limits n F hF A 0).1).pow 2

theorem matrixSpatialTruncation_direction_energy_tendsto (n : ℕ)
    (μ : Measure (MatrixRealSpace n)) (F : MatrixRealSpace n → ℝ)
    (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ) (H : MatrixRealSpace n)
    (hD : MemLp (fun A => fderiv ℝ F A H) 2 μ) :
    Tendsto (fun k => ∫ A, (fderiv ℝ (matrixSpatialTruncation n k F) A H) ^ 2 ∂μ)
      atTop (nhds (∫ A, (fderiv ℝ F A H) ^ 2 ∂μ)) := by
  obtain ⟨M, hM0, hM⟩ := matrixSpatialCutoff_derivative_bound n
  have hb (k : ℕ) (A : MatrixRealSpace n) :
      |fderiv ℝ (matrixSpatialCutoff n k) A H| ≤ M * ‖H‖ := by
    refine (hM k A H).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg H))
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  apply tendsto_integral_of_dominated_convergence
    (fun A => 2 * (M * ‖H‖) ^ 2 * F A ^ 2 + 2 * (fderiv ℝ F A H) ^ 2)
    (fun k => ((((matrixSpatialTruncation_contDiff n k F hF).continuous_fderiv
        one_ne_zero).clm_apply
      continuous_const).pow 2).aestronglyMeasurable)
    ((hv.integrable_sq.const_mul (2 * (M * ‖H‖) ^ 2)).add (hD.integrable_sq.const_mul 2))
  · intro k
    apply ae_of_all
    intro A
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (fderiv ℝ (matrixSpatialTruncation n k F) A H) ^ 2 ≤ _
    rw [matrixSpatialTruncation_fderiv n k F hF]
    obtain ⟨hc0, hc1⟩ := matrixSpatialCutoff_mem_unit n k A
    have hc2 : matrixSpatialCutoff n k A ^ 2 ≤ 1 := by nlinarith
    have hd2 : (fderiv ℝ (matrixSpatialCutoff n k) A H) ^ 2 ≤ (M * ‖H‖) ^ 2 := by
      have hh := hb k A
      nlinarith [sq_abs (fderiv ℝ (matrixSpatialCutoff n k) A H),
        abs_nonneg (fderiv ℝ (matrixSpatialCutoff n k) A H), mul_nonneg hM0 (norm_nonneg H)]
    have hx := mul_le_mul_of_nonneg_right hd2 (sq_nonneg (F A))
    have hy := mul_le_mul_of_nonneg_right hc2 (sq_nonneg (fderiv ℝ F A H))
    nlinarith [sq_nonneg (fderiv ℝ (matrixSpatialCutoff n k) A H * F A -
      matrixSpatialCutoff n k A * fderiv ℝ F A H)]
  · exact ae_of_all _ fun A => ((matrixSpatialTruncation_limits n F hF A H).2).pow 2

theorem matrixSpatialTruncation_energy_tendsto (n : ℕ)
    (μ : Measure (MatrixRealSpace n)) [IsProbabilityMeasure μ]
    (F : MatrixRealSpace n → ℝ) (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ)
    {ι : Type*} [Fintype ι] (d : ι → MatrixRealSpace n)
    (hD : ∀ i, MemLp (fun A => fderiv ℝ F A (d i)) 2 μ) :
    Tendsto (fun k => ∫ A, directionalEnergy d (matrixSpatialTruncation n k F) A ∂μ)
      atTop (nhds (∫ A, directionalEnergy d F A ∂μ)) := by
  classical
  have hcut (k : ℕ) (i : ι) : Integrable
      (fun A => (fderiv ℝ (matrixSpatialTruncation n k F) A (d i)) ^ 2) μ := by
    have hc := (matrixSpatialTruncation_compact n k F).fderiv_apply (𝕜 := ℝ) (d i)
    have hc2 : HasCompactSupport (fun A => (fderiv ℝ (matrixSpatialTruncation n k F) A (d i)) ^ 2)
        := by
      simpa only [pow_two, Pi.mul_def] using
        (hc.mul_right (f' := fun A => fderiv ℝ (matrixSpatialTruncation n k F) A (d i)))
    exact ((((matrixSpatialTruncation_contDiff n k F hF).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).pow 2).integrable_of_hasCompactSupport hc2
  have he (k : ℕ) : (∫ A, directionalEnergy d (matrixSpatialTruncation n k F) A ∂μ) =
      ∑ i, ∫ A, (fderiv ℝ (matrixSpatialTruncation n k F) A (d i)) ^ 2 ∂μ := by
    unfold directionalEnergy
    exact MeasureTheory.integral_finsetSum _ fun i _ => hcut k i
  have hf : (∫ A, directionalEnergy d F A ∂μ) =
      ∑ i, ∫ A, (fderiv ℝ F A (d i)) ^ 2 ∂μ := by
    unfold directionalEnergy
    exact MeasureTheory.integral_finsetSum _ fun i _ => (hD i).integrable_sq
  simp_rw [he]
  rw [hf]
  exact tendsto_finsetSum _ fun i _ =>
    matrixSpatialTruncation_direction_energy_tendsto n μ F hF hv (d i) (hD i)

/-- The sharp matrix Gaussian LSI for genuine C¹ H¹ observables, with no support
or global Lipschitz restriction. Both L² requirements concern the actual derivatives. -/
theorem matrixGaussian_lsi_C1_H1 (n : ℕ) (hn : 0 < n)
    (F : MatrixRealSpace n → ℝ) (hF : ContDiff ℝ 1 F)
    (hv : MemLp F 2 (matrixGaussianMeasure n))
    (hD : ∀ p : MatrixRealIndex n, MemLp
      (fun A => fderiv ℝ F A (matrixRealCoordinates n (Pi.single p 1))) 2
      (matrixGaussianMeasure n)) :
    squareEntropy (matrixGaussianMeasure n) F ≤
      (1 / (n : ℝ)) * ∫ A, matrixRealGradientEnergy n F A ∂matrixGaussianMeasure n := by
  let μ : Measure (MatrixRealSpace n) := matrixGaussianMeasure n
  let : IsProbabilityMeasure μ := matrixGaussianMeasure_isProbability n
  let d := fun p : MatrixRealIndex n => matrixRealCoordinates n (Pi.single p 1)
  let g := fun k => matrixSpatialTruncation n k F
  have hg (k : ℕ) := matrixSpatialTruncation_contDiff n k F hF
  have hc (k : ℕ) := matrixSpatialTruncation_compact n k F
  have hineq (k : ℕ) : squareEntropy μ (g k) ≤
      (1 / (n : ℝ)) * ∫ A, directionalEnergy d (g k) A ∂μ := by
    obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hc k) (hg k) one_ne_zero
    exact matrixGaussian_lsi_compactLipschitz n hn _ hK (hc k)
  have henergy := matrixSpatialTruncation_energy_tendsto n μ F hF hv d hD
  have hlim := squareEntropy_le_of_ae_tendsto μ g F
    (fun k => (1 / (n : ℝ)) * ∫ A, directionalEnergy d (g k) A ∂μ)
    ((1 / (n : ℝ)) * ∫ A, directionalEnergy d F A ∂μ)
    (fun k => (hg k).continuous.aestronglyMeasurable) hF.continuous.aestronglyMeasurable
    (fun k => (continuous_square_mul_log (hg k).continuous).integrable_of_hasCompactSupport
      (compactSupport_square_mul_log (hc k)))
    (ae_of_all _ fun A => (matrixSpatialTruncation_limits n F hF A 0).1)
    (matrixSpatialTruncation_mass_tendsto n μ F hF hv)
    (henergy.const_mul (1 / (n : ℝ))) hineq
  exact hlim.2

theorem matrixSpatialTruncation_L2_errors (n : ℕ) (μ : Measure (MatrixRealSpace n))
    (F : MatrixRealSpace n → ℝ) (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ)
    (H : MatrixRealSpace n) (hD : MemLp (fun A => fderiv ℝ F A H) 2 μ) :
    Tendsto (fun k => ∫ A, (matrixSpatialTruncation n k F A - F A) ^ 2 ∂μ)
      atTop (nhds 0) ∧
    Tendsto (fun k => ∫ A,
      (fderiv ℝ (matrixSpatialTruncation n k F) A H - fderiv ℝ F A H) ^ 2 ∂μ)
      atTop (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := matrixSpatialCutoff_derivative_bound n
  have hb (k : ℕ) (A : MatrixRealSpace n) :
      |fderiv ℝ (matrixSpatialCutoff n k) A H| ≤ M * ‖H‖ := by
    refine (hM k A H).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg H))
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  constructor
  · have ht := tendsto_integral_of_dominated_convergence (fun A => F A ^ 2)
      (fun k => (((matrixSpatialTruncation_contDiff n k F hF).continuous.sub hF.continuous).pow
          2).aestronglyMeasurable)
      hv.integrable_sq (fun k => ae_of_all _ fun A => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change (matrixSpatialCutoff n k A * F A - F A) ^ 2 ≤ F A ^ 2
        obtain ⟨h0, h1⟩ := matrixSpatialCutoff_mem_unit n k A
        have hc : (matrixSpatialCutoff n k A - 1) ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (F A))])
      (ae_of_all _ fun A => by simpa using
        (((matrixSpatialTruncation_limits n F hF A H).1.sub_const (F A)).pow 2))
    simpa using ht
  · have ht := tendsto_integral_of_dominated_convergence
      (fun A => 2 * (M * ‖H‖) ^ 2 * F A ^ 2 + 2 * (fderiv ℝ F A H) ^ 2)
      (fun k => (((((matrixSpatialTruncation_contDiff n k F hF).continuous_fderiv
          one_ne_zero).clm_apply
        continuous_const).sub ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)).pow
            2).aestronglyMeasurable)
      ((hv.integrable_sq.const_mul (2 * (M * ‖H‖) ^ 2)).add (hD.integrable_sq.const_mul 2))
      (fun k => ae_of_all _ fun A => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change (fderiv ℝ (matrixSpatialTruncation n k F) A H - fderiv ℝ F A H) ^ 2 ≤ _
        rw [matrixSpatialTruncation_fderiv n k F hF]
        obtain ⟨hc0, hc1⟩ := matrixSpatialCutoff_mem_unit n k A
        have hc2 : (matrixSpatialCutoff n k A - 1) ^ 2 ≤ 1 := by nlinarith
        have hd2 : (fderiv ℝ (matrixSpatialCutoff n k) A H) ^ 2 ≤ (M * ‖H‖) ^ 2 := by
          have hh := hb k A
          nlinarith [sq_abs (fderiv ℝ (matrixSpatialCutoff n k) A H),
            abs_nonneg (fderiv ℝ (matrixSpatialCutoff n k) A H), mul_nonneg hM0 (norm_nonneg H)]
        have hx := mul_le_mul_of_nonneg_right hd2 (sq_nonneg (F A))
        have hy := mul_le_mul_of_nonneg_right hc2 (sq_nonneg (fderiv ℝ F A H))
        nlinarith [sq_nonneg (fderiv ℝ (matrixSpatialCutoff n k) A H * F A -
          (matrixSpatialCutoff n k A - 1) * fderiv ℝ F A H)])
      (ae_of_all _ fun A => by simpa using
        (((matrixSpatialTruncation_limits n F hF A H).2.sub_const (fderiv ℝ F A H)).pow 2))
    simpa using ht

end
end GinibrePoincare
