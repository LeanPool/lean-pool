/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpatialCutoff.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixGaussianLSI

/-!
# Matrix spatial cutoff

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSpatialCutoff_compact`, `matrixSpatialCutoff_mem_unit`,
`matrixSpatialCutoff_tendsto`, `matrixSpatialCutoff_derivative_tendsto`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff NNReal
namespace GinibrePoincare
noncomputable section

/-- `n × n` complex matrices as coordinate functions, used as a real normed space. -/
abbrev MatrixRealSpace (n : ℕ) := Fin n → Fin n → ℂ

/-- A smooth bump centred at `0`, equal to `1` on the ball of radius `1` and supported in the
ball of radius `2`. -/
def matrixSpatialBump (n : ℕ) : ContDiffBump (0 : MatrixRealSpace n) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The `k`-th spatial cutoff `A ↦ matrixSpatialBump n (A / (k + 1))`. -/
def matrixSpatialCutoff (n k : ℕ) (A : MatrixRealSpace n) : ℝ :=
  matrixSpatialBump n (((k : ℝ) + 1)⁻¹ • A)

theorem matrixSpatialCutoff_smooth (n k : ℕ) : ContDiff ℝ ∞ (matrixSpatialCutoff n k) :=
  (matrixSpatialBump n).contDiff.comp (by fun_prop)

theorem matrixSpatialCutoff_compact (n k : ℕ) : HasCompactSupport (matrixSpatialCutoff n k) := by
  exact (matrixSpatialBump n).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero (((k : ℝ) + 1)⁻¹) (inv_ne_zero (by positivity)))

theorem matrixSpatialCutoff_mem_unit (n k : ℕ) (A : MatrixRealSpace n) :
    0 ≤ matrixSpatialCutoff n k A ∧ matrixSpatialCutoff n k A ≤ 1 :=
  ⟨(matrixSpatialBump n).nonneg, (matrixSpatialBump n).le_one⟩

theorem matrixSpatialCutoff_tendsto (n : ℕ) (A : MatrixRealSpace n) :
    Tendsto (fun k => matrixSpatialCutoff n k A) atTop (nhds 1) := by
  have hi : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hx := hi.smul_const A
  have hz : matrixSpatialBump n (0 : MatrixRealSpace n) = 1 :=
    (matrixSpatialBump n).one_of_mem_closedBall (by simp [matrixSpatialBump])
  simpa [matrixSpatialCutoff, hz, Function.comp_def] using
    ((matrixSpatialBump n).continuous.continuousAt.tendsto.comp hx)

theorem matrixSpatialCutoff_fderiv (n k : ℕ) (A H : MatrixRealSpace n) :
    fderiv ℝ (matrixSpatialCutoff n k) A H =
      ((k : ℝ) + 1)⁻¹ * fderiv ℝ (matrixSpatialBump n : MatrixRealSpace n → ℝ)
        (((k : ℝ) + 1)⁻¹ • A) H := by
  have hd := (((matrixSpatialBump n).contDiff (n := 1)).differentiable (by norm_num)
    (((k : ℝ) + 1)⁻¹ • A)).hasFDerivAt.comp A
      ((hasFDerivAt_id A).const_smul (((k : ℝ) + 1)⁻¹))
  unfold matrixSpatialCutoff
  simpa [matrixSpatialCutoff, Function.comp_def, ContinuousLinearMap.comp_apply,
    map_smul, smul_eq_mul] using congrArg (fun L : MatrixRealSpace n →L[ℝ] ℝ => L H) hd.fderiv

theorem matrixSpatialCutoff_derivative_bound (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k (A H : MatrixRealSpace n),
      |fderiv ℝ (matrixSpatialCutoff n k) A H| ≤ M / ((k : ℝ) + 1) * ‖H‖ := by
  obtain ⟨M, hM⟩ := ((matrixSpatialBump n).contDiff (n := 1)).continuous_fderiv one_ne_zero
    |>.bounded_above_of_compact_support ((matrixSpatialBump n).hasCompactSupport.fderiv ℝ)
  refine ⟨M, (norm_nonneg _).trans (hM 0), ?_⟩
  intro k A H
  rw [matrixSpatialCutoff_fderiv, abs_mul, abs_of_nonneg (by positivity)]
  have hnorm := (fderiv ℝ (matrixSpatialBump n : MatrixRealSpace n → ℝ)
    (((k : ℝ) + 1)⁻¹ • A)).le_opNorm H
  have hh : |fderiv ℝ (matrixSpatialBump n : MatrixRealSpace n → ℝ)
      (((k : ℝ) + 1)⁻¹ • A) H| ≤ M * ‖H‖ :=
    hnorm.trans (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg H))
  calc
    _ ≤ ((k : ℝ) + 1)⁻¹ * (M * ‖H‖) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

theorem matrixSpatialCutoff_derivative_tendsto (n : ℕ) (A H : MatrixRealSpace n) :
    Tendsto (fun k => fderiv ℝ (matrixSpatialCutoff n k) A H) atTop (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := matrixSpatialCutoff_derivative_bound n
  have hi : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun k => by simpa using hM k A H)
  simpa [div_eq_mul_inv] using (hi.const_mul M).mul_const ‖H‖

end
end GinibrePoincare
