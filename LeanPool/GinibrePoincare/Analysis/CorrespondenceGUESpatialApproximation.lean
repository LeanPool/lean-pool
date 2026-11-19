/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUESpatialApproximation.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUERealLSI
/-!
# Correspondence GUE spatial approximation

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueSpatialTruncation_mass_tendsto`, `gueSpatialTruncation_energy_tendsto`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- The bounded spatial cutoff `bakryBoundedSpatialCutoff` on `EuclideanSpace ℝ (Fin n)`. -/
abbrev gueSpatialCutoff (n k : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  bakryBoundedSpatialCutoff (EuclideanSpace ℝ (Fin n)) k
/-- Smoothness of `gueSpatialCutoff n k` (`bakryBoundedSpatialCutoff_smooth`). -/
abbrev gueSpatialCutoffSmooth (n k : ℕ) := bakryBoundedSpatialCutoff_smooth (EuclideanSpace ℝ (Fin
    n)) k
/-- Compact support of `gueSpatialCutoff n k` (`bakryBoundedSpatialCutoff_compact`). -/
abbrev gueSpatialCutoffCompact (n k : ℕ) := bakryBoundedSpatialCutoff_compact (EuclideanSpace ℝ
    (Fin n)) k
/-- The limit statement `bakryBoundedSpatialCutoff_tendsto` for `gueSpatialCutoff n`. -/
abbrev gueSpatialCutoffTendsto (n : ℕ) := bakryBoundedSpatialCutoff_tendsto (EuclideanSpace ℝ (Fin
    n))
/-- The unit-interval bound `bakryBoundedSpatialCutoff_mem_unit` for `gueSpatialCutoff n k`. -/
abbrev gueSpatialCutoffMemUnit (n k : ℕ) := bakryBoundedSpatialCutoff_mem_unit (EuclideanSpace ℝ
    (Fin n)) k
/-- The derivative bound `bakryBoundedSpatialCutoff_derivative_bound` for `gueSpatialCutoff n`. -/
abbrev gueSpatialCutoffDerivativeBound (n : ℕ) := bakryBoundedSpatialCutoff_derivative_bound
    (EuclideanSpace ℝ (Fin n))

theorem gueSpatialCutoff_derivative_tendsto (n : ℕ) (A H : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => fderiv ℝ (gueSpatialCutoff n k) A H) atTop (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := gueSpatialCutoffDerivativeBound n
  have hi : Tendsto (fun k : ℕ => ((k : ℝ)+1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun k => by simpa using hM k A H)
  simpa [div_eq_mul_inv] using (hi.const_mul M).mul_const ‖H‖

/-- The spatial truncation `A ↦ gueSpatialCutoff n k A * F A`. -/
def gueSpatialTruncation (n k : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ (Fin n) → ℝ
    :=
  fun A => gueSpatialCutoff n k A * F A

theorem gueSpatialTruncation_contDiff (n k : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 1 F) : ContDiff ℝ 1 (gueSpatialTruncation n k F) :=
  ((gueSpatialCutoffSmooth n k).of_le (by simp)).mul hF

theorem gueSpatialTruncation_compact (n k : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ) :
    HasCompactSupport (gueSpatialTruncation n k F) :=
  (gueSpatialCutoffCompact n k).mul_right

theorem gueSpatialTruncation_fderiv (n k : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 1 F) (A H : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (gueSpatialTruncation n k F) A H =
      fderiv ℝ (gueSpatialCutoff n k) A H * F A +
        gueSpatialCutoff n k A * fderiv ℝ F A H := by
  have hd := ((gueSpatialCutoffSmooth n k).differentiable (by simp) A).hasFDerivAt.mul
    (hF.differentiable (by norm_num) A).hasFDerivAt
  unfold gueSpatialTruncation
  simpa [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, mul_comm, add_comm, Pi.mul_def] using
      congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L H) hd.fderiv

theorem gueSpatialTruncation_limits (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 1 F) (A H : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => gueSpatialTruncation n k F A) atTop (nhds (F A)) ∧
      Tendsto (fun k => fderiv ℝ (gueSpatialTruncation n k F) A H)
        atTop (nhds (fderiv ℝ F A H)) := by
  constructor
  · simpa [gueSpatialTruncation] using (gueSpatialCutoffTendsto n A).mul_const (F A)
  · simp_rw [gueSpatialTruncation_fderiv n _ F hF A H]
    simpa using ((gueSpatialCutoff_derivative_tendsto n A H).mul_const (F A)).add
      ((gueSpatialCutoffTendsto n A).mul_const (fderiv ℝ F A H))

theorem gueSpatialTruncation_mass_tendsto (n : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ) :
    Tendsto (fun k => ∫ A, gueSpatialTruncation n k F A ^ 2 ∂μ)
      atTop (nhds (∫ A, F A ^ 2 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun A => F A ^ 2)
    (fun k => ((gueSpatialTruncation_contDiff n k F hF).continuous.pow 2).aestronglyMeasurable)
    hv.integrable_sq
  · intro k
    apply ae_of_all
    intro A
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨h0, h1⟩ := gueSpatialCutoffMemUnit n k A
    change (gueSpatialCutoff n k A * F A) ^ 2 ≤ F A ^ 2
    have hc : gueSpatialCutoff n k A ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (F A))]
  · exact ae_of_all _ fun A => ((gueSpatialTruncation_limits n F hF A 0).1).pow 2

theorem gueSpatialTruncation_direction_energy_tendsto (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ) (H : EuclideanSpace ℝ (Fin n))
    (hD : MemLp (fun A => fderiv ℝ F A H) 2 μ) :
    Tendsto (fun k => ∫ A, (fderiv ℝ (gueSpatialTruncation n k F) A H) ^ 2 ∂μ)
      atTop (nhds (∫ A, (fderiv ℝ F A H) ^ 2 ∂μ)) := by
  obtain ⟨M, hM0, hM⟩ := gueSpatialCutoffDerivativeBound n
  have hb (k : ℕ) (A : EuclideanSpace ℝ (Fin n)) :
      |fderiv ℝ (gueSpatialCutoff n k) A H| ≤ M * ‖H‖ := by
    refine (hM k A H).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg H))
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  apply tendsto_integral_of_dominated_convergence
    (fun A => 2 * (M * ‖H‖) ^ 2 * F A ^ 2 + 2 * (fderiv ℝ F A H) ^ 2)
    (fun k => ((((gueSpatialTruncation_contDiff n k F hF).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).pow 2).aestronglyMeasurable)
    ((hv.integrable_sq.const_mul (2 * (M * ‖H‖) ^ 2)).add (hD.integrable_sq.const_mul 2))
  · intro k
    apply ae_of_all
    intro A
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (fderiv ℝ (gueSpatialTruncation n k F) A H) ^ 2 ≤ _
    rw [gueSpatialTruncation_fderiv n k F hF]
    obtain ⟨hc0, hc1⟩ := gueSpatialCutoffMemUnit n k A
    have hc2 : gueSpatialCutoff n k A ^ 2 ≤ 1 := by nlinarith
    have hd2 : (fderiv ℝ (gueSpatialCutoff n k) A H) ^ 2 ≤ (M * ‖H‖) ^ 2 := by
      have hh := hb k A
      nlinarith [sq_abs (fderiv ℝ (gueSpatialCutoff n k) A H),
        abs_nonneg (fderiv ℝ (gueSpatialCutoff n k) A H), mul_nonneg hM0 (norm_nonneg H)]
    have hx := mul_le_mul_of_nonneg_right hd2 (sq_nonneg (F A))
    have hy := mul_le_mul_of_nonneg_right hc2 (sq_nonneg (fderiv ℝ F A H))
    nlinarith [sq_nonneg (fderiv ℝ (gueSpatialCutoff n k) A H * F A -
      gueSpatialCutoff n k A * fderiv ℝ F A H)]
  · exact ae_of_all _ fun A => ((gueSpatialTruncation_limits n F hF A H).2).pow 2

theorem gueSpatialTruncation_energy_tendsto (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ)
    {ι : Type*} [Fintype ι] (d : ι → EuclideanSpace ℝ (Fin n))
    (hD : ∀ i, MemLp (fun A => fderiv ℝ F A (d i)) 2 μ) :
    Tendsto (fun k => ∫ A, directionalEnergy d (gueSpatialTruncation n k F) A ∂μ)
      atTop (nhds (∫ A, directionalEnergy d F A ∂μ)) := by
  classical
  have hcut (k : ℕ) (i : ι) : Integrable
      (fun A => (fderiv ℝ (gueSpatialTruncation n k F) A (d i)) ^ 2) μ := by
    have hc := (gueSpatialTruncation_compact n k F).fderiv_apply (𝕜 := ℝ) (d i)
    have hc2 : HasCompactSupport (fun A => (fderiv ℝ (gueSpatialTruncation n k F) A (d i)) ^ 2) :=
        by
      simpa only [pow_two, Pi.mul_def] using
        (hc.mul_right (f' := fun A => fderiv ℝ (gueSpatialTruncation n k F) A (d i)))
    exact ((((gueSpatialTruncation_contDiff n k F hF).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).pow 2).integrable_of_hasCompactSupport hc2
  have he (k : ℕ) : (∫ A, directionalEnergy d (gueSpatialTruncation n k F) A ∂μ) =
      ∑ i, ∫ A, (fderiv ℝ (gueSpatialTruncation n k F) A (d i)) ^ 2 ∂μ := by
    unfold directionalEnergy
    exact MeasureTheory.integral_finsetSum _ fun i _ => hcut k i
  have hf : (∫ A, directionalEnergy d F A ∂μ) =
      ∑ i, ∫ A, (fderiv ℝ F A (d i)) ^ 2 ∂μ := by
    unfold directionalEnergy
    exact MeasureTheory.integral_finsetSum _ fun i _ => (hD i).integrable_sq
  simp_rw [he]
  rw [hf]
  exact tendsto_finsetSum _ fun i _ =>
    gueSpatialTruncation_direction_energy_tendsto n μ F hF hv (d i) (hD i)

end
end GinibrePoincare
