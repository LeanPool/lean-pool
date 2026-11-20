/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUESymmetricSpatialApproximation.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUESymmetricCutoff
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUESymmetricH1Closure
/-!
# Correspondence GUE symmetric spatial approximation

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueSymmetricSpatialTruncation_mass_tendsto`,
`gueSymmetricSpatialTruncation_energy_tendsto`, `gueSymmetricSpatialTruncation_L2_errors`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
/-- The symmetric spatial truncation `A ↦ gueSymmetricSpatialCutoff n k A * F A`. -/
def gueSymmetricSpatialTruncation (n k : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ
    (Fin n) → ℝ :=
  fun A => gueSymmetricSpatialCutoff n k A * F A

theorem gueSymmetricSpatialTruncation_contDiff (n k : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 1 F) : ContDiff ℝ 1 (gueSymmetricSpatialTruncation n k F) :=
  ((gueSymmetricSpatialCutoff_smooth n k).of_le (by simp)).mul hF

theorem gueSymmetricSpatialTruncation_compact (n k : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ) :
    HasCompactSupport (gueSymmetricSpatialTruncation n k F) :=
  (gueSymmetricSpatialCutoff_compact n k).mul_right

theorem gueSymmetricSpatialTruncation_fderiv (n k : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 1 F) (A H : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (gueSymmetricSpatialTruncation n k F) A H =
      fderiv ℝ (gueSymmetricSpatialCutoff n k) A H * F A +
        gueSymmetricSpatialCutoff n k A * fderiv ℝ F A H := by
  have hd := ((gueSymmetricSpatialCutoff_smooth n k).differentiable (by simp) A).hasFDerivAt.mul
    (hF.differentiable (by norm_num) A).hasFDerivAt
  unfold gueSymmetricSpatialTruncation
  simpa [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, mul_comm, add_comm, Pi.mul_def] using
      congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L H) hd.fderiv

theorem gueSymmetricSpatialTruncation_limits (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 1 F) (A H : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => gueSymmetricSpatialTruncation n k F A) atTop (nhds (F A)) ∧
      Tendsto (fun k => fderiv ℝ (gueSymmetricSpatialTruncation n k F) A H)
        atTop (nhds (fderiv ℝ F A H)) := by
  constructor
  · simpa [gueSymmetricSpatialTruncation] using (gueSymmetricSpatialCutoff_tendsto n A).mul_const (F
      A)
  · simp_rw [gueSymmetricSpatialTruncation_fderiv n _ F hF A H]
    simpa using ((gueSymmetricSpatialCutoff_derivative_tendsto n A H).mul_const (F A)).add
      ((gueSymmetricSpatialCutoff_tendsto n A).mul_const (fderiv ℝ F A H))

theorem gueSymmetricSpatialTruncation_mass_tendsto (n : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ) :
    Tendsto (fun k => ∫ A, gueSymmetricSpatialTruncation n k F A ^ 2 ∂μ)
      atTop (nhds (∫ A, F A ^ 2 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun A => F A ^ 2)
    (fun k => ((gueSymmetricSpatialTruncation_contDiff n k F hF).continuous.pow
        2).aestronglyMeasurable)
    hv.integrable_sq
  · intro k
    apply ae_of_all
    intro A
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨h0, h1⟩ := gueSymmetricSpatialCutoff_mem_unit n k A
    change (gueSymmetricSpatialCutoff n k A * F A) ^ 2 ≤ F A ^ 2
    have hc : gueSymmetricSpatialCutoff n k A ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (F A))]
  · exact ae_of_all _ fun A => ((gueSymmetricSpatialTruncation_limits n F hF A 0).1).pow 2

theorem gueSymmetricSpatialTruncation_direction_energy_tendsto (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ) (H : EuclideanSpace ℝ (Fin n))
    (hD : MemLp (fun A => fderiv ℝ F A H) 2 μ) :
    Tendsto (fun k => ∫ A, (fderiv ℝ (gueSymmetricSpatialTruncation n k F) A H) ^ 2 ∂μ)
      atTop (nhds (∫ A, (fderiv ℝ F A H) ^ 2 ∂μ)) := by
  obtain ⟨M, hM0, hM⟩ := gueSymmetricSpatialCutoff_derivative_bound n
  have hb (k : ℕ) (A : EuclideanSpace ℝ (Fin n)) :
      |fderiv ℝ (gueSymmetricSpatialCutoff n k) A H| ≤ M * ‖H‖ := by
    refine (hM k A H).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg H))
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  apply tendsto_integral_of_dominated_convergence
    (fun A => 2 * (M * ‖H‖) ^ 2 * F A ^ 2 + 2 * (fderiv ℝ F A H) ^ 2)
    (fun k => ((((gueSymmetricSpatialTruncation_contDiff n k F hF).continuous_fderiv
        one_ne_zero).clm_apply
      continuous_const).pow 2).aestronglyMeasurable)
    ((hv.integrable_sq.const_mul (2 * (M * ‖H‖) ^ 2)).add (hD.integrable_sq.const_mul 2))
  · intro k
    apply ae_of_all
    intro A
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (fderiv ℝ (gueSymmetricSpatialTruncation n k F) A H) ^ 2 ≤ _
    rw [gueSymmetricSpatialTruncation_fderiv n k F hF]
    obtain ⟨hc0, hc1⟩ := gueSymmetricSpatialCutoff_mem_unit n k A
    have hc2 : gueSymmetricSpatialCutoff n k A ^ 2 ≤ 1 := by nlinarith
    have hd2 : (fderiv ℝ (gueSymmetricSpatialCutoff n k) A H) ^ 2 ≤ (M * ‖H‖) ^ 2 := by
      have hh := hb k A
      nlinarith [sq_abs (fderiv ℝ (gueSymmetricSpatialCutoff n k) A H),
        abs_nonneg (fderiv ℝ (gueSymmetricSpatialCutoff n k) A H), mul_nonneg hM0 (norm_nonneg H)]
    have hx := mul_le_mul_of_nonneg_right hd2 (sq_nonneg (F A))
    have hy := mul_le_mul_of_nonneg_right hc2 (sq_nonneg (fderiv ℝ F A H))
    nlinarith [sq_nonneg (fderiv ℝ (gueSymmetricSpatialCutoff n k) A H * F A -
      gueSymmetricSpatialCutoff n k A * fderiv ℝ F A H)]
  · exact ae_of_all _ fun A => ((gueSymmetricSpatialTruncation_limits n F hF A H).2).pow 2

theorem gueSymmetricSpatialTruncation_energy_tendsto (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ)
    {ι : Type*} [Fintype ι] (d : ι → EuclideanSpace ℝ (Fin n))
    (hD : ∀ i, MemLp (fun A => fderiv ℝ F A (d i)) 2 μ) :
    Tendsto (fun k => ∫ A, directionalEnergy d (gueSymmetricSpatialTruncation n k F) A ∂μ)
      atTop (nhds (∫ A, directionalEnergy d F A ∂μ)) := by
  classical
  have hcut (k : ℕ) (i : ι) : Integrable
      (fun A => (fderiv ℝ (gueSymmetricSpatialTruncation n k F) A (d i)) ^ 2) μ := by
    have hc := (gueSymmetricSpatialTruncation_compact n k F).fderiv_apply (𝕜 := ℝ) (d i)
    have hc2 : HasCompactSupport (fun A => (fderiv ℝ (gueSymmetricSpatialTruncation n k F) A (d i))
        ^ 2) := by
      simpa only [pow_two, Pi.mul_def] using
        (hc.mul_right (f' := fun A => fderiv ℝ (gueSymmetricSpatialTruncation n k F) A (d i)))
    exact ((((gueSymmetricSpatialTruncation_contDiff n k F hF).continuous_fderiv
        one_ne_zero).clm_apply
      continuous_const).pow 2).integrable_of_hasCompactSupport hc2
  have he (k : ℕ) : (∫ A, directionalEnergy d (gueSymmetricSpatialTruncation n k F) A ∂μ) =
      ∑ i, ∫ A, (fderiv ℝ (gueSymmetricSpatialTruncation n k F) A (d i)) ^ 2 ∂μ := by
    unfold directionalEnergy
    exact MeasureTheory.integral_finsetSum _ fun i _ => hcut k i
  have hf : (∫ A, directionalEnergy d F A ∂μ) =
      ∑ i, ∫ A, (fderiv ℝ F A (d i)) ^ 2 ∂μ := by
    unfold directionalEnergy
    exact MeasureTheory.integral_finsetSum _ fun i _ => (hD i).integrable_sq
  simp_rw [he]
  rw [hf]
  exact tendsto_finsetSum _ fun i _ =>
    gueSymmetricSpatialTruncation_direction_energy_tendsto n μ F hF hv (d i) (hD i)

theorem gueSymmetricSpatialTruncation_L2_errors (n : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ)
    (H : EuclideanSpace ℝ (Fin n)) (hD : MemLp (fun A => fderiv ℝ F A H) 2 μ) :
    Tendsto (fun k => ∫ A, (gueSymmetricSpatialTruncation n k F A - F A) ^ 2 ∂μ)
      atTop (nhds 0) ∧
    Tendsto (fun k => ∫ A,
      (fderiv ℝ (gueSymmetricSpatialTruncation n k F) A H - fderiv ℝ F A H) ^ 2 ∂μ)
      atTop (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := gueSymmetricSpatialCutoff_derivative_bound n
  have hb (k : ℕ) (A : EuclideanSpace ℝ (Fin n)) :
      |fderiv ℝ (gueSymmetricSpatialCutoff n k) A H| ≤ M * ‖H‖ := by
    refine (hM k A H).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg H))
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  constructor
  · have ht := tendsto_integral_of_dominated_convergence (fun A => F A ^ 2)
      (fun k => (((gueSymmetricSpatialTruncation_contDiff n k F hF).continuous.sub
          hF.continuous).pow 2).aestronglyMeasurable)
      hv.integrable_sq (fun k => ae_of_all _ fun A => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change (gueSymmetricSpatialCutoff n k A * F A - F A) ^ 2 ≤ F A ^ 2
        obtain ⟨h0, h1⟩ := gueSymmetricSpatialCutoff_mem_unit n k A
        have hc : (gueSymmetricSpatialCutoff n k A - 1) ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (F A))])
      (ae_of_all _ fun A => by simpa using
        (((gueSymmetricSpatialTruncation_limits n F hF A H).1.sub_const (F A)).pow 2))
    simpa using ht
  · have ht := tendsto_integral_of_dominated_convergence
      (fun A => 2 * (M * ‖H‖) ^ 2 * F A ^ 2 + 2 * (fderiv ℝ F A H) ^ 2)
      (fun k => (((((gueSymmetricSpatialTruncation_contDiff n k F hF).continuous_fderiv
          one_ne_zero).clm_apply
        continuous_const).sub ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)).pow
            2).aestronglyMeasurable)
      ((hv.integrable_sq.const_mul (2 * (M * ‖H‖) ^ 2)).add (hD.integrable_sq.const_mul 2))
      (fun k => ae_of_all _ fun A => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change (fderiv ℝ (gueSymmetricSpatialTruncation n k F) A H - fderiv ℝ F A H) ^ 2 ≤ _
        rw [gueSymmetricSpatialTruncation_fderiv n k F hF]
        obtain ⟨hc0, hc1⟩ := gueSymmetricSpatialCutoff_mem_unit n k A
        have hc2 : (gueSymmetricSpatialCutoff n k A - 1) ^ 2 ≤ 1 := by nlinarith
        have hd2 : (fderiv ℝ (gueSymmetricSpatialCutoff n k) A H) ^ 2 ≤ (M * ‖H‖) ^ 2 := by
          have hh := hb k A
          nlinarith [sq_abs (fderiv ℝ (gueSymmetricSpatialCutoff n k) A H),
            abs_nonneg (fderiv ℝ (gueSymmetricSpatialCutoff n k) A H), mul_nonneg hM0 (norm_nonneg
                H)]
        have hx := mul_le_mul_of_nonneg_right hd2 (sq_nonneg (F A))
        have hy := mul_le_mul_of_nonneg_right hc2 (sq_nonneg (fderiv ℝ F A H))
        nlinarith [sq_nonneg (fderiv ℝ (gueSymmetricSpatialCutoff n k) A H * F A -
          (gueSymmetricSpatialCutoff n k A - 1) * fderiv ℝ F A H)])
      (ae_of_all _ fun A => by simpa using
        (((gueSymmetricSpatialTruncation_limits n F hF A H).2.sub_const (fderiv ℝ F A H)).pow 2))
    simpa using ht

end
end GinibrePoincare
