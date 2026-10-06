/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AnnealedCutoffEnergy

/-!
# High-contrast homogenization: Provider.Response.AnnealedCutoffEnergyComponent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cutoff-energy component of the pre-Young estimate

The annealed cutoff-energy estimate bounds an expectation by the expectation of
a sum of a multiple of the response and a product of two square roots.  The
compact assembly consumes instead three extended-nonnegative terms built from
the roots of the response defect and of the terminal response.

This module performs that reduction.  The product of roots is integrated by
Cauchy-Schwarz, so the two remaining expectations are the terminal response and
the partition defect; the resulting real inequality is then transferred to the
extended nonnegative reals, where the two roots reappear as the two factors of
each quadratic term.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open MeasureTheory Book.Ch05.Section53.JUpperBoundWeakNorms

open scoped ENNReal

variable {d : ℕ}

/-! ## Square integrability of a root -/

/-- The square root of a nonnegative integrable observable is square
integrable. -/
theorem memLp_two_sqrt_of_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hfnn : 0 ≤ᵐ[μ] f) :
    MemLp (fun x => Real.sqrt (f x)) 2 μ := by
  have hfm : AEStronglyMeasurable (fun x => Real.sqrt (f x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have hfsq : (fun x => Real.sqrt (f x) ^ (2 : ℕ)) =ᵐ[μ] f := by
    filter_upwards [hfnn] with x hx
    exact Real.sq_sqrt hx
  exact (memLp_two_iff_integrable_sq hfm).2 (hf.congr hfsq.symm)

/-- The product of the roots of two nonnegative integrable observables is
integrable. -/
theorem integrable_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfnn : 0 ≤ᵐ[μ] f) (hgnn : 0 ≤ᵐ[μ] g) :
    Integrable (fun x => Real.sqrt (f x) * Real.sqrt (g x)) μ :=
  (memLp_two_sqrt_of_integrable hf hfnn).integrable_mul
    (memLp_two_sqrt_of_integrable hg hgnn)

/-! ## The annealed right-hand side -/

/-- **The expectation of the samplewise cutoff-energy bound.**  The product of
the two roots is integrated by Cauchy-Schwarz, leaving only the expectations of
the response and of the partition defect. -/
theorem integral_cutoffEnergyBound_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {J D T : α → ℝ} {Ccut expo EJ tau : ℝ}
    (hJnn : 0 ≤ᵐ[μ] J) (hTnn : 0 ≤ᵐ[μ] T) (hDT : D =ᵐ[μ] T)
    (hJ : Integrable J μ) (hT : Integrable T μ)
    (hbound : Integrable (fun a => Ccut * expo * J a +
      Real.sqrt (D a) * Real.sqrt (4 * J a + 2 * T a)) μ)
    (hEJ : ∫ a, J a ∂μ = EJ) (htau : ∫ a, T a ∂μ = tau) :
    ∫ a, (Ccut * expo * J a +
        Real.sqrt (D a) * Real.sqrt (4 * J a + 2 * T a)) ∂μ ≤
      2 * tau + 4 * (Real.sqrt tau * Real.sqrt EJ) + Ccut * expo * EJ := by
  have hprod : Integrable (fun a => Real.sqrt (T a) * Real.sqrt (J a)) μ :=
    integrable_sqrt_mul_sqrt hT hJ hTnn hJnn
  have hsplit : Integrable (fun a => Ccut * expo * J a +
      (2 * T a + 4 * (Real.sqrt (T a) * Real.sqrt (J a)))) μ :=
    (hJ.const_mul _).add ((hT.const_mul 2).add (hprod.const_mul 4))
  have hpt : (fun a => Ccut * expo * J a +
        Real.sqrt (D a) * Real.sqrt (4 * J a + 2 * T a)) ≤ᵐ[μ]
      fun a => Ccut * expo * J a +
        (2 * T a + 4 * (Real.sqrt (T a) * Real.sqrt (J a))) := by
    filter_upwards [hJnn, hTnn, hDT] with a hJa hTa hDa
    have hstep := sqrt_mul_sqrt_four_add_two_le_two_mul_add_four_mul
      (T := T a) (J := J a) hJa hTa
    rw [hDa]
    linarith only [hstep]
  have hmono := integral_mono_ae hbound hsplit hpt
  have hadd₁ : ∫ a, (Ccut * expo * J a +
        (2 * T a + 4 * (Real.sqrt (T a) * Real.sqrt (J a)))) ∂μ =
      (∫ a, Ccut * expo * J a ∂μ) +
        ∫ a, (2 * T a + 4 * (Real.sqrt (T a) * Real.sqrt (J a))) ∂μ :=
    integral_add (hJ.const_mul _) ((hT.const_mul 2).add (hprod.const_mul 4))
  have hadd₂ : ∫ a, (2 * T a + 4 * (Real.sqrt (T a) * Real.sqrt (J a))) ∂μ =
      (∫ a, 2 * T a ∂μ) +
        ∫ a, 4 * (Real.sqrt (T a) * Real.sqrt (J a)) ∂μ :=
    integral_add (hT.const_mul 2) (hprod.const_mul 4)
  have hvalue : ∫ a, (Ccut * expo * J a +
        (2 * T a + 4 * (Real.sqrt (T a) * Real.sqrt (J a)))) ∂μ =
      Ccut * expo * (∫ a, J a ∂μ) +
        (2 * (∫ a, T a ∂μ) +
          4 * ∫ a, Real.sqrt (T a) * Real.sqrt (J a) ∂μ) := by
    rw [hadd₁, hadd₂, integral_const_mul, integral_const_mul, integral_const_mul]
  have hcs := integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt hT hJ hTnn hJnn
  rw [hvalue, hEJ, htau] at hmono
  rw [htau, hEJ] at hcs
  linarith only [hmono, hcs]

/-! ## The extended nonnegative component -/

/-- **The cutoff-energy component.**  A real bound by the response defect, the
mixed root product, and the scaled response becomes the exact three-term
extended-nonnegative expression consumed by the compact assembly, in which each
quadratic term is written as a product of two roots. -/
theorem ofReal_abs_le_cutoffEnergyComponent {x Ccut expo EJ tau : ℝ}
    (hCcut : 0 ≤ Ccut) (hexpo : 0 ≤ expo) (hEJ : 0 ≤ EJ) (htau : 0 ≤ tau)
    (hx : |x| ≤ 2 * tau + 4 * (Real.sqrt tau * Real.sqrt EJ) + Ccut * expo * EJ) :
    ENNReal.ofReal |x| ≤
      ENNReal.ofReal 2 * ENNReal.ofReal (Real.sqrt tau) *
          ENNReal.ofReal (Real.sqrt tau) +
        ENNReal.ofReal 4 * ENNReal.ofReal (Real.sqrt tau) *
          ENNReal.ofReal (Real.sqrt EJ) +
        ENNReal.ofReal Ccut * ENNReal.ofReal expo *
          ENNReal.ofReal (Real.sqrt EJ) * ENNReal.ofReal (Real.sqrt EJ) := by
  have hroottau : Real.sqrt tau * Real.sqrt tau = tau := Real.mul_self_sqrt htau
  have hrootEJ : Real.sqrt EJ * Real.sqrt EJ = EJ := Real.mul_self_sqrt hEJ
  have hfirst : ENNReal.ofReal 2 * ENNReal.ofReal (Real.sqrt tau) *
      ENNReal.ofReal (Real.sqrt tau) = ENNReal.ofReal (2 * tau) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt tau),
      mul_assoc, hroottau]
  have hsecond : ENNReal.ofReal 4 * ENNReal.ofReal (Real.sqrt tau) *
      ENNReal.ofReal (Real.sqrt EJ) =
      ENNReal.ofReal (4 * (Real.sqrt tau * Real.sqrt EJ)) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * Real.sqrt tau),
      mul_assoc]
  have hthird : ENNReal.ofReal Ccut * ENNReal.ofReal expo *
      ENNReal.ofReal (Real.sqrt EJ) * ENNReal.ofReal (Real.sqrt EJ) =
      ENNReal.ofReal (Ccut * expo * EJ) := by
    rw [← ENNReal.ofReal_mul hCcut,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Ccut * expo),
      ← ENNReal.ofReal_mul (by positivity :
        (0 : ℝ) ≤ Ccut * expo * Real.sqrt EJ), mul_assoc, hrootEJ]
  rw [hfirst, hsecond, hthird,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hx

/-! ## The annealed cutoff-energy component -/

end

end Response
end HighContrast
end HCPolySupport
