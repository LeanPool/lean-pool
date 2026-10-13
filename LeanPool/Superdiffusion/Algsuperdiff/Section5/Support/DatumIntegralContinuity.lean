/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.BallAverage
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DatumContinuity

/-!
# DatumIntegralContinuity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The integral of the solution over a fixed set is continuous in the datum

Reading both localized quantities off ball averages replaces every pointwise
statement about the solution by a statement about its integral over a fixed
ball.  What the reduction of the supremum over the forcing class to a countable
subclass then needs is only this: at a fixed set inside the cube, the integral of
the solution depends continuously on the forcing field in the supremum norm on
the cube.

The chain is the energy estimate, the zero-trace Poincaré inequality and
Cauchy-Schwarz against the constant one, with no regularity of the solution
used anywhere.

## Main results

* `exists_eta_abs_setIntegral_sub_le`, `exists_eta_abs_setAverage_ball_sub_le`.
* `setAverage_ball_sub_of_h1` — the average of a difference splits.

## References

* ABK26, the localized error and regularity quantities of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **At a fixed subset of the cube the integral of the solution is uniformly
continuous in the forcing field.** -/
theorem exists_eta_abs_setIntegral_sub_le [NeZero d] {y : Vec d} {n : ℤ} {a : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (cubeSetAt y n) a)
    {B : Set (Vec d)} (hB : B ⊆ cubeSetAt y n) {eps : ℝ} (heps : 0 < eps) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ g g' : Vec d → Vec d, MemVectorL2 (cubeSetAt y n) g →
        MemVectorL2 (cubeSetAt y n) g' →
        (∀ x ∈ cubeSetAt y n, ‖g x - g' x‖ ≤ eta) →
        ∀ u u' : H1Function (cubeSetAt y n),
          IsDirichletSolutionAt a y n u g → IsDirichletSolutionAt a y n u' g' →
          |(∫ z in B, u.toFun z ∂volume) - ∫ z in B, u'.toFun z ∂volume| ≤ eps := by
  obtain ⟨CP, hCP, hpoin⟩ :=
    exists_poincare_integral_constant (isOpenBoundedConvexDomain_cubeSetAt y n)
  have hlam : 0 < lam := (hEll.2 y (mem_cubeSetAt_self y n)).1
  have hlaminv : (0 : ℝ) ≤ lam⁻¹ := (inv_pos.2 hlam).le
  have hcubefin : volume (cubeSetAt y n) ≠ ⊤ :=
    ((isOpenBoundedConvexDomain_cubeSetAt y n).volume_lt_top).ne
  have hBfin : volume B ≠ ⊤ :=
    ((measure_mono hB).trans_lt (lt_top_iff_ne_top.2 hcubefin)).ne
  have hvolBnn : (0 : ℝ) ≤ volume.real B := measureReal_nonneg
  have hvolUnn : (0 : ℝ) ≤ volume.real (cubeSetAt y n) := measureReal_nonneg
  set C : ℝ := Real.sqrt (volume.real B) *
    (CP * (lam⁻¹ * (d : ℝ)) * Real.sqrt (volume.real (cubeSetAt y n))) with hCdef
  have hCnn : (0 : ℝ) ≤ C := by
    rw [hCdef]
    positivity
  refine ⟨eps / (C + 1), by positivity, ?_⟩
  intro g g' hgL2 hg'L2 hclose u u' hu hu'
  set eta : ℝ := eps / (C + 1) with hetadef
  have hetann : (0 : ℝ) ≤ eta := by rw [hetadef]; positivity
  obtain ⟨w, hwf, hwg⟩ := exists_h10Function_sub hu hu'
  have : IsFiniteMeasure (volume.restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hBfin
  have hwL2B : MemLp w.toH1Function.toFun 2 (volume.restrict B) :=
    w.toH1Function.memL2.mono_measure (Measure.restrict_mono hB le_rfl)
  have hsplit : (∫ z in B, u.toFun z ∂volume) - ∫ z in B, u'.toFun z ∂volume =
      ∫ z in B, w.toH1Function.toFun z ∂volume := by
    have hintu : IntegrableOn u.toFun B volume :=
      (u.memL2.mono_measure (Measure.restrict_mono hB le_rfl)).integrable one_le_two
    have hintu' : IntegrableOn u'.toFun B volume :=
      (u'.memL2.mono_measure (Measure.restrict_mono hB le_rfl)).integrable one_le_two
    rw [← integral_sub hintu hintu']
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show u.toFun z - u'.toFun z = w.toH1Function.toFun z
    rw [hwf z]
  rw [hsplit]
  have hUint : IntegrableOn (fun z => w.toH1Function.toFun z ^ (2 : ℕ))
      (cubeSetAt y n) volume := w.toH1Function.memL2.integrable_sq
  have h1 : |∫ z in B, w.toH1Function.toFun z ∂volume| ≤
      Real.sqrt (volume.real B) *
        Real.sqrt (∫ z in B, w.toH1Function.toFun z ^ (2 : ℕ) ∂volume) :=
    abs_setIntegral_le_sqrt hBfin hwL2B
  have h2 : Real.sqrt (∫ z in B, w.toH1Function.toFun z ^ (2 : ℕ) ∂volume) ≤
      Real.sqrt (∫ z in cubeSetAt y n, w.toH1Function.toFun z ^ (2 : ℕ) ∂volume) := by
    refine Real.sqrt_le_sqrt ?_
    exact setIntegral_mono_set hUint (Filter.Eventually.of_forall fun z => by positivity)
      (LE.le.eventuallyLE hB)
  have hgrad : (∫ x in cubeSetAt y n, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) =
      ∫ x in cubeSetAt y n, ‖u.grad x - u'.grad x‖ ^ (2 : ℕ) ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖w.toH1Function.grad x‖ ^ (2 : ℕ) = ‖u.grad x - u'.grad x‖ ^ (2 : ℕ)
    rw [hwg x]
  have h3 := hpoin w
  rw [hgrad] at h3
  have h4 := sqrt_energy_grad_sub_le_data hEll hgL2 hg'L2 hu hu'
  have h5 : Real.sqrt (∫ x in cubeSetAt y n, ‖g x - g' x‖ ^ (2 : ℕ) ∂volume) ≤
      Real.sqrt (volume.real (cubeSetAt y n)) * eta := by
    refine le_trans (Real.sqrt_le_sqrt
      (setIntegral_sq_le_of_forall_norm_le hclose)) (le_of_eq ?_)
    rw [Real.sqrt_mul hvolUnn, Real.sqrt_sq hetann]
  have hchain : Real.sqrt (∫ z in cubeSetAt y n, w.toH1Function.toFun z ^ (2 : ℕ) ∂volume) ≤
      CP * (lam⁻¹ * (d : ℝ)) * (Real.sqrt (volume.real (cubeSetAt y n)) * eta) := by
    calc Real.sqrt (∫ z in cubeSetAt y n, w.toH1Function.toFun z ^ (2 : ℕ) ∂volume)
        ≤ CP * Real.sqrt (∫ x in cubeSetAt y n,
            ‖u.grad x - u'.grad x‖ ^ (2 : ℕ) ∂volume) := h3
      _ ≤ CP * (lam⁻¹ * (d : ℝ) *
            Real.sqrt (∫ x in cubeSetAt y n, ‖g x - g' x‖ ^ (2 : ℕ) ∂volume)) :=
          mul_le_mul_of_nonneg_left h4 hCP
      _ ≤ CP * (lam⁻¹ * (d : ℝ) * (Real.sqrt (volume.real (cubeSetAt y n)) * eta)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h5 (by positivity)) hCP
      _ = CP * (lam⁻¹ * (d : ℝ)) * (Real.sqrt (volume.real (cubeSetAt y n)) * eta) := by
          ring
  have hfinal : |∫ z in B, w.toH1Function.toFun z ∂volume| ≤ C * eta := by
    calc |∫ z in B, w.toH1Function.toFun z ∂volume|
        ≤ Real.sqrt (volume.real B) *
            Real.sqrt (∫ z in B, w.toH1Function.toFun z ^ (2 : ℕ) ∂volume) := h1
      _ ≤ Real.sqrt (volume.real B) *
            Real.sqrt (∫ z in cubeSetAt y n, w.toH1Function.toFun z ^ (2 : ℕ) ∂volume) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (volume.real B) *
            (CP * (lam⁻¹ * (d : ℝ)) * (Real.sqrt (volume.real (cubeSetAt y n)) * eta)) :=
          mul_le_mul_of_nonneg_left hchain (Real.sqrt_nonneg _)
      _ = C * eta := by rw [hCdef]; ring
  refine le_trans hfinal ?_
  have hden : (0 : ℝ) < C + 1 := by linarith
  have hfrac : C / (C + 1) ≤ 1 := (div_le_one hden).2 (by linarith)
  calc C * eta = eps * (C / (C + 1)) := by rw [hetadef]; field_simp
    _ ≤ eps * 1 := mul_le_mul_of_nonneg_left hfrac heps.le
    _ = eps := mul_one eps

/-! ## 2. The same for the average, and a splitting -/

theorem setAverage_ball_sub_of_h1 {y : Vec d} {n : ℤ} (u v : H1Function (cubeSetAt y n))
    {p : Vec d} {r : ℝ} (hB : Metric.ball p r ⊆ cubeSetAt y n) :
    (⨍ z in Metric.ball p r, (u.toFun z - v.toFun z) ∂volume) =
      (⨍ z in Metric.ball p r, u.toFun z ∂volume) -
        ⨍ z in Metric.ball p r, v.toFun z ∂volume := by
  have hcubefin : volume (cubeSetAt y n) ≠ ⊤ :=
    ((isOpenBoundedConvexDomain_cubeSetAt y n).volume_lt_top).ne
  have hBfin : volume (Metric.ball p r) ≠ ⊤ :=
    ((measure_mono hB).trans_lt (lt_top_iff_ne_top.2 hcubefin)).ne
  have : IsFiniteMeasure (volume.restrict (Metric.ball p r)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hBfin
  have hintu : IntegrableOn u.toFun (Metric.ball p r) volume :=
    (u.memL2.mono_measure (Measure.restrict_mono hB le_rfl)).integrable one_le_two
  have hintv : IntegrableOn v.toFun (Metric.ball p r) volume :=
    (v.memL2.mono_measure (Measure.restrict_mono hB le_rfl)).integrable one_le_two
  rw [setAverage_eq, setAverage_eq, setAverage_eq, integral_sub hintu hintv, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, mul_sub]

/-- **At a fixed ball inside the cube the average of the solution is uniformly
continuous in the forcing field.** -/
theorem exists_eta_abs_setAverage_ball_sub_le [NeZero d] {y : Vec d} {n : ℤ}
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (cubeSetAt y n) a)
    {p : Vec d} {r : ℝ} (hr : 0 < r) (hB : Metric.ball p r ⊆ cubeSetAt y n)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ g g' : Vec d → Vec d, MemVectorL2 (cubeSetAt y n) g →
        MemVectorL2 (cubeSetAt y n) g' →
        (∀ x ∈ cubeSetAt y n, ‖g x - g' x‖ ≤ eta) →
        ∀ u u' : H1Function (cubeSetAt y n),
          IsDirichletSolutionAt a y n u g → IsDirichletSolutionAt a y n u' g' →
          |(⨍ z in Metric.ball p r, u.toFun z ∂volume) -
            ⨍ z in Metric.ball p r, u'.toFun z ∂volume| ≤ eps := by
  have hvolpos : 0 < volume.real (Metric.ball p r) := by
    rw [MeasureTheory.measureReal_def]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume p hr).ne' measure_ball_lt_top.ne
  obtain ⟨eta, hetapos, heta⟩ :=
    exists_eta_abs_setIntegral_sub_le hEll hB (mul_pos heps hvolpos)
  refine ⟨eta, hetapos, fun g g' hgL2 hg'L2 hclose u u' hu hu' => ?_⟩
  have hbd := heta g g' hgL2 hg'L2 hclose u u' hu hu'
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, ← mul_sub, abs_mul,
    abs_of_nonneg (inv_nonneg.2 hvolpos.le)]
  calc (volume.real (Metric.ball p r))⁻¹ *
        |(∫ z in Metric.ball p r, u.toFun z ∂volume) -
          ∫ z in Metric.ball p r, u'.toFun z ∂volume|
      ≤ (volume.real (Metric.ball p r))⁻¹ * (eps * volume.real (Metric.ball p r)) :=
        mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 hvolpos.le)
    _ = eps := by field_simp

end

end Algsuperdiff.Section5.Support
