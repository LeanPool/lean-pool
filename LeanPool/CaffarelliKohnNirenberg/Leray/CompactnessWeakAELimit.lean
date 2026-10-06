/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLp
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Compactness Weak AELimit

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace CKN.Leray

/-- A uniformly bounded `L²` sequence with a weak limit and an almost
everywhere pointwise limit has the same limit in both senses. -/
theorem ae_eq_of_weak_l2_and_ae_tendsto
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsFiniteMeasure μ]
    (f : ℕ → α → E) (g : α → E) (v : Lp E 2 μ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hbound : ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ n, eLpNorm (f n) 2 μ ≤ B)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds (g x)))
    (hweak : ∀ w : Lp E 2 μ, Tendsto
      (fun n => inner ℝ ((hf n).toLp (f n)) w) atTop
      (nhds (inner ℝ v w))) :
    g =ᵐ[μ] fun x => v x := by
  have hmeasure : TendstoInMeasure μ f atTop g :=
    tendstoInMeasure_of_tendsto_ae
      (fun n => (hf n).aestronglyMeasurable) hae
  have hdiffMeasure : TendstoInMeasure μ (fun n => f n - g) atTop
      (fun _ => (0 : E)) := by
    rw [tendstoInMeasure_iff_dist] at hmeasure ⊢
    simpa [dist_eq_norm, Pi.sub_apply] using hmeasure
  obtain ⟨B, hB, hBbound⟩ := hbound
  let B' : ℝ≥0∞ := B + eLpNorm g 2 μ
  have hB' : B' < ⊤ := ENNReal.add_lt_top.mpr ⟨hB, hg.eLpNorm_lt_top⟩
  have hdiffBound : ∀ n, eLpNorm (f n - g) 2 μ ≤ B' := by
    intro n
    exact (eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      (add_le_add (hBbound n) le_rfl)
  have hLone : Tendsto (fun n => eLpNorm (f n - g) 1 μ)
      atTop (nhds 0) :=
    tendsto_eLpNorm_of_tendstoInMeasure_of_uniform_high
      (by norm_num : (1 : ℝ≥0∞) ≤ 1)
      (by norm_num : (1 : ℝ≥0∞) < 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (fun n => (hf n).sub hg) ⟨B', hB', hdiffBound⟩ hdiffMeasure
  have hfi (n : ℕ) : Integrable (f n) μ :=
    memLp_one_iff_integrable.mp ((hf n).mono_exponent (by norm_num))
  have hgi : Integrable g μ :=
    memLp_one_iff_integrable.mp (hg.mono_exponent (by norm_num))
  have hvi : Integrable (fun x => v x) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp v).mono_exponent (by norm_num))
  apply Integrable.ae_eq_of_forall_setIntegral_eq g (fun x => v x) hgi hvi
  intro S hS hSfinite
  have hstrongInt : Tendsto (fun n => ∫ x in S, f n x ∂μ)
      atTop (nhds (∫ x in S, g x ∂μ)) :=
    tendsto_setIntegral_of_L1' g
      (Eventually.of_forall hfi) hLone S
  have hweakInt (a : E) : Tendsto
      (fun n => inner ℝ a (∫ x in S, f n x ∂μ)) atTop
      (nhds (inner ℝ a (∫ x in S, v x ∂μ))) := by
    have hEqn (n : ℕ) : inner ℝ ((hf n).toLp (f n))
        (indicatorConstLp 2 hS hSfinite.ne a) =
        inner ℝ a (∫ x in S, f n x ∂μ) := by
      rw [real_inner_comm,
        L2.inner_indicatorConstLp_eq_inner_setIntegral]
      rw [setIntegral_congr_ae hS]
      filter_upwards [(hf n).coeFn_toLp] with x hx _
      exact hx
    have hEqv : inner ℝ v (indicatorConstLp 2 hS hSfinite.ne a) =
        inner ℝ a (∫ x in S, v x ∂μ) := by
      rw [real_inner_comm,
        L2.inner_indicatorConstLp_eq_inner_setIntegral]
    have hpair := hweak
      (indicatorConstLp 2 hS hSfinite.ne a)
    simpa only [hEqn, hEqv] using hpair
  have heq (a : E) : inner ℝ a (∫ x in S, g x ∂μ) =
      inner ℝ a (∫ x in S, v x ∂μ) := by
    have hcont : Continuous (fun b : E => inner ℝ a b) := by fun_prop
    have hstrong := (hcont.tendsto _).comp hstrongInt
    exact tendsto_nhds_unique hstrong (hweakInt a)
  have hinnerZero : inner ℝ
      ((∫ x in S, g x ∂μ) - (∫ x in S, v x ∂μ))
      ((∫ x in S, g x ∂μ) - (∫ x in S, v x ∂μ)) = 0 := by
    rw [inner_sub_right]
    exact sub_eq_zero.mpr (heq _)
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp hinnerZero)

end CKN.Leray
