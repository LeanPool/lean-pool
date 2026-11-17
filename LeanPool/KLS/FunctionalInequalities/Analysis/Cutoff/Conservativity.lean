/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Conservativity from cutoffs with a vanishing defect

For a probability law `μ`, a bounded `f` of any sign, `c > 0` and `g` with `g + c f ≥ 0`, cutoffs `0
≤ χ_n ≤ 1` with
`χ_n → 1` and defects `d_n ∈ L¹(μ)` with `∫ |d_n| dμ → 0` such that `∫ χ_n g = ∫ f d_n`, the
function `g` is integrable and
`∫ g dμ = 0`: Fatou's lemma gives integrability of `g + c f`, then dominated convergence. Generic
tool; the analytic core of
Letwin arXiv:2607.24164v1, Lemma A.5 (p. 18), with `g = Lf`, `d_n = Lχ_n`. Neither the integrability
of `g` nor its zero
integral is assumed. Same generic cutoff role as `Analysis/Cutoff/Integrability.lean` (Fatou
integrability from bounded
cutoff integrals), but a separate module: it needs the dominated-convergence and probability-measure
imports, under which
the existing `integrable_of_cutoff_bounds` would elaborate different instance terms; it does not
import that module.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace FunctionalInequalities.Analysis

/--
**Conservativity from cutoffs** (Letwin, Lemma A.5, analytic core): bounded `f`, `0 ≤ g + c f` with
`c > 0`,
cutoffs `0 ≤ χ_n ≤ 1`, `χ_n → 1`, defects with `∫ |d_n| → 0` and `∫ χ_n g = ∫ f d_n` give `g ∈
L¹(μ)` and
`∫ g dμ = 0`. -/
theorem integrable_and_integral_eq_zero_of_cutoff_defect {α : Type*} [MeasurableSpace α]
    (mu : ProbabilityMeasure α) (f g : α → ℝ) (hf : AEStronglyMeasurable f (mu : Measure α))
    (hg : AEStronglyMeasurable g (mu : Measure α)) (C : ℝ) (hC : 0 ≤ C)
    (hfBound : ∀ᵐ x ∂(mu : Measure α), |f x| ≤ C) (c : ℝ) (hc : 0 < c)
    (hLower : ∀ᵐ x ∂(mu : Measure α), 0 ≤ g x + c * f x) (chi defect : ℕ → α → ℝ)
    (hChiMeas : ∀ n, AEStronglyMeasurable (chi n) (mu : Measure α))
    (hChiBounds : ∀ n, ∀ᵐ x ∂(mu : Measure α), 0 ≤ chi n x ∧ chi n x ≤ 1)
    (hChiLim : ∀ᵐ x ∂(mu : Measure α), Tendsto (fun n => chi n x) atTop (𝓝 1))
    (hDefect : ∀ n, Integrable (defect n) (mu : Measure α))
    (hDefectLim : Tendsto (fun n => ∫ x, |defect n x| ∂(mu : Measure α)) atTop (𝓝 0))
    (hCutoffG : ∀ n, Integrable (fun x => chi n x * g x) (mu : Measure α))
    (hSym :
      ∀ n, (∫ x, chi n x * g x ∂(mu : Measure α)) = ∫ x, f x * defect n x ∂(mu : Measure α)) :
    Integrable g (mu : Measure α) ∧ (∫ x, g x ∂(mu : Measure α)) = 0 := by
  have hScaledInt : Integrable (fun x => c * f x) (mu : Measure α) :=
    (integrable_const (c * C)).mono' (hf.const_mul c)
      (by
        filter_upwards [hfBound] with x hx
        calc
          ‖c * f x‖ = c * |f x| := by rw [Real.norm_eq_abs, abs_mul, abs_of_pos hc]
          _ ≤ c * C := mul_le_mul_of_nonneg_left hx hc.le)
  have hMulBound (n : ℕ) : ∀ᵐ x ∂(mu : Measure α), ∀ r : ℝ, ‖chi n x * r‖ ≤ ‖r‖ := by
    filter_upwards [hChiBounds n] with x hx
    intro r
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.1, one_mul] using
      mul_le_mul_of_nonneg_right hx.2 (abs_nonneg r)
  have hCutoffFBound (n : ℕ) : ∀ᵐ x ∂(mu : Measure α), ‖chi n x * f x‖ ≤ C := by
    filter_upwards [hChiBounds n, hfBound] with x hx hfx
    calc
      ‖chi n x * f x‖ = chi n x * |f x| := by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.1]
      _ ≤ chi n x * C := mul_le_mul_of_nonneg_left hfx hx.1
      _ ≤ 1 * C := mul_le_mul_of_nonneg_right hx.2 hC
      _ = C := one_mul C
  have hCutoffF (n : ℕ) : Integrable (fun x => chi n x * f x) (mu : Measure α) :=
    (integrable_const C).mono' ((hChiMeas n).mul hf) (hCutoffFBound n)
  have hCutoffFLim :
    Tendsto (fun n => ∫ x, chi n x * f x ∂(mu : Measure α)) atTop
      (𝓝 (∫ x, f x ∂(mu : Measure α))) := by
    apply
      tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => (hChiMeas n).mul hf)
        (integrable_const C) hCutoffFBound
    filter_upwards [hChiLim] with x hx
    simpa only [Pi.mul_apply, one_mul] using hx.mul_const (f x)
  have hProductBound (n : ℕ) : ∀ᵐ x ∂(mu : Measure α), ‖f x * defect n x‖ ≤ C * ‖defect n x‖ := by
    filter_upwards [hfBound] with x hx
    simpa only [norm_mul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hx (abs_nonneg (defect n x))
  have hProductInt (n : ℕ) : Integrable (fun x => f x * defect n x) (mu : Measure α) :=
    ((hDefect n).norm.const_mul C).mono' (hf.mul (hDefect n).aestronglyMeasurable)
      (hProductBound n)
  have hCutoffGLim : Tendsto (fun n => ∫ x, chi n x * g x ∂(mu : Measure α)) atTop (𝓝 0) := by
    have hBound (n : ℕ) :
      ‖∫ x, chi n x * g x ∂(mu : Measure α)‖ ≤ C * ∫ x, |defect n x| ∂(mu : Measure α) := by
      calc
        ‖∫ x, chi n x * g x ∂(mu : Measure α)‖ = ‖∫ x, f x * defect n x ∂(mu : Measure α)‖ := by
          rw [hSym n]
        _ ≤ ∫ x, ‖f x * defect n x‖ ∂(mu : Measure α) := norm_integral_le_integral_norm _
        _ ≤ ∫ x, C * ‖defect n x‖ ∂(mu : Measure α) :=
          integral_mono_ae (hProductInt n).norm ((hDefect n).norm.const_mul C) (hProductBound n)
        _ = C * ∫ x, |defect n x| ∂(mu : Measure α) := by
          rw [integral_const_mul]
          simp only [Real.norm_eq_abs]
    exact squeeze_zero_norm hBound (by simpa only [mul_zero] using hDefectLim.const_mul C)
  let H : α → ℝ := fun x => g x + c * f x
  let F : ℕ → α → ℝ := fun n x => chi n x * H x
  have hHMeas : AEStronglyMeasurable H (mu : Measure α) := hg.add (hf.const_mul c)
  have hFInt (n : ℕ) : Integrable (F n) (mu : Measure α) := by
    have heq : F n = fun x => chi n x * g x + c * (chi n x * f x) := by
      funext x
      dsimp [F, H]
      ring
    rw [heq]
    exact (hCutoffG n).add ((hCutoffF n).const_mul c)
  have hFNonneg (n : ℕ) : 0 ≤ᵐ[(mu : Measure α)] F n := by
    filter_upwards [hChiBounds n, hLower] with x hx hL
    exact mul_nonneg hx.1 hL
  have hFLim : ∀ᵐ x ∂(mu : Measure α), Tendsto (fun n => F n x) atTop (𝓝 (H x)) := by
    filter_upwards [hChiLim] with x hx
    simpa only [F, one_mul] using hx.mul_const (H x)
  have hFIntegral (n : ℕ) :
    (∫ x, F n x ∂(mu : Measure α)) =
      (∫ x, chi n x * g x ∂(mu : Measure α)) + c * ∫ x, chi n x * f x ∂(mu : Measure α) := by
    calc
      (∫ x, F n x ∂(mu : Measure α)) =
          ∫ x, chi n x * g x + c * (chi n x * f x) ∂(mu : Measure α) := by
        apply integral_congr_ae
        exact
          Filter.Eventually.of_forall
            (fun x => by
              dsimp [F, H]
              ring)
      _ = _ := by rw [integral_add (hCutoffG n) ((hCutoffF n).const_mul c), integral_const_mul]
  have hFIntegralLim :
    Tendsto (fun n => ∫ x, F n x ∂(mu : Measure α)) atTop
      (𝓝 (c * ∫ x, f x ∂(mu : Measure α))) := by
    simpa only [hFIntegral, zero_add] using hCutoffGLim.add (hCutoffFLim.const_mul c)
  have hLIntegralLim :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂(mu : Measure α)) atTop
      (𝓝 (ENNReal.ofReal (c * ∫ x, f x ∂(mu : Measure α)))) := by
    have heq :
      (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂(mu : Measure α)) =
        (fun n => ENNReal.ofReal (∫ x, F n x ∂(mu : Measure α))) := by
      funext n
      exact (ofReal_integral_eq_lintegral_ofReal (hFInt n) (hFNonneg n)).symm
    rw [heq]
    exact ENNReal.tendsto_ofReal hFIntegralLim
  have hFatou :
    (∫⁻ x, ENNReal.ofReal (H x) ∂(mu : Measure α)) ≤
      ENNReal.ofReal (c * ∫ x, f x ∂(mu : Measure α)) := by
    calc
      (∫⁻ x, ENNReal.ofReal (H x) ∂(mu : Measure α)) =
          ∫⁻ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂(mu : Measure α) := by
        apply lintegral_congr_ae
        filter_upwards [hFLim] with x hx
        exact (ENNReal.tendsto_ofReal hx).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂(mu : Measure α)) atTop :=
        lintegral_liminf_le'
          (fun n =>
            ENNReal.continuous_ofReal.measurable.comp_aemeasurable
              (hFInt n).aestronglyMeasurable.aemeasurable)
      _ = ENNReal.ofReal (c * ∫ x, f x ∂(mu : Measure α)) := hLIntegralLim.liminf_eq
  have hHInt : Integrable H (mu : Measure α) := by
    refine ⟨hHMeas, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal hLower).2 (lt_of_le_of_lt hFatou ENNReal.ofReal_lt_top)
  have hgInt : Integrable g (mu : Measure α) := by
    convert hHInt.sub hScaledInt using 1
    funext x
    simp [H]
  have hgIntegralLim :
    Tendsto (fun n => ∫ x, chi n x * g x ∂(mu : Measure α)) atTop
      (𝓝 (∫ x, g x ∂(mu : Measure α))) := by
    apply
      tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
        (fun n => (hCutoffG n).aestronglyMeasurable) hgInt.norm
    · intro n
      filter_upwards [hMulBound n] with x hx
      exact hx (g x)
    · filter_upwards [hChiLim] with x hx
      simpa only [one_mul] using hx.mul_const (g x)
  exact ⟨hgInt, tendsto_nhds_unique hgIntegralLim hCutoffGLim⟩

end FunctionalInequalities.Analysis
