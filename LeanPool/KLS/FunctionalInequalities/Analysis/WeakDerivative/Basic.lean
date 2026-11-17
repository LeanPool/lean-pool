/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Mollification.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Weak directional derivatives and classical identification
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `g` is the **weak directional derivative** of `f` along `v`, tested against `C¹` functions with
compact support; both functions are locally integrable (so the integrals are not junk). -/
def HasWeakDerivAlong (f g : E → ℝ) (v : E) : Prop :=
  LocallyIntegrable f (volume : Measure E) ∧ LocallyIntegrable g (volume : Measure E) ∧
    ∀ ψ : E → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      ∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E) = -∫ x, g x * ψ x ∂(volume : Measure E)

/-- Weak derivatives are unique almost everywhere. -/
theorem HasWeakDerivAlong.ae_eq {f g₁ g₂ : E → ℝ} {v : E} (h₁ : HasWeakDerivAlong f g₁ v)
    (h₂ : HasWeakDerivAlong f g₂ v) : g₁ =ᵐ[(volume : Measure E)] g₂ := by
  apply ae_eq_of_integral_contDiff_smul_eq h₁.2.1 h₂.2.1
  intro ψ hψ hψc
  have hψ' : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have e₁ := h₁.2.2 ψ hψ' hψc
  have e₂ := h₂.2.2 ψ hψ' hψc
  have e : (∫ x, g₁ x * ψ x ∂(volume : Measure E)) =
      ∫ x, g₂ x * ψ x ∂(volume : Measure E) := by
    linarith
  simpa only [smul_eq_mul, mul_comm] using e

/-- A `C¹` function with locally integrable derivative has its classical directional derivative as
weak derivative. -/
theorem hasWeakDerivAlong_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ 1 f) (v : E) :
    HasWeakDerivAlong f (fun x => fderiv ℝ f x v) v := by
  refine ⟨hf.continuous.locallyIntegrable, ?_, ?_⟩
  · exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).locallyIntegrable
  · intro ψ hψ hψc
    have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
      change HasCompactSupport ((fun L : E →L[ℝ] ℝ => L v) ∘ fderiv ℝ ψ)
      exact (hψc.fderiv ℝ).comp_left (by simp)
    have hf'g : Integrable (fun x => fderiv ℝ f x v * ψ x) (volume : Measure E) := by
      exact
        ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul hψ.continuous
          |>.integrable_of_hasCompactSupport hψc.mul_left
    have hfg' : Integrable (fun x => f x * fderiv ℝ ψ x v) (volume : Measure E) := by
      exact (hf.continuous.mul hψd).integrable_of_hasCompactSupport hψdc.mul_left
    have hfg : Integrable (fun x => f x * ψ x) (volume : Measure E) := by
      have hfg₀ : Integrable (fun x => ψ x * f x) (volume : Measure E) :=
        hf.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
          hψ.continuous hψc
      convert hfg₀ using 1
      funext x
      exact mul_comm _ _
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
      (fun x _ => (hf.differentiable (by simp)).differentiableAt)
      (fun x _ => (hψ.differentiable (by simp)).differentiableAt)

/-- A Lipschitz function has its almost-everywhere (Rademacher) derivative as weak derivative. -/
theorem hasWeakDerivAlong_of_lipschitz {f : E → ℝ} {L : NNReal} (hf : LipschitzWith L f) (v : E) :
    HasWeakDerivAlong f (fun x => fderiv ℝ f x v) v := by
  have hline : LocallyIntegrable (fun x => lineDeriv ℝ f x v) (volume : Measure E) :=
    hf.locallyIntegrable_lineDeriv v
  have hdiff : ∀ᵐ x : E ∂(volume : Measure E), DifferentiableAt ℝ f x :=
    hf.ae_differentiableAt
  have hae : (fun x => lineDeriv ℝ f x v) =ᵐ[(volume : Measure E)]
      (fun x => fderiv ℝ f x v) := by
    filter_upwards [hdiff] with x hx
    exact hx.lineDeriv_eq_fderiv
  refine ⟨hf.continuous.locallyIntegrable, hline.congr hae, ?_⟩
  intro ψ hψ hψc
  obtain ⟨D, hψlip⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ (by simp)
  have hleft : (fun x => fderiv ℝ f x v * ψ x) =ᵐ[(volume : Measure E)]
      (fun x => lineDeriv ℝ f x v * ψ x) := by
    filter_upwards [hae] with x hx
    rw [hx]
  have hlineeq :
      (∫ x, lineDeriv ℝ f x v * ψ x ∂(volume : Measure E)) =
        -(∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E)) := by
    calc
      ∫ x, lineDeriv ℝ f x v * ψ x ∂(volume : Measure E) =
          ∫ x, lineDeriv ℝ ψ x (-v) * f x ∂(volume : Measure E) :=
        hf.integral_lineDeriv_mul_eq hψlip hψc v
      _ = ∫ x, -(f x * fderiv ℝ ψ x v) ∂(volume : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hx : DifferentiableAt ℝ ψ x :=
          (hψ.differentiable (by simp)).differentiableAt
        rw [hx.lineDeriv_eq_fderiv]
        simp [mul_comm]
      _ = -(∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E)) :=
        integral_neg _
  calc
    ∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E) =
        -(∫ x, lineDeriv ℝ f x v * ψ x ∂(volume : Measure E)) := by
      linarith [hlineeq]
    _ = -(∫ x, fderiv ℝ f x v * ψ x ∂(volume : Measure E)) := by
      rw [integral_congr_ae hleft]

/-- Product rule with a `C¹` multiplier of compact support. -/
theorem HasWeakDerivAlong.mul_contDiff {f g : E → ℝ} {v : E} (h : HasWeakDerivAlong f g v)
    {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    HasWeakDerivAlong (fun x => χ x * f x) (fun x => χ x * g x + fderiv ℝ χ x v * f x) v := by
  have hχd : Continuous (fun x => fderiv ℝ χ x v) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχdc : HasCompactSupport (fun x => fderiv ℝ χ x v) := by
    change HasCompactSupport ((fun L : E →L[ℝ] ℝ => L v) ∘ fderiv ℝ χ)
    exact (hχc.fderiv ℝ).comp_left (by simp)
  have hχf : LocallyIntegrable (fun x => χ x * f x) (volume : Measure E) := by
    simpa [mul_comm] using h.1.continuous_mul hχ.continuous
  have hχg : LocallyIntegrable (fun x => χ x * g x) (volume : Measure E) := by
    simpa [mul_comm] using h.2.1.continuous_mul hχ.continuous
  have hχdf : LocallyIntegrable (fun x => fderiv ℝ χ x v * f x)
      (volume : Measure E) := by
    simpa [mul_comm] using h.1.continuous_mul hχd
  refine ⟨hχf, hχg.add hχdf, ?_⟩
  intro ψ hψ hψc
  have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
    change HasCompactSupport ((fun L : E →L[ℝ] ℝ => L v) ∘ fderiv ℝ ψ)
    exact (hψc.fderiv ℝ).comp_left (by simp)
  have iA : Integrable
      (fun x => (χ x * f x) * fderiv ℝ ψ x v) (volume : Measure E) := by
    have hi := hχf.integrable_smul_left_of_hasCompactSupport hψd hψdc
    convert hi using 1
    funext x
    ring
  have iB : Integrable
      (fun x => (f x * ψ x) * fderiv ℝ χ x v) (volume : Measure E) := by
    have hi := h.1.continuous_mul hψ.continuous
      |>.integrable_smul_left_of_hasCompactSupport hχd hχdc
    convert hi using 1
    funext x
    ring
  have iC : Integrable
      (fun x => (χ x * g x) * ψ x) (volume : Measure E) := by
    have hi := hχg.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    convert hi using 1
    funext x
    ring
  have iD : Integrable
      (fun x => (fderiv ℝ χ x v * f x) * ψ x) (volume : Measure E) := by
    have hi := hχdf.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    convert hi using 1
    funext x
    ring
  have hderiv : ∀ x,
      fderiv ℝ (fun y => χ y * ψ y) x v =
        χ x * fderiv ℝ ψ x v + ψ x * fderiv ℝ χ x v := by
    intro x
    change (fderiv ℝ (χ * ψ) x) v =
      χ x * fderiv ℝ ψ x v + ψ x * fderiv ℝ χ x v
    rw [fderiv_mul
      ((hχ.differentiable (by simp)).differentiableAt)
      ((hψ.differentiable (by simp)).differentiableAt)]
    simp [smul_eq_mul]
  have hsum :
      (∫ x, (χ x * f x) * fderiv ℝ ψ x v ∂(volume : Measure E)) +
          (∫ x, (f x * ψ x) * fderiv ℝ χ x v ∂(volume : Measure E)) =
        -(∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) := by
    calc
      (∫ x, (χ x * f x) * fderiv ℝ ψ x v ∂(volume : Measure E)) +
            (∫ x, (f x * ψ x) * fderiv ℝ χ x v ∂(volume : Measure E)) =
          ∫ x, ((χ x * f x) * fderiv ℝ ψ x v +
            (f x * ψ x) * fderiv ℝ χ x v) ∂(volume : Measure E) :=
        (integral_add iA iB).symm
      _ = ∫ x, f x * fderiv ℝ (fun y => χ y * ψ y) x v ∂(volume : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hderiv x]
        ring
      _ = -∫ x, g x * (χ x * ψ x) ∂(volume : Measure E) :=
        h.2.2 (fun x => χ x * ψ x) (hχ.mul hψ) hχc.mul_right
      _ = -(∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with x
        ring
  have hBD :
      (∫ x, (f x * ψ x) * fderiv ℝ χ x v ∂(volume : Measure E)) =
        ∫ x, (fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E) := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hCD :
      (∫ x, (χ x * g x + fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E)) =
        (∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) +
          (∫ x, (fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E)) := by
    calc
      ∫ x, (χ x * g x + fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E) =
          ∫ x, ((χ x * g x) * ψ x + (fderiv ℝ χ x v * f x) * ψ x) ∂(volume : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = (∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) +
          (∫ x, (fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E)) :=
        integral_add iC iD
  calc
    ∫ x, (χ x * f x) * fderiv ℝ ψ x v ∂(volume : Measure E) =
        -(∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) -
          ∫ x, (fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E) := by
      linarith [hsum, hBD]
    _ = -∫ x, (χ x * g x + fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E) := by
      rw [hCD]
      ring

/-- Affine weak chain rule: `c + d f` has weak derivative `d g`. No `L²` hypothesis. -/
theorem HasWeakDerivAlong.const_add_mul {f g : E → ℝ} {v : E} (h : HasWeakDerivAlong f g v)
    (c d : ℝ) : HasWeakDerivAlong (fun x => c + d * f x) (fun x => d * g x) v := by
  have hc : HasWeakDerivAlong (fun _ : E => c) (fun _ => 0) v := by
    simpa using hasWeakDerivAlong_of_contDiff (contDiff_const (c := c)) v
  have hlocf : LocallyIntegrable (fun x => c + d * f x) (volume : Measure E) := by
    exact (hc.1.add (h.1.smul d)).congr (ae_of_all _ fun x => rfl)
  have hlocg : LocallyIntegrable (fun x => d * g x) (volume : Measure E) := by
    exact (h.2.1.smul d).congr (ae_of_all _ fun x => rfl)
  refine ⟨hlocf, hlocg, ?_⟩
  intro ψ hψ hψc
  have hD : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := hψc.fderiv_apply ℝ v
  have hci : Integrable (fun x => c * fderiv ℝ ψ x v) (volume : Measure E) :=
    (hD.const_mul c).integrable_of_hasCompactSupport hDc.mul_left
  have hfi : Integrable (fun x => f x * fderiv ℝ ψ x v) (volume : Measure E) := by
    simpa only [smul_eq_mul, mul_comm] using
      h.1.integrable_smul_left_of_hasCompactSupport hD hDc
  calc
    (∫ x, (c + d * f x) * fderiv ℝ ψ x v) =
        (∫ x, c * fderiv ℝ ψ x v) + d * (∫ x, f x * fderiv ℝ ψ x v) := by
      rw [← integral_const_mul d]
      rw [← integral_add hci (hfi.const_mul d)]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = -(∫ x, 0 * ψ x) + d * (-(∫ x, g x * ψ x)) := by rw [hc.2.2 ψ hψ hψc, h.2.2 ψ hψ hψc]
    _ = -(∫ x, (d * g x) * ψ x) := by
      simp only [zero_mul, integral_zero, neg_zero, zero_add]
      rw [show (fun x => (d * g x) * ψ x) = (fun x => d * (g x * ψ x)) from
          funext fun _ => by ring,
        integral_const_mul]
      ring

end FunctionalInequalities.Analysis

universe u

namespace FunctionalInequalities.Analysis

/-- Weak directional derivatives are invariant under almost-everywhere
changes of both the function and its derivative. Local integrability is produced. -/
theorem HasWeakDerivAlong.congr_ae {E : Type u}
    [instNormedAddCommGroup : NormedAddCommGroup E]
    [instInnerProductSpace : InnerProductSpace ℝ E]
    [instFiniteDimensional : FiniteDimensional ℝ E]
    [instMeasurableSpace : MeasurableSpace E] [instBorelSpace : BorelSpace E]
    {f f' g g' : E → ℝ} {v : E}
    (h : HasWeakDerivAlong f g v)
    (hf : f =ᵐ[(volume : Measure E)] f')
    (hg : g =ᵐ[(volume : Measure E)] g') :
    HasWeakDerivAlong f' g' v := by
  refine ⟨h.1.congr hf, h.2.1.congr hg, ?_⟩
  intro ψ hψ hψc
  have ef :
      (∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E)) =
        ∫ x, f' x * fderiv ℝ ψ x v ∂(volume : Measure E) := by
    apply integral_congr_ae
    exact hf.mono (fun x hx => congrArg (fun r : ℝ => r * fderiv ℝ ψ x v) hx)
  have eg :
      (∫ x, g x * ψ x ∂(volume : Measure E)) =
        ∫ x, g' x * ψ x ∂(volume : Measure E) := by
    apply integral_congr_ae
    exact hg.mono (fun x hx => congrArg (fun r : ℝ => r * ψ x) hx)
  calc
    (∫ x, f' x * fderiv ℝ ψ x v ∂(volume : Measure E)) =
        ∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E) := ef.symm
    _ = -∫ x, g x * ψ x ∂(volume : Measure E) := h.2.2 ψ hψ hψc
    _ = -∫ x, g' x * ψ x ∂(volume : Measure E) :=
      congrArg (fun r : ℝ => -r) eg


end FunctionalInequalities.Analysis
