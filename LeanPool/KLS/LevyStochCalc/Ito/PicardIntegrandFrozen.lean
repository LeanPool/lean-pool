/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardIntegrandBounds

/-!
# The Picard step along a frozen state process

`picardStep` asks for its integrands to be square integrable at every horizon, while a member
of the process space is `L²`-controlled only on `[0, T]`. Freezing the path at the horizon
closes that gap: off `[0, T]` the frozen path repeats its value at `T`, so the linear growth of
the coefficients bounds the integrands at every horizon. The measurability and square
integrability of the integrands are specialised here to a frozen path, both for a member of the
process space and for a raw state process of finite Bielecki norm, and the Picard step is run
on each.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Frozen

variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
variable {ν : MeasureTheory.Measure E}
variable {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

/-- Joint measurability of the diffusion integrand along the frozen process. -/
theorem measurable_sigma_stop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    (Y : SBoundedProcess (n := n) P ℱ T) (i : Fin n) (j : Fin d) :
    Measurable (Function.uncurry fun ω s => coeffs.σ s (Y.stop.X s ω) i j) :=
  measurable_sigma_comp_state coeffs hReg Y.stop.measurable_path i j

/-- Progressive measurability of the diffusion integrand along the frozen process. -/
theorem progressivelyMeasurable_sigma_stop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    (Y : SBoundedProcess (n := n) P ℱ T) (i : Fin n) (j : Fin d) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y.stop.X s ω) i j) := by
  have h : Measurable (Function.uncurry fun (s : ℝ) (x : Fin n → ℝ) => coeffs.σ s x i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hReg.2.1)
  exact progressivelyMeasurable_comp_state Y.stop.adapted h

/-- Joint measurability of the jump integrand along the frozen process. -/
theorem measurable_gamma_stop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    (Y : SBoundedProcess (n := n) P ℱ T) (i : Fin n) :
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y.stop.X p.2.1 p.1) p.2.2 i :=
  measurable_gamma_comp_state coeffs hReg Y.stop.measurable_path i

/-- Marked progressive measurability of the jump integrand along the frozen process. -/
theorem markedProgressivelyMeasurable_gamma_stop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    (Y : SBoundedProcess (n := n) P ℱ T) (i : Fin n) :
    Probability.MarkedProgressivelyMeasurable ℱ
      (fun ω s e => coeffs.γ s (Y.stop.X s ω) e i) := by
  have h : Measurable fun p : ℝ × (Fin n → ℝ) × E => coeffs.γ p.1 p.2.1 p.2.2 i :=
    (measurable_pi_apply i).comp hReg.2.2.1
  exact markedProgressivelyMeasurable_comp_state
    (g := fun (s : ℝ) (x : Fin n → ℝ) (e : E) => coeffs.γ s x e i) Y.stop.adapted h


/-- Joint measurability of the drift integrand along the frozen process. -/
theorem measurable_mu_stop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    (Y : SBoundedProcess (n := n) P ℱ T) (i : Fin n) :
    Measurable (Function.uncurry fun ω s => coeffs.μ s (Y.stop.X s ω) i) :=
  measurable_mu_comp_state coeffs hReg Y.stop.measurable_path i

/-- Progressive measurability of the drift integrand along the frozen process. -/
theorem progressivelyMeasurable_mu_stop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    (Y : SBoundedProcess (n := n) P ℱ T) (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.μ s (Y.stop.X s ω) i) := by
  have h : Measurable (Function.uncurry fun (s : ℝ) (x : Fin n → ℝ) => coeffs.μ s x i) :=
    (measurable_pi_apply i).comp hReg.1
  exact progressivelyMeasurable_comp_state Y.stop.adapted h

/-! ### The Picard step along a raw state process -/

/-- Joint measurability of the diffusion integrand along a raw process frozen at the horizon. -/
theorem measurable_sigma_rawStop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z)) (T : ℝ)
    (i : Fin n) (j : Fin d) :
    Measurable (Function.uncurry fun ω s => coeffs.σ s (Z (min s T) ω) i j) :=
  measurable_sigma_comp_state coeffs hReg (X := fun s ω => Z (min s T) ω)
    (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)) i j

/-- Progressive measurability of the diffusion integrand along a raw process frozen at the
horizon. -/
theorem progressivelyMeasurable_sigma_rawStop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i) (T : ℝ)
    (i : Fin n) (j : Fin d) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (Z (min s T) ω) i j := by
  have h : Measurable (Function.uncurry fun (s : ℝ) (x : Fin n → ℝ) => coeffs.σ s x i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hReg.2.1)
  exact progressivelyMeasurable_comp_state (X := fun s ω => Z (min s T) ω)
    (fun i' => (hZa i').minTime T) h

/-- Joint measurability of the jump integrand along a raw process frozen at the horizon. -/
theorem measurable_gamma_rawStop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z)) (T : ℝ) (i : Fin n) :
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Z (min p.2.1 T) p.1) p.2.2 i :=
  measurable_gamma_comp_state coeffs hReg (X := fun s ω => Z (min s T) ω)
    (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)) i

/-- Marked progressive measurability of the jump integrand along a raw process frozen at the
horizon. -/
theorem markedProgressivelyMeasurable_gamma_rawStop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i) (T : ℝ)
    (i : Fin n) :
    Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => coeffs.γ s (Z (min s T) ω) e i := by
  have h : Measurable fun p : ℝ × (Fin n → ℝ) × E => coeffs.γ p.1 p.2.1 p.2.2 i :=
    (measurable_pi_apply i).comp hReg.2.2.1
  exact markedProgressivelyMeasurable_comp_state (X := fun s ω => Z (min s T) ω)
    (g := fun s x e => coeffs.γ s x e i) (fun i' => (hZa i').minTime T) h

/-- Joint measurability of the drift integrand along a raw process frozen at the horizon. -/
theorem measurable_mu_rawStop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z)) (T : ℝ) (i : Fin n) :
    Measurable (Function.uncurry fun ω s => coeffs.μ s (Z (min s T) ω) i) :=
  measurable_mu_comp_state coeffs hReg (X := fun s ω => Z (min s T) ω)
    (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)) i

/-- Progressive measurability of the drift integrand along a raw process frozen at the
horizon. -/
theorem progressivelyMeasurable_mu_rawStop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i) (T : ℝ)
    (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.μ s (Z (min s T) ω) i := by
  have h : Measurable (Function.uncurry fun (s : ℝ) (x : Fin n → ℝ) => coeffs.μ s x i) :=
    (measurable_pi_apply i).comp hReg.1
  exact progressivelyMeasurable_comp_state (X := fun s ω => Z (min s T) ω)
    (fun i' => (hZa i').minTime T) h

/-- The horizon energy bounds of a raw process frozen at the horizon, from a finite Bielecki
norm at weight `0`. -/
theorem lintegral_sq_rawStop_lt_top {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) (hZb : bieleckiNorm (P := P) 0 T Z < ⊤)
    (hT : 0 ≤ T) (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i', (‖Z (min s T) ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lt_of_le_of_lt (lintegral_lintegral_sq_stopOf_le T Z hZm hT b)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hZb))

/-- **The Picard step along a raw state process frozen at the horizon.** -/
noncomputable def picardStepOnRawStop [MeasureTheory.SigmaFinite ν]
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) (hT : 0 ≤ T) (x₀ : Fin n → ℝ) :
    ℝ → Ω → (Fin n → ℝ) :=
  picardStep W N ℱ hℱW hℱN coeffs (fun s ω => Z (min s T) ω) x₀
    (measurable_sigma_rawStop coeffs hReg hZm T)
    (progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i j _ hT' => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT) i j hT')
    (measurable_gamma_rawStop coeffs hReg hZm T)
    (markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i _ hT' => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT) i hT')

/-- **The Picard map applied to a frozen member of the process space.**

Freezing at the horizon is what makes the step total: `picardStep` asks for its integrands to be
square integrable at every horizon, which `SBoundedProcess.sup_L2` supplies only on `[0, T]`. -/
noncomputable def picardStepOnStop [MeasureTheory.SigmaFinite ν]
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T) (x₀ : Fin n → ℝ) :
    ℝ → Ω → (Fin n → ℝ) :=
  picardStep W N ℱ hℱW hℱN coeffs Y.stop.X x₀
    (fun i j => measurable_sigma_stop coeffs hReg Y i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg Y i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT i j hT')
    (fun i => measurable_gamma_stop coeffs hReg Y i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg Y i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT i hT')

end Frozen

end LevyStochCalc.Ito.Picard
