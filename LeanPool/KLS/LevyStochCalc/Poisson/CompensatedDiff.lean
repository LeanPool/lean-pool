/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system (module
-- header, public imports, exposed public section) for Lean/Mathlib v4.35.0; proofs use the v4.35.0
-- `eLpNorm`/`MemLp` API.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedProcessQuadVar

/-!
# The difference isometry of the compensated integral process

For two integrands `φ₁, φ₂`, the `L²` integral processes satisfy
`∫⁻ ‖F₁(t) − F₂(t)‖² = ∫⁻∫⁻_{[0,t]}∫⁻ ‖φ₁ − φ₂‖²`: the stage approximants of the two
integrands are refined to a common dyadic grid, where the difference isometry of mark-step
integrands holds at every time, and both sides pass to the limit in `L²`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ₁ φ₂ : Ω → ℝ → E → ℝ)
  (h_meas₁ : Measurable (fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2))
  (h_meas₂ : Measurable (fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2))
  (h_progMeas₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
  (h_progMeas₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
  (h_sq₁ : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (h_sq₂ : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in
/-- The difference isometry of the stage approximants of two integrands at every time. -/
lemma stageIntegral_sub_lintegral_sq {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∫⁻ ω, (‖stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
        - stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ p, (‖stageEval N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n p
          - stageEval N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n p‖₊ : ℝ≥0∞) ^ 2
          ∂(horizonMeasure ν P t) := by
  have hA₁ := master_adapted N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n
  have hA₂ := master_adapted N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n
  have h₁ := le_max_left (master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).1
    (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).1
  have h₂ := le_max_right (master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).1
    (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).1
  have hiso := ((master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.dyadicRefine
    h₁).lintegral_integral_sub_sq_at N hℱ
    ((master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.dyadicRefine h₂) (hA₁.dyadicRefine N h₁)
    (hA₂.dyadicRefine N h₂) ht
  have hm : Measurable (fun p : Ω × ℝ × E =>
      (‖(master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval p.2.1 p.2.2 p.1
        - (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp
      ((master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval_measurable.sub
        (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval_measurable).nnNorm).pow_const 2
  have hL : ∫⁻ ω, (‖stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
        - stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖((master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.dyadicRefine h₁).integral N t ω
        - ((master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.dyadicRefine h₂).integral N t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [(master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.integral_dyadicRefine N hℱ h₁
      hA₁ t,
      (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.integral_dyadicRefine N hℱ h₂ hA₂ t]
      with ω hω₁ hω₂
    simp only [stageIntegral]
    rw [hω₁, hω₂]
  rw [hL, hiso]
  unfold stageEval
  rw [lintegral_horizonMeasure t (fun ω s e =>
    (‖(master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval s e ω
      - (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hm]
  refine lintegral_congr fun ω => ?_
  rw [← lintegral_swap_es (fun ω s e =>
    (‖(master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval s e ω
      - (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hm ω]
  refine lintegral_congr fun e => setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  rw [(master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval_dyadicRefine h₁,
    (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval_dyadicRefine h₂]

include hℱ in
/-- The difference isometry of the `L²` integral processes of two integrands. -/
theorem process_sub_lintegral_sq {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, (‖process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω
        - process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
          (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  have hI : Tendsto (fun n => eLpNorm
      ((fun ω => stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
        - stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω)
      - fun ω => process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω
        - process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω) 2 P) atTop (𝓝 0) := by
    have h₁ := stageIntegral_tendsto_process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t
    have h₂ := stageIntegral_tendsto_process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using h₁.add h₂) (Eventually.of_forall fun n => bot_le)
      (Eventually.of_forall fun n => ?_)
    calc eLpNorm ((fun ω => stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
            - stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω)
          - fun ω => process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω
            - process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω) 2 P
        = eLpNorm ((fun ω => stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
            - process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω)
          - fun ω => stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω
            - process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω) 2 P := by
          refine eLpNorm_congr_ae (Eventually.of_forall fun ω => ?_)
          simp only [Pi.sub_apply]
          ring
      _ ≤ _ := eLpNorm_sub_le (by norm_num)
  have hL := LevyStochCalc.Brownian.Ito.tendsto_lintegral_nnnorm_sq_of_eLpNorm
    (gₙ := fun n ω => stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
      - stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω)
    (g := fun ω => process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω
      - process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω)
    (fun n => ((memLp_stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t).sub
      (memLp_stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t)).aestronglyMeasurable)
    ((process_memLp N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t).sub
      (process_memLp N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t)).aestronglyMeasurable
    ((process_memLp N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t).sub
      (process_memLp N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t)).eLpNorm_ne_top hI
  have hE : Tendsto (fun n => eLpNorm
      ((fun p => stageEval N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n p
        - stageEval N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n p)
      - fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 - φ₂ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t))
      atTop (𝓝 0) := by
    have h₁ := stageEval_tendsto N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t
    have h₂ := stageEval_tendsto N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using h₁.add h₂) (Eventually.of_forall fun n => bot_le)
      (Eventually.of_forall fun n => ?_)
    calc eLpNorm ((fun p => stageEval N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n p
            - stageEval N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n p)
          - fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 - φ₂ p.1 p.2.1 p.2.2) 2
          (horizonMeasure ν P t)
        = eLpNorm ((stageEval N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n
            - fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
          - (stageEval N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n
            - fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)) 2 (horizonMeasure ν P t) := by
          refine eLpNorm_congr_ae (Eventually.of_forall fun p => ?_)
          simp only [Pi.sub_apply]
          ring
      _ ≤ _ := eLpNorm_sub_le (by norm_num)
  have hR := LevyStochCalc.Brownian.Ito.tendsto_lintegral_nnnorm_sq_of_eLpNorm
    (gₙ := fun n p => stageEval N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n p
      - stageEval N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n p)
    (g := fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 - φ₂ p.1 p.2.1 p.2.2)
    (fun n => ((measurable_stageEval N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).sub
      (measurable_stageEval N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n)).aestronglyMeasurable)
    (h_meas₁.sub h_meas₂).aestronglyMeasurable
    ((memLp_phi_horizon φ₁ h_meas₁ h_sq₁ ht).sub
      (memLp_phi_horizon φ₂ h_meas₂ h_sq₂ ht)).eLpNorm_ne_top hE
  simp_rw [stageIntegral_sub_lintegral_sq N ℱ hℱ φ₁ φ₂ h_meas₁ h_meas₂ h_progMeas₁ h_progMeas₂ h_sq₁
    h_sq₂ ht.le] at hL
  rw [tendsto_nhds_unique hL hR]
  exact lintegral_horizonMeasure t (fun ω s e => (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2)
    ((ENNReal.continuous_coe.measurable.comp (h_meas₁.sub h_meas₂).nnNorm).pow_const 2)

end LevyStochCalc.Poisson.Compensated
