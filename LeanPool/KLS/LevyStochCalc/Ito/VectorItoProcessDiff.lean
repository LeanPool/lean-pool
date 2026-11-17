/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoTruncate
public import LeanPool.KLS.LevyStochCalc.Ito.PicardOutput

/-!
# The `L²` distance between two vector Itô processes

Two vector Itô processes with the same initial value differ by the time integral of the difference
of their drifts and the Itô integral of the difference of their diffusion matrices. Cauchy–Schwarz
bounds the first in `L²` by the energy of the drift difference and the Itô isometry identifies the
second with the energy of the diffusion difference.

The file sits in the `Ito` layer only because the Cauchy–Schwarz bound
`LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le` lives there; nothing here depends on the
Picard construction itself.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_sq_norm_vectorItoProcess_sub_le` — the bound.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Diff

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

omit [IsProbabilityMeasure P] in
/-- A path with finite energy on a window is integrable there, almost surely. -/
theorem ae_integrableOn_of_energy_lt_top {b : Ω → ℝ → ℝ}
    (hbm : Measurable (Function.uncurry b)) {t : ℝ}
    (hbq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, IntegrableOn (b ω) (Set.Icc (0 : ℝ) t) volume := by
  have : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  filter_upwards [MeasureTheory.ae_lt_top (measurable_energyDensity hbm t) hbq.ne] with ω hω
  exact (LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top
    (Measurable.of_uncurry_left hbm) hω).integrable (by norm_num)

/-- **The `L²` distance between two vector Itô processes with the same initial value.** -/
theorem lintegral_sq_norm_vectorItoProcess_sub_le
    {H₁ H₂ : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm₁ : ∀ p k, Measurable (Function.uncurry (H₁ p k)))
    (hp₁ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₁ p k))
    (hq₁ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : ∀ p k, Measurable (Function.uncurry (H₂ p k)))
    (hp₂ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₂ p k))
    (hq₂ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b₁ b₂ : Fin n → Ω → ℝ → ℝ}
    (hbm₁ : ∀ p, Measurable (Function.uncurry (b₁ p)))
    (hbm₂ : ∀ p, Measurable (Function.uncurry (b₂ p)))
    {t : ℝ} (ht : 0 < t)
    (hbq₁ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hbq₂ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω
        - vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ p : Fin n, (2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
  classical
  have hXm₁ : Measurable (vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t) :=
    measurable_vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ hX₀ hbm₁ t
  have hXm₂ : Measurable (vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t) :=
    measurable_vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ hX₀ hbm₂ t
  have hcoordm : ∀ p : Fin n, Measurable fun ω =>
      (‖vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
        - vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p‖₊ : ℝ≥0∞) ^ 2 := by
    intro p
    exact ((((measurable_pi_apply p).comp hXm₂).sub
      ((measurable_pi_apply p).comp hXm₁)).nnnorm.coe_nnreal_ennreal).pow_const 2
  -- reduce to the coordinates
  have hred : ∫⁻ ω, (‖vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω
        - vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ p : Fin n, ∫⁻ ω, (‖vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
          - vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    rw [← MeasureTheory.lintegral_finsetSum _ fun p _ => hcoordm p]
    refine MeasureTheory.lintegral_mono fun ω => ?_
    simpa using sq_enorm_pi_le_sum (vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω
      - vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω)
  refine hred.trans (Finset.sum_le_sum fun p _ => ?_)
  -- split the coordinate difference into a drift part and a martingale part
  have hsplit : ∀ ω : Ω,
      vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
        - vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p
      = (((∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
            - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume))
        + (vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
          - vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω) := by
    intro ω
    simp only [vectorItoProcess]
    ring
  have hDbm : Measurable fun ω : Ω =>
      (‖(∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
        - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume‖₊ : ℝ≥0∞) ^ 2 :=
    ((((measurable_setIntegral (hbm₂ p) _).sub
      (measurable_setIntegral (hbm₁ p) _)).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hDmm : Measurable fun ω : Ω =>
      (‖vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
        - vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω‖₊ : ℝ≥0∞) ^ 2 :=
    ((((measurable_vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t).sub
      (measurable_vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t)).nnnorm
        ).coe_nnreal_ennreal).pow_const 2
  have hsum : ∫⁻ ω, (‖vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
        - vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * ∫⁻ ω, (‖(∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
            - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume‖₊ : ℝ≥0∞) ^ 2 ∂P
        + 2 * ∫⁻ ω, (‖vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
            - vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    have hmono : ∫⁻ ω, (‖vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
          - vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, (2 * (‖(∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
              - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume‖₊ : ℝ≥0∞) ^ 2
            + 2 * (‖vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
              - vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
      refine MeasureTheory.lintegral_mono fun ω => ?_
      rw [hsplit ω]
      have := sq_nnnorm_add_le_two_mul
        ((∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
          - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume)
        (vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
          - vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω)
      refine this.trans (le_of_eq ?_)
      rw [mul_add]
    refine hmono.trans (le_of_eq ?_)
    rw [MeasureTheory.lintegral_add_left (hDbm.const_mul 2),
      MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤),
      MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
  refine hsum.trans (add_le_add ?_ ?_)
  · -- the drift part, by Cauchy–Schwarz
    have hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
      lintegral_energy_lt_top_of_bound (fun ω s => sq_nnnorm_sub_le_two_mul _ _)
        (hbm₂ p) (hbm₁ p) (hbq₂ p) (hbq₁ p) t ht
    have heq : ∫⁻ ω, (‖(∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
          - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) t, (b₂ p ω s - b₁ p ω s) ∂volume‖₊ : ℝ≥0∞) ^ 2 ∂P := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [ae_integrableOn_of_energy_lt_top (hbm₁ p) (hbq₁ p t ht),
        ae_integrableOn_of_energy_lt_top (hbm₂ p) (hbq₂ p t ht)] with ω h1 h2
      rw [MeasureTheory.integral_sub h2 h1]
    rw [heq]
    exact mul_le_mul' le_rfl
      (LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le
        ((hbm₂ p).sub (hbm₁ p)) ht.le hfin)
  · -- the martingale part, by the difference isometry
    have hM : ∀ ω : Ω, vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
        - vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω
        = ∑ k : Fin d, (coordItoIntegral W ℱ hcoord H₂ hm₂ hp₂ hq₂ p k t ω
          - coordItoIntegral W ℱ hcoord H₁ hm₁ hp₁ hq₁ p k t ω) := by
      intro ω
      rw [vectorItoMartingale, vectorItoMartingale, ← Finset.sum_sub_distrib]
    have hkm : ∀ k : Fin d, Measurable fun ω : Ω =>
        (‖coordItoIntegral W ℱ hcoord H₂ hm₂ hp₂ hq₂ p k t ω
          - coordItoIntegral W ℱ hcoord H₁ hm₁ hp₁ hq₁ p k t ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro k
      exact ((((measurable_coordItoIntegral W ℱ hcoord H₂ hm₂ hp₂ hq₂ p k t).sub
        (measurable_coordItoIntegral W ℱ hcoord H₁ hm₁ hp₁ hq₁ p k t)).nnnorm
          ).coe_nnreal_ennreal).pow_const 2
    have hstep : ∫⁻ ω, (‖vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
          - vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ (d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω,
            (‖coordItoIntegral W ℱ hcoord H₂ hm₂ hp₂ hq₂ p k t ω
              - coordItoIntegral W ℱ hcoord H₁ hm₁ hp₁ hq₁ p k t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
      rw [← MeasureTheory.lintegral_finsetSum _ fun k _ => hkm k,
        ← MeasureTheory.lintegral_const_mul' _ _ (by simp : (d : ℝ≥0∞) ≠ ⊤)]
      refine MeasureTheory.lintegral_mono fun ω => ?_
      rw [hM ω]
      exact sq_enorm_finsetSum_le _
    refine mul_le_mul' le_rfl (hstep.trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun k _ => ?_)))
    exact le_of_eq (isometry_diff_stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
      (H₂ p k) (H₁ p k) (hm₂ p k) (hm₁ p k) (hp₂ p k) (hp₁ p k) (hq₂ p k) (hq₁ p k) ht)

end Diff

end LevyStochCalc.Brownian.Ito
