/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicLimits
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.BallRotation
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.DeficitIntegrability
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# From complex disc submeans to ball deficit estimates

The nonnegative deficit is integrated without assuming in advance that the
potential is locally integrable or even finite almost everywhere.
-/

@[expose] public section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Unit discs in directions shorter than the ball radius stay in the ball. -/
theorem affineClosedDisc_subset_ball (a v : E) {R : ℝ} (hv : ‖v‖ < R) :
    affineClosedDisc a v 1 ⊆ ball a R := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg v) (by simpa using hz)).trans_lt hv

variable [MeasurableSpace E] [BorelSpace E]

/-- Local upper semicontinuity gives a measurable zero extension of the deficit.
No regularity outside the indicated measurable set is assumed. -/
theorem DiscPshOn.measurable_indicator_deficit {u : E → EReal} {U s : Set E}
    (hu : DiscPshOn u U) (hs : MeasurableSet s) (hsU : s ⊆ U) (C : ℝ) :
    Measurable (s.indicator (fun x => ((C : EReal) - u x).toENNReal)) := by
  classical
  have hsc : UpperSemicontinuousOn (fun x : s => u x) univ :=
    hu.upperSemicontinuousOn.comp continuous_subtype_val.continuousOn
      (fun x _ => hsU x.property)
  have hm : Measurable (fun x : s => ((C : EReal) - u x).toENNReal) :=
    (continuous_finiteDeficit C).measurable.comp
      (upperSemicontinuousOn_univ_iff.mp hsc).measurable
  refine measurable_of_restrict_of_restrict_compl hs ?_ ?_
  · convert hm using 1
    funext x
    simp [Set.domRestrict, x.property]
  · have hzero : sᶜ.domRestrict
        (s.indicator (fun x => ((C : EReal) - u x).toENNReal)) =
        fun _ : (sᶜ : Set E) => (0 : ℝ≥0∞) := by
      funext x
      change s.indicator (fun x => ((C : EReal) - u x).toENNReal) (x : E) = 0
      exact Set.indicator_of_notMem x.property _
    rw [hzero]
    exact measurable_const

theorem DiscPshOn.aemeasurable_deficit_restrict {u : E → EReal} {U s : Set E}
    (hu : DiscPshOn u U) (hs : MeasurableSet s) (hsU : s ⊆ U) (C : ℝ)
    (μ : Measure E) :
    AEMeasurable (fun x => ((C : EReal) - u x).toENNReal) (μ.restrict s) :=
  (aemeasurable_indicator_iff hs).mp
    (hu.measurable_indicator_deficit hs hsU C).aemeasurable

omit [MeasurableSpace E] [BorelSpace E] in
/-- Compact subsets admit a finite majorant, even if the potential has poles. -/
theorem DiscPshOn.exists_compact_upper_bound {u : E → EReal} {U K : Set E}
    (hu : DiscPshOn u U) (hK : IsCompact K) (hne : K.Nonempty) (hKU : K ⊆ U) :
    ∃ C : ℝ, ∀ y ∈ K, u y ≤ (C : EReal) := by
  obtain ⟨y, hy, hmax⟩ := (hu.upperSemicontinuousOn.mono hKU).exists_isMaxOn hne hK
  obtain ⟨C, hC, _⟩ := EReal.exists_rat_btwn_of_lt
    (lt_top_iff_ne_top.mpr (hu.ne_top y (hKU hy)))
  exact ⟨C, fun z hz => (hmax hz).trans hC.le⟩

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- Integrating the disc criterion over directions gives a ball estimate.
The center may have value `⊥`; no integrability assumption is used. -/
theorem DiscPshOn.ball_deficit_le {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : E) (R C : ℝ) (hBU : ball a R ⊆ U)
    (hC : ∀ y ∈ ball a R, u y ≤ (C : EReal)) :
    ∫⁻ x in ball a R, ((C : EReal) - u x).toENNReal ∂μ ≤
      μ (ball 0 R) * ((C : EReal) - u a).toENNReal := by
  let d : E → ℝ≥0∞ := fun x => ((C : EReal) - u x).toENNReal
  let f : E → ℝ≥0∞ := (ball a R).indicator d
  have hm : Measurable f := hu.measurable_indicator_deficit measurableSet_ball hBU C
  have hf : ∫⁻ x in ball a R, f x ∂μ = ∫⁻ x in ball a R, d x ∂μ :=
    setLIntegral_congr_fun measurableSet_ball (fun x hx => by simp [f, hx])
  have hrot (t : ℝ) :
      ∫⁻ v in ball 0 R, f (a + circleMap 0 1 t • v) ∂μ =
        ∫⁻ x in ball a R, d x ∂μ :=
    (lintegral_ball_add_circleMap_smul μ f a t R).trans hf
  have hc : Continuous (fun p : E × ℝ => a + circleMap 0 1 p.2 • p.1) := by
    fun_prop
  have hswap := lintegral_lintegral_swap
    (μ := μ.restrict (ball 0 R)) (ν := volume.restrict (Ioc 0 (2 * Real.pi)))
    (f := fun v t => f (a + circleMap 0 1 t • v)) (hm.comp hc.measurable).aemeasurable
  have hangle (v : E) (hv : v ∈ ball 0 R) :
      ∫⁻ t in Ioc 0 (2 * Real.pi), f (a + circleMap 0 1 t • v) ≤
        ENNReal.ofReal (2 * Real.pi) * d a := by
    have hD := affineClosedDisc_subset_ball a v (by simpa using hv)
    have heq :
        ∫⁻ t in Ioc 0 (2 * Real.pi), f (a + circleMap 0 1 t • v) =
          circleDeficit u a v 1 C := by
      apply lintegral_congr
      intro t
      have ht := hD (circle_mem_affineClosedDisc a v (by norm_num : (0 : ℝ) ≤ 1) t)
      simp [f, d, ht]
    rw [heq]
    exact hu.submean a v 1 (by norm_num) (hD.trans hBU) C (fun y hy => hC y (hD hy))
  have hmul : (∫⁻ x in ball a R, d x ∂μ) * ENNReal.ofReal (2 * Real.pi) ≤
      (μ (ball 0 R) * d a) * ENNReal.ofReal (2 * Real.pi) := by
    calc
      (∫⁻ x in ball a R, d x ∂μ) * ENNReal.ofReal (2 * Real.pi) =
          ∫⁻ t in Ioc 0 (2 * Real.pi),
            ∫⁻ v in ball 0 R, f (a + circleMap 0 1 t • v) ∂μ := by
              simp_rw [hrot]
              simp
      _ = ∫⁻ v in ball 0 R,
          (∫⁻ t in Ioc 0 (2 * Real.pi), f (a + circleMap 0 1 t • v)) ∂μ := hswap.symm
      _ ≤ ∫⁻ _v in ball 0 R, ENNReal.ofReal (2 * Real.pi) * d a ∂μ :=
        setLIntegral_mono' measurableSet_ball hangle
      _ = (μ (ball 0 R) * d a) * ENNReal.ofReal (2 * Real.pi) := by
        simp [mul_comm, mul_assoc]
  exact (ENNReal.mul_le_mul_iff_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) Real.pi_pos)))
    ENNReal.ofReal_ne_top).mp hmul

/-- A finite center of a disc-PSH potential controls an entire interior ball,
including its almost-everywhere finiteness and actual real representative. -/
theorem DiscPshOn.ae_finite_and_integrableOn_ball {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : E) {R : ℝ} (hR : 0 < R) (hB : closedBall a R ⊆ U) (ha : u a ≠ ⊥) :
    (∀ᵐ x ∂μ.restrict (ball a R), u x ≠ ⊤ ∧ u x ≠ ⊥) ∧
      IntegrableOn (fun x => (u x).toReal) (ball a R) μ ∧
      ((fun x => ((u x).toReal : EReal)) =ᶠ[ae (μ.restrict (ball a R))] u) := by
  obtain ⟨C, hC⟩ := hu.exists_compact_upper_bound (isCompact_closedBall a R)
    ⟨a, mem_closedBall_self hR.le⟩ hB
  have hBU : ball a R ⊆ U := ball_subset_closedBall.trans hB
  have hCa : u a ≠ ⊤ := hu.ne_top a (hB (mem_closedBall_self hR.le))
  have hda : ((C : EReal) - u a).toENNReal < ⊤ := by
    rw [← EReal.coe_toReal hCa ha, ← EReal.coe_sub, EReal.real_coe_toENNReal]
    exact ENNReal.ofReal_lt_top
  have hI := (hu.ball_deficit_le μ a R C hBU
    (fun y hy => hC y (ball_subset_closedBall hy))).trans_lt
      (ENNReal.mul_lt_top measure_ball_lt_top hda)
  refine ae_finite_and_integrableOn_of_lintegral_deficit_lt_top measure_ball_lt_top ?_
    (hu.aemeasurable_deficit_restrict measurableSet_ball hBU C μ) hI
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact hC x (ball_subset_closedBall hx)

end SGPT.Foundations.Analysis
