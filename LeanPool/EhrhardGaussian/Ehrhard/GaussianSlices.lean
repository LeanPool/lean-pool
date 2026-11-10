/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.ScalarFunctional
public import LeanPool.EhrhardGaussian.Gaussian.GaussianPoincareFinite
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Analysis.Normed.Group.CocompactMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-! # Gaussian slicing, tails, and quantile marginals for tensorization -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open EhrhardGaussian.Gaussian (standardGaussianMeasure finCons)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- Integration against the zero dimensional standard Gaussian measure evaluates at zero. -/
theorem integral_standardGaussian_zero (F : (Fin 0 → ℝ) → ℝ) :
    (∫ z, F z ∂standardGaussianMeasure 0) = F 0 := by
  have heq : F = fun _ => F 0 := funext fun z => congrArg F (Subsingleton.elim z 0)
  rw [heq]
  simp

/-- Adding a first coordinate commutes with linear combinations. -/
theorem finCons_linear_combination {n : ℕ} (p q r s : ℝ) (x y : Fin n → ℝ) :
    p • finCons r x + q • finCons s y = finCons (p * r + q * s) (p • x + q • y) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [finCons, smul_eq_mul]

/-- The map adjoining a first coordinate is continuous. -/
theorem continuous_finCons {n : ℕ} : Continuous (fun p : ℝ × (Fin n → ℝ) => finCons p.1 p.2) :=
  (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).continuous

/-- The norm of the first coordinate is bounded by the norm of the full vector. -/
theorem norm_finCons_first {n : ℕ} (r : ℝ) (x : Fin n → ℝ) : ‖r‖ ≤ ‖finCons r x‖ := by
  simpa only [finCons, Fin.cons_zero] using norm_le_pi_norm (finCons r x) 0

/-- The norm of the remaining coordinates is bounded by the norm of the full vector. -/
theorem norm_finCons_tail {n : ℕ} (r : ℝ) (x : Fin n → ℝ) : ‖x‖ ≤ ‖finCons r x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  simpa only [finCons, Fin.cons_succ] using norm_le_pi_norm (finCons r x) i.succ

/-- A vector escapes compact sets when its first coordinate does and its tail is fixed. -/
theorem finCons_scalar_cocompact {n : ℕ} (x : Fin n → ℝ) :
    Tendsto (fun r : ℝ => finCons r x) (cocompact ℝ) (cocompact (Fin (n + 1) → ℝ)) := by
  apply tendsto_cocompact_cocompact_of_norm
  intro R
  exact ⟨R, fun r hr => hr.trans_le (norm_finCons_first r x)⟩


/-- The Gaussian marginal integrates out the first coordinate against standard Gaussian measure. -/
def gaussianMarginal {n : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ r, F (finCons r x) ∂gaussianReal 0 1

/-- The Gaussian marginal of a bounded continuous function is continuous. -/
theorem continuous_gaussianMarginal {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : Continuous F) {B : ℝ} (hbound : ∀ z, |F z| ≤ B) : Continuous (gaussianMarginal F) := by
  apply continuous_of_dominated (μ := gaussianReal 0 1) (bound := fun _ => B)
  · intro x
    exact (hF.comp (continuous_finCons.comp (continuous_id.prodMk
      continuous_const))).aestronglyMeasurable
  · intro x
    exact ae_of_all _ fun r => by simpa only [Real.norm_eq_abs] using hbound _
  · exact integrable_const B
  · exact ae_of_all _ fun r => hF.comp (continuous_finCons.comp (continuous_const.prodMk
    continuous_id))

/-- Integrating a Gaussian marginal recovers the integral over all coordinates. -/
theorem integral_gaussianMarginal {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : Continuous F) {B : ℝ} (hbound : ∀ z, |F z| ≤ B) :
    (∫ x, gaussianMarginal F x ∂standardGaussianMeasure n) = ∫ z, F z ∂standardGaussianMeasure (n +
      1) := by
  let μ := fun _ : Fin (n + 1) => gaussianReal 0 1
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have heq : (e.symm : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ)) = fun p => finCons p.1 p.2 := by
    funext p
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
    change Fin.insertNth 0 p.1 p.2 = finCons p.1 p.2
    exact Fin.insertNth_zero' _ _
  have hrep := (measurePreserving_piFinSuccAbove μ 0).symm.integral_comp' F
  rw [heq] at hrep
  have hint : Integrable (fun p : ℝ × (Fin n → ℝ) => F (finCons p.1 p.2))
      ((gaussianReal 0 1).prod (standardGaussianMeasure n)) :=
    Integrable.of_bound (hF.comp continuous_finCons).aestronglyMeasurable B
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hbound _)
  exact (integral_prod_symm _ hint).symm.trans hrep

/-- The Gaussian marginal of a continuous Gaussian distribution function takes values strictly
between zero and one. -/
theorem gaussianMarginal_CDF_mem_Ioo {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ}
    (hu : Continuous u) (x : Fin n → ℝ) : gaussianMarginal (gaussianCDF ∘ u) x ∈ Ioo (0 : ℝ) 1 :=
  integral_gaussianCDF_mem_Ioo (gaussianReal 0 1)
    (hu.comp (continuous_finCons.comp (continuous_id.prodMk continuous_const))).measurable

/-- A Gaussian distribution marginal tends to zero when its argument tends to minus infinity at
infinity. -/
theorem tendsto_gaussianMarginal_CDF_zero {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ}
    (hu : Continuous u) (htail : Tendsto u (cocompact (Fin (n + 1) → ℝ)) atBot) :
    Tendsto (gaussianMarginal (gaussianCDF ∘ u)) (cocompact (Fin n → ℝ)) (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun x => ha.trans_le (integral_nonneg (fun r => (gaussianCDF_pos
      _).le))
  · intro b hb
    have hPhi : Tendsto gaussianCDF atBot (𝓝 0) := tendsto_cdf_atBot (gaussianReal 0 1)
    obtain ⟨m, hm⟩ := (hPhi.eventually (gt_mem_nhds hb)).exists
    obtain ⟨R, hR⟩ := closedBall_compl_subset_of_mem_cocompact
      (htail.eventually (eventually_le_atBot m)) 0
    filter_upwards [(isCompact_closedBall (0 : Fin n → ℝ) R).compl_mem_cocompact] with x hx
    have hxnorm : R < ‖x‖ := by simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
      using hx
    have hupper (r : ℝ) : gaussianCDF (u (finCons r x)) ≤ gaussianCDF m := by
      apply strictMono_gaussianCDF.monotone
      apply hR
      simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using
        hxnorm.trans_le (norm_finCons_tail r x)
    have hi := integral_mem_Icc_of_range (gaussianReal 0 1)
      ((continuous_gaussianCDF.comp hu).comp
        (continuous_finCons.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
      (fun r => ⟨(gaussianCDF_pos _).le, hupper r⟩)
    exact hi.2.trans_lt hm

/-- Gaussian quantiles tend to minus infinity when probabilities in the open unit interval tend to
zero. -/
theorem quantile_tendsto_atBot_of_tendsto_zero {α : Type*} {l : Filter α} {F : α → ℝ}
    (hF : Tendsto F l (𝓝 0)) (hrange : ∀ x, F x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => gaussianCDFChart.symm (F x)) l atBot := by
  apply tendsto_atBot.mpr
  intro b
  filter_upwards [hF.eventually (gt_mem_nhds (gaussianCDF_pos b))] with x hx
  apply strictMono_gaussianCDF.le_iff_le.mp
  rw [gaussianCDF_chart_symm (hrange x)]
  exact hx.le

/-- The Gaussian quantile marginal is the Gaussian quantile of the distribution function marginal.
-/
def gaussianQuantileMarginal {n : ℕ} (u : (Fin (n + 1) → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  gaussianCDFChart.symm (gaussianMarginal (gaussianCDF ∘ u) x)

/-- The Gaussian quantile marginal of a continuous function is continuous. -/
theorem continuous_gaussianQuantileMarginal {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ}
    (hu : Continuous u) : Continuous (gaussianQuantileMarginal u) := by
  have hF := continuous_gaussianMarginal (continuous_gaussianCDF.comp hu)
    (fun z => by simpa only [Function.comp_apply, abs_of_pos (gaussianCDF_pos _)] using
      (gaussianCDF_lt_one (u z)).le)
  exact contDiffOn_gaussianCDFChart_symm.continuousOn.comp_continuous hF
    (gaussianMarginal_CDF_mem_Ioo hu)

/-- Gaussian quantile marginalization preserves decay to minus infinity at infinity. -/
theorem tendsto_gaussianQuantileMarginal_atBot {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ}
    (hu : Continuous u) (htail : Tendsto u (cocompact (Fin (n + 1) → ℝ)) atBot) :
    Tendsto (gaussianQuantileMarginal u) (cocompact (Fin n → ℝ)) atBot :=
  quantile_tendsto_atBot_of_tendsto_zero (tendsto_gaussianMarginal_CDF_zero hu htail)
    (gaussianMarginal_CDF_mem_Ioo hu)

/-- The Gaussian distribution function of the quantile marginal equals the distribution function
marginal. -/
theorem gaussianCDF_gaussianQuantileMarginal {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ}
    (hu : Continuous u) (x : Fin n → ℝ) :
    gaussianCDF (gaussianQuantileMarginal u x) = gaussianMarginal (gaussianCDF ∘ u) x :=
  gaussianCDF_chart_symm (gaussianMarginal_CDF_mem_Ioo hu x)

/-- Gaussian quantile marginalization preserves an upper bound. -/
theorem gaussianQuantileMarginal_le {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ}
    (hu : Continuous u) {U : ℝ} (hU : ∀ z, u z ≤ U) (x : Fin n → ℝ) : gaussianQuantileMarginal u x ≤
      U := by
  apply strictMono_gaussianCDF.le_iff_le.mp
  rw [gaussianCDF_gaussianQuantileMarginal hu]
  exact (integral_mem_Icc_of_range (gaussianReal 0 1)
    ((continuous_gaussianCDF.comp hu).comp
      (continuous_finCons.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
    (fun r => ⟨(gaussianCDF_pos _).le, strictMono_gaussianCDF.monotone (hU _)⟩)).2

end EhrhardGaussian.Ehrhard

end
