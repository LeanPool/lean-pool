/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Scalar Hilbert pairings on space-time slabs

The scalar real `L²` pairing is an integral on any measurable carrier.
Strong `L²` convergence consequently implies convergence against every
fixed `L²` test field.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology


noncomputable section

namespace ESS

/-- The real scalar `L²` pairing equals the integral of the product on
any measurable carrier (`prop:lps-smoothing`). -/
theorem lps_scalar_lp_inner_integral_generic
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ z, f z * g z ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- A scalar `L²` class pairs with a square-integrable representative
by integrating its chosen measurable representative (`prop:lps-smoothing`). -/
theorem lps_scalar_lp_inner_left_integral_generic
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : Lp ℝ 2 μ) {g : α → ℝ} (hg : MemLp g 2 μ) :
    inner ℝ F (hg.toLp g) = ∫ z, F z * g z ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with z h
  rw [h]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- Strong scalar `L²` convergence gives convergence of all fixed
`L²` pairings (`prop:lps-smoothing`). -/
theorem lps_scalar_lp_pairing_tendsto_of_strong
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {fseq : ℕ → α → ℝ} {f w : α → ℝ}
    (hfseq : ∀ n, MemLp (fseq n) 2 μ)
    (hf : MemLp f 2 μ) (hw : MemLp w 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (fseq n - f) 2 μ)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, fseq n z * w z ∂μ) atTop
      (𝓝 (∫ z, f z * w z ∂μ)) := by
  have hstrong : Tendsto
      (fun n => (hfseq n).toLp (fseq n)) atTop
      (𝓝 (hf.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fseq hfseq f hf).2 hconv
  have hcontinuous : Continuous
      (fun F : Lp ℝ 2 μ => inner ℝ F (hw.toLp w)) :=
    continuous_inner.comp (continuous_id.prodMk continuous_const)
  have hpair := hcontinuous.continuousAt.tendsto.comp hstrong
  convert hpair using 1
  · funext n
    exact (lps_scalar_lp_inner_integral_generic (hfseq n) hw).symm
  · exact congrArg nhds (lps_scalar_lp_inner_integral_generic hf hw).symm

end ESS
