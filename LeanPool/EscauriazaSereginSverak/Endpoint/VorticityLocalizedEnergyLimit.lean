/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyCurve

/-!
# Limits of the mollified weak heat solution

The uniform limit `Z` of the mollified curves is continuous on `[a, τ]`,
starts at `w₀`, and agrees with the time slices of `w` for almost every time.
The mollified gradients converge in `L²` of the slab to the weak gradient of
`w` (`lem:localized-vorticity-energy`).
-/

public section

open MeasureTheory Set Filter
open scoped Topology Interval InnerProductSpace


noncomputable section

namespace ESS

open CKN CKN.Foundation.Parabolic

variable {a τ : ℝ} {w f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ} {w₀ : Vec3 → ℝ}

/-- An integral of a product of square-integrable functions is an `L²` inner
product. -/
theorem vl_integral_mul_eq_inner {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g ψ : α → ℝ} (hg : MemLp g 2 μ) (hψ : MemLp ψ 2 μ) :
    ∫ x, g x * ψ x ∂μ = ⟪hg.toLp g, hψ.toLp ψ⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp, hψ.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

/-- The limit curve. -/
@[expose] def vlLimit (sol : VlHeatSolution a τ w H f w₀) (t : Icc a τ) :
    Lp ℝ 2 (volume : Measure Vec3) :=
  limUnder atTop fun n => vlCurve sol n t

theorem vlLimit_tendsto (sol : VlHeatSolution a τ w H f w₀) (t : Icc a τ) :
    Tendsto (fun n => vlCurve sol n t) atTop (𝓝 (vlLimit sol t)) := by
  have hc := (vlCurve_uniformCauchy sol).cauchySeq (mem_univ t)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  exact tendsto_nhds_limUnder ⟨L, hL⟩

theorem vlLimit_continuous (sol : VlHeatSolution a τ w H f w₀) :
    Continuous (vlLimit sol) := by
  have hunif := (vlCurve_uniformCauchy sol).tendstoUniformlyOn_of_tendsto
    (fun t _ => vlLimit_tendsto sol t)
  rw [tendstoUniformlyOn_univ] at hunif
  exact hunif.continuous (Frequently.of_forall fun n => vlCurve_continuous sol n)

/-- At the initial time the limit is the initial datum. -/
theorem vlLimit_initial (sol : VlHeatSolution a τ w H f w₀) :
    vlLimit sol ⟨a, left_mem_Icc.2 sol.lt.le⟩ = sol.w₀_L2.toLp w₀ := by
  set t₀ : Icc a τ := ⟨a, left_mem_Icc.2 sol.lt.le⟩
  refine tendsto_nhds_unique (vlLimit_tendsto sol t₀) ?_
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hsq : ∀ n, ‖vlCurve sol n t₀ - sol.w₀_L2.toLp w₀‖ ^ 2 =
      ∫ x, (vlConv (vlMoll n) w₀ x - w₀ x) ^ 2 := by
    intro n
    have hn := (vlPrim_energy_le sol (vlMoll_kernel n) t₀.2).1
    rw [vlCurve, ← MemLp.toLp_sub, vl_norm_toLp_sq]
    congr 1
    funext x
    simp [vlPrim, t₀]
  have hlim := vlMoll_tendsto sol.w₀_L2
  have hroot : Tendsto (fun n => Real.sqrt (∫ x, (vlConv (vlMoll n) w₀ x - w₀ x) ^ 2))
      atTop (𝓝 0) := by
    simpa using hlim.sqrt
  refine hroot.congr (fun n => ?_)
  rw [← hsq n, Real.sqrt_sq (norm_nonneg _)]

/-- A jointly measurable version of the time primitive. -/
@[expose] def vlPrimM (a : ℝ) (k : Vec3 → ℝ) (w₀ : Vec3 → ℝ) (w : Vec3 × ℝ → ℝ)
    (H : Fin 3 → Vec3 × ℝ → ℝ) (f : Vec3 × ℝ → ℝ) (p : Vec3 × ℝ) : ℝ :=
  vlConv k w₀ p.1 + ∫ s, (Ioc a p.2).indicator (fun s => vlSource k w H f p.1 s) s

theorem vlPrimM_eq (a : ℝ) (k : Vec3 → ℝ) (w₀ : Vec3 → ℝ) (w : Vec3 × ℝ → ℝ)
    (H : Fin 3 → Vec3 × ℝ → ℝ) (f : Vec3 × ℝ → ℝ) (x : Vec3) {t : ℝ} (ht : a ≤ t) :
    vlPrimM a k w₀ w H f (x, t) = vlPrim a k w₀ w H f x t := by
  simp only [vlPrimM, vlPrim]
  rw [intervalIntegral.integral_of_le ht, integral_indicator measurableSet_Ioc]

theorem vlPrimM_stronglyMeasurable (sol : VlHeatSolution a τ w H f w₀) {k : Vec3 → ℝ}
    (hk : IsVlKernel k) :
    StronglyMeasurable (vlPrimM a k w₀ w H f) := by
  have hc : StronglyMeasurable (fun p : Vec3 × ℝ => vlConv k w₀ p.1) :=
    ((vlConv_continuous hk (sol.w₀_L2.locallyIntegrable (by norm_num))).comp
      continuous_fst).stronglyMeasurable
  have hG := vlSource_stronglyMeasurable sol hk
  have hset : MeasurableSet {q : (Vec3 × ℝ) × ℝ | q.2 ∈ Ioc a q.1.2} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.snd)
  have hF : StronglyMeasurable (fun q : (Vec3 × ℝ) × ℝ =>
      (Ioc a q.1.2).indicator (fun s => vlSource k w H f q.1.1 s) q.2) := by
    have h := StronglyMeasurable.indicator
      (hG.comp_measurable (measurable_fst.fst.prodMk measurable_snd)) hset
    have heq : (fun q : (Vec3 × ℝ) × ℝ =>
        (Ioc a q.1.2).indicator (fun s => vlSource k w H f q.1.1 s) q.2) =
        {q : (Vec3 × ℝ) × ℝ | q.2 ∈ Ioc a q.1.2}.indicator
          ((fun p : Vec3 × ℝ => vlSource k w H f p.1 p.2) ∘
            fun q : (Vec3 × ℝ) × ℝ => (q.1.1, q.2)) := by
      funext q
      simp only [indicator, mem_ofPred_eq, Function.comp_apply]
    rw [heq]
    exact h
  exact hc.add (hF.integral_prod_right' (ν := volume))

/-- For almost every time, each mollified primitive is the mollification of the
time slice. -/
theorem vlPrim_slice_ae (sol : VlHeatSolution a τ w H f w₀) (n : ℕ) :
    ∀ᵐ t ∂(volume.restrict (Ioo a τ)), ∀ᵐ x ∂(volume : Measure Vec3),
      vlPrim a (vlMoll n) w₀ w H f x t = vlConvT (vlMoll n) w x t := by
  have hk := vlMoll_kernel n
  have hmeas : MeasurableSet {p : Vec3 × ℝ |
      vlConvT (vlMoll n) w p.1 p.2 = vlPrimM a (vlMoll n) w₀ w H f (p.1, p.2)} :=
    measurableSet_eq_fun (vlConvT_stronglyMeasurable hk.continuous sol.w_meas).measurable
      (vlPrimM_stronglyMeasurable sol hk).measurable
  have hx : ∀ᵐ x ∂(volume : Measure Vec3), ∀ᵐ t ∂(volume.restrict (Ioo a τ)),
      vlConvT (vlMoll n) w x t = vlPrimM a (vlMoll n) w₀ w H f (x, t) := by
    filter_upwards [] with x
    filter_upwards [vlConvT_ae_eq_prim sol hk x, ae_restrict_mem measurableSet_Ioo]
      with t ht htI
    rw [ht, vlPrimM_eq _ _ _ _ _ _ x htI.1.le]
  have hswap := (Measure.ae_ae_comm hmeas).1 hx
  filter_upwards [hswap, ae_restrict_mem measurableSet_Ioo] with t ht htI
  filter_upwards [ht] with x hxt
  rw [hxt, vlPrimM_eq _ _ _ _ _ _ x htI.1.le]

/-- For almost every time, the limit curve is the time slice of `w`. -/
theorem vlLimit_slice_ae (sol : VlHeatSolution a τ w H f w₀) :
    ∀ᵐ t ∂(volume.restrict (Ioo a τ)), ∀ (ht : t ∈ Icc a τ),
      ((vlLimit sol ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ)
        =ᵐ[volume] fun x => w (x, t) := by
  filter_upwards [ae_all_iff.2 (vlPrim_slice_ae sol), vlSlab_slice_memLp sol.w_meas sol.w_L2]
    with t hslice hwt ht
  set t₁ : Icc a τ := ⟨t, ht⟩
  have heq : vlLimit sol t₁ = hwt.toLp _ := by
    refine tendsto_nhds_unique (vlLimit_tendsto sol t₁) ?_
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have hsq : ∀ n, ‖vlCurve sol n t₁ - hwt.toLp _‖ ^ 2 =
        ∫ x, (vlConv (vlMoll n) (fun y => w (y, t)) x - w (x, t)) ^ 2 := by
      intro n
      rw [vlCurve, ← MemLp.toLp_sub, vl_norm_toLp_sq]
      refine integral_congr_ae ?_
      filter_upwards [hslice n] with x hx
      simp only [Pi.sub_apply]
      rw [hx]
      rfl
    have hlim := vlMoll_tendsto hwt
    have hroot : Tendsto (fun n => Real.sqrt
        (∫ x, (vlConv (vlMoll n) (fun y => w (y, t)) x - w (x, t)) ^ 2)) atTop (𝓝 0) := by
      simpa using hlim.sqrt
    refine hroot.congr (fun n => ?_)
    rw [← hsq n, Real.sqrt_sq (norm_nonneg _)]
  rw [heq]
  exact hwt.coeFn_toLp

end ESS

end
