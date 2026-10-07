/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyCauchy

/-!
# The continuous `L²` curve of a weak heat solution

The mollified primitives `Wₙ(t)` are continuous curves in `L²(ℝ³)` on `[a, τ]`.
The Cauchy estimate makes them uniformly Cauchy, so they converge uniformly to
a continuous curve `Z` (`lem:localized-vorticity-energy`).
-/

public section

open MeasureTheory Set Filter
open scoped Topology Interval


noncomputable section

namespace ESS

open CKN CKN.Foundation.Parabolic

variable {a τ : ℝ} {w f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ} {w₀ : Vec3 → ℝ}

/-- Cauchy–Schwarz on a bounded interval. -/
theorem vl_sq_setIntegral_le {u v : ℝ} (huv : u ≤ v) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo u v) volume)
    (hg2 : IntegrableOn (fun s => g s ^ 2) (Ioo u v) volume) :
    (∫ s in Ioo u v, g s) ^ 2 ≤ (v - u) * ∫ s in Ioo u v, g s ^ 2 := by
  rcases huv.eq_or_lt with h | h
  · subst h
    simp
  set L := v - u with hL
  have hLpos : 0 < L := sub_pos.2 h
  set I₁ := ∫ s in Ioo u v, g s with hI₁
  set I₂ := ∫ s in Ioo u v, g s ^ 2 with hI₂
  set m := I₁ / L with hm
  have hconst : IntegrableOn (fun _ : ℝ => m ^ 2) (Ioo u v) volume := by
    exact integrableOn_const (by simp [Real.volume_Ioo])
  have hexp : ∫ s in Ioo u v, (g s - m) ^ 2 = I₂ - 2 * m * I₁ + m ^ 2 * L := by
    have h1 : IntegrableOn (fun s => g s ^ 2 - 2 * m * g s) (Ioo u v) volume :=
      hg2.sub (hg.const_mul _)
    calc
      ∫ s in Ioo u v, (g s - m) ^ 2 =
          ∫ s in Ioo u v, ((g s ^ 2 - 2 * m * g s) + m ^ 2) := by
        congr 1
        funext s
        ring
      _ = I₂ - 2 * m * I₁ + m ^ 2 * L := by
        rw [integral_add h1 hconst, integral_sub hg2 (hg.const_mul _), integral_const_mul,
          setIntegral_const, Real.volume_real_Ioo_of_le huv, smul_eq_mul]
        ring
  have hnn : 0 ≤ ∫ s in Ioo u v, (g s - m) ^ 2 := integral_nonneg fun s => sq_nonneg _
  rw [hexp] at hnn
  have hkey : L * I₂ - I₁ ^ 2 = L * (I₂ - 2 * m * I₁ + m ^ 2 * L) := by
    rw [hm]
    field_simp
    ring
  have hfinal : 0 ≤ L * I₂ - I₁ ^ 2 := by
    rw [hkey]
    exact mul_nonneg hLpos.le hnn
  linarith only [hfinal]

/-- The mollified primitive as an `L²` curve on `[a, τ]`. -/
@[expose] def vlCurve (sol : VlHeatSolution a τ w H f w₀) (n : ℕ) (t : Icc a τ) :
    Lp ℝ 2 (volume : Measure Vec3) :=
  (vlPrim_energy_le sol (vlMoll_kernel n) t.2).1.toLp
    (fun x => vlPrim a (vlMoll n) w₀ w H f x t)

theorem vlCurve_norm_sq (sol : VlHeatSolution a τ w H f w₀) (n : ℕ) (t : Icc a τ) :
    ‖vlCurve sol n t‖ ^ 2 = ∫ x, (vlPrim a (vlMoll n) w₀ w H f x t) ^ 2 :=
  vl_norm_toLp_sq _

/-- The difference of two curves at a time, squared. -/
theorem vlCurve_sub_norm_sq (sol : VlHeatSolution a τ w H f w₀) (n m : ℕ) (t : Icc a τ) :
    ‖vlCurve sol n t - vlCurve sol m t‖ ^ 2 =
      ∫ x, (vlPrim a (vlMoll n - vlMoll m) w₀ w H f x t) ^ 2 := by
  have hn := (vlPrim_energy_le sol (vlMoll_kernel n) t.2).1
  have hm := (vlPrim_energy_le sol (vlMoll_kernel m) t.2).1
  have hsub : vlCurve sol n t - vlCurve sol m t = (hn.sub hm).toLp _ := by
    simp only [vlCurve]
    exact (MemLp.toLp_sub hn hm).symm
  rw [hsub, vl_norm_toLp_sq]
  congr 1
  funext x
  rw [vlPrim_sub_kernel sol (vlMoll_kernel n) (vlMoll_kernel m) x t.2]
  rfl

/-- The uniform Cauchy estimate. -/
theorem vlCurve_dist_sq_le (sol : VlHeatSolution a τ w H f w₀) (n m : ℕ) (t : Icc a τ) :
    ‖vlCurve sol n t - vlCurve sol m t‖ ^ 2 ≤
      2 * vlErr w₀ w H f a τ n + 2 * vlErr w₀ w H f a τ m := by
  have hk : IsVlKernel (vlMoll n - vlMoll m) := (vlMoll_kernel n).sub (vlMoll_kernel m)
  have hE := (vlPrim_energy_le sol hk t.2).2
  have hgrad : 0 ≤ ∫ s in Ioo a t.1, ∑ j : Fin 3,
      ∫ x, (vlConvT (vlDeriv (vlMoll n - vlMoll m) j) w x s) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo fun s _ =>
      Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _
  have hrhs := vlMoll_diff_rhs_le sol n m t.2
  rw [vlCurve_sub_norm_sq]
  linarith only [hE, hgrad, hrhs]

/-- Each mollified curve is Hölder continuous in time. -/
theorem vlCurve_dist_sq_le_time (sol : VlHeatSolution a τ w H f w₀) (n : ℕ)
    {t t' : Icc a τ} (htt : t'.1 ≤ t.1) :
    ‖vlCurve sol n t - vlCurve sol n t'‖ ^ 2 ≤
      (t.1 - t'.1) * ∫ p in vlSlab a τ, (vlSource (vlMoll n) w H f p.1 p.2) ^ 2 := by
  have hk := vlMoll_kernel n
  have hn := (vlPrim_energy_le sol hk t.2).1
  have hn' := (vlPrim_energy_le sol hk t'.2).1
  have hsub : vlCurve sol n t - vlCurve sol n t' = (hn.sub hn').toLp _ := by
    simp only [vlCurve]
    exact (MemLp.toLp_sub hn hn').symm
  rw [hsub, vl_norm_toLp_sq]
  have hG := vlSource_memLp sol hk
  have hG2 := hG.integrable_sq
  rw [vlSlab_measure] at hG2
  have hdiff : ∀ x, vlPrim a (vlMoll n) w₀ w H f x t - vlPrim a (vlMoll n) w₀ w H f x t' =
      ∫ s in Ioo t'.1 t.1, vlSource (vlMoll n) w H f x s := by
    intro x
    simp only [vlPrim]
    rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
      (vlSource_intervalIntegrable sol hk x t.2) (vlSource_intervalIntegrable sol hk x t'.2),
      intervalIntegral.integral_of_le htt, integral_Ioc_eq_integral_Ioo]
  have hsubI : Ioo t'.1 t.1 ⊆ Ioo a τ := Ioo_subset_Ioo t'.2.1 t.2.2
  have hpoint : ∀ᵐ x ∂(volume : Measure Vec3),
      (vlPrim a (vlMoll n) w₀ w H f x t - vlPrim a (vlMoll n) w₀ w H f x t') ^ 2 ≤
        (t.1 - t'.1) * ∫ s in Ioo a τ, (vlSource (vlMoll n) w H f x s) ^ 2 := by
    filter_upwards [hG2.prod_right_ae] with x hx
    rw [hdiff x]
    have hxJ : IntegrableOn (fun s => (vlSource (vlMoll n) w H f x s) ^ 2) (Ioo a τ) volume :=
      hx
    refine (vl_sq_setIntegral_le htt ((vlSource_integrableOn sol hk x).mono_set hsubI)
      (hxJ.mono_set hsubI)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 htt)
    exact setIntegral_mono_set hxJ (Eventually.of_forall fun s => sq_nonneg _)
      (Eventually.of_forall hsubI)
  have hRint : Integrable (fun x => (t.1 - t'.1) *
      ∫ s in Ioo a τ, (vlSource (vlMoll n) w H f x s) ^ 2) volume :=
    hG2.integral_prod_left.const_mul _
  refine (integral_mono_ae (hn.sub hn').integrable_sq hRint hpoint).trans_eq ?_
  rw [integral_const_mul]
  congr 1
  rw [vlSlab_measure, integral_prod _ hG2]

theorem vlCurve_continuous (sol : VlHeatSolution a τ w H f w₀) (n : ℕ) :
    Continuous (vlCurve sol n) := by
  set K := ∫ p in vlSlab a τ, (vlSource (vlMoll n) w H f p.1 p.2) ^ 2 with hK
  have hK0 : 0 ≤ K := integral_nonneg fun p => sq_nonneg _
  have hbound : ∀ t t' : Icc a τ, dist (vlCurve sol n t) (vlCurve sol n t') ≤
      Real.sqrt (K * |t.1 - t'.1|) := by
    intro t t'
    rw [dist_eq_norm]
    rcases le_total t'.1 t.1 with h | h
    · have := vlCurve_dist_sq_le_time sol n h
      rw [abs_of_nonneg (sub_nonneg.2 h)]
      apply Real.le_sqrt_of_sq_le
      linarith only [this]
    · have := vlCurve_dist_sq_le_time sol n h
      rw [abs_of_nonpos (sub_nonpos.2 h), norm_sub_rev]
      apply Real.le_sqrt_of_sq_le
      linarith only [this]
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  refine tendsto_iff_dist_tendsto_zero.2 ?_
  have hlim : Tendsto (fun t : Icc a τ => Real.sqrt (K * |t.1 - t₀.1|)) (𝓝 t₀) (𝓝 0) := by
    have hc : Continuous (fun t : Icc a τ => Real.sqrt (K * |t.1 - t₀.1|)) :=
      (continuous_const.mul ((continuous_subtype_val.sub continuous_const).abs)).sqrt
    have := hc.tendsto t₀
    simpa using this
  exact squeeze_zero (fun t => dist_nonneg) (fun t => hbound t t₀) hlim

/-- The mollified curves converge uniformly on `[a, τ]`. -/
theorem vlCurve_uniformCauchy (sol : VlHeatSolution a τ w H f w₀) :
    UniformCauchySeqOn (fun n => vlCurve sol n) atTop univ := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hlim := vlErr_tendsto sol
  have hev : ∀ᶠ n in atTop, vlErr w₀ w H f a τ n < ε ^ 2 / 8 :=
    hlim.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun m hm n hn t _ => ?_⟩
  rw [dist_eq_norm]
  have h := vlCurve_dist_sq_le sol m n t
  have hm' := hN m hm
  have hn' := hN n hn
  have hsq : ‖vlCurve sol m t - vlCurve sol n t‖ ^ 2 < ε ^ 2 := by
    have hε2 : 0 < ε ^ 2 := by positivity
    linarith only [h, hm', hn', hε2]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

end ESS

end
