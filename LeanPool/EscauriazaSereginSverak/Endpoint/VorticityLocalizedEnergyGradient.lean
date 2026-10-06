/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyLimit

/-!
# The weak gradient of a weak heat solution

The mollified gradients `(∂ⱼρₙ) ⋆ w` form a Cauchy sequence in `L²` of the
slab. Their limit is the weak spatial gradient of `w`
(`lem:localized-vorticity-energy`).
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped Topology Interval InnerProductSpace


noncomputable section

namespace ESS

open CKN.Foundation.Parabolic

variable {a τ : ℝ} {w f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ} {w₀ : Vec3 → ℝ}

/-- The mollified gradient component. -/
@[expose] def vlGrad (w : Vec3 × ℝ → ℝ) (n : ℕ) (j : Fin 3) : Vec3 × ℝ → ℝ :=
  fun p => vlConvT (vlDeriv (vlMoll n) j) w p.1 p.2

theorem vlGrad_memLp (sol : VlHeatSolution a τ w H f w₀) (n : ℕ) (j : Fin 3) :
    MemLp (vlGrad w n j) 2 (volume.restrict (vlSlab a τ)) :=
  vlConvT_memLp ((vlMoll_kernel n).deriv j) sol.w_meas sol.w_L2

/-- The gradient Cauchy estimate. -/
theorem vlGrad_sub_sq_le (sol : VlHeatSolution a τ w H f w₀) (n m : ℕ) (j : Fin 3) :
    ∫ p in vlSlab a τ, (vlGrad w n j p - vlGrad w m j p) ^ 2 ≤
      2 * vlErr w₀ w H f a τ n + 2 * vlErr w₀ w H f a τ m := by
  set k := vlMoll n - vlMoll m with hk_def
  have hk : IsVlKernel k := (vlMoll_kernel n).sub (vlMoll_kernel m)
  have hτ : τ ∈ Icc a τ := right_mem_Icc.2 sol.lt.le
  have hE := (vlPrim_energy_le sol hk hτ).2
  have hrhs := vlMoll_diff_rhs_le sol n m hτ
  have hP : 0 ≤ ∫ x, (vlPrim a k w₀ w H f x τ) ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hdiff : MemLp (fun p => vlGrad w n j p - vlGrad w m j p) 2
      (volume.restrict (vlSlab a τ)) := (vlGrad_memLp sol n j).sub (vlGrad_memLp sol m j)
  rw [vlSlab_integral_sq hdiff]
  have hDj : ∀ i : Fin 3, IntegrableOn
      (fun s => ∫ x, (vlConvT (vlDeriv k i) w x s) ^ 2) (Ioo a τ) volume := fun i =>
    vlSlab_sliceSq_integrableOn (vlConvT_memLp (hk.deriv i) sol.w_meas sol.w_L2)
  have hslice : ∀ᵐ s ∂(volume.restrict (Ioo a τ)),
      ∫ x, (vlGrad w n j (x, s) - vlGrad w m j (x, s)) ^ 2 =
        ∫ x, (vlConvT (vlDeriv k j) w x s) ^ 2 := by
    filter_upwards [vlConvT_sub_kernel_ae ((vlMoll_kernel n).deriv j)
      ((vlMoll_kernel m).deriv j) sol.w_meas sol.w_L2] with s hs
    congr 1
    funext x
    rw [hk_def, vlDeriv_sub (vlMoll_kernel n) (vlMoll_kernel m) j, hs x]
    rfl
  have hsum : ∫ s in Ioo a τ, ∫ x, (vlConvT (vlDeriv k j) w x s) ^ 2 ≤
      ∫ s in Ioo a τ, ∑ i : Fin 3, ∫ x, (vlConvT (vlDeriv k i) w x s) ^ 2 := by
    refine integral_mono (hDj j) (integrable_finsetSum _ fun i _ => hDj i) (fun s => ?_)
    exact Finset.single_le_sum (f := fun i => ∫ x, (vlConvT (vlDeriv k i) w x s) ^ 2)
      (fun i _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ j)
  rw [integral_congr_ae hslice]
  linarith only [hE, hrhs, hP, hsum]

/-- The limit of the mollified gradients. -/
@[expose] def vlGradLimit (sol : VlHeatSolution a τ w H f w₀) (j : Fin 3) :
    Lp ℝ 2 (volume.restrict (vlSlab a τ)) :=
  limUnder atTop fun n => (vlGrad_memLp sol n j).toLp (vlGrad w n j)

theorem vlGradLimit_tendsto (sol : VlHeatSolution a τ w H f w₀) (j : Fin 3) :
    Tendsto (fun n => (vlGrad_memLp sol n j).toLp (vlGrad w n j)) atTop
      (𝓝 (vlGradLimit sol j)) := by
  have hc : CauchySeq fun n => (vlGrad_memLp sol n j).toLp (vlGrad w n j) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hlim := vlErr_tendsto sol
    have hev : ∀ᶠ n in atTop, vlErr w₀ w H f a τ n < ε ^ 2 / 8 :=
      hlim.eventually (gt_mem_nhds (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun m hm n hn => ?_⟩
    have hsq : ‖(vlGrad_memLp sol m j).toLp (vlGrad w m j) -
        (vlGrad_memLp sol n j).toLp (vlGrad w n j)‖ ^ 2 < ε ^ 2 := by
      rw [← MemLp.toLp_sub, vl_norm_toLp_sq]
      have h := vlGrad_sub_sq_le sol m n j
      have hm' := hN m hm
      have hn' := hN n hn
      have hε2 : 0 < ε ^ 2 := by positivity
      exact lt_of_le_of_lt h (by linarith only [hm', hn', hε2])
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  exact tendsto_nhds_limUnder ⟨L, hL⟩

end ESS

end
