/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyScalar

/-!
# The energy inequality in the limit

The kernel energy inequality for the mollifiers `ρₙ`, with Young's inequality
`‖ρₙ ⋆ g‖₂ ≤ ‖g‖₂`, gives a bound uniform in `n`. It passes to the limit
curve and to the limit gradient, which proves the energy estimate for weak
heat solutions with `L²` data (`lem:localized-vorticity-energy`).
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped Topology Interval


noncomputable section

namespace ESS

open CKN.Foundation.Parabolic

variable {a τ : ℝ} {w f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ} {w₀ : Vec3 → ℝ}

/-- The energy of the data up to time `t`. -/
@[expose] def vlDataEnergy (w₀ : Vec3 → ℝ) (w : Vec3 × ℝ → ℝ) (H : Fin 3 → Vec3 × ℝ → ℝ)
    (f : Vec3 × ℝ → ℝ) (a t : ℝ) : ℝ :=
  (∫ x, (w₀ x) ^ 2) + ∫ s in Ioo a t, ((∑ j : Fin 3, ∫ x, (H j (x, s)) ^ 2) +
    (∫ x, (w (x, s)) ^ 2) + ∫ x, (f (x, s)) ^ 2)

/-- The uniform bound for the mollified curves and gradients. -/
theorem vlCurve_energy_le (sol : VlHeatSolution a τ w H f w₀) (n : ℕ) (t : Icc a τ) :
    ‖vlCurve sol n t‖ ^ 2 + ∑ j : Fin 3, ∫ p in vlSlab a t.1, (vlGrad w n j p) ^ 2 ≤
      vlDataEnergy w₀ w H f a t.1 := by
  have hk := vlMoll_kernel n
  have hE := (vlPrim_energy_le sol hk t.2).2
  have hwt := vlSlab_memLp_mono t.2.2 sol.w_L2
  have hHt := fun j => vlSlab_memLp_mono t.2.2 (sol.H_L2 j)
  have hft := vlSlab_memLp_mono t.2.2 sol.f_L2
  have hGt : ∀ j, MemLp (vlGrad w n j) 2 (volume.restrict (vlSlab a t.1)) := fun j =>
    vlSlab_memLp_mono t.2.2 (vlGrad_memLp sol n j)
  have hgrad : ∫ s in Ioo a t.1, ∑ j : Fin 3, ∫ x, (vlConvT (vlDeriv (vlMoll n) j) w x s) ^ 2 =
      ∑ j : Fin 3, ∫ p in vlSlab a t.1, (vlGrad w n j p) ^ 2 := by
    have hI : ∀ j : Fin 3, IntegrableOn
        (fun s => ∫ x, (vlConvT (vlDeriv (vlMoll n) j) w x s) ^ 2) (Ioo a t.1) volume :=
      fun j => vlSlab_sliceSq_integrableOn (hGt j)
    rw [integral_finsetSum _ fun j _ => hI j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [vlSlab_integral_sq (hGt j)]
    rfl
  have hRHS : ∫ s in Ioo a t.1, ((∑ j : Fin 3, ∫ x, (vlConvT (vlMoll n) (H j) x s) ^ 2) +
        (∫ x, (vlConvT (vlMoll n) w x s) ^ 2) + ∫ x, (vlConvT (vlMoll n) f x s) ^ 2) ≤
      ∫ s in Ioo a t.1, ((∑ j : Fin 3, ∫ x, (H j (x, s)) ^ 2) +
        (∫ x, (w (x, s)) ^ 2) + ∫ x, (f (x, s)) ^ 2) := by
    have hL : IntegrableOn (fun s => (∑ j : Fin 3, ∫ x, (vlConvT (vlMoll n) (H j) x s) ^ 2) +
        (∫ x, (vlConvT (vlMoll n) w x s) ^ 2) + ∫ x, (vlConvT (vlMoll n) f x s) ^ 2)
        (Ioo a t.1) volume := by
      refine (Integrable.add ?_ ?_).add ?_
      · exact integrable_finsetSum _ fun j _ =>
          vlSlab_sliceSq_integrableOn (vlConvT_memLp hk (sol.H_meas j) (hHt j))
      · exact vlSlab_sliceSq_integrableOn (vlConvT_memLp hk sol.w_meas hwt)
      · exact vlSlab_sliceSq_integrableOn (vlConvT_memLp hk sol.f_meas hft)
    have hR : IntegrableOn (fun s => (∑ j : Fin 3, ∫ x, (H j (x, s)) ^ 2) +
        (∫ x, (w (x, s)) ^ 2) + ∫ x, (f (x, s)) ^ 2) (Ioo a t.1) volume := by
      refine (Integrable.add ?_ ?_).add ?_
      · exact integrable_finsetSum _ fun j _ => vlSlab_sliceSq_integrableOn (hHt j)
      · exact vlSlab_sliceSq_integrableOn hwt
      · exact vlSlab_sliceSq_integrableOn hft
    refine integral_mono_ae hL hR ?_
    have hHae : ∀ᵐ s ∂(volume.restrict (Ioo a t.1)),
        ∀ j, MemLp (fun y => H j (y, s)) 2 volume :=
      ae_all_iff.2 fun j => vlSlab_slice_memLp (sol.H_meas j) (hHt j)
    filter_upwards [vlSlab_slice_memLp sol.w_meas hwt, hHae,
      vlSlab_slice_memLp sol.f_meas hft] with s hws hHs hfs
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      vlMoll_sq_le n (hHs j)
    have h2 := vlMoll_sq_le n hws
    have h3 := vlMoll_sq_le n hfs
    simp only [vlConvT]
    linarith only [hsum, h2, h3]
  have h0 := vlMoll_sq_le n sol.w₀_L2
  rw [vlCurve_norm_sq, ← hgrad]
  unfold vlDataEnergy
  linarith only [hE, hRHS, h0]

/-- The squared `L²` integral of the limit gradient on a shorter slab is the
limit of the mollified ones. -/
theorem vlGrad_sq_tendsto (sol : VlHeatSolution a τ w H f w₀) (j : Fin 3) (t : Icc a τ) :
    Tendsto (fun n => ∫ p in vlSlab a t.1, (vlGrad w n j p) ^ 2) atTop
      (𝓝 (∫ p in vlSlab a t.1, ((vlGradLimit sol j : Vec3 × ℝ → ℝ) p) ^ 2)) := by
  set D : Vec3 × ℝ → ℝ := (vlGradLimit sol j : Vec3 × ℝ → ℝ) with hD_def
  have hDQ : MemLp D 2 (volume.restrict (vlSlab a τ)) := Lp.memLp _
  have hDt : MemLp D 2 (volume.restrict (vlSlab a t.1)) := vlSlab_memLp_mono t.2.2 hDQ
  have hgt : ∀ n, MemLp (vlGrad w n j) 2 (volume.restrict (vlSlab a t.1)) := fun n =>
    vlSlab_memLp_mono t.2.2 (vlGrad_memLp sol n j)
  have hμ : volume.restrict (vlSlab a t.1) ≤ volume.restrict (vlSlab a τ) :=
    Measure.restrict_mono (prod_mono subset_rfl (Ioo_subset_Ioo_right t.2.2)) le_rfl
  -- norm convergence on the shorter slab
  have hconv : Tendsto (fun n => (hgt n).toLp (vlGrad w n j)) atTop (𝓝 (hDt.toLp D)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have hbig := tendsto_iff_norm_sub_tendsto_zero.1 (vlGradLimit_tendsto sol j)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hbig
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
    have hDL : vlGradLimit sol j = hDQ.toLp D := (Lp.toLp_coeFn _ hDQ).symm
    rw [hDL, ← MemLp.toLp_sub, Lp.norm_toLp]
    exact ENNReal.toReal_mono (((vlGrad_memLp sol n j).sub hDQ).eLpNorm_ne_top)
      (eLpNorm_mono_measure _ hμ)
  have hnorm := (hconv.norm).pow 2
  simp_rw [vl_norm_toLp_sq] at hnorm
  exact hnorm

/-- The energy inequality for the limit. -/
theorem vlLimit_energy_le (sol : VlHeatSolution a τ w H f w₀) (t : Icc a τ) :
    ‖vlLimit sol t‖ ^ 2 +
        ∑ j : Fin 3, ∫ p in vlSlab a t.1, ((vlGradLimit sol j : Vec3 × ℝ → ℝ) p) ^ 2 ≤
      vlDataEnergy w₀ w H f a t.1 := by
  have hlim : Tendsto (fun n => ‖vlCurve sol n t‖ ^ 2 +
      ∑ j : Fin 3, ∫ p in vlSlab a t.1, (vlGrad w n j p) ^ 2) atTop
      (𝓝 (‖vlLimit sol t‖ ^ 2 +
        ∑ j : Fin 3, ∫ p in vlSlab a t.1, ((vlGradLimit sol j : Vec3 × ℝ → ℝ) p) ^ 2)) :=
    ((vlLimit_tendsto sol t).norm.pow 2).add
      (tendsto_finsetSum _ fun j _ => vlGrad_sq_tendsto sol j t)
  exact le_of_tendsto' hlim fun n => vlCurve_energy_le sol n t

/-- The energy estimate for a weak heat solution with square-integrable data
(`lem:localized-vorticity-energy`, one component). -/
theorem vlHeat_energy (sol : VlHeatSolution a τ w H f w₀) :
    ∃ Z : Icc a τ → Lp ℝ 2 (volume : Measure Vec3), ∃ D : Fin 3 → Vec3 × ℝ → ℝ,
      Continuous Z ∧
      ((Z ⟨a, left_mem_Icc.2 sol.lt.le⟩ : Vec3 → ℝ) =ᵐ[volume] w₀) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo a τ)), ∀ ht : t ∈ Icc a τ,
        (Z ⟨t, ht⟩ : Vec3 → ℝ) =ᵐ[volume] fun x => w (x, t)) ∧
      (∀ j, MemLp (D j) 2 (volume.restrict (vlSlab a τ))) ∧
      (∀ j, ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a τ),
        ∫ p in vlSlab a τ, w p * CKN.spatialPartial φ j p =
          -∫ p in vlSlab a τ, D j p * φ p) ∧
      ∀ t : Icc a τ, ‖Z t‖ ^ 2 + ∑ j : Fin 3, ∫ p in vlSlab a t.1, (D j p) ^ 2 ≤
        vlDataEnergy w₀ w H f a t.1 := by
  refine ⟨vlLimit sol, fun j => (vlGradLimit sol j : Vec3 × ℝ → ℝ), vlLimit_continuous sol,
    ?_, vlLimit_slice_ae sol, fun j => Lp.memLp _, fun j φ hφ => vlGradLimit_weak sol j hφ,
    vlLimit_energy_le sol⟩
  rw [vlLimit_initial]
  exact sol.w₀_L2.coeFn_toLp

end ESS

end
