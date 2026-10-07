/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinEnergyEquality

/-!
# Time functions in the Gronwall argument

The Gronwall coefficient `τ ↦ ‖u(τ)‖₅⁵` is integrable in time for a space-time
`L⁵` field, and the squared `L²` distance of two finite-energy solutions is a
measurable, essentially bounded function of time. These are the inputs of the
Gronwall step of `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The fifth power of the slice `L⁵` norm is integrable in time. -/
theorem serrin_slice_norm5_integrable {T : ℝ} {u : ParabolicPoint → Vec3}
    (hu5 : MemLp u (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    IntegrableOn (fun τ => (eLpNorm (fun x : Vec3 => u (x, τ)) (ENNReal.ofReal 5) volume).toReal
      ^ 5) (Ioo 0 T) := by
  rw [serrin_slab_measure_eq] at hu5
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  have hr : (ENNReal.ofReal 5).toReal = 5 := by simp
  have hfm : AEStronglyMeasurable (fun z : Vec3 × ℝ => u z) ν := hu5.aestronglyMeasurable
  have hgm : AEMeasurable (fun z : Vec3 × ℝ => ‖u z‖ₑ ^ (5 : ℝ)) ν := hfm.enorm.pow_const _
  have hfin : (∫⁻ z, ‖u z‖ₑ ^ (5 : ℝ) ∂ν) ≠ ⊤ := by
    have h1 := hu5.eLpNorm_lt_top
    have hfm' : AEStronglyMeasurable u ν := hfm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp) hfm', hr] at h1
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h1 |>.ne
  have hGm : AEMeasurable (fun τ => ∫⁻ x, ‖u (x, τ)‖ₑ ^ (5 : ℝ) ∂volume)
      (volume.restrict (Ioo 0 T)) := hgm.lintegral_prod_left'
  have hGfin : (∫⁻ τ, ∫⁻ x, ‖u (x, τ)‖ₑ ^ (5 : ℝ) ∂volume ∂(volume.restrict (Ioo 0 T))) ≠ ⊤ := by
    rw [← lintegral_prod_symm _ hgm]
    exact hfin
  have hint := integrable_toReal_of_lintegral_ne_top hGm hGfin
  refine hint.congr ?_
  filter_upwards [hfm.prodMk_right] with τ hτ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp) hτ, hr,
    ← ENNReal.toReal_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num

/-- The squared `L²` distance of two slices is measurable in time. -/
theorem serrin_distance_aestronglyMeasurable {T : ℝ} {a b : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3} {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu) (hV : IsSerrinWeakSolution T b v Dv pv) :
    AEStronglyMeasurable (fun τ => ∫ x : Vec3, ∑ k : Fin 3, (v (x, τ) k - u (x, τ) k) ^ 2)
      (volume.restrict (Ioo 0 T)) := by
  have hu := serrin_aesm_prod hU.meas_u
  have hv := serrin_aesm_prod hV.meas_u
  have hF : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => ∑ k : Fin 3, (v z k - u z k) ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) :=
    Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
      (((continuous_apply k).comp_aestronglyMeasurable hv).sub
        ((continuous_apply k).comp_aestronglyMeasurable hu)).pow 2
  exact hF.prod_swap.integral_prod_right'

private theorem serrin_sum_sq_le (v : Vec3) : ∑ k : Fin 3, v k ^ 2 ≤ 3 * ‖v‖ ^ 2 := by
  have h (k : Fin 3) : v k ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v k) 2
  calc
    ∑ k : Fin 3, v k ^ 2 ≤ ∑ _k : Fin 3, ‖v‖ ^ 2 := Finset.sum_le_sum fun k _ => h k
    _ = 3 * ‖v‖ ^ 2 := by simp

/-- The slice energies of a finite-energy weak solution are essentially bounded. -/
theorem serrinWeak_slice_energy_bound {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hU : IsSerrinWeakSolution T a u Du p) :
    ∃ B : ℝ, ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      ∫ x : Vec3, ∑ k : Fin 3, u (x, τ) k ^ 2 ≤ B := by
  set M := essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ)) (volume.restrict (Ioo 0 T))
  refine ⟨3 * M.toReal, ?_⟩
  filter_upwards [ENNReal.ae_le_essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ)),
    serrinWeak_slices_ae hU] with τ hτ hsl
  have h2 := hsl.1
  have hint : Integrable (fun x => ‖u (x, τ)‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2
  have hsq : ∫ x : Vec3, ‖u (x, τ)‖ ^ 2 ≤ M.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity)
      hint.aestronglyMeasurable]
    refine ENNReal.toReal_mono (ne_top_of_le_ne_top hU.slice_bound.ne le_rfl) ?_
    refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) hτ
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two]
  calc
    ∫ x : Vec3, ∑ k : Fin 3, u (x, τ) k ^ 2 ≤ ∫ x : Vec3, 3 * ‖u (x, τ)‖ ^ 2 := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun x => ?_) (hint.const_mul 3)
        (Eventually.of_forall fun x => serrin_sum_sq_le _)
      exact Finset.sum_nonneg fun k _ => sq_nonneg _
    _ = 3 * ∫ x : Vec3, ‖u (x, τ)‖ ^ 2 := integral_const_mul _ _
    _ ≤ 3 * M.toReal := by gcongr

end ESS
