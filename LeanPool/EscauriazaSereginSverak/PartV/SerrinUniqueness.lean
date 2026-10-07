/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinRelativeEnergy
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinGronwall

/-!
# Weak–strong uniqueness at exponents (5,5)

A finite-energy weak solution with pressure in space-time `L⁵` and a
finite-energy weak solution in `L^{10/3}` satisfying the energy inequality,
with the same datum, agree almost everywhere on the slab. The proof is the
relative energy inequality followed by Gronwall's inequality; this is
`lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Weak–strong uniqueness for finite-energy weak solutions with pressures:
the first in space-time `L⁵`, the second in `L^{10/3}` with the energy
inequality. -/
theorem serrin_weak_strong_uniqueness {T : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3} {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu) (hV : IsSerrinWeakSolution T a v Dv pv)
    (hu5 : MemLp u (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hv103 : MemLp v (ENNReal.ofReal (10 / 3))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hvE : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * v (x, t) k) ≤
        (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) -
          2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv q k j * Dv q k j) :
    v =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u := by
  obtain ⟨C, hC, hineq⟩ := serrin_relative_energy_inequality hU hV hu5 hv103 hvE
  set m : ℝ → ℝ := fun τ =>
    (eLpNorm (fun x : Vec3 => u (x, τ)) (ENNReal.ofReal 5) volume).toReal ^ 5 with hmdef
  set E : ℝ → ℝ := fun τ => ∫ x : Vec3, ∑ k : Fin 3, (v (x, τ) k - u (x, τ) k) ^ 2 with hEdef
  have hT : 0 < T := hU.pos
  have hIcc : (volume.restrict (Icc 0 T) : Measure ℝ) = volume.restrict (Ioo 0 T) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  have hm : IntegrableOn m (Ioo 0 T) := serrin_slice_norm5_integrable hu5
  have hEm := serrin_distance_aestronglyMeasurable hU hV
  obtain ⟨Bu, hBu⟩ := serrinWeak_slice_energy_bound hU
  obtain ⟨Bv, hBv⟩ := serrinWeak_slice_energy_bound hV
  have hE0 (τ : ℝ) : 0 ≤ E τ :=
    integral_nonneg fun x => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hEb : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)), ‖E τ‖ ≤ 2 * (Bu + Bv) := by
    filter_upwards [hBu, hBv, serrinWeak_slices_ae hU, serrinWeak_slices_ae hV]
      with τ hu hv hsu hsv
    have hu2' := hsu.1
    have hv2' := hsv.1
    have hiu : Integrable (fun x => ∑ k : Fin 3, u (x, τ) k ^ 2) volume :=
      integrable_finsetSum _ fun k _ => (memLp_two_iff_integrable_sq_norm
        (hu2'.eval k).aestronglyMeasurable).mp (hu2'.eval k) |>.congr
          (Eventually.of_forall fun x => by simp)
    have hiv : Integrable (fun x => ∑ k : Fin 3, v (x, τ) k ^ 2) volume :=
      integrable_finsetSum _ fun k _ => (memLp_two_iff_integrable_sq_norm
        (hv2'.eval k).aestronglyMeasurable).mp (hv2'.eval k) |>.congr
          (Eventually.of_forall fun x => by simp)
    rw [Real.norm_eq_abs, abs_of_nonneg (hE0 τ)]
    calc
      E τ ≤ ∫ x : Vec3, 2 * (∑ k : Fin 3, u (x, τ) k ^ 2) + 2 * ∑ k : Fin 3, v (x, τ) k ^ 2 := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x =>
          Finset.sum_nonneg fun k _ => sq_nonneg _) ((hiu.const_mul 2).add (hiv.const_mul 2))
          (Eventually.of_forall fun x => ?_)
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun k _ => by nlinarith only [sq_nonneg (v (x, τ) k + u (x, τ) k)]
      _ = 2 * (∫ x : Vec3, ∑ k : Fin 3, u (x, τ) k ^ 2) +
          2 * ∫ x : Vec3, ∑ k : Fin 3, v (x, τ) k ^ 2 := by
        rw [integral_add (hiu.const_mul 2) (hiv.const_mul 2), integral_const_mul,
          integral_const_mul]
      _ ≤ 2 * (Bu + Bv) := by linarith only [hu, hv]
  have hmE : IntegrableOn (fun τ => m τ * E τ) (Ioo 0 T) :=
    hm.mul_bdd (c := 2 * (Bu + Bv)) hEm hEb
  have hm0 (τ : ℝ) : 0 ≤ m τ := by positivity
  have hzero := serrin_integral_gronwall_zero (T := T) (C := C) (b := m) (q := E) hT.le hC
    (by rw [IntegrableOn, hIcc]; exact hm) (Eventually.of_forall hm0)
    (Eventually.of_forall hE0) (by rw [hIcc]; exact hmE)
    (Eventually.of_forall fun τ => mul_nonneg (hm0 τ) (hE0 τ))
    (by rw [hIcc]; exact hineq)
  rw [hIcc] at hzero
  -- almost every slice of the difference vanishes almost everywhere
  have hslice : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      ∀ᵐ x ∂(volume : Measure Vec3), v (x, τ) = u (x, τ) := by
    filter_upwards [hzero, serrinWeak_slices_ae hU, serrinWeak_slices_ae hV] with τ hτ hsu hsv
    have hu2' := hsu.1
    have hv2' := hsv.1
    have hint : Integrable (fun x => ∑ k : Fin 3, (v (x, τ) k - u (x, τ) k) ^ 2) volume :=
      integrable_finsetSum _ fun k _ => (memLp_two_iff_integrable_sq_norm
        ((hv2'.eval k).sub (hu2'.eval k)).aestronglyMeasurable).mp
          ((hv2'.eval k).sub (hu2'.eval k)) |>.congr (Eventually.of_forall fun x => by simp)
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => Finset.sum_nonneg fun k _ =>
      sq_nonneg _) hint).mp hτ
    filter_upwards [hae] with x hx
    funext k
    have hk : (v (x, τ) k - u (x, τ) k) ^ 2 = 0 := by
      have hsum : ∑ i : Fin 3, (v (x, τ) i - u (x, τ) i) ^ 2 = 0 := hx
      exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).mp hsum k
        (Finset.mem_univ k)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hk
    linarith only [this]
  -- conclude on the product measure
  have hvm := serrin_aesm_prod hV.meas_u
  have hum := serrin_aesm_prod hU.meas_u
  have hdm : AEMeasurable (fun z : Vec3 × ℝ => ‖v z - u z‖ₑ)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) :=
    (hvm.sub hum).enorm
  have hlint : (∫⁻ z, ‖v z - u z‖ₑ ∂((volume : Measure Vec3).prod
      (volume.restrict (Ioo 0 T)))) = 0 := by
    rw [lintegral_prod_symm _ hdm]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hslice] with τ hτ
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hτ] with x hx
    simp [hx]
  have hae := (lintegral_eq_zero_iff' hdm).mp hlint
  rw [serrin_slab_measure_eq]
  filter_upwards [hae] with z hz
  have : ‖v z - u z‖ₑ = 0 := hz
  rw [enorm_eq_zero, sub_eq_zero] at this
  exact this

end ESS
