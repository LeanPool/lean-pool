/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.EnergyEquality
public import LeanPool.EscauriazaSereginSverak.LPS.FiniteRelativeEnergy
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakFromLerayHopf
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSlices

/-!
# Uniqueness in the finite Serrin branch

The distinguished Leray–Hopf solution supplies the a.e. energy equality;
the finite mixed-norm cross identity and relative-energy estimate then force
the competitor to agree with it almost everywhere.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Zero relative slice energy almost everywhere implies equality of the
space-time velocity fields almost everywhere. -/
theorem lps_zero_relative_distance_implies_ae_eq
    {T : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3} {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    (hU : IsLerayHopfSolution T a u Du)
    (hV : IsLerayHopfSolution T a v Dv)
    (hZero : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      lpsComparisonDistanceSq u v t = 0) :
    v =ᵐ[volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))] u := by
  obtain ⟨pU, hWeakU⟩ := serrinWeak_of_lerayHopf hU
  obtain ⟨pV, hWeakV⟩ := serrinWeak_of_lerayHopf hV
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∀ᵐ x ∂(volume : Measure Vec3), v (x,t) = u (x,t) := by
    filter_upwards [hZero, serrinWeak_slices_ae hWeakU, serrinWeak_slices_ae hWeakV]
      with t hEq hu hv
    rcases hu with ⟨hu2, -, -, -, -⟩
    rcases hv with ⟨hv2, -, -, -, -⟩
    have hDiff : MemLp (fun x : Vec3 => v (x,t) - u (x,t)) 2 volume := hv2.sub hu2
    have hInt : Integrable (fun x : Vec3 =>
        ∑ k : Fin 3, (v (x,t) k - u (x,t) k) ^ 2) volume := by
      refine integrable_finsetSum _ fun k _ => ?_
      exact (memLp_two_iff_integrable_sq_norm
        ((hDiff.eval k).aestronglyMeasurable)).mp (hDiff.eval k) |>.congr
          (Eventually.of_forall fun x => by simp)
    have hzeroInt :
        (∫ x : Vec3, ∑ k : Fin 3, (v (x,t) k - u (x,t) k) ^ 2) = 0 := by
      simpa [lpsComparisonDistanceSq] using hEq
    have hAE := (integral_eq_zero_iff_of_nonneg
      (fun x => Finset.sum_nonneg fun k _ => sq_nonneg _)
      hInt).mp hzeroInt
    filter_upwards [hAE] with x hx
    funext k
    have hsum : ∑ i : Fin 3, (v (x,t) i - u (x,t) i) ^ 2 = 0 := hx
    have hk := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (v (x,t) i - u (x,t) i))).mp hsum k (Finset.mem_univ k)
    have hsub : v (x,t) k - u (x,t) k = 0 :=
      (pow_eq_zero_iff (n := 2) (by norm_num)).mp hk
    linarith only [hsub]
  have hvm := serrin_aesm_prod hWeakV.meas_u
  have hum := serrin_aesm_prod hWeakU.meas_u
  have hdiff : AEMeasurable (fun z : Vec3 × ℝ => ‖v z - u z‖ₑ)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) :=
    (hvm.sub hum).enorm
  have hlin :
      (∫⁻ z : Vec3 × ℝ, ‖v z - u z‖ₑ ∂
        ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))) = 0 := by
    rw [lintegral_prod_symm _ hdiff]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hslice] with t ht
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ht] with x hx
    simp [hx]
  have hAE := (lintegral_eq_zero_iff' hdiff).mp hlin
  rw [serrin_slab_measure_eq]
  filter_upwards [hAE] with z hz
  have hnorm : ‖v z - u z‖ₑ = 0 := hz
  rw [enorm_eq_zero, sub_eq_zero] at hnorm
  exact hnorm

/-- Weak–strong uniqueness for the finite branch of the Serrin condition.
The competitor is assumed only to be Leray–Hopf; D2 supplies the distinguished
solution's a.e. energy equality. -/
theorem lps_finite_leray_hopf_uniqueness
    {T s : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    (hU : IsLerayHopfSolution T a u Du)
    (hV : IsLerayHopfSolution T a v Dv)
    (hs : 3 < s)
    (hmix : (∫⁻ t in Ioo (0 : ℝ) T,
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ s) ^
          ((2 * s / (s - 3)) / s)) < ⊤) :
    v =ᵐ[volume.restrict (spaceTimeSet Set.univ (Ioo (0 : ℝ) T))] u := by
  obtain ⟨pu, hUweak⟩ := serrinWeak_of_lerayHopf hU
  obtain ⟨pv, hVweak⟩ := serrinWeak_of_lerayHopf hV
  have hEnergyEquality := lps_serrin_energy_equality hU (Or.inl ⟨s, hs, hmix⟩)
  have hZero := lps_finite_relative_energy_zero hU hV hUweak hVweak hs hmix
    hEnergyEquality
  exact lps_zero_relative_distance_implies_ae_eq hU hV hZero

end ESS

end
