/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.FiniteUniqueness
public import LeanPool.EscauriazaSereginSverak.LPS.RelativeEnergyAssembly
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinGronwallInputs
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinLerayHopf

/-!
# Common relative-energy assembly for Leray–Hopf solutions

Once a branch supplies the cross identity, its explicit relative-convection
integrability, and the fixed-time estimate, this theorem combines the
distinguished solution's a.e. energy equality with the competitor's
Leray–Hopf energy inequality and applies Gronwall.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Multiplication by an integrable time coefficient preserves integrability
of the relative slice energy: the two Leray–Hopf slice energies bound that
energy uniformly almost everywhere. -/
theorem lps_comparison_time_weight_integrable
    {T : ℝ} {a b : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ} {m : ℝ → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T b v Dv pv)
    (hm : IntegrableOn m (Ioo 0 T)) :
    IntegrableOn (fun t => m t * lpsComparisonDistanceSq u v t) (Ioo 0 T) := by
  obtain ⟨Bu, hBu⟩ := serrinWeak_slice_energy_bound hU
  obtain ⟨Bv, hBv⟩ := serrinWeak_slice_energy_bound hV
  have hDistanceBound : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      lpsComparisonDistanceSq u v t ≤ 2 * Bu + 2 * Bv := by
    filter_upwards [hBu, hBv, serrinWeak_slices_ae hU, serrinWeak_slices_ae hV]
      with t hBu_t hBv_t hu hv
    have hu2 := hu.1
    have hv2 := hv.1
    have hUsq : Integrable (fun x : Vec3 => ∑ k : Fin 3, u (x, t) k ^ 2) volume :=
      integrable_finsetSum _ fun k _ =>
        ((hu2.eval k).integrable_mul (hu2.eval k)).congr
          (Eventually.of_forall fun x => by simp [pow_two])
    have hVsq : Integrable (fun x : Vec3 => ∑ k : Fin 3, v (x, t) k ^ 2) volume :=
      integrable_finsetSum _ fun k _ =>
        ((hv2.eval k).integrable_mul (hv2.eval k)).congr
          (Eventually.of_forall fun x => by simp [pow_two])
    have hRhsInt : Integrable (fun x : Vec3 =>
        2 * (∑ k : Fin 3, v (x, t) k ^ 2) +
          2 * (∑ k : Fin 3, u (x, t) k ^ 2)) volume :=
      (hVsq.const_mul 2).add (hUsq.const_mul 2)
    have hPoint (x : Vec3) :
        (∑ k : Fin 3, (v (x, t) k - u (x, t) k) ^ 2) ≤
          2 * (∑ k : Fin 3, v (x, t) k ^ 2) +
            2 * (∑ k : Fin 3, u (x, t) k ^ 2) := by
      calc
        _ ≤ ∑ k : Fin 3, (2 * v (x, t) k ^ 2 + 2 * u (x, t) k ^ 2) :=
          Finset.sum_le_sum fun k _ => by
            nlinarith only [sq_nonneg (v (x, t) k + u (x, t) k)]
        _ = (∑ k : Fin 3, 2 * v (x, t) k ^ 2) +
              ∑ k : Fin 3, 2 * u (x, t) k ^ 2 := Finset.sum_add_distrib
        _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
    have hIntegral := integral_mono_of_nonneg
      (Eventually.of_forall fun x => Finset.sum_nonneg fun k _ => sq_nonneg _)
      hRhsInt (Eventually.of_forall hPoint)
    have hExpand :
        (∫ x : Vec3, 2 * (∑ k : Fin 3, v (x, t) k ^ 2) +
          2 * (∑ k : Fin 3, u (x, t) k ^ 2)) =
          2 * (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k ^ 2) +
            2 * (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k ^ 2) := by
      rw [integral_add (hVsq.const_mul 2) (hUsq.const_mul 2),
        integral_const_mul, integral_const_mul]
    change (∫ x : Vec3, ∑ k : Fin 3,
      (v (x, t) k - u (x, t) k) ^ 2) ≤ 2 * Bu + 2 * Bv
    rw [hExpand] at hIntegral
    calc
      _ ≤ 2 * (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k ^ 2) +
          2 * (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k ^ 2) := hIntegral
      _ ≤ 2 * Bv + 2 * Bu := by gcongr
      _ = 2 * Bu + 2 * Bv := by ring
  have hDistanceMeas := serrin_distance_aestronglyMeasurable hU hV
  have hDistanceNonneg (t : ℝ) : 0 ≤ lpsComparisonDistanceSq u v t :=
    integral_nonneg fun x => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hDistanceBoundNorm : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ‖lpsComparisonDistanceSq u v t‖ ≤ 2 * Bu + 2 * Bv := by
    filter_upwards [hDistanceBound] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hDistanceNonneg t)]
    exact ht
  have hm' : Integrable m (volume.restrict (Ioo 0 T)) := hm
  exact hm'.mul_bdd hDistanceMeas hDistanceBoundNorm

/-- Relative-energy and Gronwall conclusion from branch-specific comparison
data. The energy equality remains an explicit hypothesis, supplied by `lem:lps-energy-equality`;
the cross identity and convection integrability are the outputs of a branch's
cross-testing limit. -/
theorem lps_leray_hopf_relative_energy_zero_of_comparison_data
    {T K : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ} {m : ℝ → ℝ}
    (hVLH : IsLerayHopfSolution T a v Dv)
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T a v Dv pv)
    (hK : 0 ≤ K)
    (hEnergyEquality : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Du z k j)
    (hRelativeCross : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -(∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            lpsRelativeConvection u v Du Dv z) -
          2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j)
    (hSliceBound : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, lpsRelativeConvection u v Du Dv (x, τ)) ≤
        (1 / 2 : ℝ) *
          (∫ x : Vec3, lpsRelativeGradientSq Du Dv (x, τ)) +
          K * (m τ * lpsComparisonDistanceSq u v τ))
    (hC : Integrable (lpsRelativeConvection u v Du Dv)
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (hm : IntegrableOn m (Ioo 0 T))
    (hmNonneg : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), 0 ≤ m t)
    :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      lpsComparisonDistanceSq u v t = 0 := by
  have hGradient := lps_relative_gradient_sq_integrable hU hV
  have hEnergyInequality : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * v (x, t) k) ≤
        (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) -
          2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv z k j * Dv z k j := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    have hSlices := (ae_restrict_iff' measurableSet_Ioo).mp
      (serrinWeak_slices_ae hV)
    filter_upwards [hSlices] with t ht htI
    exact lerayHopf_energy_inequality_real hVLH ⟨htI.1.le, htI.2.le⟩ (ht htI).1
  have hmE := lps_comparison_time_weight_integrable hU hV hm
  exact lps_relative_energy_zero_from_slice_bound hU hV hK hEnergyEquality
    hEnergyInequality hRelativeCross hSliceBound hC hGradient hm hmNonneg hmE

/-- The same assembly stated as the comparison inequality before the final
Gronwall conclusion. -/
theorem lps_leray_hopf_relative_energy_inequality_of_comparison_data
    {T K : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ} {m : ℝ → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T a v Dv pv)
    (hEnergyEquality : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Du z k j)
    (hEnergyInequality : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * v (x, t) k) ≤
        (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) -
          2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv z k j * Dv z k j)
    (hRelativeCross : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -(∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            lpsRelativeConvection u v Du Dv z) -
          2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j)
    (hSliceBound : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, lpsRelativeConvection u v Du Dv (x, τ)) ≤
        (1 / 2 : ℝ) *
          (∫ x : Vec3, lpsRelativeGradientSq Du Dv (x, τ)) +
          K * (m τ * lpsComparisonDistanceSq u v τ))
    (hC : Integrable (lpsRelativeConvection u v Du Dv)
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (hGradient : Integrable (lpsRelativeGradientSq Du Dv)
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (hmE : IntegrableOn
      (fun t => m t * lpsComparisonDistanceSq u v t) (Ioo 0 T)) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      lpsComparisonDistanceSq u v t ≤
        2 * K * ∫ τ in (0 : ℝ)..t,
          m τ * lpsComparisonDistanceSq u v τ := by
  have hConvectionBound := lps_relative_convection_bound_integrated
    hSliceBound hC hGradient hmE
  exact lps_relative_energy_inequality_from_identities hU hV hEnergyEquality
    hEnergyInequality hRelativeCross hConvectionBound

end ESS

end
