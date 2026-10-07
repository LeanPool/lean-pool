/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointRelative
public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointRelativeBound
public import LeanPool.EscauriazaSereginSverak.LPS.FiniteUniqueness
public import LeanPool.EscauriazaSereginSverak.LPS.LerayHopfRelativeEnergy

/-!
# Two-branch Leray–Hopf uniqueness

Weak–strong uniqueness among Leray–Hopf solutions under either Serrin condition
of the Ladyzhenskaya–Prodi–Serrin theorem (`thm:lps`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Weak–strong uniqueness under either Serrin condition of `thm:lps`: a
Leray–Hopf solution `v` with the same datum as a Leray–Hopf solution `u` that is
in `L^ℓ_t L^s_x` with `3/s + 2/ℓ = 1`, `3 < s < ∞`, or in `L²_t L∞_x`, agrees
with `u` almost everywhere. -/
theorem lps_leray_hopf_uniqueness
    {T : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    (hU : IsLerayHopfSolution T a u Du)
    (hV : IsLerayHopfSolution T a v Dv)
    (hSerrin :
      (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo 0 T,
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
              ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo 0 T,
        (essSup (fun x : Vec3 =>
          ENNReal.ofReal (vec3EuclideanNorm (u (x,t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) :
    v =ᵐ[volume.restrict
      (spaceTimeSet Set.univ (Ioo (0 : ℝ) T))] u := by
  obtain ⟨pu, hUweak⟩ := serrinWeak_of_lerayHopf hU
  obtain ⟨pv, hVweak⟩ := serrinWeak_of_lerayHopf hV
  rcases hSerrin with hFinite | hEndpoint
  · obtain ⟨s, hs, hmix⟩ := hFinite
    exact lps_finite_leray_hopf_uniqueness hU hV hs hmix
  · let m : ℝ → ℝ := fun τ =>
      (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,τ))) ⊤ volume).toReal ^ 2
    obtain ⟨hCross, hInt⟩ := lps_endpoint_relative_cross_identity hU hV hUweak hVweak hEndpoint
    have hSlice := lps_endpoint_relative_slice_bound hUweak hVweak hEndpoint
    obtain ⟨-, -, -, hm⟩ := lps_endpoint_norm_slice_facts hUweak.meas_u hEndpoint
    have hEnergyEquality := lps_serrin_energy_equality hU (Or.inr hEndpoint)
    have hZero := lps_leray_hopf_relative_energy_zero_of_comparison_data
      hV hUweak hVweak (by norm_num : 0 ≤ (81 / 2 : ℝ))
      hEnergyEquality hCross hSlice hInt
      (by simpa only [m] using hm)
      (by
        filter_upwards [] with τ
        exact sq_nonneg _)
    exact lps_zero_relative_distance_implies_ae_eq hU hV hZero

end ESS

end
