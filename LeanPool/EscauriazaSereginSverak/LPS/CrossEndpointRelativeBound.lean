/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointEssSup
public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointSlice
public import LeanPool.EscauriazaSereginSverak.LPS.RelativeEnergyAssembly
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinGronwallInputs

/-!
# Endpoint fixed-time relative convection bound

At almost every time the relative convection is bounded by half the relative
gradient energy plus the squared `L∞` norm of the distinguished velocity times
the relative slice energy (`lem:lps-comparison`, endpoint case).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Fixed-time endpoint estimate for the relative convection, in the form used
by the relative-energy assembly. -/
theorem lps_endpoint_relative_slice_bound
    {T : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T a v Dv pv)
    (hEndpoint : (∫⁻ t in Ioo (0 : ℝ) T,
      (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x,t))))
        (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) :
    ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, lpsRelativeConvection u v Du Dv (x,τ)) ≤
        (1 / 2 : ℝ) *
          (∫ x : Vec3, lpsRelativeGradientSq Du Dv (x,τ)) +
          (81 / 2 : ℝ) *
            ((eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,τ)))
                ⊤ volume).toReal ^ 2 * lpsComparisonDistanceSq u v τ) := by
  obtain ⟨-, -, hβbound, -⟩ := lps_endpoint_norm_slice_facts hU.meas_u hEndpoint
  filter_upwards [serrinWeak_slices_ae hU, serrinWeak_slices_ae hV, hβbound,
    (serrin_aesm_prod hU.meas_u).prodMk_right] with τ hu hv hb hum
  have huInf : MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x,τ))) ⊤ volume :=
    memLp_top_of_bound
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hum)
      _ (hb.mono fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
        exact hx)
  have hw2 : MemLp (fun x : Vec3 => v (x,τ) - u (x,τ)) 2 volume := hv.1.sub hu.1
  have hDw2 : MemLp (fun x : Vec3 => Dv (x,τ) - Du (x,τ)) 2 volume := hv.2.1.sub hu.2.1
  have hslice := (lps_endpoint_relative_convection_slice (u := fun x => u (x,τ))
    (w := fun x => v (x,τ) - u (x,τ)) (Dw := fun x => Dv (x,τ) - Du (x,τ))
    hum huInf hw2 hDw2).1
  have hle := (le_abs_self _).trans hslice
  have hconv : (∫ x : Vec3, lpsRelativeConvection u v Du Dv (x,τ)) =
      ∫ x : Vec3, ∑ i : Fin 3, u (x,τ) i *
        ∑ j : Fin 3, (v (x,τ) - u (x,τ)) j * (Dv (x,τ) - Du (x,τ)) i j := by
    simp [lpsRelativeConvection]
  have hgrad : (∫ x : Vec3, lpsRelativeGradientSq Du Dv (x,τ)) =
      ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Dv (x,τ) - Du (x,τ)) i j ^ 2 := by
    simp [lpsRelativeGradientSq]
  have hdist : lpsComparisonDistanceSq u v τ =
      ∫ x : Vec3, ∑ i : Fin 3, (v (x,τ) - u (x,τ)) i ^ 2 := by
    simp [lpsComparisonDistanceSq]
  rw [hconv, hgrad, hdist]
  calc _ ≤ _ := hle
    _ = _ := by ring

end ESS

end
