/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointEssSup
public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointProducts
public import LeanPool.EscauriazaSereginSverak.LPS.MixedCrossDensityLimit
public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormSumMoment
public import LeanPool.CaffarelliKohnNirenberg.Leray.TenThirds
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinGronwallInputs
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.SerrinPairingLimit
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSlab

/-!
# Endpoint cross-density limits

For a Leray--Hopf solution with `L²_t L∞_x` velocity, both oriented cross
densities have the integrability and cutoff-mollification limits needed for the
cross-testing identity (`lem:lps-comparison`, endpoint case).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A weak solution has uniformly bounded slice `L²` norms of every velocity
component. -/
theorem lps_component_energy_bound {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hU : IsSerrinWeakSolution T a u Du p) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ j : Fin 3, ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => u (x,τ) j) 2 volume ∧
      eLpNorm (fun x : Vec3 => u (x,τ) j) 2 volume ≤ K := by
  obtain ⟨B, hB⟩ := serrinWeak_slice_energy_bound hU
  refine ⟨ENNReal.ofReal (Real.sqrt B), ENNReal.ofReal_ne_top, fun j => ?_⟩
  filter_upwards [hB, serrinWeak_slices_ae hU] with τ hBτ hτ
  have hu2 := hτ.1
  have hj : MemLp (fun x : Vec3 => u (x,τ) j) 2 volume := hu2.eval j
  refine ⟨hj, lps_eLpNorm_two_le_sqrt hj ?_⟩
  have hsq (k : Fin 3) : Integrable (fun x : Vec3 => u (x,τ) k ^ 2) volume :=
    ((hu2.eval k).integrable_mul (hu2.eval k)).congr
      (Eventually.of_forall fun x => by simp [pow_two])
  calc (∫ x : Vec3, u (x,τ) j ^ 2) ≤ ∫ x : Vec3, ∑ k : Fin 3, u (x,τ) k ^ 2 := by
        refine integral_mono (hsq j) (integrable_finsetSum _ fun k _ => hsq k) fun x => ?_
        exact Finset.single_le_sum (f := fun k : Fin 3 => u (x,τ) k ^ 2)
          (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ B := hBτ

/-- Both oriented cross densities have the required integrability and
cutoff-mollification limits when the distinguished velocity satisfies the
endpoint Serrin condition. The first product is the distinguished velocity
against the rival's advective convection. -/
theorem lps_mixed_cross_density_limits_endpoint
    {T : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hULH : IsLerayHopfSolution T a u Du)
    (hVLH : IsLerayHopfSolution T a v Dv)
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T a v Dv pv)
    (hEndpoint : (∫⁻ t in Ioo (0 : ℝ) T,
      (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x,t))))
        (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) :
    (∀ t, t ∈ Ioo (0 : ℝ) T →
      (∀ᶠ n in atTop, Integrable
        (serrinCrossDensity v Dv pv u Du n (serrinCutoff n))
        (volume.restrict (spaceTimeSet Set.univ (Ioo 0 t)))) ∧
      Tendsto (fun n => ∫ q in spaceTimeSet Set.univ (Ioo 0 t),
        serrinCrossDensity v Dv pv u Du n (serrinCutoff n) q) atTop
        (𝓝 (-(∫ q in spaceTimeSet Set.univ (Ioo 0 t),
            ∑ k : Fin 3, u q k * ∑ j : Fin 3, v q j * Dv q k j)
          - ∫ q in spaceTimeSet Set.univ (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Dv q k j))) ∧
    (∀ t, t ∈ Ioo (0 : ℝ) T →
      (∀ᶠ n in atTop, Integrable
        (serrinCrossDensity u Du pu v Dv n (serrinCutoff n))
        (volume.restrict (spaceTimeSet Set.univ (Ioo 0 t)))) ∧
      Tendsto (fun n => ∫ q in spaceTimeSet Set.univ (Ioo 0 t),
        serrinCrossDensity u Du pu v Dv n (serrinCutoff n) q) atTop
        (𝓝 (-(∫ q in spaceTimeSet Set.univ (Ioo 0 t),
            ∑ k : Fin 3, v q k * ∑ j : Fin 3, u q j * Du q k j)
          - ∫ q in spaceTimeSet Set.univ (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv q k j * Du q k j))) := by
  obtain ⟨hβmeas, hβint, hβbound, -⟩ := lps_endpoint_norm_slice_facts hU.meas_u hEndpoint
  set β : ℝ → ℝ := fun τ =>
    (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,τ))) ⊤ volume).toReal with hβdef
  have hβ (j : Fin 3) : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      ∀ᵐ x ∂(volume : Measure Vec3), |u (x,τ) j| ≤ β τ := by
    filter_upwards [hβbound] with τ hτ
    filter_upwards [hτ] with x hx
    exact (abs_apply_le_vec3EuclideanNorm _ j).trans hx
  obtain ⟨Ku, hKu, hKuBound⟩ := lps_component_energy_bound hU
  obtain ⟨Kv, hKv, hKvBound⟩ := lps_component_energy_bound hV
  have hDU2 := serrinWeak_gradient_memLp_two hU
  have hDV2 := serrinWeak_gradient_memLp_two hV
  have hU2 := serrinWeak_velocity_memLp_two hU
  have hV2 := serrinWeak_velocity_memLp_two hV
  have hU52 : MemLp u (ENNReal.ofReal (5 / 2))
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) :=
    serrin_memLp_interpolate (p := 2) (q := ENNReal.ofReal (10 / 3))
      (r := ENNReal.ofReal (5 / 2)) (by norm_num) (by simp)
      (by rw [← ENNReal.ofReal_ofNat 2]; exact ENNReal.ofReal_le_ofReal (by norm_num))
      (ENNReal.ofReal_le_ofReal (by norm_num)) hU2 (lerayHopf_memLp_tenThirds hULH).1
  have hV52 : MemLp v (ENNReal.ofReal (5 / 2))
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) :=
    serrin_memLp_interpolate (p := 2) (q := ENNReal.ofReal (10 / 3))
      (r := ENNReal.ofReal (5 / 2)) (by norm_num) (by simp)
      (by rw [← ENNReal.ofReal_ofNat 2]; exact ENNReal.ofReal_le_ofReal (by norm_num))
      (ENNReal.ofReal_le_ofReal (by norm_num)) hV2 (lerayHopf_memLp_tenThirds hVLH).1
  constructor
  · -- distinguished velocity `u` tested against the convection `(v · ∇) v`
    intro t ht
    have hPair (k : Fin 3) := by
      have hProd (j : Fin 3) := lps_endpoint_product_l2_l1 (T := T)
        (A := fun z => v z j) (B := fun z => Dv z k j) (K := Kv)
        ((hDV2.eval k).eval j) (by filter_upwards [hKvBound j] with τ h using h.1) hKv
        (by filter_upwards [hKvBound j] with τ h using h.2)
      have hsum := lps_mixed_sum_three_moment (T := T) (p := 2) (q := 1)
        (f := fun j z => v z j * Dv z k j) (by norm_num) (by norm_num)
        (fun j => (lps_coordinate_aesm hV.meas_u j).mul
          (lps_gradient_entry_aesm hV.meas_Du k j))
        (fun j => (hProd j).1) (fun j => (hProd j).2)
      refine lps_endpoint_cutoff_pairing_limit_linf_l1 (T := T) ht.2.le
        (f := fun r => u r k) (g := fun r => ∑ j : Fin 3, v r j * Dv r k j) (β := β)
        (lps_coordinate_aesm hU.meas_u k)
        (lps_convection_aesm hV.meas_u hV.meas_Du k)
        hβmeas (hβ k) hβint ?_ ?_
      · filter_upwards [hsum.1] with τ h
        have := h
        rw [ENNReal.ofReal_one] at this
        exact memLp_one_iff_integrable.mp this
      · refine lt_of_le_of_lt (le_of_eq ?_) hsum.2
        refine lintegral_congr_ae ?_
        filter_upwards [hsum.1] with τ h
        rw [ENNReal.ofReal_one] at h ⊢
        rw [eLpNorm_one_eq_lintegral_enorm h.aestronglyMeasurable]
    exact lps_cross_density_limit_of_pairing ht.2.le
      (fun k => Eventually.of_forall fun n => (hPair k).2.1 n)
      (fun k => (hPair k).2.2) (fun k => (hPair k).1)
      (fun k j => (hDU2.eval k).eval j) (fun k j => (hDV2.eval k).eval j)
      (fun k => hU2.eval k) (fun k => hU52.eval k) hV.pressure
  · -- distinguished velocity `v` tested against the convection `(u · ∇) u`
    intro t ht
    have hPair (k : Fin 3) := by
      have hProd (j : Fin 3) := lps_endpoint_product_linf_l2 (T := T)
        (A := fun z => u z j) (B := fun z => Du z k j) (β := β)
        (lps_coordinate_aesm hU.meas_u j) ((hDU2.eval k).eval j) hβmeas (hβ j) hβint
      have hsum := lps_mixed_sum_three_moment (T := T) (p := 1) (q := 2)
        (f := fun j z => u z j * Du z k j) (by norm_num) (by norm_num)
        (fun j => (lps_coordinate_aesm hU.meas_u j).mul
          (lps_gradient_entry_aesm hU.meas_Du k j))
        (fun j => (hProd j).1) (fun j => (hProd j).2)
      refine lps_endpoint_cutoff_pairing_limit_l2_l2 (T := T) ht.2.le
        (f := fun r => v r k) (g := fun r => ∑ j : Fin 3, u r j * Du r k j) (K := Kv)
        (lps_coordinate_aesm hV.meas_u k)
        (lps_convection_aesm hU.meas_u hU.meas_Du k)
        (by filter_upwards [hKvBound k] with τ h using h.1) hKv
        (by filter_upwards [hKvBound k] with τ h using h.2) ?_ ?_
      · filter_upwards [hsum.1] with τ h
        simpa using h
      · simpa using hsum.2
    exact lps_cross_density_limit_of_pairing ht.2.le
      (fun k => Eventually.of_forall fun n => (hPair k).2.1 n)
      (fun k => (hPair k).2.2) (fun k => (hPair k).1)
      (fun k j => (hDV2.eval k).eval j) (fun k j => (hDU2.eval k).eval j)
      (fun k => hV2.eval k) (fun k => hV52.eval k) hU.pressure

end ESS

end
