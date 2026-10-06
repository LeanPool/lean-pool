/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointDensityLimits
public import LeanPool.EscauriazaSereginSverak.LPS.MixedCrossFiniteData
public import LeanPool.EscauriazaSereginSverak.LPS.MixedCrossIdentityAssembly
public import LeanPool.EscauriazaSereginSverak.LPS.RelativeCancellation
public import LeanPool.EscauriazaSereginSverak.LPS.RelativeEnergyAssembly
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinEnergyEquality

/-!
# Relative cross identity for an endpoint Serrin solution

The endpoint Serrin coefficient makes both oriented convection pairings
integrable; the slice cancellation at a fixed exponent then combines them into
the relative convection form (`lem:lps-comparison`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Integrability of an essentially bounded velocity component against the
advective convection of an `L∞_t L²_x ∩ L²_t H¹_x` field. -/
theorem lps_endpoint_velocity_convection_integrable
    {T : ℝ} {u w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {β : ℝ → ℝ} {K : ℝ≥0∞} (k : Fin 3)
    (hu : AEStronglyMeasurable (fun z : ParabolicPoint => u z k)
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (hw : AEStronglyMeasurable w
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (hDw : AEStronglyMeasurable Dw
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (hβmeas : AEMeasurable (fun τ => ENNReal.ofReal (β τ)) (volume.restrict (Ioo 0 T)))
    (hβ : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      ∀ᵐ x ∂(volume : Measure Vec3), |u (x,τ) k| ≤ β τ)
    (hβint : (∫⁻ τ in Ioo 0 T, ENNReal.ofReal (β τ) ^ (2 : ℝ)) < ⊤)
    (hK : K ≠ ⊤)
    (hwK : ∀ j : Fin 3, ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => w (x,τ) j) 2 volume ∧
      eLpNorm (fun x : Vec3 => w (x,τ) j) 2 volume ≤ K)
    (hDw2 : ∀ j : Fin 3, MemLp (fun z : ParabolicPoint => Dw z k j) 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T)))) :
    Integrable (fun z : ParabolicPoint => u z k * ∑ j : Fin 3, w z j * Dw z k j)
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) := by
  have hProd (j : Fin 3) := lps_endpoint_product_l2_l1 (T := T)
    (A := fun z => w z j) (B := fun z => Dw z k j) (K := K)
    (hDw2 j) (by filter_upwards [hwK j] with τ h using h.1) hK
    (by filter_upwards [hwK j] with τ h using h.2)
  have hsum := lps_mixed_sum_three_moment (T := T) (p := 2) (q := 1)
    (f := fun j z => w z j * Dw z k j) (by norm_num) (by norm_num)
    (fun j => ((continuous_apply j).comp_aestronglyMeasurable hw).mul
      ((continuous_apply j).comp_aestronglyMeasurable
        ((continuous_apply k).comp_aestronglyMeasurable hDw)))
    (fun j => (hProd j).1) (fun j => (hProd j).2)
  refine (lps_endpoint_cutoff_pairing_limit_linf_l1 (T := T) le_rfl
    (f := fun r => u r k) (g := fun r => ∑ j : Fin 3, w r j * Dw r k j) (β := β)
    hu ?_ hβmeas hβ hβint ?_ ?_).1
  · refine Finset.univ.aestronglyMeasurable_fun_sum ?_
    intro j _
    exact ((continuous_apply j).comp_aestronglyMeasurable hw).mul
      ((continuous_apply j).comp_aestronglyMeasurable
        ((continuous_apply k).comp_aestronglyMeasurable hDw))
  · filter_upwards [hsum.1] with τ h
    have := h
    rw [ENNReal.ofReal_one] at this
    exact memLp_one_iff_integrable.mp this
  · refine lt_of_le_of_lt (le_of_eq ?_) hsum.2
    refine lintegral_congr_ae ?_
    filter_upwards [hsum.1] with τ h
    rw [ENNReal.ofReal_one] at h ⊢
    rw [eLpNorm_one_eq_lintegral_enorm h.aestronglyMeasurable]

/-- Integrability of an `L∞_t L²_x` velocity component against the advective
convection of an essentially bounded `L²_t L∞_x` field. -/
theorem lps_endpoint_energy_convection_integrable
    {T : ℝ} {z w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {β : ℝ → ℝ} {K : ℝ≥0∞} (k : Fin 3)
    (hz : AEStronglyMeasurable (fun q : ParabolicPoint => z q k)
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (hw : AEStronglyMeasurable w
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (hDw : AEStronglyMeasurable Dw
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (hβmeas : AEMeasurable (fun τ => ENNReal.ofReal (β τ)) (volume.restrict (Ioo 0 T)))
    (hβ : ∀ j : Fin 3, ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      ∀ᵐ x ∂(volume : Measure Vec3), |w (x,τ) j| ≤ β τ)
    (hβint : (∫⁻ τ in Ioo 0 T, ENNReal.ofReal (β τ) ^ (2 : ℝ)) < ⊤)
    (hK : K ≠ ⊤)
    (hzK : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => z (x,τ) k) 2 volume ∧
      eLpNorm (fun x : Vec3 => z (x,τ) k) 2 volume ≤ K)
    (hDw2 : ∀ j : Fin 3, MemLp (fun q : ParabolicPoint => Dw q k j) 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T)))) :
    Integrable (fun q : ParabolicPoint => z q k * ∑ j : Fin 3, w q j * Dw q k j)
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) := by
  have hProd (j : Fin 3) := lps_endpoint_product_linf_l2 (T := T)
    (A := fun q => w q j) (B := fun q => Dw q k j) (β := β)
    ((continuous_apply j).comp_aestronglyMeasurable hw) (hDw2 j) hβmeas (hβ j) hβint
  have hsum := lps_mixed_sum_three_moment (T := T) (p := 1) (q := 2)
    (f := fun j q => w q j * Dw q k j) (by norm_num) (by norm_num)
    (fun j => ((continuous_apply j).comp_aestronglyMeasurable hw).mul
      ((continuous_apply j).comp_aestronglyMeasurable
        ((continuous_apply k).comp_aestronglyMeasurable hDw)))
    (fun j => (hProd j).1) (fun j => (hProd j).2)
  refine (lps_endpoint_cutoff_pairing_limit_l2_l2 (T := T) le_rfl
    (f := fun r => z r k) (g := fun r => ∑ j : Fin 3, w r j * Dw r k j) (K := K)
    hz ?_ (by filter_upwards [hzK] with τ h using h.1) hK
    (by filter_upwards [hzK] with τ h using h.2) ?_ ?_).1
  · refine Finset.univ.aestronglyMeasurable_fun_sum ?_
    intro j _
    exact ((continuous_apply j).comp_aestronglyMeasurable hw).mul
      ((continuous_apply j).comp_aestronglyMeasurable
        ((continuous_apply k).comp_aestronglyMeasurable hDw))
  · filter_upwards [hsum.1] with τ h
    simpa using h
  · simpa using hsum.2

/-- The endpoint Serrin cross-testings combine into the relative cross
identity. The two oriented densities are `u · ((v · ∇)v)` and `v · ((u · ∇)u)`;
their cancellation uses only the integrable products in the slice lemma. -/
theorem lps_endpoint_relative_cross_identity
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
    (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x,t) k * u (x,t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -(∫ z in spaceTimeSet Set.univ (Ioo 0 t),
            lpsRelativeConvection u v Du Dv z) -
          2 * ∫ z in spaceTimeSet Set.univ (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j) ∧
      Integrable (lpsRelativeConvection u v Du Dv)
        (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) := by
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
  let μT : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))
  have hA (k : Fin 3) : Integrable
      (fun z : ParabolicPoint => u z k * ∑ j : Fin 3, v z j * Dv z k j) μT :=
    lps_endpoint_velocity_convection_integrable k
      ((continuous_apply k).comp_aestronglyMeasurable hU.meas_u) hV.meas_u hV.meas_Du
      hβmeas (hβ k) hβint hKv (fun j => by
        filter_upwards [hKvBound j] with τ h using h)
      (fun j => (hDV2.eval k).eval j)
  have hB (k : Fin 3) : Integrable
      (fun z : ParabolicPoint => v z k * ∑ j : Fin 3, u z j * Du z k j) μT :=
    lps_endpoint_energy_convection_integrable k
      ((continuous_apply k).comp_aestronglyMeasurable hV.meas_u) hU.meas_u hU.meas_Du
      hβmeas hβ hβint hKv (by filter_upwards [hKvBound k] with τ h using h)
      (fun j => (hDU2.eval k).eval j)
  have hR (k : Fin 3) : Integrable
      (fun z : ParabolicPoint => u z k * ∑ j : Fin 3,
        (v z j - u z j) * (Dv z k j - Du z k j)) μT :=
    lps_endpoint_velocity_convection_integrable (w := fun z => v z - u z)
      (Dw := fun z => Dv z - Du z) k
      ((continuous_apply k).comp_aestronglyMeasurable hU.meas_u)
      (hV.meas_u.sub hU.meas_u) (hV.meas_Du.sub hU.meas_Du)
      hβmeas (hβ k) hβint (ENNReal.add_ne_top.mpr ⟨hKv, hKu⟩) (fun j => by
        filter_upwards [hKvBound j, hKuBound j] with τ h1 h2
        refine ⟨h1.1.sub h2.1, ?_⟩
        calc _ ≤ eLpNorm (fun x : Vec3 => v (x,τ) j) 2 volume +
            eLpNorm (fun x : Vec3 => u (x,τ) j) 2 volume :=
              eLpNorm_sub_le (by norm_num)
          _ ≤ Kv + Ku := add_le_add h1.2 h2.2)
      (fun j => ((hDV2.sub hDU2).eval k).eval j)
  have hAall : Integrable
      (fun z : ParabolicPoint =>
        ∑ k : Fin 3, u z k * ∑ j : Fin 3, v z j * Dv z k j) μT :=
    integrable_finsetSum _ fun k _ => hA k
  have hBall : Integrable
      (fun z : ParabolicPoint =>
        ∑ k : Fin 3, v z k * ∑ j : Fin 3, u z j * Du z k j) μT :=
    integrable_finsetSum _ fun k _ => hB k
  have hRsum : Integrable
      (fun z : ParabolicPoint =>
        ∑ k ∈ (Finset.univ : Finset (Fin 3)),
          u z k * ∑ j : Fin 3, (v z j - u z j) * (Dv z k j - Du z k j)) μT :=
    integrable_finsetSum Finset.univ (fun k _ => hR k)
  have hRall : Integrable (lpsRelativeConvection u v Du Dv) μT := by
    refine hRsum.congr ?_
    filter_upwards [] with z
    simp [lpsRelativeConvection]
  let F : ParabolicPoint → ℝ := fun z =>
    (∑ k : Fin 3, u z k * ∑ j : Fin 3, v z j * Dv z k j) +
      (∑ k : Fin 3, v z k * ∑ j : Fin 3, u z j * Du z k j) -
        lpsRelativeConvection u v Du Dv z
  have hFint : Integrable F μT := by
    exact (hAall.add hBall).sub hRall |>.congr
      (Eventually.of_forall fun z => by simp [F])
  have hCancel : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∫ x : Vec3, F (x,t) = 0 := by
    have hslU := serrinWeak_slice_ae hU
    have hslV := serrinWeak_slice_ae hV
    have hUe := lps_energy_coordinate_mixed_data hULH hU (s := 4) (by norm_num)
    have hVe := lps_energy_coordinate_mixed_data hVLH hV (s := 4) (by norm_num)
    filter_upwards [hslU, hslV, (hUe 0).1, (hUe 1).1, (hUe 2).1,
      (hVe 0).1, (hVe 1).1, (hVe 2).1] with
      t hu hv hu0 hu1 hu2 hv0 hv1 hv2
    have huQ : MemLp (fun x : Vec3 => u (x,t)) (ENNReal.ofReal (2 * 4 / (4 - 2))) volume := by
      apply memLp_pi_iff.mpr
      intro k
      fin_cases k <;> assumption
    have hvQ : MemLp (fun x : Vec3 => v (x,t)) (ENNReal.ofReal (2 * 4 / (4 - 2))) volume := by
      apply memLp_pi_iff.mpr
      intro k
      fin_cases k <;> assumption
    have huS : MemLp (fun x : Vec3 => u (x,t)) (ENNReal.ofReal 4) volume := by
      have h4 : ((2 : ℝ) * 4 / (4 - 2)) = 4 := by norm_num
      rw [h4] at huQ
      exact huQ
    have hcancel := lps_slice_relative_cancellation (s := 4) (by norm_num) hu huS huQ hv hvQ
    simpa [F, lpsRelativeConvection] using hcancel
  refine ⟨?_, hRall⟩
  have hDens := lps_mixed_cross_density_limits_endpoint
    hULH hVLH hU hV hEndpoint
  have hCross := lps_cross_identity_from_density_limits hU hV hDens.1 hDens.2
  have hCrossOpen := (ae_restrict_iff' measurableSet_Ioo).mp hCross
  have hCancelOpen := (ae_restrict_iff' measurableSet_Ioo).mp hCancel
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hCrossOpen, hCancelOpen] with t hc hcan ht
  have hslab0 := serrin_slab_integral_eq_zero ht.1.le ht.2.le
    (hFint.mono_measure (serrin_slab_restrict_le ht.2.le)) hCancel
  have hsum :
      (∫ z in spaceTimeSet Set.univ (Ioo 0 t),
          ∑ k : Fin 3, u z k * ∑ j : Fin 3, v z j * Dv z k j) +
        ∫ z in spaceTimeSet Set.univ (Ioo 0 t),
          ∑ k : Fin 3, v z k * ∑ j : Fin 3, u z j * Du z k j =
        ∫ z in spaceTimeSet Set.univ (Ioo 0 t), lpsRelativeConvection u v Du Dv z := by
    have hAt := hAall.mono_measure (serrin_slab_restrict_le ht.2.le)
    have hBt := hBall.mono_measure (serrin_slab_restrict_le ht.2.le)
    have hRt := hRall.mono_measure (serrin_slab_restrict_le ht.2.le)
    have hAB := hAt.add hBt
    let A : ParabolicPoint → ℝ := fun z =>
      ∑ k : Fin 3, u z k * ∑ j : Fin 3, v z j * Dv z k j
    let B : ParabolicPoint → ℝ := fun z =>
      ∑ k : Fin 3, v z k * ∑ j : Fin 3, u z j * Du z k j
    let R : ParabolicPoint → ℝ := lpsRelativeConvection u v Du Dv
    have hslab0' :
        (∫ z in spaceTimeSet Set.univ (Ioo 0 t), (A + B - R) z) = 0 := by
      simpa [F, A, B, R] using hslab0
    have hsub :
        (∫ z in spaceTimeSet Set.univ (Ioo 0 t), (A + B - R) z) =
          (∫ z in spaceTimeSet Set.univ (Ioo 0 t), (A + B) z) -
            ∫ z in spaceTimeSet Set.univ (Ioo 0 t), R z :=
      integral_sub hAB hRt
    have hadd :
        (∫ z in spaceTimeSet Set.univ (Ioo 0 t), (A + B) z) =
          (∫ z in spaceTimeSet Set.univ (Ioo 0 t), A z) +
            ∫ z in spaceTimeSet Set.univ (Ioo 0 t), B z :=
      integral_add hAt hBt
    rw [hsub, hadd] at hslab0'
    linarith only [hslab0']
  have hgradComm :
      (∫ z in spaceTimeSet Set.univ (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Dv z k j * Du z k j) =
        ∫ z in spaceTimeSet Set.univ (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j := by
    congr 1
    funext z
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hAlg :
      ((-(∫ z in spaceTimeSet Set.univ (Ioo 0 t),
          ∑ k : Fin 3, u z k * ∑ j : Fin 3, v z j * Dv z k j) -
        (∫ z in spaceTimeSet Set.univ (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j)) +
       (-(∫ z in spaceTimeSet Set.univ (Ioo 0 t),
          ∑ k : Fin 3, v z k * ∑ j : Fin 3, u z j * Du z k j) -
        (∫ z in spaceTimeSet Set.univ (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Dv z k j * Du z k j))) =
      -(∫ z in spaceTimeSet Set.univ (Ioo 0 t),
          lpsRelativeConvection u v Du Dv z) -
        2 * (∫ z in spaceTimeSet Set.univ (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j) := by
    have hsumNeg :
        -(∫ z in spaceTimeSet Set.univ (Ioo 0 t),
            ∑ k : Fin 3, u z k * ∑ j : Fin 3, v z j * Dv z k j) +
          -(∫ z in spaceTimeSet Set.univ (Ioo 0 t),
            ∑ k : Fin 3, v z k * ∑ j : Fin 3, u z j * Du z k j) =
        -(∫ z in spaceTimeSet Set.univ (Ioo 0 t),
            lpsRelativeConvection u v Du Dv z) := by
      linarith only [hsum]
    rw [hgradComm]
    linarith only [hsumNeg]
  rw [hc ht]
  exact hAlg

end ESS

end
