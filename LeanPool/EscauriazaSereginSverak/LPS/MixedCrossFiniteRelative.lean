/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.MixedCrossFiniteLimits
public import LeanPool.EscauriazaSereginSverak.LPS.MixedCrossIdentityAssembly
public import LeanPool.EscauriazaSereginSverak.LPS.RelativeCancellation
public import LeanPool.EscauriazaSereginSverak.LPS.RelativeEnergyAssembly
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinEnergyEquality

/-!
# Relative cross identity for a finite Serrin solution

The finite mixed norms make both oriented weak cross-testings integrable.
The slice cancellation then combines them into the relative convection form.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The finite Serrin cross-testings combine into the relative cross identity.
The two oriented densities are `u · ((v · ∇)v)` and `v · ((u · ∇)u)`;
their cancellation uses only the integrable products in the slice lemma. -/
theorem lps_finite_relative_cross_identity
    {T s : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hULH : IsLerayHopfSolution T a u Du)
    (hVLH : IsLerayHopfSolution T a v Dv)
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T a v Dv pv)
    (hs : 3 < s)
    (hmix : (∫⁻ t in Ioo (0 : ℝ) T,
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ s) ^
          ((2 * s / (s - 3)) / s)) < ⊤) :
    (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x,t) k * u (x,t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -(∫ z in spaceTimeSet Set.univ (Ioo 0 t),
            lpsRelativeConvection u v Du Dv z) -
          2 * ∫ z in spaceTimeSet Set.univ (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j) ∧
      Integrable (lpsRelativeConvection u v Du Dv)
        (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) := by
  let ell : ℝ := 2 * s / (s - 3)
  let qE : ℝ := 2 * s / (s - 2)
  let pE : ℝ := 2 * s / 3
  let qN : ℝ := s / (s - 1)
  let pN : ℝ := 2 * s / (s + 3)
  let qNS : ℝ := 2 * s / (s + 2)
  let pNS : ℝ := 2 * s / (2 * s - 3)
  have hs0 : 0 < s := by linarith only [hs]
  have hs1 : 0 < s - 1 := by linarith only [hs]
  have hs2 : 0 < s - 2 := by linarith only [hs]
  have hs3 : 0 < s - 3 := by linarith only [hs]
  have hsplus2 : 0 < s + 2 := by positivity
  have hsplus3 : 0 < s + 3 := by positivity
  have h2sminus3 : 0 < 2 * s - 3 := by linarith only [hs]
  have hqE1 : 1 ≤ qE := by
    dsimp [qE]
    rw [le_div_iff₀ hs2]
    nlinarith only [hs]
  have hpE1 : 1 ≤ pE := by
    dsimp [pE]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith only [hs]
  have hqN1 : 1 ≤ qN := by
    dsimp [qN]
    rw [le_div_iff₀ hs1]
    linarith only [hs]
  have hpN1 : 1 ≤ pN := by
    dsimp [pN]
    rw [le_div_iff₀ hsplus3]
    linarith only [hs]
  have hqNS1 : 1 ≤ qNS := by
    dsimp [qNS]
    rw [le_div_iff₀ hsplus2]
    linarith only [hs]
  have hpNS1 : 1 ≤ pNS := by
    dsimp [pNS]
    rw [le_div_iff₀ h2sminus3]
    nlinarith only [hs]
  have hSpaceE : qE⁻¹ + (2 : ℝ)⁻¹ = qN⁻¹ := by
    dsimp [qE, qN]
    field_simp [ne_of_gt hs0, ne_of_gt hs1, ne_of_gt hs2]
    ring
  have hTimeE : pE⁻¹ + (2 : ℝ)⁻¹ = pN⁻¹ := by
    dsimp [pE, pN]
    field_simp [ne_of_gt hs0, ne_of_gt h2sminus3]
    ring
  have hSpaceS : s⁻¹ + (2 : ℝ)⁻¹ = qNS⁻¹ := by
    dsimp [qNS]
    field_simp [ne_of_gt hs0, ne_of_gt hsplus2]
    ring
  have hTimeS : ell⁻¹ + (2 : ℝ)⁻¹ = pNS⁻¹ := by
    dsimp [ell, pNS]
    field_simp [ne_of_gt hs0, ne_of_gt hs3, ne_of_gt h2sminus3]
    ring
  have hZVspace : s⁻¹ + qN⁻¹ = 1 := by
    dsimp [qN]
    field_simp [ne_of_gt hs0, ne_of_gt hs1]
    ring
  have hZVtime : ell⁻¹ + pN⁻¹ = 1 := by
    dsimp [ell, pN]
    field_simp [ne_of_gt hs0, ne_of_gt hs3, ne_of_gt hsplus3]
    ring
  have hUVspace : qE⁻¹ + qNS⁻¹ = 1 := by
    dsimp [qE, qNS]
    field_simp [ne_of_gt hs0, ne_of_gt hs2, ne_of_gt hsplus2]
    ring
  have hUVtime : pE⁻¹ + pNS⁻¹ = 1 := by
    dsimp [pE, pNS]
    field_simp [ne_of_gt hs0, ne_of_gt h2sminus3]
    ring
  have hHolderZVspace : s.HolderConjugate qN :=
    lps_real_holder_pair hs0 (by positivity) hZVspace
  have hHolderZVtime : ell.HolderConjugate pN :=
    lps_real_holder_pair (by dsimp [ell]; positivity) (by positivity) hZVtime
  have hHolderUVspace : qE.HolderConjugate qNS :=
    lps_real_holder_pair (by positivity) (by positivity) hUVspace
  have hHolderUVtime : pE.HolderConjugate pNS :=
    lps_real_holder_pair (by positivity) (by positivity) hUVtime
  have hUserrin := lps_finite_coordinate_mixed_data hU hs hmix
  have hUenergy := lps_energy_coordinate_mixed_data hULH hU hs
  have hVenergy := lps_energy_coordinate_mixed_data hVLH hV hs
  have hDU2 := serrinWeak_gradient_memLp_two hU
  have hDV2 := serrinWeak_gradient_memLp_two hV
  have hConvV := lps_mixed_convection_moment hqE1 hpE1 hqN1 hpN1
    hSpaceE hTimeE hV.meas_u hV.meas_Du
    (fun j => (hVenergy j).1) (fun j => (hVenergy j).2) hDV2
  have hConvU := lps_mixed_convection_moment (by linarith only [hs])
      (by dsimp [ell]; rw [le_div_iff₀ hs3]; linarith only [hs])
      hqNS1 hpNS1 hSpaceS hTimeS hU.meas_u hU.meas_Du
    (fun j => (hUserrin j).1) (fun j => (hUserrin j).2) hDU2
  have hSpaceConvW : ∀ j, (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => v (x,t) j - u (x,t) j)
        (ENNReal.ofReal qE) volume) ∧
      (∫⁻ t in Ioo 0 T,
        eLpNorm (fun x : Vec3 => v (x,t) j - u (x,t) j)
          (ENNReal.ofReal qE) volume ^ pE) < ⊤ := by
    intro j
    let f : Fin 3 → ParabolicPoint → ℝ := fun i =>
      if i = 0 then fun z => v z j else if i = 1 then fun z => -u z j
        else fun _ => (0 : ℝ)
    have hsum := lps_mixed_sum_three_moment (T := T) (p := pE) (q := qE)
      (f := f) hpE1 hqE1
      (by
        intro i
        fin_cases i
        · exact (lps_coordinate_aesm hV.meas_u j)
        · exact (lps_coordinate_aesm hU.meas_u j).neg
        · exact aestronglyMeasurable_zero)
      (by
        intro i
        fin_cases i
        · simpa [f] using (hVenergy j).1
        · filter_upwards [(hUenergy j).1] with t ht
          change MemLp (fun x : Vec3 => -u ((x,t) : ParabolicPoint) j)
            (ENNReal.ofReal qE) volume
          have hneg : (fun x : Vec3 => -u ((x,t) : ParabolicPoint) j) =
              -(fun x : Vec3 => u ((x,t) : ParabolicPoint) j) := by
            funext x
            rfl
          rw [hneg]
          simpa [qE] using ht.neg
        · filter_upwards [] with t
          change MemLp (fun _ : Vec3 => (0 : ℝ)) (ENNReal.ofReal qE) volume
          exact MemLp.zero)
      (by
        intro i
        fin_cases i
        · simpa [f] using (hVenergy j).2
        · have hneg (t : ℝ) : (fun x : Vec3 => -u ((x,t) : ParabolicPoint) j) =
              -(fun x : Vec3 => u ((x,t) : ParabolicPoint) j) := by
            funext x
            rfl
          change (∫⁻ t in Ioo 0 T,
            eLpNorm (fun x : Vec3 => -u ((x,t) : ParabolicPoint) j)
              (ENNReal.ofReal qE) volume ^ pE) < ⊤
          simp_rw [hneg, eLpNorm_neg]
          simpa [qE, pE] using (hUenergy j).2
        · change (∫⁻ t in Ioo 0 T,
            (eLpNorm (0 : Vec3 → ℝ) (ENNReal.ofReal qE) volume) ^ pE) < ⊤
          rw [eLpNorm_zero]
          rw [ENNReal.zero_rpow_of_pos (by linarith only [hpE1])]
          simp)
    have hsumEq (t : ℝ) : (fun x : Vec3 => ∑ i : Fin 3, f i (x,t)) =
        (fun x => v (x,t) j - u (x,t) j) := by
      funext x
      simp [f, Fin.sum_univ_three]
      ring
    constructor
    · filter_upwards [hsum.1] with t ht
      rw [← hsumEq t]
      exact ht
    · have hEq : (fun t : ℝ => eLpNorm
          (fun x : Vec3 => ∑ i : Fin 3, f i (x,t))
          (ENNReal.ofReal qE) volume ^ pE) =ᵐ[volume.restrict (Ioo 0 T)]
          (fun t => eLpNorm (fun x : Vec3 => v (x,t) j - u (x,t) j)
            (ENNReal.ofReal qE) volume ^ pE) := by
        filter_upwards [] with t
        rw [hsumEq t]
      rw [← lintegral_congr_ae hEq]
      exact hsum.2
  have hDiff2 : MemLp (fun z : ParabolicPoint => Dv z - Du z) 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) := hDV2.sub hDU2
  have hConvW := lps_mixed_convection_moment hqE1 hpE1 hqN1 hpN1
    hSpaceE hTimeE (hV.meas_u.sub hU.meas_u) (hV.meas_Du.sub hU.meas_Du)
    (fun j => (hSpaceConvW j).1) (fun j => (hSpaceConvW j).2) hDiff2
  let μT : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))
  have hA (k : Fin 3) : Integrable
      (fun z : ParabolicPoint => u z k * ∑ j : Fin 3, v z j * Dv z k j) μT :=
    (lps_mixed_product_integrable hs0 (by positivity)
      (by dsimp [ell]; positivity) (by positivity)
      hHolderZVspace hHolderZVtime
      (lps_coordinate_aesm hU.meas_u k)
      (lps_convection_aesm hV.meas_u hV.meas_Du k)
      (hUserrin k).1 (hConvV k).1 (hUserrin k).2 (hConvV k).2).1
  have hB (k : Fin 3) : Integrable
      (fun z : ParabolicPoint => v z k * ∑ j : Fin 3, u z j * Du z k j) μT :=
    (lps_mixed_product_integrable (by positivity) (by positivity)
      (by positivity) (by positivity)
      hHolderUVspace hHolderUVtime
      (lps_coordinate_aesm hV.meas_u k)
      (lps_convection_aesm hU.meas_u hU.meas_Du k)
      (hVenergy k).1 (hConvU k).1 (hVenergy k).2 (hConvU k).2).1
  have hR (k : Fin 3) : Integrable
      (fun z : ParabolicPoint => u z k * ∑ j : Fin 3,
        (v z j - u z j) * (Dv z k j - Du z k j)) μT :=
    (lps_mixed_product_integrable (by positivity) (by positivity)
      (by positivity) (by positivity)
      hHolderZVspace hHolderZVtime
      (lps_coordinate_aesm hU.meas_u k)
      (lps_convection_aesm (hV.meas_u.sub hU.meas_u)
        (hV.meas_Du.sub hU.meas_Du) k)
      (hUserrin k).1 (hConvW k).1 (hUserrin k).2 (hConvW k).2).1
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
    filter_upwards [hslU, hslV,
      (hUserrin 0).1, (hUserrin 1).1, (hUserrin 2).1,
      (lps_energy_coordinate_mixed_data hULH hU hs 0).1,
      (lps_energy_coordinate_mixed_data hULH hU hs 1).1,
      (lps_energy_coordinate_mixed_data hULH hU hs 2).1,
      (lps_energy_coordinate_mixed_data hVLH hV hs 0).1,
      (lps_energy_coordinate_mixed_data hVLH hV hs 1).1,
      (lps_energy_coordinate_mixed_data hVLH hV hs 2).1] with
      t hu hv huS0 huS1 huS2 hu0 hu1 hu2 hv0 hv1 hv2
    have huQ : MemLp (fun x : Vec3 => u (x,t)) (ENNReal.ofReal qE) volume := by
      apply memLp_pi_iff.mpr
      intro k
      fin_cases k <;> assumption
    have hvQ : MemLp (fun x : Vec3 => v (x,t)) (ENNReal.ofReal qE) volume := by
      apply memLp_pi_iff.mpr
      intro k
      fin_cases k <;> assumption
    have huSvec : MemLp (fun x : Vec3 => u (x,t)) (ENNReal.ofReal s) volume := by
      apply memLp_pi_iff.mpr
      intro k
      fin_cases k <;> assumption
    have hcancel := lps_slice_relative_cancellation hs hu huSvec huQ hv hvQ
    simpa [F, lpsRelativeConvection] using hcancel
  refine ⟨?_, hRall⟩
  have hDens := lps_mixed_cross_density_limits_finite
    hULH hVLH hU hV hs hmix
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
