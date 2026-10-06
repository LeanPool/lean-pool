/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.MixedCrossDensityLimit
public import LeanPool.EscauriazaSereginSverak.LPS.MixedConvectionMoment
public import LeanPool.EscauriazaSereginSverak.LPS.MixedCrossFiniteData
public import LeanPool.CaffarelliKohnNirenberg.Leray.TenThirds
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.SerrinPairingLimit
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSlab

/-!
# Finite Serrin cross-density limits

The energy interpolation and the Serrin mixed norm provide the two oriented
convection pairings needed for the finite-exponent cross identity.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Both oriented cross densities have the required finite-exponent
integrability and cutoff-mollification limits. The first product is the
distinguished velocity against the rival's advective convection. -/
theorem lps_mixed_cross_density_limits_finite
    {T : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ} {s : ℝ}
    (hULH : IsLerayHopfSolution T a u Du)
    (hVLH : IsLerayHopfSolution T a v Dv)
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T a v Dv pv)
    (hs : 3 < s)
    (hmix : (∫⁻ t in Ioo 0 T,
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
          ((2 * s / (s - 3)) / s)) < ⊤) :
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
  have hell0 : 0 < ell := by dsimp [ell]; positivity
  have hell1 : 1 ≤ ell := by
    dsimp [ell]
    rw [le_div_iff₀ hs3]
    linarith only [hs]
  have hqE0 : 0 < qE := by dsimp [qE]; positivity
  have hpE0 : 0 < pE := by dsimp [pE]; positivity
  have hqN0 : 0 < qN := by dsimp [qN]; positivity
  have hpN0 : 0 < pN := by dsimp [pN]; positivity
  have hqNS0 : 0 < qNS := by dsimp [qNS]; positivity
  have hpNS0 : 0 < pNS := by dsimp [pNS]; positivity
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
    lps_real_holder_pair hs0 hqN0 hZVspace
  have hHolderZVtime : ell.HolderConjugate pN :=
    lps_real_holder_pair hell0 hpN0 hZVtime
  have hHolderUVspace : qE.HolderConjugate qNS :=
    lps_real_holder_pair hqE0 hqNS0 hUVspace
  have hHolderUVtime : pE.HolderConjugate pNS :=
    lps_real_holder_pair hpE0 hpNS0 hUVtime
  have hUserrin := lps_finite_coordinate_mixed_data hU hs hmix
  have hUenergy := lps_energy_coordinate_mixed_data hULH hU hs
  have hVenergy := lps_energy_coordinate_mixed_data hVLH hV hs
  have hDU2 := serrinWeak_gradient_memLp_two hU
  have hDV2 := serrinWeak_gradient_memLp_two hV
  have hConvV := lps_mixed_convection_moment hqE1 hpE1 hqN1 hpN1
    hSpaceE hTimeE hV.meas_u hV.meas_Du
    (fun j => (hVenergy j).1) (fun j => (hVenergy j).2) hDV2
  have hConvU := lps_mixed_convection_moment (by linarith only [hs]) hell1
      hqNS1 hpNS1 hSpaceS hTimeS hU.meas_u hU.meas_Du
    (fun j => (hUserrin j).1) (fun j => (hUserrin j).2) hDU2
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
  have hDensityVU : ∀ t, t ∈ Ioo (0 : ℝ) T →
      (∀ᶠ n in atTop, Integrable
        (serrinCrossDensity v Dv pv u Du n (serrinCutoff n))
        (volume.restrict (spaceTimeSet Set.univ (Ioo 0 t)))) ∧
      Tendsto (fun n => ∫ q in spaceTimeSet Set.univ (Ioo 0 t),
        serrinCrossDensity v Dv pv u Du n (serrinCutoff n) q) atTop
        (𝓝 (-(∫ q in spaceTimeSet Set.univ (Ioo 0 t),
            ∑ k : Fin 3, u q k * ∑ j : Fin 3, v q j * Dv q k j)
          - ∫ q in spaceTimeSet Set.univ (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Dv q k j)) := by
    intro t ht
    apply lps_mixed_cross_density_limit ht.2.le
      (by linarith only [hs]) hqN1 hell1 hpN1 hHolderZVspace hHolderZVtime
      (fun k => lps_coordinate_aesm hU.meas_u k)
      (fun k => by
        refine Finset.univ.aestronglyMeasurable_fun_sum ?_
        intro j _
        exact (lps_coordinate_aesm hV.meas_u j).mul
          (lps_gradient_entry_aesm hV.meas_Du k j))
      (fun k => (hUserrin k).1)
      (fun k => (hConvV k).1)
      (fun k => (hUserrin k).2)
      (fun k => (hConvV k).2)
      (fun k j => (hDU2.eval k).eval j)
      (fun k j => (hDV2.eval k).eval j)
      (fun k => (hU2.eval k))
      (fun k => (hU52.eval k)) hV.pressure
  have hDensityUV : ∀ t, t ∈ Ioo (0 : ℝ) T →
      (∀ᶠ n in atTop, Integrable
        (serrinCrossDensity u Du pu v Dv n (serrinCutoff n))
        (volume.restrict (spaceTimeSet Set.univ (Ioo 0 t)))) ∧
      Tendsto (fun n => ∫ q in spaceTimeSet Set.univ (Ioo 0 t),
        serrinCrossDensity u Du pu v Dv n (serrinCutoff n) q) atTop
        (𝓝 (-(∫ q in spaceTimeSet Set.univ (Ioo 0 t),
            ∑ k : Fin 3, v q k * ∑ j : Fin 3, u q j * Du q k j)
          - ∫ q in spaceTimeSet Set.univ (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv q k j * Du q k j)) := by
    intro t ht
    apply lps_mixed_cross_density_limit ht.2.le
      hqE1 hqNS1 hpE1 hpNS1 hHolderUVspace hHolderUVtime
      (fun k => lps_coordinate_aesm hV.meas_u k)
      (fun k => by
        refine Finset.univ.aestronglyMeasurable_fun_sum ?_
        intro j _
        exact (lps_coordinate_aesm hU.meas_u j).mul
          (lps_gradient_entry_aesm hU.meas_Du k j))
      (fun k => (hVenergy k).1)
      (fun k => (hConvU k).1)
      (fun k => (hVenergy k).2)
      (fun k => (hConvU k).2)
      (fun k j => (hDV2.eval k).eval j)
      (fun k j => (hDU2.eval k).eval j)
      (fun k => hV2.eval k)
      (fun k => hV52.eval k) hU.pressure
  exact ⟨hDensityVU, hDensityUV⟩

end ESS

end
