/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinEnergyEquality
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakFromLerayHopf
public import LeanPool.EscauriazaSereginSverak.LPS.CrossIdentityFour
public import LeanPool.EscauriazaSereginSverak.LPS.SelfTransportFour
public import LeanPool.EscauriazaSereginSverak.LPS.EnergyClassInterpolation

/-!
# Energy equality under the mixed-norm Serrin condition

The zero-start identity is obtained from the mollified cross-testing argument
when the velocity belongs to space-time `L⁴`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_energy_equality_of_memLp_four {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hU : IsSerrinWeakSolution T a u Du p)
    (hu4 : MemLp u (ENNReal.ofReal 4)
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T)))) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j := by
  have hu2 := serrinWeak_velocity_memLp_two hU
  have hDu2 := serrinWeak_gradient_memLp_two hU
  have hcross := lps_cross_identity_four hU hU hu4 hu4
  have hslices := serrinWeak_slice_ae hU
  have hslice4 := serrin_slice_memLp_ae (by simp) (by simp) hu4
  have hzero : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      ∫ y : Vec3,
        (fun q : ParabolicPoint =>
          ∑ k : Fin 3, u q k * ∑ j : Fin 3, u q j * Du q k j) (y, τ) = 0 := by
    filter_upwards [hslices, hslice4] with τ hs h4
    exact lps_slice_self_transport_four hs h4
  have hN (k : Fin 3) := serrin_convection_memLp (r := 4) (s := 4 / 3)
    (by norm_num) (by norm_num) (by norm_num) hu4 hDu2 k
  have hHolder : ENNReal.HolderTriple (ENNReal.ofReal 4) (ENNReal.ofReal (4 / 3)) 1 :=
    serrin_holder_ofReal (by norm_num) (by norm_num) (by norm_num)
  have hFint : Integrable
      (fun q : ParabolicPoint =>
        ∑ k : Fin 3, u q k * ∑ j : Fin 3, u q j * Du q k j)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    refine integrable_finsetSum _ fun k _ => ?_
    exact memLp_one_iff_integrable.mp ((hu4.eval k).mul (r := 1) (hN k))
  rw [ae_restrict_iff' measurableSet_Ioo] at hcross ⊢
  filter_upwards [hcross] with t ht htI
  have hI :
      (∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        ∑ k : Fin 3, u q k * ∑ j : Fin 3, u q j * Du q k j) = 0 :=
    serrin_slab_integral_eq_zero htI.1.le htI.2.le
      (hFint.mono_measure (serrin_slab_restrict_le htI.2.le)) hzero
  rw [ht htI, hI]
  ring

/-- Energy equality from the initial time for almost every positive time under
either Serrin condition in `thm:lps` (`lem:lps-energy-equality`). -/
theorem lps_serrin_energy_equality {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hSerrin :
      (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo (0 : ℝ) T,
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
              ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo (0 : ℝ) T,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j := by
  obtain ⟨_, hU⟩ := serrinWeak_of_lerayHopf hLH
  rcases hSerrin with hFinite | hEndpoint
  · obtain ⟨s, hs, hmix⟩ := hFinite
    exact lps_energy_equality_of_memLp_four hU
      (lps_finite_branch_memLp_four hLH hs hmix)
  · exact lps_energy_equality_of_memLp_four hU
      (lps_endpoint_branch_memLp_four hLH hEndpoint)

end ESS

end
