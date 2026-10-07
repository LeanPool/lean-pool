/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSliceBound

/-!
# Energy equality in the Serrin class

A finite-energy weak solution with pressure that lies in space-time `L⁵`
satisfies the energy equality at almost every time: this is the cross-testing
identity of the solution with itself, whose convection term vanishes. It gives
the strong solution's side of the comparison in `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- An integrable space-time density whose spatial integrals vanish at almost
every time has vanishing integral on every shorter slab. -/
theorem serrin_slab_integral_eq_zero {t T : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    {F : ParabolicPoint → ℝ}
    (hF : Integrable F (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))))
    (hzero : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)), ∫ y : Vec3, F (y, τ) = 0) :
    ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), F q = 0 := by
  rw [← serrin_intervalIntegral_eq_slab ht0 hF]
  have h : ∀ᵐ τ ∂volume, τ ∈ Ι (0 : ℝ) t → (∫ y : Vec3, F (y, τ)) = 0 := by
    have h' := (ae_restrict_iff' measurableSet_Ioo).mp hzero
    filter_upwards [h', Measure.ae_ne volume T] with τ hτ hτT hτI
    rw [uIoc_of_le ht0] at hτI
    exact hτ ⟨hτI.1, lt_of_le_of_ne (hτI.2.trans htT) hτT⟩
  rw [intervalIntegral.integral_congr_ae h]
  simp

/-- The slice facts of a finite-energy weak solution at almost every time. -/
theorem serrinWeak_slice_ae {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hU : IsSerrinWeakSolution T a u Du p) :
    ∀ᵐ s ∂(volume.restrict (Ioo 0 T)),
      SerrinSlice (fun x => u (x, s)) (fun x => Du (x, s)) := by
  filter_upwards [serrinWeak_slices_ae hU] with s ⟨h1, h2, h3, h4, _⟩
  exact ⟨h1, h2, h3, h4⟩

/-- Energy equality at almost every time for a finite-energy weak solution with
pressure in space-time `L⁵`. -/
theorem serrin_energy_equality {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hU : IsSerrinWeakSolution T a u Du p)
    (hu5 : MemLp u (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j := by
  have hu2 := serrinWeak_velocity_memLp_two hU
  have hDu2 := serrinWeak_gradient_memLp_two hU
  have hu103 : MemLp u (ENNReal.ofReal (10 / 3))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    serrin_memLp_interpolate (p := 2) (q := ENNReal.ofReal 5) (by norm_num) (by simp)
      (by rw [← ENNReal.ofReal_ofNat 2]; exact ENNReal.ofReal_le_ofReal (by norm_num))
      (ENNReal.ofReal_le_ofReal (by norm_num)) hu2 hu5
  have hcross := serrin_cross_identity hU hU hu5 hu103
  have hslices := serrinWeak_slice_ae hU
  have hslice5 := serrin_slice_memLp_ae (by simp) (by simp) hu5
  have hzero : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      ∫ y : Vec3, (fun q : ParabolicPoint => ∑ k : Fin 3, u q k * ∑ j : Fin 3, u q j * Du q k j)
        (y, τ) = 0 := by
    filter_upwards [hslices, hslice5] with τ hs h5
    exact serrin_slice_self_transport hs h5
  have hN (k : Fin 3) := serrin_convection_memLp (r := 5) (s := 10 / 7) (by norm_num)
    (by norm_num) (by norm_num) hu5 hDu2 k
  have H : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3)) (ENNReal.ofReal (10 / 7)) 1 :=
    serrin_holder_ofReal (by norm_num) (by norm_num) (by norm_num)
  have hFint : Integrable (fun q : ParabolicPoint => ∑ k : Fin 3, u q k * ∑ j : Fin 3,
      u q j * Du q k j)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    integrable_finsetSum _ fun k _ =>
      memLp_one_iff_integrable.mp ((hu103.eval k).mul (r := 1) (hN k))
  rw [ae_restrict_iff' measurableSet_Ioo] at hcross ⊢
  filter_upwards [hcross] with t ht htI
  have hI : (∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
      ∑ k : Fin 3, u q k * ∑ j : Fin 3, u q j * Du q k j) = 0 :=
    serrin_slab_integral_eq_zero htI.1.le htI.2.le
      (hFint.mono_measure (serrin_slab_restrict_le htI.2.le)) hzero
  rw [ht htI, hI]
  ring

end ESS
