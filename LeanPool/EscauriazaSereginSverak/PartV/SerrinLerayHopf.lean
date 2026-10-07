/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinUniqueness
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakFromLerayHopf

/-!
# Weak–strong uniqueness for Leray–Hopf solutions

Two Leray–Hopf solutions with the same datum agree almost everywhere on the
slab when one of them lies in space-time `L⁵`: `lem:pv-serrin-uniqueness`. The
comparison uses only the energy inequality of the other solution.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem serrin_eucl_sq (w : Vec3) :
    vec3EuclideanNorm w ^ 2 = ∑ k : Fin 3, w k * w k := by
  rw [vec3EuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun k _ => sq (w k)

theorem serrin_lintegral_eucl_sq {w : Vec3 → Vec3} (hw : MemLp w 2 volume) :
    (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (w x)) ^ (2 : ℝ)) =
      ENNReal.ofReal (∫ x : Vec3, ∑ k : Fin 3, w x k * w x k) := by
  have hint : Integrable (fun x => ∑ k : Fin 3, w x k * w x k) volume :=
    integrable_finsetSum _ fun k _ => (hw.eval k).integrable_mul (hw.eval k)
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x =>
    Finset.sum_nonneg fun k _ => mul_self_nonneg _)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _) (by norm_num), Real.rpow_two,
    serrin_eucl_sq]

/-- The energy inequality of a Leray–Hopf solution in real form, at every time
whose slice is square integrable. -/
theorem lerayHopf_energy_inequality_real {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hut : MemLp (fun x : Vec3 => u (x, t)) 2 volume) :
    (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) ≤
      (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) -
        2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j := by
  have hE := hLH.2.2.2.2.2.2.2.2.2.2.1 t ht
  have ha2 : MemLp a 2 volume := hLH.2.1.1
  have hDu2 := serrinWeak_gradient_memLp_two (serrinWeak_of_lerayHopf hLH).choose_spec
  have hle : (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)) :
      Measure ParabolicPoint) ≤
      volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) := by
    apply Measure.restrict_mono _ le_rfl
    intro z hz
    exact ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 ht.2⟩
  have hGint : Integrable (fun q : ParabolicPoint =>
      ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
      ((((hDu2.eval k).eval j).mono_measure hle).integrable_mul
        (((hDu2.eval k).eval j).mono_measure hle))
  have hG : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
      ENNReal.ofReal (spatialGradientSq u Du z)) =
      ENNReal.ofReal (∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j) := by
    rw [ofReal_integral_eq_lintegral_ofReal hGint (Eventually.of_forall fun q =>
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _)]
    refine lintegral_congr fun q => ?_
    simp only [spatialGradientSq, sq]
  rw [serrin_lintegral_eucl_sq hut, serrin_lintegral_eucl_sq ha2, hG] at hE
  have hP0 : 0 ≤ ∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k :=
    integral_nonneg fun x => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have hA0 : 0 ≤ ∫ x : Vec3, ∑ k : Fin 3, a x k * a x k :=
    integral_nonneg fun x => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have hG0 : 0 ≤ ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
      ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j :=
    integral_nonneg fun q => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ =>
      mul_self_nonneg _
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) hG0,
    ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hE
  linarith only [hE]

/-- Weak–strong uniqueness for Leray–Hopf solutions with the same datum, one of
which lies in space-time `L⁵` (`lem:pv-serrin-uniqueness`). -/
theorem lerayHopf_serrin_uniqueness {T : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3} {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    (hU : IsLerayHopfSolution T a u Du) (hV : IsLerayHopfSolution T a v Dv)
    (hu5 : MemLp u (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    u =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] v := by
  obtain ⟨pu, hUw⟩ := serrinWeak_of_lerayHopf hU
  obtain ⟨pv, hVw⟩ := serrinWeak_of_lerayHopf hV
  have hv103 := (lerayHopf_memLp_tenThirds hV).1
  have hvE : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * v (x, t) k) ≤
        (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) -
          2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv q k j * Dv q k j := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    have hs := (ae_restrict_iff' measurableSet_Ioo).mp (serrinWeak_slices_ae hVw)
    filter_upwards [hs] with t ht htI
    exact lerayHopf_energy_inequality_real hV ⟨htI.1.le, htI.2.le⟩ (ht htI).1
  exact (serrin_weak_strong_uniqueness hUw hVw hu5 hv103 hvE).symm

end ESS
