/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationMatch
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationConcatAux

/-!
# The energy equality at the restart time

The energy equality of a Leray–Hopf solution at a good time, in the extended-real
form of the Leray–Hopf energy inequality, and its propagation along a strong
continuation (`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The real form of the energy equality at a good time, as the extended-real form of
the Leray–Hopf energy inequality with equality. -/
theorem lps_lh_energy_ennreal {T t₀ : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} (hLH : IsLerayHopfSolution T a u Du)
    (ht₀ : t₀ ∈ Ioo 0 T) (hm : MemLp (fun x : Vec3 => u (x, t₀)) 2 volume)
    (hreal : (∫ x : Vec3, ∑ k : Fin 3, u (x, t₀) k * u (x, t₀) k) -
        (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
      -2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
        ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j) :
    ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ)) +
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
        ENNReal.ofReal (spatialGradientSq u Du z)) =
      ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ) := by
  have hsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :=
    fun z hz => ⟨hz.1, hz.2.1, lt_trans hz.2.2 ht₀.2⟩
  have hDt : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀))) :=
    (lps_lh_memLp_slab hLH).2.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hDint : Integrable (fun q : ParabolicPoint => ∑ k : Fin 3, ∑ j : Fin 3,
      Du q k j * Du q k j)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀))) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
      (memLp_pi_iff.1 (memLp_pi_iff.1 hDt k) j).integrable_mul
        (memLp_pi_iff.1 (memLp_pi_iff.1 hDt k) j)
  have hgrad : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
      ENNReal.ofReal (spatialGradientSq u Du z)) =
      ENNReal.ofReal (∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
        ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j) := by
    rw [ofReal_integral_eq_lintegral_ofReal hDint (Eventually.of_forall fun q =>
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _)]
    refine lintegral_congr fun q => ?_
    simp only [spatialGradientSq, pow_two]
  have hD0 : 0 ≤ ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
      ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j :=
    integral_nonneg fun q => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ =>
      mul_self_nonneg _
  have hU0 : 0 ≤ ∫ x : Vec3, ∑ k : Fin 3, u (x, t₀) k * u (x, t₀) k :=
    integral_nonneg fun x => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  rw [serrin_lintegral_eucl_sq hm, serrin_lintegral_eucl_sq hLH.2.1.1, hgrad,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hU0) hD0,
    ← ENNReal.ofReal_mul (by norm_num)]
  refine congrArg ENNReal.ofReal ?_
  linarith only [hreal]

/-- The energy equality of a Leray–Hopf solution at the end time of a strong
solution that agrees with it, in the extended-real form
(`lem:lps-continuation`). -/
theorem lps_restart_energy {T t₀ t₁ : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {U W : ParabolicPoint → Vec3}
    {DU : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hLH : IsLerayHopfSolution T a u Du) (hU : IsLpsStrongSolution t₀ t₁ U DU p)
    (ht₀ : 0 < t₀) (ht₁ : t₁ ≤ T)
    (hae : U =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))] u)
    (hU0 : (fun x : Vec3 => U (x, t₀)) =ᵐ[volume] (fun x : Vec3 => u (x, t₀)))
    (hEq₀ : ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ)) +
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
        ENNReal.ofReal (spatialGradientSq u Du z)) =
      ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ))
    (hW0 : (fun x : Vec3 => W (x, t₁)) =ᵐ[volume] (fun x : Vec3 => U (x, t₁))) :
    ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (W (x, t₁))) ^ (2 : ℝ)) +
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₁),
        ENNReal.ofReal (spatialGradientSq u Du z)) =
      ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ) := by
  have hgrad := lps_strong_gradient_ae_eq_slab hLH hU ht₀.le ht₁ hae
  have hUe := lps_strong_energy_ennreal hU (t := t₁) ⟨hU.1.le, le_rfl⟩
  have hGU : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁),
      ENNReal.ofReal (spatialGradientSq U DU z)) =
      ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁),
        ENNReal.ofReal (spatialGradientSq u Du z) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hgrad] with z hz
    simp only [spatialGradientSq, hz]
  have EW : (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (W (x, t₁))) ^ (2 : ℝ)) =
      ∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (U (x, t₁))) ^ (2 : ℝ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hW0] with x hx
    rw [hx]
  have EU0 : (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (U (x, t₀))) ^ (2 : ℝ)) =
      ∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hU0] with x hx
    rw [hx]
  have hsplit := lps_lintegral_slab_split ht₀.le hU.1.le
    (fun z => ENNReal.ofReal (spatialGradientSq u Du z)) (a := 0) (c := t₁)
  rw [EW, hsplit, ← hGU]
  calc ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (U (x, t₁))) ^ (2 : ℝ)) +
      ((∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
        ENNReal.ofReal (spatialGradientSq u Du z)) +
        ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁),
          ENNReal.ofReal (spatialGradientSq U DU z))
      = (ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (U (x, t₁))) ^ (2 : ℝ)) +
        ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁),
          ENNReal.ofReal (spatialGradientSq U DU z)) +
        ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
          ENNReal.ofReal (spatialGradientSq u Du z) := by ring
    _ = _ := by rw [hUe, EU0, hEq₀]

end ESS

end
