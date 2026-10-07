/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.PositiveBound
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Positive-time L⁵ integrability

This file proves `lem:pv-positive-l5`: under the critical hypothesis of
`thm:ess-global`, a Leray–Hopf solution lies in L⁵(ℝ³ × (δ, T)) for every
δ > 0. With the essential bound |u| ≤ B of `lem:pv-positive-bound` on the
slab, |u|⁵ ≤ B² |u|³ there, and the critical hypothesis bounds the slab
integral of |u|³ by (T - δ) M³.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Positive-time L⁵ integrability, `lem:pv-positive-l5`. -/
theorem pvPositiveL5
    (hE1 : ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
    ∀ p : ParabolicPoint → ℝ,
      AEStronglyMeasurable u
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      AEStronglyMeasurable Du
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      AEStronglyMeasurable p
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      essSup
        (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict (Ioo (-1) 0)) < ⊤ →
      (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ →
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      essSup
        (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo (-1) 0)) < ⊤ →
      (∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
        HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
          (fun x => u (x, t) i) (fun x => Du (x, t) i)) →
      (∀ ψ : ParabolicPoint → ℝ,
        ψ ∈ spaceTimeTestFunction (V := ℝ)
          (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0) →
      (∀ φ : ParabolicPoint → Vec3,
        φ ∈ spaceTimeTestFunction (V := Vec3)
          (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du z i j * spatialPartial (fun y => φ y i) j z
            - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
            - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0) →
      ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict
            (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))] u ∧
          ParabolicHolderVecOn
            (closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))) w γ)
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hL3 : essSup (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤)
    {δ : ℝ} (hδ : 0 < δ) :
    MemLp u (ENNReal.ofReal (5 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) := by
  obtain ⟨B, hB⟩ := pvPositiveBound hE1 hLH hL3 hδ
  have hJ : Ioo δ T ⊆ Ioo 0 T := Ioo_subset_Ioo_left hδ.le
  have hS : spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := Set.prod_mono subset_rfl hJ
  have hU : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) :=
    hLH.2.2.1.mono_measure (Measure.restrict_mono hS le_rfl)
  let E : ParabolicPoint → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)
  let c : ℝ≥0∞ := ENNReal.ofReal B ^ (2 : ℕ)
  have hEm : AEMeasurable E
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable
        (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
          hU).aemeasurable)
  have hslice : ∀ᵐ t ∂volume.restrict (Ioo δ T),
      ∫⁻ x : Vec3, E (x, t) ≤ essSup (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
          (volume.restrict (Ioo 0 T)) :=
    ae_restrict_of_ae_restrict_of_subset hJ (ae_le_essSup (μ := volume.restrict (Ioo 0 T))
      (f := fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ)))
  have hEfin := pv_setLIntegral_slab_le hEm hslice
  have hpoint : ∀ᵐ z ∂volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)),
      ‖u z‖ₑ ^ (5 : ℝ) ≤ c * E z := by
    filter_upwards [hB] with z hz
    have h1 : ‖u z‖ₑ ≤ ENNReal.ofReal (vec3EuclideanNorm (u z)) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm _)
    calc
      ‖u z‖ₑ ^ (5 : ℝ) ≤ ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (5 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℕ) * E z := by
        rw [show (5 : ℝ) = ((2 : ℕ) : ℝ) + 3 by norm_num,
          ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by norm_num),
          ENNReal.rpow_natCast]
      _ ≤ ENNReal.ofReal B ^ (2 : ℕ) * E z := by
        gcongr
  have hfin : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T),
      ‖u z‖ₑ ^ (5 : ℝ)) < ⊤ := by
    calc
      _ ≤ ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T), c * E z :=
        lintegral_mono_ae hpoint
      _ = c * ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T), E z :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ?_
        refine lt_of_le_of_lt hEfin (ENNReal.mul_lt_top ?_ hL3)
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_lt_top
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num)
    ENNReal.ofReal_ne_top hU,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 5)]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

end ESS
