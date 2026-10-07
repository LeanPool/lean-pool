/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.PositiveBoundUnit
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceS2
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceS3S4

/-!
# Rescaled equations on the unit cylinder

Continuing the rescaling step of `lem:pv-positive-bound`: the divergence-free
condition, the momentum identity with pressure, and the L^{3/2} pressure
bound pass from the slab ℝ³ × (0, T) to the rescaled fields on the unit
cylinder B₁ × (-1, 0), for cylinders ending at any time t₀ ≤ T.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem pv_unit_subset_rescaledSet {T t₀ R : ℝ} (x₀ : Vec3) (hR : 0 < R)
    (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T) :
    spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) ⊆
      spaceTimeSet (CKN.rescaledSpace R x₀ (Set.univ : Set Vec3))
        (CKN.rescaledTime R t₀ (Ioo 0 T)) := by
  exact pv_unit_subset_rescaled_slab x₀ hR hlow hup

private theorem pv_rescaledSet_measurable {T t₀ R : ℝ} (x₀ : Vec3) :
    MeasurableSet (spaceTimeSet (CKN.rescaledSpace R x₀ (Set.univ : Set Vec3))
        (CKN.rescaledTime R t₀ (Ioo 0 T))) :=
  MeasurableSet.univ.prod (measurableSet_Ioo.preimage (by
    change Measurable (fun s : ℝ => t₀ + R ^ 2 * s)
    fun_prop))

/-- The rescaled pressure lies in L^{3/2} of the unit cylinder. -/
theorem pv_unit_pressure_memLp {T t₀ R : ℝ} (x₀ : Vec3) (hR : 0 < R)
    (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T) {p : ParabolicPoint → ℝ}
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    MemLp (CKN.rescalePressure R (x₀, t₀) p) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) := by
  have hcomp := ((pv_memLp_comp_scalingParabolic R hR (x₀, t₀) hp).mono_measure
    (Measure.restrict_mono (pv_unit_subset_rescaled_slab x₀ hR hlow hup) le_rfl))
  exact hcomp.const_smul (R ^ 2)

/-- The rescaled velocity is divergence free on the unit cylinder. -/
theorem pv_unit_divergence {T t₀ R : ℝ} (x₀ : Vec3) (hR : 0 < R)
    (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T) {u : ParabolicPoint → Vec3}
    (hS2 : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 T) →
      IntegrableOn (fun z => ∑ i, u z i * spatialPartial ψ i z)
          (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ∑ i, u z i * spatialPartial ψ i z = 0) :
    ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, CKN.rescaleVelocity R (x₀, t₀) u z i * spatialPartial ψ i z = 0 := by
  intro ψ hψ
  have hsub := pv_unit_subset_rescaledSet x₀ hR hlow hup (T := T)
  have hψR : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (CKN.rescaledSpace R x₀ (Set.univ : Set Vec3)) (CKN.rescaledTime R t₀ (Ioo 0 T)) :=
    ⟨hψ.1, hψ.2.1, hψ.2.2.trans hsub⟩
  have hscaled := CKN.s2_rescale MeasurableSet.univ measurableSet_Ioo hS2 (x₀, t₀) hR ψ hψR
  refine Eq.trans ?_ hscaled.2
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (pv_rescaledSet_measurable x₀) hsub
  intro z hz
  have hzψ : z ∉ tsupport (show Vec3 × ℝ → ℝ from ψ) := fun h => hz.2 (hψ.2.2 h)
  have hpartial : ∀ i : Fin 3, spatialPartial ψ i z = 0 := fun i =>
    CKN.spatialPartial_zero_of_not_mem_tsupport_public hψ.1 hzψ i
  simp [hpartial]

/-- The rescaled fields satisfy the momentum identity with the rescaled
pressure on the unit cylinder. -/
theorem pv_unit_momentum {T t₀ R : ℝ} (x₀ : Vec3) (hR : 0 < R)
    (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T) {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hS3 : ∀ φ : Vec3 × ℝ → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
      IntegrableOn (fun z =>
          (-(∑ i, u z i * timePartial (fun w => φ w i) z))
            - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
            + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
            - p z * ∑ i, spatialPartial (fun w => φ w i) i z
            - ∑ i, (0 : ParabolicPoint → Vec3) z i * φ z i) (tsupport φ) volume ∧
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        (-(∑ i, u z i * timePartial (fun w => φ w i) z))
          - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
          - p z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, (0 : ParabolicPoint → Vec3) z i * φ z i = 0) :
    ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, CKN.rescaleVelocity R (x₀, t₀) u z i *
            timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              CKN.rescaleVelocity R (x₀, t₀) u z i *
                CKN.rescaleVelocity R (x₀, t₀) u z j *
                spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              CKN.rescaleGradient R (x₀, t₀) Du z i j *
                spatialPartial (fun y => φ y i) j z
          - CKN.rescalePressure R (x₀, t₀) p z *
              ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0 := by
  intro φ hφ
  have hsub := pv_unit_subset_rescaledSet x₀ hR hlow hup (T := T)
  have hφR : φ ∈ spaceTimeTestFunction (V := Vec3)
      (CKN.rescaledSpace R x₀ (Set.univ : Set Vec3)) (CKN.rescaledTime R t₀ (Ioo 0 T)) :=
    ⟨hφ.1, hφ.2.1, hφ.2.2.trans hsub⟩
  have hscaled := CKN.s3_rescale MeasurableSet.univ measurableSet_Ioo hS3 (x₀, t₀) hR φ hφR
  have hforce : ∀ z : ParabolicPoint, ∀ i : Fin 3,
      CKN.rescaleForce R (x₀, t₀) (0 : ParabolicPoint → Vec3) z i = 0 := by
    intro z i
    simp [CKN.rescaleForce]
  have hzeroR := hscaled.2
  simp only [hforce, zero_mul, Finset.sum_const_zero, sub_zero] at hzeroR
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
  refine Eq.trans ?_ hzeroR
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (pv_rescaledSet_measurable x₀) hsub
  intro z hz
  have hzφ : z ∉ tsupport (show Vec3 × ℝ → Vec3 from φ) := fun h => hz.2 (hφ.2.2 h)
  have hcomp : ∀ i : Fin 3, z ∉ tsupport (fun w : Vec3 × ℝ => φ w i) := by
    intro i h
    exact hzφ ((tsupport_comp_subset (g := fun v : Vec3 => v i) (by simp)
      (show Vec3 × ℝ → Vec3 from φ)) h)
  have hcont : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => φ w i) :=
    fun i => (contDiff_apply ℝ ℝ i).comp hφ.1
  have htime : ∀ i : Fin 3, timePartial (fun w => φ w i) z = 0 := fun i =>
    CKN.timePartial_zero_of_not_mem_tsupport_public (hcont i) (hcomp i)
  have hspace : ∀ i j : Fin 3, spatialPartial (fun w => φ w i) j z = 0 := fun i j =>
    CKN.spatialPartial_zero_of_not_mem_tsupport_public (hcont i) (hcomp i) j
  simp [htime, hspace]

end ESS
