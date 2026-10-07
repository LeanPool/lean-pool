/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitMain
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitCompactness

/-!
# Leray Limit Assembly Support

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- A uniform slice energy identity bounds the squared spatial integral on
each nonnegative time slice. -/
theorem lerayLimit_lintegral_slice_bound_of_energy
    (F : ParabolicPoint → Vec3) (A : ℝ≥0∞)
    (hSlice : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => F (x,t)) 2 volume)
    (hEnergy : ∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice F t) 2 volume ^ (2 : ℕ) ≤ A ^ (2 : ℕ)) :
    ∀ t : ℝ, 0 ≤ t →
      (∫⁻ x : Vec3, ‖WithLp.toLp 2 (F (x,t))‖ₑ ^ (2 : ℝ) ∂volume) ≤
        A ^ (2 : ℕ) := by
  intro t ht
  have hvectorMem : MemLp
      (fun x : Vec3 => WithLp.toLp 2 (F (x,t))) 2 volume := by
    exact (hSlice t ht).continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hS : MemLp (regUniformVelocitySlice F t) 2 volume := by
    have hcoord : MemLp
        (fun x : L2Vec3 => F (WithLp.ofLp x,t)) 2 volume :=
      (hSlice t ht).comp_measurePreserving
        (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hchange := eLpNorm_comp_measurePreserving
    (p := (2 : ℝ≥0∞)) (f := (WithLp.toLp 2 : Vec3 → L2Vec3))
    hS.aestronglyMeasurable vec3ToL2Vec3_measurePreserving
  have hvector : eLpNorm
      (fun x : Vec3 => WithLp.toLp 2 (F (x,t))) 2 volume =
        eLpNorm (regUniformVelocitySlice F t) 2 volume := by
    have hfun : (fun x : Vec3 => WithLp.toLp 2 (F (x,t))) =
        fun x => regUniformVelocitySlice F t (WithLp.toLp 2 x) := by
      funext x
      simp [regUniformVelocitySlice]
    rw [hfun]
    exact hchange
  have hsq : eLpNorm
      (fun x : Vec3 => WithLp.toLp 2 (F (x,t))) 2 volume ^ (2 : ℝ) ≤
        A ^ (2 : ℝ) := by
    rw [hvector]
    have h := hEnergy t ht
    have hnorm : eLpNorm (regUniformVelocitySlice F t) 2 volume ≤ A :=
      (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h
    exact ENNReal.rpow_le_rpow hnorm (by norm_num)
  have hidentity := lerayLimit_eLpNorm_two_sq_eq_lintegral
    hvectorMem.aestronglyMeasurable
  have hfinal :
      (∫⁻ x : Vec3, ‖WithLp.toLp 2 (F (x,t))‖ₑ ^ (2 : ℝ) ∂volume) ≤
        A ^ (2 : ℝ) := hidentity.symm.trans_le hsq
  calc
    (∫⁻ x : Vec3, ‖WithLp.toLp 2 (F (x,t))‖ₑ ^ (2 : ℝ) ∂volume) ≤
        A ^ (2 : ℝ) := hfinal
    _ = A ^ (2 : ℕ) := ENNReal.rpow_natCast _ 2

/-- A real exterior energy estimate controls the corresponding squared
integral of the Euclidean `L²` representative. -/
theorem lerayLimit_lintegral_spatial_tail_of_real_bound
    (F : Vec3 → Vec3) (E : Set Vec3) (b : ℝ)
    (hF : MemLp F 2 volume)
    (hbound : (∫ x in E, (vec3EuclideanNorm (F x)) ^ (2 : ℕ)
      ∂volume) ≤ b) :
    (∫⁻ x in E, ‖WithLp.toLp 2 (F x)‖ₑ ^ (2 : ℝ) ∂volume) ≤
      ENNReal.ofReal b := by
  let G : Vec3 → L2Vec3 := fun x => WithLp.toLp 2 (F x)
  have hG : MemLp G 2 volume := by
    exact hF.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  let f : Vec3 → ℝ := fun x => (vec3EuclideanNorm (F x)) ^ (2 : ℕ)
  have hf : Integrable f (volume.restrict E) := by
    have hnorm := hG.integrable_norm_pow (by norm_num : 2 ≠ 0)
    have hpoint (x : Vec3) : ‖G x‖ ^ (2 : ℕ) = f x := by
      simp only [G]
      rw [← vec3EuclideanNorm_eq_l2]
    have hEq : (fun x : Vec3 => ‖G x‖ ^ (2 : ℕ)) = f := funext hpoint
    rw [hEq] at hnorm
    exact hnorm.integrableOn
  have hnonneg : ∀ᵐ x ∂(volume.restrict E), 0 ≤ f x :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  have hconvert := ofReal_integral_eq_lintegral_ofReal hf hnonneg
  have hpoint (x : Vec3) :
      ‖G x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (f x) := by
    rw [← ofReal_norm, ← vec3EuclideanNorm_eq_l2]
    calc
      ENNReal.ofReal (vec3EuclideanNorm (F x)) ^ (2 : ℝ) =
          ENNReal.ofReal (vec3EuclideanNorm (F x)) ^ (2 : ℕ) :=
        ENNReal.rpow_natCast _ 2
      _ = ENNReal.ofReal ((vec3EuclideanNorm (F x)) ^ (2 : ℕ)) :=
        (ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 2).symm
      _ = ENNReal.ofReal (f x) := rfl
  have hlintegral :
      (∫⁻ x in E, ‖G x‖ₑ ^ (2 : ℝ) ∂volume) =
        ENNReal.ofReal (∫ x in E, f x ∂volume) := by
    calc
      _ = ∫⁻ x in E, ENNReal.ofReal (f x) ∂volume := by
        apply lintegral_congr
        intro x
        exact hpoint x
      _ = ENNReal.ofReal (∫ x in E, f x ∂volume) := hconvert.symm
  rw [hlintegral]
  exact ENNReal.ofReal_le_ofReal hbound

end CKN.Leray

end
