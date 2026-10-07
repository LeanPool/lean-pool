/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformConvolution
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Foundation.RellichBalls
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Component bounds for the regularized convolution

The finite-dimensional coordinate decomposition transfers scalar slice
estimates through the vector-valued mollifier.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem regUniform_toLp_eLpNorm_le_sum
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u : Vec3 → Vec3}
    (hvec : AEStronglyMeasurable
      (fun x : Vec3 => WithLp.toLp 2 (u x)) volume)
    (hu : ∀ i : Fin 3, AEStronglyMeasurable (fun x : Vec3 => u x i) volume) :
    eLpNorm (fun x : Vec3 => WithLp.toLp 2 (u x)) p volume ≤
      ∑ i : Fin 3, eLpNorm (fun x : Vec3 => u x i) p volume := by
  have hpoint (x : Vec3) :
    ‖WithLp.toLp 2 (u x)‖ ≤ ∑ i : Fin 3, |u x i| := by
    calc
      ‖WithLp.toLp 2 (u x)‖ = vec3EuclideanNorm (u x) :=
        (vec3EuclideanNorm_eq_l2 (u x)).symm
      _ ≤ ∑ i : Fin 3, |u x i| := vec3EuclideanNorm_le_sum_abs (u x)
  calc
    eLpNorm (fun x : Vec3 => WithLp.toLp 2 (u x)) p volume ≤
          eLpNorm (fun x => ∑ i : Fin 3, |u x i|) p volume := by
          apply eLpNorm_mono_ae_real hvec
          exact Filter.Eventually.of_forall hpoint
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x : Vec3 => |u x i|) p volume :=
      eLpNorm_sum_le (p := p) (s := (Finset.univ : Finset (Fin 3)))
        (f := fun i => fun x : Vec3 => |u x i|) hp
    _ = ∑ i : Fin 3, eLpNorm (fun x : Vec3 => u x i) p volume := by
      apply Finset.sum_congr rfl
      intro i hi
      exact eLpNorm_norm _ (hu i)

/-- Convolution by the regularizing profile does not increase a scalar
component's `L^p` norm beyond the sum of the input component norms. -/
theorem regMollifyVector_component_eLpNorm_le_sum
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {u : Vec3 → Vec3} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hu₂ : MemLp u 2 volume)
    (hup : ∀ j : Fin 3, MemLp (fun x : Vec3 => u x j) p volume)
    (i : Fin 3) :
    eLpNorm (fun x : Vec3 =>
      (WithLp.ofLp (regMollifyVector ρ ε hε
        (regUniformSpatialField u) (WithLp.toLp 2 x))) i) p volume ≤
      ∑ j : Fin 3, eLpNorm (fun x : Vec3 => u x j) p volume := by
  let f := regUniformSpatialField u
  have h₂ : MemLp f 2 volume := by
    have hcoord : MemLp (fun x : L2Vec3 => u (WithLp.ofLp x)) 2 volume :=
      hu₂.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hupVec : MemLp u p volume := memLp_pi_iff.mpr hup
  have hvec : AEStronglyMeasurable
      (fun x : Vec3 => WithLp.toLp 2 (u x)) volume :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp_aestronglyMeasurable
      hupVec.aestronglyMeasurable
  have hinput := regUniform_toLp_eLpNorm_le_sum hp hvec
    (fun j => (hup j).aestronglyMeasurable)
  have hcontract := regMollifyVector_eLpNorm_le ρ ε hε h₂ hp hpTop
  have houtput : AEStronglyMeasurable
      (fun x : Vec3 => regMollifyVector ρ ε hε f (WithLp.toLp 2 x)) volume := by
    exact (regMollifyVector_aestronglyMeasurable ρ ε hε h₂).comp_measurePreserving
      vec3ToL2Vec3_measurePreserving
  let coordEquiv := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hcomponent : AEStronglyMeasurable
      (fun x : Vec3 =>
        (WithLp.ofLp (regMollifyVector ρ ε hε f (WithLp.toLp 2 x))) i) volume := by
    have hraw : AEStronglyMeasurable
        (fun x : Vec3 => coordEquiv (regMollifyVector ρ ε hε f (WithLp.toLp 2 x)))
        volume := coordEquiv.continuous.comp_aestronglyMeasurable houtput
    exact (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hraw
  calc
    eLpNorm (fun x : Vec3 =>
        (WithLp.ofLp (regMollifyVector ρ ε hε f (WithLp.toLp 2 x))) i) p volume ≤
      eLpNorm (fun x : Vec3 => regMollifyVector ρ ε hε f (WithLp.toLp 2 x)) p volume := by
        apply eLpNorm_mono_enorm_ae hcomponent
        filter_upwards [] with x
        rw [← ofReal_norm, ← ofReal_norm]
        let v := regMollifyVector ρ ε hε f (WithLp.toLp 2 x)
        have hEuclidean (v : L2Vec3) : vec3EuclideanNorm (WithLp.ofLp v) = ‖v‖ := by
          rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_ofLp]
        have hreal : ‖(WithLp.ofLp v) i‖ ≤ ‖v‖ := by
          calc
            ‖(WithLp.ofLp v) i‖ ≤ ‖WithLp.ofLp v‖ :=
              norm_le_pi_norm (WithLp.ofLp v) i
            _ ≤ vec3EuclideanNorm (WithLp.ofLp v) :=
              CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm _
            _ = ‖v‖ := hEuclidean v
        exact ENNReal.ofReal_le_ofReal hreal
    _ = eLpNorm (regMollifyVector ρ ε hε f) p volume := by
      exact eLpNorm_comp_measurePreserving
        (regMollifyVector_aestronglyMeasurable ρ ε hε h₂)
        vec3ToL2Vec3_measurePreserving
    _ ≤ eLpNorm (regUniformL2VectorNormOnVec3 f) p volume := hcontract
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x : Vec3 => u x j) p volume := by
      change eLpNorm (fun x : Vec3 => ‖WithLp.toLp 2 (u x)‖) p volume ≤ _
      rw [eLpNorm_norm (fun x : Vec3 => WithLp.toLp 2 (u x)) hvec]
      exact hinput

end CKN.Leray

end
