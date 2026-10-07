/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformConvolution
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureLp
public import Mathlib.MeasureTheory.Function.Holder
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# The positive-time `L²` pressure estimate for regularized solutions

The slice pressure is the double Riesz transform of the regularized tensor.
This file bounds that pressure class by the two spatial `L⁴` norms in
`lem:reg-pressure-L2`.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The tensor in the Riesz pressure formula for a regularized velocity. -/
@[expose]
def regPressureTensorSlice (ρ : RegMollifierProfile) (ε : ℝ)
    (hε : 0 < ε) (u : ParabolicPoint → Vec3) (t : ℝ)
    (i j : Fin 3) (x : Vec3) : ℝ :=
  regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j

private theorem regPressure_velocity_memLp_four
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hU2 : MemLp (regUniformVelocitySlice u t) (2 : ℝ≥0∞) volume)
    (hUbdd : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Vec3,
      vec3EuclideanNorm (u (x, t)) ≤ B) :
    MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
      (ENNReal.ofReal (4 : ℝ)) volume := by
  have hLift : MemLp (fun x : Vec3 => WithLp.toLp 2 (u (x, t)))
      (2 : ℝ≥0∞) volume := by
    have hcomp := hU2.comp_measurePreserving vec3ToL2Vec3_measurePreserving
    change MemLp (fun x : Vec3 => WithLp.toLp 2 (u (x, t)))
      (2 : ℝ≥0∞) volume at hcomp
    exact hcomp
  have hNorm2 : MemLp (fun x : Vec3 => ‖WithLp.toLp 2 (u (x, t))‖)
      (2 : ℝ≥0∞) volume := hLift.norm
  obtain ⟨B, hB, hbound⟩ := hUbdd
  have hNormTop : MemLp (fun x : Vec3 => ‖WithLp.toLp 2 (u (x, t))‖)
      ⊤ volume := by
    apply memLp_top_of_bound hNorm2.aestronglyMeasurable B
    filter_upwards [] with x
    simpa only [norm_norm] using
      (calc
        ‖WithLp.toLp 2 (u (x, t))‖ = vec3EuclideanNorm (u (x, t)) :=
          (vec3EuclideanNorm_eq_l2 (u (x, t))).symm
        _ ≤ B := hbound x)
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) ⊤ 2 := inferInstance
  have hProduct : MemLp
      (fun x : Vec3 => ‖WithLp.toLp 2 (u (x, t))‖ *
        ‖WithLp.toLp 2 (u (x, t))‖) (2 : ℝ≥0∞) volume :=
    hNorm2.mul hNormTop
  have hSquare : MemLp
      (fun x : Vec3 => ‖WithLp.toLp 2 (u (x, t))‖ ^ (2 : ℝ))
      (2 : ℝ≥0∞) volume := by
    apply (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).2 hProduct
    rw [Real.rpow_two, pow_two]
  have hLift4 : MemLp (fun x : Vec3 => WithLp.toLp 2 (u (x, t)))
      (ENNReal.ofReal (4 : ℝ)) volume := by
    apply (memLp_norm_rpow_iff (q := (2 : ℝ≥0∞)) hLift.aestronglyMeasurable
      (by norm_num) (by norm_num)).1
    have hExponent : ENNReal.ofReal (4 : ℝ) / 2 = 2 := by
      have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
      have hreal : (4 : ℝ) / 2 = 2 := by norm_num
      calc
        ENNReal.ofReal (4 : ℝ) / 2 =
            ENNReal.ofReal (4 : ℝ) / ENNReal.ofReal (2 : ℝ) := by rw [htwo]
        _ = ENNReal.ofReal ((4 : ℝ) / 2) :=
          (ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)).symm
        _ = 2 := by rw [hreal]; norm_num
    rw [hExponent]
    exact hSquare
  have hNorm4 : MemLp (fun x : Vec3 => ‖WithLp.toLp 2 (u (x, t))‖)
      (ENNReal.ofReal (4 : ℝ)) volume := hLift4.norm
  have hEuclidean : (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) =
      fun x => ‖WithLp.toLp 2 (u (x, t))‖ := by
    funext x
    exact vec3EuclideanNorm_eq_l2 (u (x, t))
  exact (memLp_congr_ae (Filter.Eventually.of_forall fun x =>
    congrFun hEuclidean x)).2 hNorm4

private theorem regPressure_velocity_component_memLp_four
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hU2 : MemLp (regUniformVelocitySlice u t) (2 : ℝ≥0∞) volume)
    (hU4 : MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
      (ENNReal.ofReal (4 : ℝ)) volume)
    (i : Fin 3) :
    MemLp (fun x : Vec3 => u (x, t) i)
      (ENNReal.ofReal (4 : ℝ)) volume := by
  apply hU4.of_le
  · have hLift : AEStronglyMeasurable
        (fun x : Vec3 => WithLp.toLp 2 (u (x, t))) volume :=
      (hU2.comp_measurePreserving vec3ToL2Vec3_measurePreserving).aestronglyMeasurable
    have hU : AEStronglyMeasurable (fun x : Vec3 => u (x, t)) volume := by
      have hcoords :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous.comp_aestronglyMeasurable
          hLift
      simpa only [PiLp.coe_continuousLinearEquiv, WithLp.ofLp_toLp] using hcoords
    exact (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hU
  · filter_upwards [] with x
    calc
      ‖u (x, t) i‖ = |u (x, t) i| := Real.norm_eq_abs _
      _ ≤ vec3EuclideanNorm (u (x, t)) := abs_apply_le_vec3EuclideanNorm _ _
      _ = ‖vec3EuclideanNorm (u (x, t))‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]

private theorem regPressure_mollified_velocity_memLp_four
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hU2 : MemLp (regUniformVelocitySlice u t) (2 : ℝ≥0∞) volume)
    (hU4 : MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
      (ENNReal.ofReal (4 : ℝ)) volume) :
    MemLp (fun x : Vec3 => vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε u (x, t)))
      (ENNReal.ofReal (4 : ℝ)) volume := by
  let f : Vec3 → Vec3 := fun x => u (x, t)
  have hf₂ : MemLp (regUniformSpatialField f) (2 : ℝ≥0∞) volume := by
    change MemLp (regUniformVelocitySlice u t) (2 : ℝ≥0∞) volume
    exact hU2
  have hcontract := regMollifyVector_eLpNorm_le
    ρ ε hε hf₂
    (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (4 : ℝ))
    (by norm_num : ENNReal.ofReal (4 : ℝ) ≠ ⊤)
  have hinput : eLpNorm (regUniformL2VectorNormOnVec3
      (regUniformSpatialField f)) (ENNReal.ofReal (4 : ℝ)) volume =
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume := by
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simpa [regUniformL2VectorNormOnVec3, regUniformSpatialField, f] using
      (vec3EuclideanNorm_eq_l2 (u (x, t))).symm
  have hcontract' : eLpNorm
      (fun x : Vec3 => vec3EuclideanNorm
        (regUniformMollifiedVelocity ρ ε hε u (x, t)))
      (ENNReal.ofReal (4 : ℝ)) volume ≤
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume := by
    have hraw : AEStronglyMeasurable
        (regMollifyVector ρ ε hε (regUniformSpatialField f)) volume :=
      regMollifyVector_aestronglyMeasurable ρ ε hε hf₂
    have hcomp := hraw.comp_measurePreserving vec3ToL2Vec3_measurePreserving
    have hcoerce : (fun x : Vec3 => vec3EuclideanNorm
        (regUniformMollifiedVelocity ρ ε hε u (x, t))) =
        fun x => ‖regMollifyVector ρ ε hε (regUniformSpatialField f)
          (WithLp.toLp 2 x)‖ := by
      funext x
      change vec3EuclideanNorm (WithLp.ofLp (regMollifyVector ρ ε hε
        (regUniformVelocitySlice u t) (WithLp.toLp 2 x))) =
        ‖regMollifyVector ρ ε hε (regUniformSpatialField f) (WithLp.toLp 2 x)‖
      rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_ofLp]
      rfl
    calc
      _ = eLpNorm (fun x : Vec3 => ‖regMollifyVector ρ ε hε
            (regUniformSpatialField f) (WithLp.toLp 2 x)‖)
            (ENNReal.ofReal (4 : ℝ)) volume := by
        exact eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => congrFun hcoerce x)
      _ = eLpNorm (fun x : Vec3 => regMollifyVector ρ ε hε
            (regUniformSpatialField f) (WithLp.toLp 2 x))
            (ENNReal.ofReal (4 : ℝ)) volume := eLpNorm_norm _ hcomp
      _ = eLpNorm (regMollifyVector ρ ε hε
            (regUniformSpatialField f)) (ENNReal.ofReal (4 : ℝ)) volume :=
        eLpNorm_comp_measurePreserving hraw vec3ToL2Vec3_measurePreserving
      _ ≤ eLpNorm (regUniformL2VectorNormOnVec3
            (regUniformSpatialField f)) (ENNReal.ofReal (4 : ℝ)) volume := hcontract
      _ = eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
            (ENNReal.ofReal (4 : ℝ)) volume := hinput
  rw [memLp_iff]
  have hfinite : eLpNorm
      (fun x : Vec3 => vec3EuclideanNorm
        (regUniformMollifiedVelocity ρ ε hε u (x, t)))
      (ENNReal.ofReal (4 : ℝ)) volume < ⊤ := by
    exact hcontract'.trans_lt hU4.eLpNorm_lt_top
  exact hfinite

private theorem regPressure_mollified_velocity_component_memLp_four
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hU2 : MemLp (regUniformVelocitySlice u t) (2 : ℝ≥0∞) volume)
    (hJu4 : MemLp (fun x : Vec3 => vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε u (x, t)))
      (ENNReal.ofReal (4 : ℝ)) volume) (i : Fin 3) :
    MemLp (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i)
      (ENNReal.ofReal (4 : ℝ)) volume := by
  apply hJu4.of_le
  · have hraw := regMollifyVector_aestronglyMeasurable ρ ε hε hU2
    have hcomp := hraw.comp_measurePreserving vec3ToL2Vec3_measurePreserving
    have hcoords :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous.comp_aestronglyMeasurable
        hcomp
    have hJu : AEStronglyMeasurable
        (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t)) volume := by
      simpa only [PiLp.coe_continuousLinearEquiv, regUniformMollifiedVelocity,
        Function.comp_apply] using hcoords
    exact (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hJu
  · filter_upwards [] with x
    calc
      ‖regUniformMollifiedVelocity ρ ε hε u (x, t) i‖ =
          |regUniformMollifiedVelocity ρ ε hε u (x, t) i| := Real.norm_eq_abs _
      _ ≤ vec3EuclideanNorm (regUniformMollifiedVelocity ρ ε hε u (x, t)) :=
        abs_apply_le_vec3EuclideanNorm _ _
      _ = ‖vec3EuclideanNorm (regUniformMollifiedVelocity ρ ε hε u (x, t))‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]

private theorem regPressure_tensor_component_memLp_two
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hU2 : MemLp (regUniformVelocitySlice u t) (2 : ℝ≥0∞) volume)
    (hUbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Vec3,
      vec3EuclideanNorm (u (x, t)) ≤ B)
    (i j : Fin 3) :
    MemLp (regPressureTensorSlice ρ ε hε u t i j)
      (ENNReal.ofReal (2 : ℝ)) volume := by
  let f : Vec3 → Vec3 := fun x => u (x, t)
  let g : Vec3 → Vec3 := fun x => regUniformMollifiedVelocity ρ ε hε u (x, t)
  have hU4 := regPressure_velocity_memLp_four u t hU2 hUbound
  have hJu4 := regPressure_mollified_velocity_memLp_four ρ ε hε u t hU2 hU4
  have hUi4 := regPressure_velocity_component_memLp_four u t hU2 hU4 j
  have hJUi4 := regPressure_mollified_velocity_component_memLp_four
    ρ ε hε u t hU2 hJu4 i
  let : ENNReal.HolderTriple (ENNReal.ofReal (4 : ℝ))
      (ENNReal.ofReal (4 : ℝ)) (ENNReal.ofReal (2 : ℝ)) := by
    refine ⟨?_⟩
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    norm_num
  change MemLp (fun x : Vec3 => g x i * f x j)
    (ENNReal.ofReal (2 : ℝ)) volume
  exact hJUi4.mul hUi4

/-- The positive-time Riesz pressure is bounded in `L²` by the two `L⁴`
norms in `lem:reg-pressure-L2`. The pressure binder is exactly the (R4)
slice identity in the `L²` realization of the double Riesz transform. -/
theorem regPressure_slice_L2_bound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3)
    (P : ℝ → Lp ℝ (ENNReal.ofReal (2 : ℝ)) (volume : Measure Vec3))
    (hU2 : ∀ t, 0 ≤ t →
      MemLp (regUniformVelocitySlice u t) (2 : ℝ≥0∞) volume)
    (hUbound : ∀ t, 0 < t → ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Vec3,
      vec3EuclideanNorm (u (x, t)) ≤ B)
    (hR4 : ∀ t, 0 < t → ∃ F : PressureTensorLp (2 : ℝ),
      (∀ i j, (F i j : Vec3 → ℝ) =ᵐ[volume]
        regPressureTensorSlice ρ ε hε u t i j) ∧
      P t = rieszPressureSlice (2 : ℝ) (by norm_num) F) :
    ∀ t, 0 < t →
      ‖P t‖ ≤ 9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
        (eLpNorm (fun x : Vec3 => vec3EuclideanNorm
          (regUniformMollifiedVelocity ρ ε hε u (x, t)))
          (ENNReal.ofReal (4 : ℝ)) volume).toReal *
        (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
          (ENNReal.ofReal (4 : ℝ)) volume).toReal := by
  intro t ht
  have hU2t := hU2 t (le_of_lt ht)
  obtain ⟨B, hB, hbound⟩ := hUbound t ht
  have hFmem : ∀ i j, MemLp (regPressureTensorSlice ρ ε hε u t i j)
      (ENNReal.ofReal (2 : ℝ)) volume := by
    intro i j
    exact regPressure_tensor_component_memLp_two ρ ε hε u t hU2t
      ⟨B, hB, hbound⟩ i j
  obtain ⟨F, hFae, hPeq⟩ := hR4 t ht
  have hFclass (i j : Fin 3) :
      F i j = (hFmem i j).toLp (regPressureTensorSlice ρ ε hε u t i j) := by
    apply Lp.ext
    filter_upwards [hFae i j, (hFmem i j).coeFn_toLp] with x h₁ h₂
    exact h₁.trans h₂.symm
  have hU4 := regPressure_velocity_memLp_four u t hU2t ⟨B, hB, hbound⟩
  have hJu4 := regPressure_mollified_velocity_memLp_four ρ ε hε u t hU2t hU4
  have hFnorm : ∀ i j, ‖F i j‖ ≤
      (eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        (regUniformMollifiedVelocity ρ ε hε u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume).toReal *
      (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume).toReal := by
    intro i j
    have hJu : AEStronglyMeasurable
        (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t)) volume := by
      have hraw := regMollifyVector_aestronglyMeasurable ρ ε hε hU2t
      have hcomp := hraw.comp_measurePreserving vec3ToL2Vec3_measurePreserving
      have hcoords :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous.comp_aestronglyMeasurable
          hcomp
      simpa only [PiLp.coe_continuousLinearEquiv, regUniformMollifiedVelocity,
        Function.comp_apply] using hcoords
    have hU : AEStronglyMeasurable (fun x : Vec3 => u (x, t)) volume := by
      have hLift :=
        (hU2t.comp_measurePreserving vec3ToL2Vec3_measurePreserving).aestronglyMeasurable
      have hcoords :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous.comp_aestronglyMeasurable
          hLift
      simpa only [PiLp.coe_continuousLinearEquiv, regUniformVelocitySlice,
        WithLp.ofLp_toLp, Function.comp_apply] using hcoords
    have hJcomponent (x : Vec3) :
        ‖regUniformMollifiedVelocity ρ ε hε u (x, t) i‖ ≤
          vec3EuclideanNorm (regUniformMollifiedVelocity ρ ε hε u (x, t)) := by
      calc
        ‖regUniformMollifiedVelocity ρ ε hε u (x, t) i‖ =
            |regUniformMollifiedVelocity ρ ε hε u (x, t) i| := Real.norm_eq_abs _
        _ ≤ vec3EuclideanNorm (regUniformMollifiedVelocity ρ ε hε u (x, t)) :=
          abs_apply_le_vec3EuclideanNorm _ _
    have hUcomponent (x : Vec3) : ‖u (x, t) j‖ ≤
        vec3EuclideanNorm (u (x, t)) := by
      calc
        ‖u (x, t) j‖ = |u (x, t) j| := Real.norm_eq_abs _
        _ ≤ vec3EuclideanNorm (u (x, t)) := abs_apply_le_vec3EuclideanNorm _ _
    let : ENNReal.HolderTriple (ENNReal.ofReal (4 : ℝ))
        (ENNReal.ofReal (4 : ℝ)) (ENNReal.ofReal (2 : ℝ)) := by
      refine ⟨?_⟩
      rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
        ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num
    have hHolder : eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        (regUniformMollifiedVelocity ρ ε hε u (x, t)) *
        vec3EuclideanNorm (u (x, t))) (ENNReal.ofReal (2 : ℝ)) volume ≤
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm
          (regUniformMollifiedVelocity ρ ε hε u (x, t)))
          (ENNReal.ofReal (4 : ℝ)) volume *
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
          (ENNReal.ofReal (4 : ℝ)) volume := by
      have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (p := ENNReal.ofReal (4 : ℝ)) (q := ENNReal.ofReal (4 : ℝ))
        (r := ENNReal.ofReal (2 : ℝ)) (b := fun a b : ℝ => a * b)
        (c := (1 : NNReal)) (hb := continuous_mul)
        (hf := continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hJu)
        (hg := continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hU)
        (Filter.Eventually.of_forall fun x => by
          have ha := vec3EuclideanNorm_nonneg (regUniformMollifiedVelocity ρ ε hε u (x, t))
          have hb := vec3EuclideanNorm_nonneg (u (x, t))
          simp [Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb])
      simpa using h
    have hJuNormTop : eLpNorm
        (fun x : Vec3 => vec3EuclideanNorm
          (regUniformMollifiedVelocity ρ ε hε u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume < ⊤ := hJu4.eLpNorm_lt_top
    have hUNormTop : eLpNorm
        (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume < ⊤ := hU4.eLpNorm_lt_top
    have hJscalar : AEStronglyMeasurable
        (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i) volume :=
      (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hJu
    have hUscalar : AEStronglyMeasurable (fun x : Vec3 => u (x, t) j) volume :=
      (ContinuousLinearMap.proj (R := ℝ) j).continuous.comp_aestronglyMeasurable hU
    have hCompare : eLpNorm (fun x : Vec3 =>
        regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j)
        (ENNReal.ofReal (2 : ℝ)) volume ≤
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm
          (regUniformMollifiedVelocity ρ ε hε u (x, t)))
          (ENNReal.ofReal (4 : ℝ)) volume *
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
          (ENNReal.ofReal (4 : ℝ)) volume := by
      calc
        _ ≤ eLpNorm (fun x : Vec3 =>
            vec3EuclideanNorm (regUniformMollifiedVelocity ρ ε hε u (x, t)) *
              vec3EuclideanNorm (u (x, t))) (ENNReal.ofReal (2 : ℝ)) volume := by
          apply eLpNorm_mono_ae (hJscalar.mul hUscalar)
          filter_upwards [] with x
          calc
            ‖regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j‖ =
                ‖regUniformMollifiedVelocity ρ ε hε u (x, t) i‖ * ‖u (x, t) j‖ :=
                  norm_mul _ _
            _ ≤ vec3EuclideanNorm (regUniformMollifiedVelocity ρ ε hε u (x, t)) *
                vec3EuclideanNorm (u (x, t)) :=
              mul_le_mul (hJcomponent x) (hUcomponent x)
                (norm_nonneg _) (vec3EuclideanNorm_nonneg _)
            _ = ‖vec3EuclideanNorm (regUniformMollifiedVelocity ρ ε hε u (x, t)) *
                vec3EuclideanNorm (u (x, t))‖ := by
              rw [Real.norm_eq_abs,
                abs_of_nonneg (mul_nonneg (vec3EuclideanNorm_nonneg _)
                  (vec3EuclideanNorm_nonneg _))]
        _ ≤ eLpNorm (fun x : Vec3 => vec3EuclideanNorm
            (regUniformMollifiedVelocity ρ ε hε u (x, t)))
              (ENNReal.ofReal (4 : ℝ)) volume *
            eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
              (ENNReal.ofReal (4 : ℝ)) volume := by
          simpa using hHolder
    rw [hFclass i j, Lp.norm_toLp]
    calc
      ENNReal.toReal (eLpNorm (regPressureTensorSlice ρ ε hε u t i j)
        (ENNReal.ofReal (2 : ℝ)) volume) ≤
        ENNReal.toReal
          (eLpNorm (fun x : Vec3 => vec3EuclideanNorm
            (regUniformMollifiedVelocity ρ ε hε u (x, t)))
            (ENNReal.ofReal (4 : ℝ)) volume *
          eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
            (ENNReal.ofReal (4 : ℝ)) volume) := by
        exact ENNReal.toReal_mono (ENNReal.mul_lt_top hJuNormTop hUNormTop).ne
          (by
            change eLpNorm (fun x : Vec3 =>
              regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j)
              (ENNReal.ofReal (2 : ℝ)) volume ≤ _
            exact hCompare)
      _ = (eLpNorm (fun x : Vec3 => vec3EuclideanNorm
            (regUniformMollifiedVelocity ρ ε hε u (x, t)))
            (ENNReal.ofReal (4 : ℝ)) volume).toReal *
          (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
            (ENNReal.ofReal (4 : ℝ)) volume).toReal := by
        rw [ENNReal.toReal_mul]
  have hPressureNorm :
      ‖rieszPressureSlice (2 : ℝ) (by norm_num) F‖ ≤
        rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
          ∑ i : Fin 3, ∑ j : Fin 3, ‖F i j‖ :=
    rieszPressureSlice_norm_le (2 : ℝ) (by norm_num) F
  rw [hPeq]
  calc
    ‖rieszPressureSlice (2 : ℝ) (by norm_num) F‖ ≤
        rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
          ∑ i : Fin 3, ∑ j : Fin 3, ‖F i j‖ := hPressureNorm
    _ ≤ rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
        ∑ i : Fin 3, ∑ j : Fin 3,
          (eLpNorm (fun x : Vec3 => vec3EuclideanNorm
            (regUniformMollifiedVelocity ρ ε hε u (x, t)))
            (ENNReal.ofReal (4 : ℝ)) volume).toReal *
          (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
            (ENNReal.ofReal (4 : ℝ)) volume).toReal := by
      gcongr
      · have hnorm := rieszPressureOperator_norm_le (2 : ℝ) (by norm_num)
          (0 : Fin 3) (0 : Fin 3)
        exact le_trans (norm_nonneg _) hnorm
      · exact hFnorm _ _
    _ = 9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
        (eLpNorm (fun x : Vec3 => vec3EuclideanNorm
          (regUniformMollifiedVelocity ρ ε hε u (x, t)))
          (ENNReal.ofReal (4 : ℝ)) volume).toReal *
        (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
          (ENNReal.ofReal (4 : ℝ)) volume).toReal := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

end CKN.Leray

end
