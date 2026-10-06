/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.EscauriazaSereginSverak.LPS.UniformRelativeBound
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSliceBound
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Endpoint relative convection estimate

At the spatial endpoint, Hölder with exponents `∞, 2, 2` and Young's
inequality give the fixed-time estimate needed in `lem:lps-comparison`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Fixed-time relative convection estimate for the spatial endpoint. The
coefficient is the square of the distinguished field's spatial `L∞` norm,
as in `lem:lps-comparison`. -/
theorem lps_slice_relative_bound_infty
    {u w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3}
    (huMeas : AEStronglyMeasurable u volume)
    (huInf : MemLp (fun x => vec3EuclideanNorm (u x)) ∞ volume)
    (hw2 : MemLp w 2 volume) (hDw2 : MemLp Dw 2 volume) :
    |∫ x : Vec3, ∑ i : Fin 3, u x i * ∑ j : Fin 3, w x j * Dw x i j| ≤
      (1 / 2 : ℝ) * (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, Dw x i j ^ 2) +
        (81 / 2 : ℝ) *
          (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u x)) ∞ volume).toReal ^ 2 *
          (∫ x : Vec3, ∑ i : Fin 3, w x i ^ 2) := by
  let U : ℝ := (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u x)) ∞ volume).toReal
  let W : ℝ := (eLpNorm w 2 volume).toReal
  let D : ℝ := (eLpNorm Dw 2 volume).toReal
  let B : Vec3 × (Vec3 × (Fin 3 → Vec3)) → ℝ := fun z =>
    ∑ i : Fin 3, z.1 i * ∑ j : Fin 3, z.2.1 j * z.2.2 i j
  have hHolderInf : ENNReal.HolderTriple ∞ 2 2 := by
    constructor
    simp
  have hHolder22 : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := by
    exact ENNReal.HolderConjugate.instTwoTwo
  have h12mem : MemLp (fun x : Vec3 =>
      vec3EuclideanNorm (u x) * ‖w x‖) 2 volume := by
    change MemLp ((fun x : Vec3 => vec3EuclideanNorm (u x)) *
      (fun x : Vec3 => ‖w x‖)) 2 volume
    exact MemLp.mul huInf hw2.norm (hpqr := hHolderInf)
  have h12bound : eLpNorm (fun x : Vec3 =>
      vec3EuclideanNorm (u x) * ‖w x‖) 2 volume ≤
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u x)) ∞ volume *
      eLpNorm w 2 volume := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (p := ∞) (q := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞))
      (fun a b : ℝ => a * b) 1 continuous_mul huInf.aestronglyMeasurable
      hw2.aestronglyMeasurable.norm
      (Eventually.of_forall fun x => by
        change ‖vec3EuclideanNorm (u x) * ‖w x‖‖ ≤
          (1 : ℝ) * ‖vec3EuclideanNorm (u x)‖ * ‖‖w x‖‖
        rw [norm_mul]
        simp [abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      ) (hpqr := hHolderInf)
    have h' : eLpNorm (fun x : Vec3 =>
        vec3EuclideanNorm (u x) * ‖w x‖) 2 volume ≤
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u x)) ∞ volume *
          eLpNorm (fun x : Vec3 => ‖w x‖) 2 volume := by
      simpa only [ENNReal.coe_one, Pi.mul_apply, one_mul] using h
    simpa only [eLpNorm_norm w hw2.aestronglyMeasurable] using h'
  have hprodMem : MemLp (fun x : Vec3 =>
      vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) 1 volume := by
    change MemLp (((fun x : Vec3 => vec3EuclideanNorm (u x) * ‖w x‖) *
      (fun x : Vec3 => ‖Dw x‖))) 1 volume
    exact MemLp.mul h12mem hDw2.norm (hpqr := hHolder22)
  have hprodInt : Integrable (fun x : Vec3 =>
      vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) volume :=
    memLp_one_iff_integrable.mp hprodMem
  have hprodBound : eLpNorm (fun x : Vec3 =>
      vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) 1 volume ≤
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u x)) ∞ volume *
        eLpNorm w 2 volume * eLpNorm Dw 2 volume := by
    have h3 := eLpNorm_smul_le_mul_eLpNorm (p := (2 : ℝ≥0∞))
      (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞)) h12mem.aestronglyMeasurable
      hDw2.aestronglyMeasurable.norm
    have h3' : eLpNorm (fun x : Vec3 =>
        vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) 1 volume ≤
        eLpNorm (fun x => vec3EuclideanNorm (u x) * ‖w x‖) 2 volume *
          eLpNorm Dw 2 volume := by
      change eLpNorm ((fun x : Vec3 => vec3EuclideanNorm (u x) * ‖w x‖) *
        (fun x : Vec3 => ‖Dw x‖)) 1 volume ≤ _
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
        eLpNorm_norm Dw hDw2.aestronglyMeasurable] using h3
    calc
      _ ≤ eLpNorm (fun x => vec3EuclideanNorm (u x) * ‖w x‖) 2 volume *
          eLpNorm Dw 2 volume := h3'
      _ ≤ _ := mul_le_mul_of_nonneg_right h12bound (by positivity)
  have hnonneg (x : Vec3) :
      0 ≤ vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖ :=
    mul_nonneg (mul_nonneg (vec3EuclideanNorm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have huNormMeas : AEStronglyMeasurable
      (fun x : Vec3 => vec3EuclideanNorm (u x)) volume :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable huMeas
  have hprodMeas : AEStronglyMeasurable
      (fun x : Vec3 => vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) volume :=
    (huNormMeas.mul hw2.aestronglyMeasurable.norm).mul hDw2.aestronglyMeasurable.norm
  have hprodIntegral :
      (∫ x : Vec3, vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) =
        (eLpNorm (fun x : Vec3 =>
          vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) 1 volume).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnonneg) hprodMeas,
      eLpNorm_one_eq_lintegral_enorm hprodMeas]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal (hnonneg x)]
  have hfin :
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u x)) ∞ volume *
        eLpNorm w 2 volume * eLpNorm Dw 2 volume ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top huInf.eLpNorm_ne_top hw2.eLpNorm_ne_top)
      hDw2.eLpNorm_ne_top
  have hproduct :
      ∫ x : Vec3, vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖ ≤ U * W * D := by
    rw [hprodIntegral]
    have ht := ENNReal.toReal_mono hfin hprodBound
    simpa only [U, W, D, ENNReal.toReal_mul] using ht
  have hBcont : Continuous B := by fun_prop
  have htuple : AEStronglyMeasurable (fun x : Vec3 => (u x, (w x, Dw x))) volume :=
    huMeas.prodMk (hw2.aestronglyMeasurable.prodMk hDw2.aestronglyMeasurable)
  let F : Vec3 → ℝ := fun x => B (u x, (w x, Dw x))
  have hFmeas : AEStronglyMeasurable F volume := by
    simpa only [F] using hBcont.comp_aestronglyMeasurable htuple
  have hFbound (x : Vec3) : ‖F x‖ ≤
      9 * (vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) := by
    rw [Real.norm_eq_abs]
    simpa only [F, B] using lps_triple_pointwise_euclidean (u x) (w x) (Dw x)
  have hDom : Integrable (fun x : Vec3 =>
      9 * (vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖)) volume := hprodInt.const_mul 9
  have hFint : Integrable F volume := by
    refine hDom.mono' hFmeas (Eventually.of_forall fun x => ?_)
    simpa only [Real.norm_eq_abs] using hFbound x
  have hAbsolute : |∫ x : Vec3, F x| ≤ 9 * (U * W * D) := by
    calc
      |∫ x : Vec3, F x| ≤ ∫ x : Vec3, |F x| := abs_integral_le_integral_abs
      _ ≤ ∫ x : Vec3,
          9 * (vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) := by
        apply integral_mono (by simpa only [Real.norm_eq_abs] using hFint.norm) hDom
        exact fun x => by simpa only [Real.norm_eq_abs] using hFbound x
      _ = 9 * ∫ x : Vec3,
          vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖ := by rw [integral_const_mul]
      _ ≤ 9 * (U * W * D) := by
        exact mul_le_mul_of_nonneg_left hproduct (by norm_num)
  have hU0 : 0 ≤ U := ENNReal.toReal_nonneg
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have hYoung : 9 * (U * W * D) ≤
      (1 / 2 : ℝ) * D ^ 2 + (81 / 2 : ℝ) * U ^ 2 * W ^ 2 := by
    nlinarith only [sq_nonneg (D - 9 * U * W)]
  have hsqD := lps_sq_eLpNorm_le hDw2 _
    (fun x => lps_norm_sq_le_sum_sq₂ (Dw x))
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (memLp_two_iff_integrable_sq_norm
        ((hDw2.eval i).eval j).aestronglyMeasurable).mp ((hDw2.eval i).eval j) |>.congr
          (Eventually.of_forall fun x => by simp))
  have hsqW := lps_sq_eLpNorm_le hw2 _
    (fun x => lps_norm_sq_le_sum_sq (w x))
    (integrable_finsetSum _ fun i _ =>
      (memLp_two_iff_integrable_sq_norm (hw2.eval i).aestronglyMeasurable).mp
        (hw2.eval i) |>.congr (Eventually.of_forall fun x => by simp))
  calc
    |∫ x : Vec3, ∑ i : Fin 3, u x i * ∑ j : Fin 3, w x j * Dw x i j| =
        |∫ x : Vec3, F x| := by rfl
    _ ≤ (1 / 2 : ℝ) * D ^ 2 + (81 / 2 : ℝ) * U ^ 2 * W ^ 2 := hAbsolute.trans hYoung
    _ ≤ (1 / 2 : ℝ) *
          (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, Dw x i j ^ 2) +
        (81 / 2 : ℝ) * U ^ 2 *
          (∫ x : Vec3, ∑ i : Fin 3, w x i ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hsqD (by norm_num))
        (mul_le_mul_of_nonneg_left hsqW (by positivity))
    _ = _ := by simp [U]

end ESS
