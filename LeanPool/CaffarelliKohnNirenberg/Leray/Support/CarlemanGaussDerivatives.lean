/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanGaussWeights
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreDefs
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Derivatives of the Gaussian Carleman phase

The calculations below specialize `eq:carleman-commutator` of the
Escauriaza–Seregin–Šverák manuscript to the phase in
`prop:carleman-gauss` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open CKN CKN.Foundation.Parabolic
open Set
open scoped Topology

noncomputable section

namespace CKN

/-- The product normed additive group structure on space-time for Gaussian derivative
calculations. -/
local instance gaussDerivativesNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

/-- The real product normed-space structure on space-time for Gaussian derivative calculations. -/
local instance gaussDerivativesNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- The spatial Hessian of the Gaussian phase on positive time. -/
theorem gaussCarlemanPhase_spatialSecondPartial (q : ℝ)
    (z : ParabolicPoint) (ht : 0 < z.2) (i j : Fin 3) :
    spatialSecondPartial (gaussCarlemanPhase q) i j z =
      if i = j then -1 / (4 * z.2) else 0 := by
  rcases z with ⟨x, t⟩
  have hfun : (fun y : Vec3 => spatialPartial (gaussCarlemanPhase q) i (y, t)) =
      fun y => -(y i) / (4 * t) := by
    funext y
    exact gaussCarlemanPhase_spatialPartial q (y, t) ht i
  change (fderiv ℝ (fun y : Vec3 => spatialPartial (gaussCarlemanPhase q) i (y, t)) x)
    (basisVec j) = _
  rw [hfun]
  have hd : DifferentiableAt ℝ (fun y : Vec3 => y i) x := by fun_prop
  have heq : (fun y : Vec3 => -(y i) / (4 * t)) =
      fun y => (-(1 / (4 * t))) • y i := by
    funext y
    simp only [smul_eq_mul]
    ring
  rw [heq, fderiv_fun_const_smul hd]
  simp only [smul_apply, smul_eq_mul]
  rw [show fderiv ℝ (fun y : Vec3 => y i) x = ContinuousLinearMap.proj i by
    calc
      fderiv ℝ (fun y : Vec3 => y i) x =
          ContinuousLinearMap.proj i ∘SL fderiv ℝ (fun y : Vec3 => y) x :=
        fderiv_apply differentiableAt_id i
      _ = ContinuousLinearMap.proj i := by simp]
  simp [ContinuousLinearMap.proj_apply, basisVec_apply]
  split_ifs
  · field_simp [ne_of_gt ht]
  · rfl

/-- The squared spatial gradient of the Gaussian phase. -/
theorem gaussCarlemanPhase_scalarGradSq (q : ℝ)
    (z : ParabolicPoint) (ht : 0 < z.2) :
    scalarGradSq (gaussCarlemanPhase q) z =
      (∑ i : Fin 3, z.1 i ^ 2) / (16 * z.2 ^ 2) := by
  rw [scalarGradSq]
  simp_rw [gaussCarlemanPhase_spatialPartial q z ht]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [ne_of_gt ht]
  ring

/-- The phase potential in the conjugated heat operator. -/
theorem gaussCarlemanPhase_potential (q : ℝ)
    (z : ParabolicPoint) (ht : 0 < z.2) :
    scalarGradSq (gaussCarlemanPhase q) z -
      timePartial (gaussCarlemanPhase q) z =
      -scalarGradSq (gaussCarlemanPhase q) z +
        q * (1 / z.2 - 1 / 3) := by
  rw [gaussCarlemanPhase_timePartial q z ht,
    gaussCarlemanPhase_scalarGradSq q z ht]
  ring

/-- The spatial Laplacian of the Gaussian phase. -/
theorem gaussCarlemanPhase_scalarLaplacian (q : ℝ)
    (z : ParabolicPoint) (ht : 0 < z.2) :
    scalarLaplacian (gaussCarlemanPhase q) z = -3 / (4 * z.2) := by
  rw [scalarLaplacian]
  simp_rw [gaussCarlemanPhase_spatialSecondPartial q z ht]
  simp
  ring

/-- The time derivative of each spatial derivative of the Gaussian phase. -/
theorem gaussCarlemanPhase_time_spatialPartial (q : ℝ)
    (z : ParabolicPoint) (ht : 0 < z.2) (i : Fin 3) :
    timePartial (fun y => spatialPartial (gaussCarlemanPhase q) i y) z =
      z.1 i / (4 * z.2 ^ 2) := by
  rcases z with ⟨x, t⟩
  change (fderiv ℝ (fun s : ℝ =>
    spatialPartial (gaussCarlemanPhase q) i (x, s)) t) 1 = _
  rw [fderiv_apply_one_eq_deriv]
  have heq : (fun s : ℝ => spatialPartial (gaussCarlemanPhase q) i (x, s)) =ᶠ[𝓝 t]
      (fun s : ℝ => -(x i) / (4 * s)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact gaussCarlemanPhase_spatialPartial q (x, s) hs i
  rw [heq.deriv_eq]
  have hinv := (hasDerivAt_inv (ne_of_gt ht)).const_mul (-(x i) / 4)
  have hfun : (fun s : ℝ => -(x i) / (4 * s)) =
      fun s => (-(x i) / 4) * s⁻¹ := by
    funext s
    ring
  rw [hfun]
  convert hinv.deriv using 1
  field_simp [ne_of_gt ht]

/-- The second time derivative of the Gaussian phase. -/
theorem gaussCarlemanPhase_time_timePartial (q : ℝ)
    (z : ParabolicPoint) (ht : 0 < z.2) :
    timePartial (fun y => timePartial (gaussCarlemanPhase q) y) z =
      -(∑ i : Fin 3, z.1 i ^ 2) / (4 * z.2 ^ 3) + q / z.2 ^ 2 := by
  rcases z with ⟨x, t⟩
  change (fderiv ℝ (fun s : ℝ => timePartial (gaussCarlemanPhase q) (x, s)) t) 1 = _
  rw [fderiv_apply_one_eq_deriv]
  let Q : ℝ := ∑ i : Fin 3, x i ^ 2
  have heq : (fun s : ℝ => timePartial (gaussCarlemanPhase q) (x, s)) =ᶠ[𝓝 t]
      (fun s : ℝ => Q / (8 * s ^ 2) - q * (1 / s - 1 / 3)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    simpa only [Q] using gaussCarlemanPhase_timePartial q (x, s) hs
  rw [heq.deriv_eq]
  have htne : t ≠ 0 := ne_of_gt ht
  have hpow := (hasDerivAt_id t).pow 2
  have hinv := hpow.inv (pow_ne_zero 2 htne)
  have hfirst := hinv.const_mul (Q / 8)
  have hsecond := ((hasDerivAt_inv htne).sub_const (1 / 3)).const_mul q
  have hderiv := hfirst.sub hsecond
  have hfun : (fun s : ℝ => Q / (8 * s ^ 2) - q * (1 / s - 1 / 3)) =
      fun s => Q / 8 * (s ^ 2)⁻¹ - q * (s⁻¹ - 1 / 3) := by
    funext s
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp only [id_eq, Nat.reduceSub, pow_one, mul_one] at hderiv
  change HasDerivAt (fun s => Q / 8 * (s ^ 2)⁻¹ - q * (s⁻¹ - 1 / 3))
    (Q / 8 * (-(2 * t) / (t ^ 2) ^ 2) - q * -(t ^ 2)⁻¹) t at hderiv
  rw [hfun, hderiv.deriv]
  field_simp [htne]
  ring

/-- Every third spatial derivative of the Gaussian phase vanishes. -/
theorem gaussCarlemanPhase_spatial_third (q : ℝ)
    (z : ParabolicPoint) (ht : 0 < z.2) (i j k : Fin 3) :
    spatialPartial (fun y => spatialSecondPartial (gaussCarlemanPhase q) i j y) k z =
      0 := by
  rcases z with ⟨x, t⟩
  have hfun : (fun y : Vec3 =>
      spatialSecondPartial (gaussCarlemanPhase q) i j (y, t)) =
      fun _ => if i = j then -1 / (4 * t) else 0 := by
    funext y
    exact gaussCarlemanPhase_spatialSecondPartial q (y, t) ht i j
  change (fderiv ℝ (fun y : Vec3 =>
    spatialSecondPartial (gaussCarlemanPhase q) i j (y, t)) x) (basisVec k) = 0
  rw [hfun]
  simp

/-- Every fourth spatial derivative entering `Δ²φ` vanishes. -/
theorem gaussCarlemanPhase_spatial_fourth (q : ℝ)
    (z : ParabolicPoint) (ht : 0 < z.2) (i j : Fin 3) :
    spatialSecondPartial
      (fun y => spatialSecondPartial (gaussCarlemanPhase q) i i y) j j z = 0 := by
  rcases z with ⟨x, t⟩
  have hfun : (fun y : Vec3 => spatialPartial
      (fun w => spatialSecondPartial (gaussCarlemanPhase q) i i w) j (y, t)) =
      fun _ => 0 := by
    funext y
    exact gaussCarlemanPhase_spatial_third q (y, t) ht i i j
  change (fderiv ℝ (fun y : Vec3 => spatialPartial
    (fun w => spatialSecondPartial (gaussCarlemanPhase q) i i w) j (y, t)) x)
      (basisVec j) = 0
  rw [hfun]
  simp

/-- The commutator density for the Gaussian phase is positive and explicit. -/
theorem gaussCarleman_commutatorDensity (q : ℝ)
    (v : ParabolicPoint → ℝ) (z : ParabolicPoint) (ht : 0 < z.2) :
    carlemanCommutatorDensity (gaussCarlemanPhase q) v z =
      q / 3 * z.2 * v z ^ 2 := by
  unfold carlemanCommutatorDensity
  rw [gaussCarlemanPhase_potential q z ht,
    gaussCarlemanPhase_scalarGradSq q z ht,
    gaussCarlemanPhase_time_timePartial q z ht]
  simp_rw [gaussCarlemanPhase_spatial_fourth q z ht,
    gaussCarlemanPhase_time_spatialPartial q z ht,
    gaussCarlemanPhase_spatialSecondPartial q z ht,
    gaussCarlemanPhase_spatialPartial q z ht]
  simp only [scalarGradSq, Fin.sum_univ_three]
  simp
  field_simp [ne_of_gt ht]
  ring

/-- The Gaussian phase is smooth on the positive-time cylinder. -/
theorem gaussCarlemanPhase_contDiffOn (q : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (gaussCarlemanPhase q)
      (spaceTimeSet univ (Ioo (0 : ℝ) 2)) := by
  intro z hz
  have ht : 0 < z.2 := hz.2.1
  have hden : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ParabolicPoint => 8 * y.2) z := by
    fun_prop
  have hsq : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ParabolicPoint => ∑ i : Fin 3, y.1 i ^ 2) z := by
    fun_prop
  have hweight : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ParabolicPoint => gaussCarlemanTimeWeight y.2) z := by
    unfold gaussCarlemanTimeWeight
    fun_prop
  have hlog := hweight.log (ne_of_gt (mul_pos ht (Real.exp_pos _)))
  have hfirst : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ParabolicPoint => (-(8 * y.2)⁻¹) •
        (∑ i : Fin 3, y.1 i ^ 2)) z := by
    exact (hden.inv (mul_ne_zero (by norm_num) (ne_of_gt ht))).neg.smul hsq
  have hphase : ContDiffAt ℝ (⊤ : ℕ∞) (gaussCarlemanPhase q) z := by
    unfold gaussCarlemanPhase
    exact hfirst.sub (contDiffAt_const.mul hlog)
  exact hphase.contDiffWithinAt

end CKN
