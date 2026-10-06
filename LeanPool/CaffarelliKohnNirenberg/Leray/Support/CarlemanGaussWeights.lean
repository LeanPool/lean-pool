/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Carleman Gauss Weights

Supporting estimates for the Navier–Stokes development.
-/

public section

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The time factor in the Gaussian weight from `prop:carleman-gauss` of the
Escauriaza–Seregin–Šverák manuscript. -/
@[expose]
def gaussCarlemanTimeWeight (t : ℝ) : ℝ := t * Real.exp ((1 - t) / 3)

/-- The logarithmic Gaussian phase used in the proof of `prop:carleman-gauss` (ESS). -/
@[expose]
def gaussCarlemanPhase (q : ℝ) (z : ParabolicPoint) : ℝ :=
  (-(8 * z.2)⁻¹) • (∑ i : Fin 3, z.1 i ^ 2) -
    q * Real.log (gaussCarlemanTimeWeight z.2)

/-- The derivative of a coordinate function on Vec3 is the coordinate projection. -/
theorem vec3_coordDeriv (x : Vec3) (j : Fin 3) :
    fderiv ℝ (fun y : Vec3 => y j) x = ContinuousLinearMap.proj j := by
  calc
    fderiv ℝ (fun y : Vec3 => y j) x =
        ContinuousLinearMap.proj j ∘SL fderiv ℝ (fun y : Vec3 => y) x :=
      fderiv_apply differentiableAt_id j
    _ = ContinuousLinearMap.proj j := by simp

/-- The directional derivative of a squared coordinate on Vec3. -/
theorem vec3_coordSqDeriv (x : Vec3) (j i : Fin 3) :
    (fderiv ℝ (fun y : Vec3 => y j ^ 2) x) (basisVec i) =
      if j = i then 2 * x j else 0 := by
  have hd : DifferentiableAt ℝ (fun y : Vec3 => y j) x := by fun_prop
  rw [fderiv_fun_pow 2 hd, vec3_coordDeriv]
  simp [ContinuousLinearMap.proj_apply, basisVec_apply]

private theorem sum_sq_spatial_deriv (x : Vec3) (i : Fin 3) :
    (fderiv ℝ (fun y : Vec3 => ∑ j : Fin 3, y j ^ 2) x) (basisVec i) =
      2 * x i := by
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun j : Fin 3 => fun y : Vec3 => y j ^ 2)]
  · simp only [sum_apply]
    simp_rw [vec3_coordSqDeriv]
    simp
  · intro j hj
    fun_prop

/-- The spatial derivative of the Gaussian phase, used in the explicit
weight calculation for `prop:carleman-gauss` (ESS). -/
theorem gaussCarlemanPhase_spatialPartial (q : ℝ) (z : ParabolicPoint)
    (ht : 0 < z.2) (i : Fin 3) :
    spatialPartial (gaussCarlemanPhase q) i z = -z.1 i / (4 * z.2) := by
  rcases z with ⟨x, t⟩
  change (fderiv ℝ (fun x : Vec3 =>
    (-(8 * t)⁻¹) • (∑ j : Fin 3, x j ^ 2) -
      q * Real.log (gaussCarlemanTimeWeight t)) x) (basisVec i) = -x i / (4 * t)
  have hdiff : DifferentiableAt ℝ
      (fun y : Vec3 => ∑ j : Fin 3, y j ^ 2) x := by
    fun_prop
  change (fderiv ℝ
    (fun y : Vec3 => (-(8 * t)⁻¹) • (∑ j : Fin 3, y j ^ 2) -
      q * Real.log (gaussCarlemanTimeWeight t)) x)
        (basisVec i) = -x i / (4 * t)
  rw [fderiv_sub_const (q * Real.log (gaussCarlemanTimeWeight t)),
    fderiv_fun_const_smul hdiff (-(8 * t)⁻¹)]
  simp only [smul_apply, smul_eq_mul]
  rw [sum_sq_spatial_deriv]
  field_simp [ne_of_gt ht]
  ring

private theorem gaussCarlemanTimeWeight_pos {t : ℝ} (ht : 0 < t) :
    0 < gaussCarlemanTimeWeight t := by
  exact mul_pos ht (Real.exp_pos _)

/-- The time derivative of the Gaussian phase on positive time, used in the
weight calculation for `prop:carleman-gauss` (ESS). -/
theorem gaussCarlemanPhase_timePartial (q : ℝ) (z : ParabolicPoint)
    (ht : 0 < z.2) :
    timePartial (gaussCarlemanPhase q) z =
      (∑ i : Fin 3, z.1 i ^ 2) / (8 * z.2 ^ 2) -
        q * (1 / z.2 - 1 / 3) := by
  rcases z with ⟨x, t⟩
  change (fderiv ℝ (fun s : ℝ =>
    (-(8 * s)⁻¹) • (∑ i : Fin 3, x i ^ 2) -
      q * Real.log (gaussCarlemanTimeWeight s)) t) 1 = _
  rw [fderiv_apply_one_eq_deriv]
  let Q : ℝ := ∑ i : Fin 3, x i ^ 2
  let E : ℝ := Real.exp ((1 - t) / 3)
  have ht0 : 0 < t := ht
  have hr : HasDerivAt (fun s : ℝ => (1 - s) / 3) (-(1 / 3 : ℝ)) t := by
    convert ((hasDerivAt_id t).const_sub 1).div_const 3 using 1 <;> norm_num
  have hexp : HasDerivAt (fun s : ℝ => Real.exp ((1 - s) / 3))
      (Real.exp ((1 - t) / 3) * (-(1 / 3 : ℝ))) t := by
    exact (Real.hasDerivAt_exp ((1 - t) / 3)).comp t hr
  have hm := (hasDerivAt_id t).mul hexp
  have hweight : HasDerivAt (fun s : ℝ => s * Real.exp ((1 - s) / 3))
      (E + t * (E * (-(1 / 3 : ℝ)))) t := by
    convert hm using 1
    · funext s
      rfl
    · simp only [id_eq, one_mul, E]
  have hlog0 := hweight.log (ne_of_gt (gaussCarlemanTimeWeight_pos ht0))
  have hlogCoeff :
      (E + t * (E * (-(1 / 3 : ℝ)))) / (t * E) = 1 / t - 1 / 3 := by
    have hE : E ≠ 0 := ne_of_gt (Real.exp_pos ((1 - t) / 3))
    field_simp [ne_of_gt ht0, hE]
    ring
  have hlog : HasDerivAt (fun s : ℝ => Real.log (gaussCarlemanTimeWeight s))
      (1 / t - 1 / 3) t := by
    have hlogCoeff' :
        (E + t * (E * (-(1 / 3 : ℝ)))) / gaussCarlemanTimeWeight t =
          1 / t - 1 / 3 := by
      simpa only [gaussCarlemanTimeWeight, E] using hlogCoeff
    change HasDerivAt (fun s : ℝ => Real.log (gaussCarlemanTimeWeight s))
      ((E + t * (E * (-(1 / 3 : ℝ)))) / gaussCarlemanTimeWeight t) t at hlog0
    rw [hlogCoeff'] at hlog0
    exact hlog0
  have hden : HasDerivAt (fun s : ℝ => 8 * s) 8 t := by
    convert (hasDerivAt_id t).const_mul 8 using 1 <;> norm_num
  have hcoeff : HasDerivAt (fun s : ℝ => -(8 * s)⁻¹)
      (8 / (8 * t) ^ 2) t := by
    have h := (hden.inv (mul_ne_zero (by norm_num) (ne_of_gt ht0))).neg
    convert h using 1
    ring
  have hfirst : HasDerivAt (fun s : ℝ => (-(8 * s)⁻¹) * Q)
      ((8 / (8 * t) ^ 2) * Q) t := hcoeff.mul_const Q
  have hqlog := hlog.const_mul q
  have hcoeff' : (8 / (8 * t) ^ 2) * Q = Q / (8 * t ^ 2) := by
    field_simp [ne_of_gt ht0]
  have hphase := hfirst.sub hqlog
  rw [hcoeff'] at hphase
  have hphase' : HasDerivAt (fun s : ℝ => gaussCarlemanPhase q (x, s))
      (Q / (8 * t ^ 2) - q * (1 / t - 1 / 3)) t := by
    convert hphase using 1
    funext s
    rfl
  exact hphase'.deriv

/-- The time comparison used to return from the Gaussian conjugation to the
original weight in `prop:carleman-gauss` (ESS). -/
theorem gaussTimeRatio_sq_bounds {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2) :
    Real.exp (-(2 / 3 : ℝ)) ≤
        (t / (t * Real.exp ((1 - t) / 3))) ^ 2 ∧
      (t / (t * Real.exp ((1 - t) / 3))) ^ 2 ≤ Real.exp (2 / 3 : ℝ) := by
  let r : ℝ := (1 - t) / 3
  have hrlo : -(1 / 3 : ℝ) < r := by
    dsimp [r]
    linarith only [ht2]
  have hrhi : r < 1 / 3 := by
    dsimp [r]
    linarith only [ht0]
  have hratio : t / (t * Real.exp r) = Real.exp (-r) := by
    have hden : t * Real.exp r ≠ 0 := mul_ne_zero (ne_of_gt ht0) (ne_of_gt (Real.exp_pos r))
    field_simp [hden, ne_of_gt (Real.exp_pos r)]
    rw [← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero]
  have hsquare : (Real.exp (-r)) ^ 2 = Real.exp (-2 * r) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hlo : Real.exp (-(2 / 3 : ℝ)) ≤ Real.exp (-2 * r) := by
    apply (Real.exp_le_exp).2
    linarith only [hrhi]
  have hhi : Real.exp (-2 * r) ≤ Real.exp (2 / 3 : ℝ) := by
    apply (Real.exp_le_exp).2
    linarith only [hrlo]
  rw [show t / (t * Real.exp ((1 - t) / 3)) = t / (t * Real.exp r) by
    rw [show (1 - t) / 3 = r by rfl]]
  rw [hratio, hsquare]
  exact ⟨hlo, hhi⟩

/-- The reciprocal comparison for the Gaussian time weight on `(0,2)`. -/
theorem gaussTimeWeight_div_sq_bounds {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2) :
    Real.exp (-(2 / 3 : ℝ)) ≤ (gaussCarlemanTimeWeight t / t) ^ 2 ∧
      (gaussCarlemanTimeWeight t / t) ^ 2 ≤ Real.exp (2 / 3 : ℝ) := by
  let r : ℝ := (1 - t) / 3
  have hrlo : -(1 / 3 : ℝ) < r := by
    dsimp [r]
    linarith only [ht2]
  have hrhi : r < 1 / 3 := by
    dsimp [r]
    linarith only [ht0]
  have hratio : gaussCarlemanTimeWeight t / t = Real.exp r := by
    unfold gaussCarlemanTimeWeight
    rw [show (1 - t) / 3 = r by rfl]
    field_simp [ne_of_gt ht0]
  have hsquare : Real.exp r ^ 2 = Real.exp (2 * r) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hratio, hsquare]
  constructor
  · apply (Real.exp_le_exp).2
    linarith only [hrlo]
  · apply (Real.exp_le_exp).2
    linarith only [hrhi]

end CKN
