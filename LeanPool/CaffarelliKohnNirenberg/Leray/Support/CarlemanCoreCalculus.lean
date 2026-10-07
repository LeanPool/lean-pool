/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreSupport
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# First derivatives of conjugated scalar fields

Local product and chain rules for the ordinary space-time coordinates in
`prop:carleman-gauss` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The product normed additive group structure required for space-time differentiation. -/
local instance carlemanCoreCalculusNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

/-- The real product normed-space structure required for space-time differentiation. -/
local instance carlemanCoreCalculusNormedSpace : NormedSpace ℝ ParabolicPoint :=
  carlemanProductNormedSpace

/-- Spatial product rule at a point of differentiability. -/
theorem spatialPartial_mul_at {a b : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z)
    (i : Fin 3) :
    spatialPartial (fun y => a y * b y) i z =
      spatialPartial a i z * b z + a z * spatialPartial b i z := by
  have ha' : DifferentiableAt ℝ (fun x : Vec3 => a (x, z.2)) z.1 :=
    ha.comp z.1 (by fun_prop)
  have hb' : DifferentiableAt ℝ (fun x : Vec3 => b (x, z.2)) z.1 :=
    hb.comp z.1 (by fun_prop)
  change (fderiv ℝ ((fun x : Vec3 => a (x, z.2)) *
    (fun x : Vec3 => b (x, z.2))) z.1) (basisVec i) = _
  rw [fderiv_mul ha' hb']
  simp only [add_apply, smul_apply, smul_eq_mul]
  change a z * spatialPartial b i z + b z * spatialPartial a i z = _
  ring

/-- Time product rule at a point of differentiability. -/
theorem timePartial_mul_at {a b : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) :
    timePartial (fun y => a y * b y) z =
      timePartial a z * b z + a z * timePartial b z := by
  have ha' : DifferentiableAt ℝ (fun t : ℝ => a (z.1, t)) z.2 :=
    ha.comp z.2 (by fun_prop)
  have hb' : DifferentiableAt ℝ (fun t : ℝ => b (z.1, t)) z.2 :=
    hb.comp z.2 (by fun_prop)
  change (fderiv ℝ ((fun t : ℝ => a (z.1, t)) *
    (fun t : ℝ => b (z.1, t))) z.2) 1 = _
  rw [fderiv_mul ha' hb']
  simp only [add_apply, smul_apply, smul_eq_mul]
  change a z * timePartial b z + b z * timePartial a z = _
  ring

/-- Spatial derivative of the exponential of a differentiable phase. -/
theorem spatialPartial_exp_at {φ : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hφ : DifferentiableAt ℝ φ z) (i : Fin 3) :
    spatialPartial (fun y => Real.exp (φ y)) i z =
      Real.exp (φ z) * spatialPartial φ i z := by
  have hφ' : DifferentiableAt ℝ (fun x : Vec3 => φ (x, z.2)) z.1 :=
    hφ.comp z.1 (by fun_prop)
  change (fderiv ℝ (fun x : Vec3 => Real.exp (φ (x, z.2))) z.1) (basisVec i) = _
  rw [fderiv_exp hφ']
  simp only [smul_apply, smul_eq_mul]
  rfl

/-- Time derivative of the exponential of a differentiable phase. -/
theorem timePartial_exp_at {φ : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hφ : DifferentiableAt ℝ φ z) :
    timePartial (fun y => Real.exp (φ y)) z =
      Real.exp (φ z) * timePartial φ z := by
  have hφ' : DifferentiableAt ℝ (fun t : ℝ => φ (z.1, t)) z.2 :=
    hφ.comp z.2 (by fun_prop)
  change (fderiv ℝ (fun t : ℝ => Real.exp (φ (z.1, t))) z.2) 1 = _
  rw [fderiv_exp hφ']
  simp only [smul_apply, smul_eq_mul]
  rfl

/-- The first spatial derivative under exponential conjugation. -/
theorem spatialPartial_exp_mul_at
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ w : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    spatialPartial (fun y => Real.exp (φ y) * w y) i z =
      Real.exp (φ z) * (spatialPartial w i z + w z * spatialPartial φ i z) := by
  have hφd : DifferentiableAt ℝ φ z :=
    (hφ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hwd : DifferentiableAt ℝ w z :=
    hw.differentiable (by simp) z
  rw [spatialPartial_mul_at hφd.exp hwd i, spatialPartial_exp_at hφd i]
  ring

/-- The first time derivative under exponential conjugation. -/
theorem timePartial_exp_mul_at
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ w : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {z : ParabolicPoint} (hz : z ∈ U) :
    timePartial (fun y => Real.exp (φ y) * w y) z =
      Real.exp (φ z) * (timePartial w z + w z * timePartial φ z) := by
  have hφd : DifferentiableAt ℝ φ z :=
    (hφ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hwd : DifferentiableAt ℝ w z :=
    hw.differentiable (by simp) z
  rw [timePartial_mul_at hφd.exp hwd, timePartial_exp_at hφd]
  ring

/-- The spatial gradient of a field before conjugation is controlled by its
conjugated gradient and the phase gradient
(`eq:carleman-half-gradient-estimate` of the Escauriaza–Seregin–Šverák
manuscript). -/
theorem exp_sq_scalarGradSq_le
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ w : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {z : ParabolicPoint} (hz : z ∈ U) :
    Real.exp (φ z) ^ 2 * scalarGradSq w z ≤
      2 * (scalarGradSq (fun y => Real.exp (φ y) * w y) z +
        (Real.exp (φ z) * w z) ^ 2 * scalarGradSq φ z) := by
  let E : ℝ := Real.exp (φ z)
  let V : ℝ := E * w z
  let v : ParabolicPoint → ℝ := fun y => Real.exp (φ y) * w y
  have hcoord (i : Fin 3) :
      E ^ 2 * spatialPartial w i z ^ 2 ≤
        2 * (spatialPartial v i z ^ 2 + V ^ 2 * spatialPartial φ i z ^ 2) := by
    have hid : E * spatialPartial w i z =
        spatialPartial v i z - V * spatialPartial φ i z := by
      dsimp [E, V, v]
      rw [spatialPartial_exp_mul_at hU hφ hw hz i]
      ring
    have hsq (A B : ℝ) : (A - B) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) := by
      nlinarith only [sq_nonneg (A + B)]
    calc
      E ^ 2 * spatialPartial w i z ^ 2 = (E * spatialPartial w i z) ^ 2 := by ring
      _ = (spatialPartial v i z - V * spatialPartial φ i z) ^ 2 := by rw [hid]
      _ ≤ 2 * (spatialPartial v i z ^ 2 + (V * spatialPartial φ i z) ^ 2) :=
        hsq _ _
      _ = 2 * (spatialPartial v i z ^ 2 + V ^ 2 * spatialPartial φ i z ^ 2) :=
        by ring
  calc
    Real.exp (φ z) ^ 2 * scalarGradSq w z
        = ∑ i : Fin 3, E ^ 2 * spatialPartial w i z ^ 2 := by
            simp only [scalarGradSq, Finset.mul_sum, E]
    _ ≤ ∑ i : Fin 3,
          2 * (spatialPartial v i z ^ 2 + V ^ 2 * spatialPartial φ i z ^ 2) := by
            apply Finset.sum_le_sum
            intro i _
            exact hcoord i
    _ = 2 * (scalarGradSq v z + V ^ 2 * scalarGradSq φ z) := by
          simp only [scalarGradSq, Finset.mul_sum]
          simp_rw [mul_add, Finset.sum_add_distrib]
          rw [Finset.mul_sum, Finset.mul_sum]
    _ = 2 * (scalarGradSq (fun y => Real.exp (φ y) * w y) z +
          (Real.exp (φ z) * w z) ^ 2 * scalarGradSq φ z) := rfl

end CKN
