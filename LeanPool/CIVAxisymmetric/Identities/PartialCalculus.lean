/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Partial Calculus

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

theorem spatialPartial_add_of_differentiableAt {g h : ParabolicPoint → ℝ} {i : Fin 3} {z :
    ParabolicPoint}
    (hg : DifferentiableAt ℝ (fun x : Vec3 => g (x, z.2)) z.1)
    (hh : DifferentiableAt ℝ (fun x : Vec3 => h (x, z.2)) z.1) :
    spatialPartial (fun w => g w + h w) i z = spatialPartial g i z + spatialPartial h i z := by
  unfold spatialPartial
  have h_fderiv := fderiv_fun_add hg hh
  have h_apply := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) h_fderiv
  have hz_eq : z = (z.1, z.2) := rfl
  rw [hz_eq] at h_apply ⊢
  simpa [add_apply] using h_apply

theorem spatialPartial_sub_of_differentiableAt {g h : ParabolicPoint → ℝ} {i : Fin 3} {z :
    ParabolicPoint}
    (hg : DifferentiableAt ℝ (fun x : Vec3 => g (x, z.2)) z.1)
    (hh : DifferentiableAt ℝ (fun x : Vec3 => h (x, z.2)) z.1) :
    spatialPartial (fun w => g w - h w) i z = spatialPartial g i z - spatialPartial h i z := by
  change fderiv ℝ (fun y : Vec3 => g (y, z.2) - h (y, z.2)) z.1 (basisVec i) = _
  rw [fderiv_fun_sub hg hh]
  rfl

theorem spatialPartial_mul_of_differentiableAt {g h : ParabolicPoint → ℝ} {i : Fin 3} {z :
    ParabolicPoint}
    (hg : DifferentiableAt ℝ (fun x : Vec3 => g (x, z.2)) z.1)
    (hh : DifferentiableAt ℝ (fun x : Vec3 => h (x, z.2)) z.1) :
    spatialPartial (fun w => g w * h w) i z = g z * spatialPartial h i z + h z * spatialPartial
      g i z := by
  unfold spatialPartial
  have h_fderiv := fderiv_fun_mul hg hh
  have h_apply := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) h_fderiv
  have hz_eq : z = (z.1, z.2) := rfl
  rw [hz_eq] at h_apply ⊢
  simpa [add_apply, smul_apply, smul_eq_mul, mul_comm, add_comm] using h_apply

theorem spatialPartial_const_mul_of_differentiableAt {g : ParabolicPoint → ℝ} {i : Fin 3} {z :
    ParabolicPoint}
    (c : ℝ) (hg : DifferentiableAt ℝ (fun x : Vec3 => g (x, z.2)) z.1) :
    spatialPartial (fun w => c * g w) i z = c * spatialPartial g i z := by
  unfold spatialPartial
  have h_fderiv := fderiv_const_mul hg c
  have h_apply := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) h_fderiv
  simpa [smul_apply, smul_eq_mul] using h_apply

theorem spatialPartial_time_weight_mul {g : ParabolicPoint → ℝ} {i : Fin 3} {z : ParabolicPoint}
    (φ : ℝ → ℝ)
    (hg : DifferentiableAt ℝ (fun x : Vec3 => g (x, z.2)) z.1) :
    spatialPartial (fun w => φ w.2 * g w) i z = φ z.2 * spatialPartial g i z := by
  unfold spatialPartial
  have h_fderiv := fderiv_const_mul hg (φ z.2)
  have h_apply := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) h_fderiv
  simpa [smul_apply, smul_eq_mul] using h_apply

theorem timePartial_add_of_differentiableAt {g h : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hg : DifferentiableAt ℝ (fun t : ℝ => g (z.1, t)) z.2)
    (hh : DifferentiableAt ℝ (fun t : ℝ => h (z.1, t)) z.2) :
    timePartial (fun w => g w + h w) z = timePartial g z + timePartial h z := by
  unfold timePartial
  have h_fderiv := fderiv_fun_add hg hh
  have h_apply := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h_fderiv
  simpa [add_apply] using h_apply

theorem timePartial_mul_of_differentiableAt {g h : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hg : DifferentiableAt ℝ (fun t : ℝ => g (z.1, t)) z.2)
    (hh : DifferentiableAt ℝ (fun t : ℝ => h (z.1, t)) z.2) :
    timePartial (fun w => g w * h w) z = g z * timePartial h z + h z * timePartial g z := by
  unfold timePartial
  have h_fderiv := fderiv_fun_mul hg hh
  have h_apply := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h_fderiv
  have hz_eq : z = (z.1, z.2) := rfl
  rw [hz_eq] at h_apply ⊢
  simpa [add_apply, smul_apply, smul_eq_mul, mul_comm, add_comm] using h_apply

theorem timePartial_neg_rpow_mul {g : ParabolicPoint → ℝ} {z : ParabolicPoint} (η : ℝ) (hz : z.2
    < 0)
    (hg : DifferentiableAt ℝ (fun t : ℝ => g (z.1, t)) z.2) :
    timePartial (fun w => (-w.2) ^ η * g w) z =
      -(η * (-z.2) ^ (η - 1)) * g z + (-z.2) ^ η * timePartial g z := by
  unfold timePartial
  have h_deriv_eq : ∀ (f : ParabolicPoint → ℝ),
      (fderiv ℝ (fun s : ℝ => f (z.1, s)) z.2) 1 = deriv (fun s : ℝ => f (z.1, s)) z.2 := by
    intro f; rw [fderiv_eq_deriv_mul, mul_one]
  have hneg_ne_zero : -z.2 ≠ 0 := by linarith only [hz]
  have h_rpow_deriv : HasDerivAt (fun s : ℝ => (-s) ^ η) (-(η * (-z.2) ^ (η - 1))) z.2 := by
    have h_neg : HasDerivAt (fun s : ℝ => -s) (-1) z.2 := by
      have h := (hasDerivAt_id z.2).neg
      simpa [show (-id : ℝ → ℝ) = (fun s => -s) by ext s; rfl] using h
    have h := h_neg.rpow_const (Or.inl hneg_ne_zero) (p := η)
    simpa [mul_comm, mul_left_comm, mul_assoc, neg_mul, one_mul] using h
  have h_rpow_diff : DifferentiableAt ℝ (fun s : ℝ => (-s) ^ η) z.2 :=
    h_rpow_deriv.differentiableAt
  have h_deriv_mul_raw := deriv_mul h_rpow_diff hg
  -- h_deriv_mul_raw : deriv ((fun s => (-s)^η) * (fun t => g (z.1, t))) z.2 = ...
  -- Expand pointwise multiplication using funext
  have h_fun_eq : ((fun s : ℝ => (-s) ^ η) * (fun t : ℝ => g (z.1, t))) = (fun s : ℝ => (-s) ^ η
    * g (z.1, s)) := by
    ext s; rfl
  rw [h_fun_eq] at h_deriv_mul_raw
  rw [h_deriv_eq (fun w => (-w.2) ^ η * g w)]
  dsimp
  rw [h_deriv_eq g]
  rw [h_deriv_mul_raw]
  rw [h_rpow_deriv.deriv]
  -- Goal: (-(η * (-z.2)^(η-1))) * g (z.1, z.2) + (-z.2)^η * deriv (fun t => g (z.1, t)) z.2 =
  --       -(η * (-z.2)^(η-1)) * g z + (-z.2)^η * deriv (fun s => g (z.1, s)) z.2
  -- g(z.1,z.2) = g z definitionally, and deriv (fun t => ...) = deriv (fun s => ...) by
  -- alpha conversion
  rfl

theorem timePartial_space_weight_mul {g : ParabolicPoint → ℝ} {z : ParabolicPoint} (ψ : Vec3 → ℝ)
    (hg : DifferentiableAt ℝ (fun t : ℝ => g (z.1, t)) z.2) :
    timePartial (fun w => ψ w.1 * g w) z = ψ z.1 * timePartial g z := by
  unfold timePartial
  have h_fderiv := fderiv_const_mul hg (ψ z.1)
  have h_apply := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h_fderiv
  simp [smul_apply, smul_eq_mul, h_apply]

theorem spatialSecondPartial_time_weight_mul {g : ParabolicPoint → ℝ} {i j : Fin 3} {z :
    ParabolicPoint} (φ : ℝ → ℝ)
    (hg : ∀ x : Vec3, DifferentiableAt ℝ (fun y : Vec3 => g (y, z.2)) x)
    (hg' : DifferentiableAt ℝ (fun x : Vec3 => spatialPartial g i (x, z.2)) z.1) :
    spatialSecondPartial (fun w => φ w.2 * g w) i j z = φ z.2 * spatialSecondPartial g i j z := by
  -- Prove the inner equality: spatialPartial (fun w' => φ w'.2 * g w') i (x, z.2) = φ z.2
  -- * spatialPartial g i (x, z.2)
  have h_inner_eq : (fun (x : Vec3) => spatialPartial (fun w' => φ w'.2 * g w') i (x, z.2)) =
      (fun x : Vec3 => φ z.2 * spatialPartial g i (x, z.2)) := by
    ext x
    unfold spatialPartial
    have h_fderiv := fderiv_const_mul (hg x) (φ z.2)
    have h_apply := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) h_fderiv
    simpa [smul_apply, smul_eq_mul] using h_apply
  -- Use conv to rewrite only the outer spatialPartial on LHS
  rw [spatialSecondPartial]
  -- Goal: spatialPartial (fun w => spatialPartial (fun w' => φ w'.2 * g w') i w) j z = φ
  -- z.2 * spatialSecondPartial g i j z
  conv =>
    lhs
    rw [spatialPartial]
  -- Goal: (fderiv ℝ (fun x : Vec3 => spatialPartial (fun w' => φ w'.2 * g w') i (x, z.2))
  -- z.1) (basisVec j) = φ z.2 * spatialSecondPartial g i j z
  rw [spatialSecondPartial, spatialPartial]
  -- Goal: (fderiv ℝ (fun x : Vec3 => spatialPartial (fun w' => φ w'.2 * g w') i (x, z.2))
  -- z.1) (basisVec j) =
  --   φ z.2 * (fderiv ℝ (fun x : Vec3 => spatialPartial g i (x, z.2)) z.1) (basisVec j)
  rw [h_inner_eq]
  -- Goal: (fderiv ℝ (fun x : Vec3 => φ z.2 * spatialPartial g i (x, z.2)) z.1) (basisVec j) =
  --   φ z.2 * (fderiv ℝ (fun x : Vec3 => spatialPartial g i (x, z.2)) z.1) (basisVec j)
  have h_fderiv := fderiv_const_mul hg' (φ z.2)
  have h_apply := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j)) h_fderiv
  simpa [smul_apply, smul_eq_mul] using h_apply

end CIV
