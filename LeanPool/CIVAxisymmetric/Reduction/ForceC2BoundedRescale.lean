/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CIVAxisymmetric.Reduction.ParabolicRescaleSolution

/-! ### Iterating a single spatial derivative through a constant multiple precomposed with
    parabolic dilation -/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



private theorem iterate_spatialPartial_const_mul_comp' (μ : ℝ) (z₀ : ParabolicPoint) (i : Fin 3) :
    ∀ (n : ℕ) (c : ℝ) (g : ParabolicPoint → ℝ),
      (fun k => spatialPartial k i)^[n] (fun w : ParabolicPoint => c * g (scalingParabolic μ z₀ w))
        = fun w : ParabolicPoint =>
            c * μ ^ n * (fun k => spatialPartial k i)^[n] g (scalingParabolic μ z₀ w) := by
  intro n
  induction n with
  | zero =>
      intro c g
      funext w
      simp
  | succ n ih =>
      intro c g
      have hstep : spatialPartial (fun w : ParabolicPoint => c * g (scalingParabolic μ z₀ w)) i
          = fun w : ParabolicPoint =>
              c * μ * spatialPartial g i (scalingParabolic μ z₀ w) :=
        funext fun w => spatialPartial_const_mul_comp_scalingParabolic c μ z₀ g i w
      rw [Function.iterate_succ_apply, hstep, ih (c * μ) (spatialPartial g i),
        Function.iterate_succ_apply]
      funext w
      ring

/-! ### Multi-index spatial derivative of a constant multiple precomposed with parabolic dilation -/

theorem multiPartial_const_mul_comp_scalingParabolic (c μ : ℝ) (z₀ : ParabolicPoint)
    (g : ParabolicPoint → ℝ) (α : Fin 3 → ℕ) (z : ParabolicPoint) :
    multiPartial (fun w : ParabolicPoint => c * g (scalingParabolic μ z₀ w)) α z
      = c * μ ^ (α 0 + α 1 + α 2) * multiPartial g α (scalingParabolic μ z₀ z) := by
  have h2 := iterate_spatialPartial_const_mul_comp' μ z₀ 2 (α 2) c g
  have h1 := iterate_spatialPartial_const_mul_comp' μ z₀ 1 (α 1) (c * μ ^ (α 2))
      ((fun k => spatialPartial k 2)^[α 2] g)
  have h0 := iterate_spatialPartial_const_mul_comp' μ z₀ 0 (α 0) (c * μ ^ (α 2) * μ ^ (α 1))
      ((fun k => spatialPartial k 1)^[α 1] ((fun k => spatialPartial k 2)^[α 2] g))
  show ((fun k => spatialPartial k 0)^[α 0] ((fun k => spatialPartial k 1)^[α 1]
      ((fun k => spatialPartial k 2)^[α 2]
        (fun w : ParabolicPoint => c * g (scalingParabolic μ z₀ w))))) z
      = c * μ ^ (α 0 + α 1 + α 2) *
        ((fun k => spatialPartial k 0)^[α 0] ((fun k => spatialPartial k 1)^[α 1]
            ((fun k => spatialPartial k 2)^[α 2] g))) (scalingParabolic μ z₀ z)
  rw [h2, h1, h0]
  ring

/-! ### Parabolic dilation centered at the origin -/

private theorem scalingParabolic_zero (R : ℝ) (z : ParabolicPoint) :
    scalingParabolic R ((0 : Vec3), (0 : ℝ)) z = ((R • z.1 : Vec3), R ^ 2 * z.2) := by
  show ((0 : Vec3) + R • z.1, (0 : ℝ) + R ^ 2 * z.2) = ((R • z.1 : Vec3), R ^ 2 * z.2)
  rw [zero_add, zero_add]

/-! ### Shrinking the unit cylinder by parabolic dilation -/

private theorem mem_unitCylinder_of_scalingParabolic {z : ParabolicPoint} {R : ℝ} (hR0 : 0 < R)
    (hR1 : R ≤ 1) (hz : z ∈ unitCylinder) :
    scalingParabolic R ((0 : Vec3), (0 : ℝ)) z ∈ unitCylinder := by
  rw [scalingParabolic_zero]
  have hz_ball : vec3EuclideanNorm z.1 < 1 := by
    have := hz.1
    simpa [unitCylinder, spaceTimeSet, vec3Ball, sub_zero] using this
  have hz_time : z.2 ∈ Ioo (-1 : ℝ) 0 := by
    have := hz.2
    simpa [unitCylinder, spaceTimeSet] using this
  have hmem_ball : (R • z.1 : Vec3) ∈ vec3Ball 0 1 := by
    show vec3EuclideanNorm ((R • z.1 : Vec3) - 0) < 1
    rw [sub_zero, vec3EuclideanNorm_smul, abs_of_pos hR0]
    have hpos : 0 ≤ vec3EuclideanNorm z.1 := vec3EuclideanNorm_nonneg _
    nlinarith only [hz_ball, hR1, hpos]
  have hmem_time : R ^ 2 * z.2 ∈ Ioo (-1 : ℝ) 0 := by
    rcases hz_time with ⟨hzl, hzr⟩
    have hR2pos : 0 < R ^ 2 := pow_pos hR0 2
    have hR2le1 : R ^ 2 ≤ 1 := pow_le_one₀ hR0.le hR1 (n := 2)
    have h_lower : -1 < R ^ 2 * z.2 := by
      have hz2_nonpos : z.2 ≤ 0 := by linarith only [hzr]
      have h_mul_ge : z.2 ≤ R ^ 2 * z.2 := by nlinarith only [hR2le1, hz2_nonpos]
      linarith only [hzl, h_mul_ge]
    have h_upper : R ^ 2 * z.2 < 0 := by nlinarith only [hzr, hR2pos]
    exact ⟨h_lower, h_upper⟩
  exact ⟨hmem_ball, hmem_time⟩

/-! ### Componentwise formula for the Navier-Stokes force rescaling -/

private theorem rescaleForce_apply_eq (R : ℝ) (f : ParabolicPoint → Vec3) (w : ParabolicPoint)
    (i : Fin 3) :
    rescaleForce R ((0 : Vec3), (0 : ℝ)) f w i
      = R ^ 3 * f (scalingParabolic R ((0 : Vec3), (0 : ℝ)) w) i := by
  show (R ^ 3 • f (scalingParabolic R ((0 : Vec3), (0 : ℝ)) w)) i
      = R ^ 3 * f (scalingParabolic R ((0 : Vec3), (0 : ℝ)) w) i
  simp

/-! ### `C^2` force bound survives parabolic rescaling -/

theorem forceC2Bounded_rescale {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1)
    {f : ParabolicPoint → Vec3} (hf : ForceC2Bounded f) :
    ForceC2Bounded (rescaleForce R ((0 : Vec3), (0 : ℝ)) f) := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨R ^ 3 * M, fun z hz i α hα => ?_⟩
  have hmp : multiPartial (fun w => rescaleForce R ((0 : Vec3), (0 : ℝ)) f w i) α z
      = R ^ 3 * R ^ (α 0 + α 1 + α 2) * multiPartial (fun w => f w i) α
          (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z) := by
    have := multiPartial_const_mul_comp_scalingParabolic (R ^ 3) R ((0 : Vec3), (0 : ℝ))
      (fun w => f w i) α z
    simpa [rescaleForce_apply_eq] using this
  rw [hmp, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ R ^ 3),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ R ^ (α 0 + α 1 + α 2))]
  have hz' : scalingParabolic R ((0 : Vec3), (0 : ℝ)) z ∈ unitCylinder :=
    mem_unitCylinder_of_scalingParabolic hR0 hR1 hz
  have hbound := hM (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z) hz' i α hα
  have hR3nn : (0:ℝ) ≤ R ^ 3 := by positivity
  have hMnn : (0:ℝ) ≤ M := le_trans (abs_nonneg _) hbound
  have hRorder_le_one : R ^ (α 0 + α 1 + α 2) ≤ 1 := pow_le_one₀ hR0.le hR1
  have hstep : R ^ 3 * R ^ (α 0 + α 1 + α 2) * |multiPartial (fun w => f w i) α
      (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z)| ≤ R ^ 3 * 1 * M := by
    have h1 : R ^ (α 0 + α 1 + α 2) * |multiPartial (fun w => f w i) α
        (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z)| ≤ 1 * M := by
      calc R ^ (α 0 + α 1 + α 2) * |multiPartial (fun w => f w i) α
              (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z)|
          ≤ 1 * |multiPartial (fun w => f w i) α
              (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z)| := by gcongr
        _ ≤ 1 * M := by gcongr
    calc R ^ 3 * R ^ (α 0 + α 1 + α 2) * |multiPartial (fun w => f w i) α
            (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z)|
        = R ^ 3 * (R ^ (α 0 + α 1 + α 2) * |multiPartial (fun w => f w i) α
            (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z)|) := by ring
      _ ≤ R ^ 3 * (1 * M) := by gcongr
      _ = R ^ 3 * 1 * M := by ring
  linarith only [hstep]

end CIV

