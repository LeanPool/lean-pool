/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.OneDistillabilityDefs
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional

/-!
Positive scalar rescaling of actual completely positive maps and positive
functionals. These constructions retain every finite matrix amplification.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped CStarAlgebra ComplexOrder

section Scaling

variable {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
  [PartialOrder E] [PartialOrder F] [StarOrderedRing E] [StarOrderedRing F]

/-- Nonnegative real rescaling, with complete positivity proved at every size. -/
def distillationScaleCP (c : ℝ) (hc : 0 ≤ c) (T : E →CP F) : E →CP F where
  toLinearMap := c • T.toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    have he : M.map (c • T.toLinearMap) = c • M.map T.toLinearMap := by
      apply CStarMatrix.ext
      intro i j
      rfl
    rw [he]
    exact smul_nonneg hc (T.map_cstarMatrix_nonneg' k M hM)

@[simp] theorem distillationScaleCP_apply (c : ℝ) (hc : 0 ≤ c)
    (T : E →CP F) (x : E) : distillationScaleCP c hc T x = c • T x := rfl

/-- Nonnegative real rescaling of an actual positive complex-linear functional. -/
def distillationScaleFunctional (c : ℝ) (hc : 0 ≤ c) (τ : E →ₚ[ℂ] ℂ) : E →ₚ[ℂ] ℂ where
  toLinearMap := c • τ.toLinearMap
  monotone' := fun _ _ h => smul_le_smul_of_nonneg_left (τ.monotone' h) hc

omit [StarOrderedRing E] in
@[simp] theorem distillationScaleFunctional_apply (c : ℝ) (hc : 0 ≤ c)
    (τ : E →ₚ[ℂ] ℂ) (x : E) : distillationScaleFunctional c hc τ x = c • τ x := rfl

/-- Automatic continuity and the exact norm-at-one formula for positive functionals. -/
theorem positiveFunctional_one_eq_norm (τ : E →ₚ[ℂ] ℂ) :
    τ 1 = (‖(PositiveContinuousLinearMap.ofClass τ).toContinuousLinearMap‖ : ℂ) :=
  (PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
    (PositiveContinuousLinearMap.ofClass τ)).symm

/-- A positive unital functional has norm one, including on closed VNA carriers. -/
theorem stateFunctional_norm_apply_le (τ : E →ₚ[ℂ] ℂ) (hτ : τ 1 = 1) (x : E) :
    ‖τ x‖ ≤ ‖x‖ := by
  let τc := (PositiveContinuousLinearMap.ofClass τ).toContinuousLinearMap
  have hn : ‖τc‖ = 1 := by
    have he := congrArg Complex.re (positiveFunctional_one_eq_norm τ)
    simpa only [hτ, Complex.one_re, Complex.ofReal_re] using he.symm
  have h := τc.le_opNorm x
  have heval : τc x = τ x := rfl
  simpa only [heval, hn, one_mul] using h

end Scaling

/-- A strictly positive scale that sends every element into the unit ball. -/
def distillationUnitScale {E : Type*} [NormedAddCommGroup E] (x : E) : ℝ :=
  (1 + ‖x‖)⁻¹

theorem distillationUnitScale_pos {E : Type*} [NormedAddCommGroup E] (x : E) :
    0 < distillationUnitScale x :=
  inv_pos.mpr (by linarith [norm_nonneg x])

theorem norm_distillationUnitScale_smul_le_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x : E) : ‖distillationUnitScale x • x‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (distillationUnitScale_pos x)]
  calc
    distillationUnitScale x * ‖x‖ ≤ distillationUnitScale x * (1 + ‖x‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (distillationUnitScale_pos x).le
    _ = 1 := inv_mul_cancel₀ (ne_of_gt (by linarith [norm_nonneg x]))

/-- Strictly positive output scaling preserves and reflects the PPT condition. -/
theorem twoQubitPPT_scale_iff (c : ℝ) (hc : 0 < c)
    (τ : TwoQubitAlgebra →ₚ[ℂ] ℂ) :
    TwoQubitPPT (distillationScaleFunctional c hc.le τ) ↔ TwoQubitPPT τ := by
  constructor
  · intro h Z hZ
    have hs := smul_nonneg (inv_pos.mpr hc).le (h Z hZ)
    simpa only [distillationScaleFunctional_apply, smul_smul,
      inv_mul_cancel₀ hc.ne', one_smul] using hs
  · intro h Z hZ
    exact smul_nonneg hc.le (h Z hZ)

/-- NPT excludes the zero positive functional, so its mass is strictly positive. -/
theorem exists_positive_twoQubit_mass (τ : TwoQubitAlgebra →ₚ[ℂ] ℂ)
    (hτ : ¬ TwoQubitPPT τ) : ∃ p : ℝ, 0 < p ∧ τ 1 = (p : ℂ) := by
  let τc := (PositiveContinuousLinearMap.ofClass τ).toContinuousLinearMap
  have hn : τc ≠ 0 := by
    intro hz
    apply hτ
    intro Z _
    have he := congrArg (fun F : TwoQubitAlgebra →L[ℂ] ℂ => F (partialTransposeLeft Z)) hz
    change τ (partialTransposeLeft Z) = 0 at he
    simpa only [he] using (le_refl (0 : ℂ))
  exact ⟨‖τc‖, norm_pos_iff.mpr hn, positiveFunctional_one_eq_norm τ⟩

/-- The literal tensor-generator identity at the two identities. -/
theorem qubitTensor_one_one : qubitTensor 1 1 = 1 := by
  apply CStarMatrix.ext
  rintro ⟨i, k⟩ ⟨j, l⟩
  change (if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0) =
    if (i, k) = (j, l) then (1 : ℂ) else 0
  by_cases hij : i = j <;> by_cases hkl : k = l <;> simp [hij, hkl]

end VacuumBellSeparation.Bipartite
