/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CauchyGreenOperator
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Calculus rules for directional Wirtinger derivatives

Linearity in the function, conjugate-linearity in the direction, the product
rule with a real factor, commutation of two Wirtinger derivatives of a `C²`
function, and vanishing of derivatives along directions of translation
invariance.
-/

@[expose] public section

open Set Filter Complex
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.CauchyGreen

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dbarDir_congr {v : E} {f g : E → ℂ} {x : E} (h : f =ᶠ[𝓝 x] g) :
    dbarDir v f x = dbarDir v g x := by
  simp only [dbarDir, h.fderiv_eq]

theorem dbarDir_add {v : E} {f g : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    dbarDir v (fun y ↦ f y + g y) x = dbarDir v f x + dbarDir v g x := by
  simp only [dbarDir, fderiv_fun_add hf hg, add_apply]
  ring

theorem dbarDir_sub {v : E} {f g : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    dbarDir v (fun y ↦ f y - g y) x = dbarDir v f x - dbarDir v g x := by
  simp only [dbarDir, fderiv_fun_sub hf hg, sub_apply]
  ring

theorem dbarDir_const {v : E} (c : ℂ) (x : E) : dbarDir v (fun _ ↦ c) x = 0 := by
  simp [dbarDir]

theorem dbarDir_add_dir (u w : E) (f : E → ℂ) (x : E) :
    dbarDir (u + w) f x = dbarDir u f x + dbarDir w f x := by
  simp only [dbarDir, smul_add, map_add]
  ring

theorem dbarDir_real_smul_dir (c : ℝ) (v : E) (f : E → ℂ) (x : E) :
    dbarDir (c • v) f x = c * dbarDir v f x := by
  have h2 : I • c • v = c • (I • v) := smul_comm _ _ _
  simp only [dbarDir, h2, map_smul, Complex.real_smul]
  ring

theorem dbarDir_I_smul_dir (v : E) (f : E → ℂ) (x : E) :
    dbarDir (I • v) f x = -I * dbarDir v f x := by
  simp only [dbarDir, smul_smul, I_mul_I, neg_one_smul, map_neg]
  ring_nf
  rw [I_sq]
  ring

/-- Product rule with a real-valued factor. -/
theorem dbarDir_ofReal_mul {v : E} {χ : E → ℝ} {a : E → ℂ} {x : E}
    (hχ : DifferentiableAt ℝ χ x) (ha : DifferentiableAt ℝ a x) :
    dbarDir v (fun y ↦ (χ y : ℂ) * a y) x =
      dbarDir v (fun y ↦ (χ y : ℂ)) x * a x + χ x * dbarDir v a x := by
  have hχc : DifferentiableAt ℝ (fun y ↦ (χ y : ℂ)) x :=
    (Complex.ofRealCLM.differentiableAt).comp x hχ
  simp only [dbarDir, fderiv_fun_mul hχc ha, add_apply, smul_apply, smul_eq_mul]
  ring

/-- Two directional Wirtinger derivatives of a `C²` function commute. -/
theorem dbarDir_dbarDir_comm {u v : E} {g : E → ℂ} {x : E}
    (hg : ContDiffAt ℝ 2 g x) :
    dbarDir u (dbarDir v g) x = dbarDir v (dbarDir u g) x := by
  have hsymm := ContDiffAt.isSymmSndFDerivAt hg (by simp)
  have hD : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hDD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have happ (w : E) : HasFDerivAt (fun y ↦ fderiv ℝ g y w)
      ((fderiv ℝ (fderiv ℝ g) x).flip w) x := by
    have := (hDD.hasFDerivAt).clm_apply (hasFDerivAt_const w x)
    simpa using this
  have hdir (w : E) : HasFDerivAt (dbarDir w g)
      ((2 : ℂ)⁻¹ • ((fderiv ℝ (fderiv ℝ g) x).flip w +
        I • (fderiv ℝ (fderiv ℝ g) x).flip (I • w))) x := by
    have h := ((happ w).add ((happ (I • w)).const_smul I)).const_smul (2 : ℂ)⁻¹
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
    simp only [dbarDir, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  simp only [dbarDir, (hdir v).fderiv, (hdir u).fderiv]
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, smul_add]
  rw [hsymm u v, hsymm u (I • v), hsymm (I • u) v, hsymm (I • u) (I • v)]
  ring

/-- A function invariant under real translations in direction `u` has zero
derivative in that direction. -/
theorem fderiv_apply_eq_zero_of_invariant {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {u : E} (h : ∀ z (t : ℝ), f (z + t • u) = f z) (x : E) :
    fderiv ℝ f x u = 0 := by
  by_cases hf : DifferentiableAt ℝ f x
  · have hline : HasDerivAt (fun t : ℝ ↦ f (x + t • u)) (fderiv ℝ f x u) 0 := by
      have hp : HasDerivAt (fun t : ℝ ↦ x + t • u) u 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
      exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hp (by simp)
    have hconst : HasDerivAt (fun t : ℝ ↦ f (x + t • u)) 0 0 := by
      simp only [h]
      exact hasDerivAt_const _ _
    exact hline.unique hconst
  · simp [fderiv_zero_of_not_differentiableAt hf]

end

end SGPT.Foundations.Analysis.Pending.CauchyGreen
