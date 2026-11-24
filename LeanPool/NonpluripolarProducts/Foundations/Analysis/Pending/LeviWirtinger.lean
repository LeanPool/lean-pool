/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.WeightedWirtingerAdjoint
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.LeviForm

/-!
# The Levi form in Wirtinger coordinates

`∂_u` is complex linear and `∂bar_w` complex antilinear in the direction.  For a `C²` real
function `φ` the diagonal mixed derivative is the Levi form,
`∂bar_v ∂_v φ = leviForm φ x v = (D²φ(v,v) + D²φ(iv,iv)) / 4`, and hence for directions `e_j`
and coefficients `ξ_j`

  `Σ_{j,k} (∂bar_{e_k} ∂_{e_j} φ)(x) ξ_j conj ξ_k = leviForm φ x (Σ_j ξ_j e_j)`,

the curvature term of the Bochner--Kodaira--Morrey--Kohn identity.
-/

@[expose] public section

open Complex
open scoped ComplexConjugate

namespace SGPT.Foundations.Analysis.Pending.CauchyGreen

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dbarDir_smul_dir (c : ℂ) (v : E) (f : E → ℂ) (x : E) :
    dbarDir (c • v) f x = conj c * dbarDir v f x := by
  have hc : c • v = c.re • v + c.im • (I • v) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, Complex.coe_smul, mul_comm, mul_smul, Complex.coe_smul, smul_comm I]
  rw [hc, dbarDir_add_dir, dbarDir_real_smul_dir, dbarDir_real_smul_dir, dbarDir_I_smul_dir]
  conv_rhs => rw [← Complex.re_add_im c]
  simp only [map_add, map_mul, Complex.conj_ofReal, conj_I]
  ring

theorem dDir_eq_conj_dbarDir_conj {v : E} {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    dDir v f x = conj (dbarDir v (fun y ↦ conj (f y)) x) := by
  rw [dbarDir_conj hf, conj_conj]

theorem dDir_smul_dir (c : ℂ) (v : E) (f : E → ℂ) (x : E) :
    dDir (c • v) f x = c * dDir v f x := by
  by_cases hf : DifferentiableAt ℝ f x
  · rw [dDir_eq_conj_dbarDir_conj hf, dDir_eq_conj_dbarDir_conj hf, dbarDir_smul_dir, map_mul,
      conj_conj]
  · simp [dDir, fderiv_zero_of_not_differentiableAt hf]

theorem dDir_add_dir (u w : E) (f : E → ℂ) (x : E) :
    dDir (u + w) f x = dDir u f x + dDir w f x := by
  simp only [dDir, smul_add, map_add]
  ring

theorem dDir_sum_dir {ι : Type*} (s : Finset ι) (ξ : ι → ℂ) (e : ι → E) (f : E → ℂ) (x : E) :
    dDir (∑ j ∈ s, ξ j • e j) f x = ∑ j ∈ s, ξ j * dDir (e j) f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dDir]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dDir_add_dir,
      dDir_smul_dir, ih]

theorem dbarDir_sum_dir {ι : Type*} (s : Finset ι) (ξ : ι → ℂ) (e : ι → E) (f : E → ℂ) (x : E) :
    dbarDir (∑ j ∈ s, ξ j • e j) f x = ∑ j ∈ s, conj (ξ j) * dbarDir (e j) f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dbarDir]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dbarDir_add_dir,
      dbarDir_smul_dir, ih]

theorem dbarDir_finset_sum_fun {ι : Type*} (s : Finset ι) {g : ι → E → ℂ} {w x : E}
    (hg : ∀ j ∈ s, DifferentiableAt ℝ (g j) x) :
    dbarDir w (fun y ↦ ∑ j ∈ s, g j y) x = ∑ j ∈ s, dbarDir w (g j) x := by
  have h : fderiv ℝ (fun y ↦ ∑ j ∈ s, g j y) x = ∑ j ∈ s, fderiv ℝ (g j) x :=
    fderiv_fun_sum hg
  simp only [dbarDir, h, sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.sum_div]

theorem dbarDir_const_mul_fun (c : ℂ) {g : E → ℂ} {w x : E} (hg : DifferentiableAt ℝ g x) :
    dbarDir w (fun y ↦ c * g y) x = c * dbarDir w g x := by
  have h : fderiv ℝ (fun y ↦ c * g y) x = c • fderiv ℝ g x := fderiv_const_mul hg c
  simp only [dbarDir, h, smul_apply, smul_eq_mul]
  ring

theorem fderiv_ofReal_comp_apply {h : E → ℝ} {y : E} (hy : DifferentiableAt ℝ h y) (b : E) :
    fderiv ℝ (fun y ↦ (h y : ℂ)) y b = (fderiv ℝ h y b : ℂ) := by
  have := ((Complex.ofRealCLM.hasFDerivAt).comp y hy.hasFDerivAt).fderiv
  exact congrArg (fun L : E →L[ℝ] ℂ ↦ L b) this

/-- The diagonal mixed Wirtinger derivative of a real `C²` function is its Levi form. -/
theorem dbarDir_dDir_ofReal_eq_leviForm {φ : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ x) (v : E) :
    dbarDir v (dDir v (fun y ↦ (φ y : ℂ))) x = (leviForm φ x v : ℂ) := by
  have hφc : ContDiffAt ℝ 2 (fun y ↦ (φ y : ℂ)) x :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp x hφ
  have hS : ∀ a b : E, fderiv ℝ (fderiv ℝ (fun y ↦ (φ y : ℂ))) x a b =
      (fderiv ℝ (fderiv ℝ φ) x a b : ℂ) := by
    intro a b
    rw [← fderiv_fderiv_apply_eq hφc, ← fderiv_fderiv_apply_eq hφ]
    have hD : ∀ y, DifferentiableAt ℝ φ y → fderiv ℝ (fun y ↦ (φ y : ℂ)) y b =
        (fderiv ℝ φ y b : ℂ) := fun y hy ↦ by
      exact fderiv_ofReal_comp_apply hy b
    have hev : (fun y ↦ fderiv ℝ (fun y ↦ (φ y : ℂ)) y b) =ᶠ[nhds x]
        fun y ↦ ((fderiv ℝ φ y b : ℝ) : ℂ) := by
      filter_upwards [(hφ.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt
        (by norm_num)] with y hy using hD y hy
    rw [hev.fderiv_eq]
    have hdiff : DifferentiableAt ℝ (fun y ↦ fderiv ℝ φ y b) x := by
      have hDD : DifferentiableAt ℝ (fderiv ℝ φ) x :=
        (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
      exact hDD.clm_apply (differentiableAt_const b)
    exact fderiv_ofReal_comp_apply hdiff a
  have hsymm := ContDiffAt.isSymmSndFDerivAt hφ (by simp)
  simp only [dbarDir, fderiv_dDir_apply hφc, hS, leviForm, realHessian_eq_fderiv]
  rw [hsymm v (I • v)]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- **The curvature term in coordinates.** -/
theorem sum_dbarDir_dDir_mul_conj_eq_leviForm {ι : Type*} [Fintype ι] (e : ι → E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (ξ : ι → ℂ) (x : E) :
    ∑ j, ∑ k, dbarDir (e k) (dDir (e j) (fun y ↦ (φ y : ℂ))) x * ξ j * conj (ξ k) =
      (leviForm φ x (∑ j, ξ j • e j) : ℂ) := by
  have hφc : ContDiff ℝ 2 (fun y ↦ (φ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hd : ∀ j, DifferentiableAt ℝ (dDir (e j) (fun y ↦ (φ y : ℂ))) x := fun j ↦
    (contDiff_dDir (k := 1) hφc).differentiable one_ne_zero x
  have hfun : dDir (∑ j, ξ j • e j) (fun y ↦ (φ y : ℂ)) =
      fun y ↦ ∑ j, ξ j * dDir (e j) (fun y ↦ (φ y : ℂ)) y := by
    funext y; exact dDir_sum_dir _ ξ e _ y
  rw [← dbarDir_dDir_ofReal_eq_leviForm hφ.contDiffAt, hfun, dbarDir_sum_dir]
  simp_rw [dbarDir_finset_sum_fun Finset.univ (fun j _ ↦ (hd j).const_mul (ξ j)),
    dbarDir_const_mul_fun _ (hd _), Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end

end SGPT.Foundations.Analysis.Pending.CauchyGreen
