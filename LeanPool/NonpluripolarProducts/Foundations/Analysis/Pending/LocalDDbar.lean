/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DolbeaultLemma

/-!
# The local `ddᶜ` lemma for smooth closed real `(1,1)`-forms

A smooth closed real two-form `a` of type `(1,1)` on an open subset of `ℂⁿ`
has, near every point, a smooth potential `ρ` with `ddᶜ ρ = a`.

By the smooth Poincaré lemma `a = dS` for a real one-form `S` on a ball. Its
`(0,1)` part is `∂bar`-closed because `a` has no `(0,2)` part, so the local
Dolbeault lemma gives a smooth `f` with `∂bar f = S^{0,1}`. Comparing real parts,
`S = d(Re f) - d(Im f) ∘ J`, hence `S - d(Re f) = dᶜ(4π Im f)` and
`ddᶜ(4π Im f) = dS - dd(Re f) = a`.
-/

@[expose] public section

open Set Filter Complex Metric
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalPotentials

open FirstPass CauchyGreen

noncomputable section

variable {n : ℕ}

theorem oneForm_apply_smul (σ : ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ) (c : ℝ)
    (p : ComplexModel n) :
    σ ![c • p] = c * σ ![p] := by
  have e : (![c • p] : Fin 1 → ComplexModel n) = Function.update ![p] 0 (c • p) := by
    ext i; fin_cases i; simp
  have e' : Function.update ![p] 0 p = ![p] := by
    ext i; fin_cases i; simp
  rw [e, σ.map_update_smul, e', smul_eq_mul]

theorem oneForm_apply_neg (σ : ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ) (p : ComplexModel n) :
    σ ![-p] = -σ ![p] := by
  simpa using oneForm_apply_smul σ (-1) p

theorem oneForm_apply_add (σ : ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ) (p q : ComplexModel n) :
    σ ![p + q] = σ ![p] + σ ![q] := by
  have e (r : ComplexModel n) : (![r] : Fin 1 → ComplexModel n) = Function.update ![p] 0 r := by
    ext i; fin_cases i; simp
  rw [e (p + q), σ.map_update_add, ← e, ← e]

/-- The `(0,1)` part `σ^{0,1}(v) = (σ(v) + i σ(Iv)) / 2` of a real one-form. -/
def zeroOnePart (σ : ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ) (v : ComplexModel n) : ℂ :=
  ((σ ![v] : ℂ) + I * (σ ![I • v] : ℂ)) / 2

/-- For fixed `v`, `σ ↦ σ^{0,1}(v)` as a continuous real-linear map. -/
def zeroOnePartCLM (v : ComplexModel n) :
    (ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℂ :=
  (2 : ℂ)⁻¹ • (ofRealCLM ∘L ContinuousAlternatingMap.apply ℝ _ ℝ ![v] +
    I • (ofRealCLM ∘L ContinuousAlternatingMap.apply ℝ _ ℝ ![I • v]))

theorem zeroOnePartCLM_apply (v : ComplexModel n) (σ : ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ) :
    zeroOnePartCLM v σ = zeroOnePart σ v := by
  simp [zeroOnePartCLM, zeroOnePart]
  ring

theorem zeroOnePart_re (σ : ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ) (v : ComplexModel n) :
    (zeroOnePart σ v).re = σ ![v] / 2 := by
  simp [zeroOnePart]

theorem fderiv_zeroOnePart {S : ComplexModel n → ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ}
    {x : ComplexModel n} (hS : DifferentiableAt ℝ S x) (v w : ComplexModel n) :
    fderiv ℝ (fun y ↦ zeroOnePart (S y) v) x w = zeroOnePart (fderiv ℝ S x w) v := by
  have h := ((zeroOnePartCLM v).hasFDerivAt.comp x hS.hasFDerivAt).fderiv
  simp only [Function.comp_def, zeroOnePartCLM_apply] at h
  rw [h]
  simp [zeroOnePartCLM_apply]

theorem zeroOnePart_add_dir (σ : ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ) (p q : ComplexModel n) :
    zeroOnePart σ (p + q) = zeroOnePart σ p + zeroOnePart σ q := by
  simp only [zeroOnePart, smul_add, oneForm_apply_add]
  push_cast
  ring

theorem zeroOnePart_real_smul_dir (σ : ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ) (c : ℝ)
    (p : ComplexModel n) : zeroOnePart σ (c • p) = c * zeroOnePart σ p := by
  have h2 : I • c • p = c • (I • p) := smul_comm _ _ _
  simp only [zeroOnePart, h2, oneForm_apply_smul]
  push_cast
  ring

theorem zeroOnePart_I_smul_dir (σ : ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ) (p : ComplexModel n) :
    zeroOnePart σ (I • p) = -I * zeroOnePart σ p := by
  simp only [zeroOnePart, smul_smul, I_mul_I, neg_one_smul, oneForm_apply_neg]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- Both `v ↦ ∂bar_v f(x)` and `v ↦ σ^{0,1}(v)` are complex antilinear, so they
agree as soon as they agree on the standard basis. -/
theorem dbarDir_eq_zeroOnePart {f : ComplexModel n → ℂ}
    {σ : ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ} {x : ComplexModel n}
    (h : ∀ i, dbarDir (basisVec i) f x = zeroOnePart σ (basisVec i))
    (v : ComplexModel n) : dbarDir v f x = zeroOnePart σ v := by
  have hv : v = ∑ i, v i • basisVec i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr v]
    simp
  rw [hv]
  refine Finset.sum_induction _ (fun w ↦ dbarDir w f x = zeroOnePart σ w) ?_ ?_ ?_
  · intro p q hp hq
    rw [dbarDir_add_dir, zeroOnePart_add_dir, hp, hq]
  · rw [show (0 : ComplexModel n) = (0 : ℝ) • 0 by simp, dbarDir_real_smul_dir,
      zeroOnePart_real_smul_dir]
    simp
  · intro i _
    simp only
    have e (c : ℂ) : c • basisVec i = c.re • basisVec i + c.im • (I • basisVec i) := by
      conv_lhs => rw [← Complex.re_add_im c]
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    rw [e, dbarDir_add_dir, zeroOnePart_add_dir, dbarDir_real_smul_dir, dbarDir_real_smul_dir,
      zeroOnePart_real_smul_dir, zeroOnePart_real_smul_dir, dbarDir_I_smul_dir,
      zeroOnePart_I_smul_dir, h]

/-- The `(0,1)` part of a one-form whose exterior derivative has type `(1,1)`
is `∂bar`-closed. -/
theorem dbarDir_zeroOnePart_comm {S : ComplexModel n → ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ}
    {x : ComplexModel n} (hS : DifferentiableAt ℝ S x) (h11 : IsOneOne (extDeriv S x))
    (u v : ComplexModel n) :
    dbarDir u (fun y ↦ zeroOnePart (S y) v) x = dbarDir v (fun y ↦ zeroOnePart (S y) u) x := by
  set T : ComplexModel n → ComplexModel n → ℝ := fun p q ↦ fderiv ℝ S x p ![q] with hT
  have hA : ∀ p q, extDeriv S x ![p, q] = T p q - T q p := by
    intro p q
    have e : Fin.removeNth 1 ![p, q] = ![p] := by
      ext i; fin_cases i; rfl
    simp [hT, extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two, e,
      sub_eq_add_neg]
  have hneg : ∀ p q, T (-p) q = -T p q ∧ T q (-p) = -T q p := fun p q ↦ by
    simp [hT, oneForm_apply_neg]
  have h1 := h11 u v
  have h2 := h11 (I • u) v
  simp only [smul_smul, I_mul_I, neg_one_smul, hA] at h1 h2
  simp only [dbarDir]
  rw [fderiv_zeroOnePart hS, fderiv_zeroOnePart hS, fderiv_zeroOnePart hS,
    fderiv_zeroOnePart hS]
  simp only [zeroOnePart]
  apply Complex.ext <;> simp [(hneg _ _).1, (hneg _ _).2] at h1 h2 ⊢ <;>
    simp only [hT] at h1 h2 <;> linarith

/-- **Local `ddᶜ` lemma** in positive dimension: a smooth closed real `(1,1)`-form
has, near every point, a globally smooth potential for the normalized `ddᶜ`. -/
theorem exists_smooth_local_ddc_potential_of_ne_zero (hn : n ≠ 0)
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (a : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : ContDiffOn ℝ ∞ a U) (hclosed : ∀ z ∈ U, extDeriv a z = 0)
    (h11 : ∀ z ∈ U, IsOneOne (a z)) {z : ComplexModel n} (hz : z ∈ U) :
    ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ), z ∈ W ∧ IsOpen W ∧ W ⊆ U ∧
      ContDiff ℝ ∞ ρ ∧ EqOn (smoothDDC ρ) a W := by
  have : Nontrivial (ComplexModel n) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    infer_instance
  obtain ⟨ε, hε, hεU, S, hS, hSa⟩ := exists_smooth_local_twoForm_primitive hU a ha hclosed hz
  have hSd : Differentiable ℝ S := hS.differentiable (by simp)
  let β : Fin n → ComplexModel n → ℂ := fun i y ↦ zeroOnePart (S y) (basisVec i)
  have hβ (i : Fin n) : ContDiff ℝ ∞ (β i) := by
    have h := (zeroOnePartCLM (basisVec i)).contDiff.comp hS
    simpa [Function.comp_def, zeroOnePartCLM_apply] using h
  have hβclosed : IsDbarClosedOn β (ball z ε) := by
    intro i j x hx
    refine dbarDir_zeroOnePart_comm (hSd x) ?_ _ _
    rw [hSa x hx]
    exact h11 x (hεU hx)
  obtain ⟨W, hW, hzW, hWball, f, hf, hfβ⟩ :=
    exists_dbar_primitive isOpen_ball β (fun i ↦ (hβ i).contDiffOn) hβclosed (mem_ball_self hε)
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  set u : ComplexModel n → ℝ := fun y ↦ (f y).re with hu
  set w : ComplexModel n → ℝ := fun y ↦ (f y).im with hw
  have hudiff : ContDiff ℝ ∞ u := reCLM.contDiff.comp hf
  have hwdiff : ContDiff ℝ ∞ w := imCLM.contDiff.comp hf
  -- Real parts of `∂bar f = S^{0,1}`: `S = du - dw ∘ J` on `W`.
  have hre : ∀ y ∈ W, ∀ v, S y ![v] = fderiv ℝ u y v - fderiv ℝ w y (I • v) := by
    intro y hy v
    have h := congrArg Complex.re (dbarDir_eq_zeroOnePart (fun i ↦ hfβ i y hy) v)
    rw [zeroOnePart_re] at h
    have hu' : fderiv ℝ u y = reCLM.comp (fderiv ℝ f y) :=
      (reCLM.hasFDerivAt.comp y (hfd y).hasFDerivAt).fderiv
    have hw' : fderiv ℝ w y = imCLM.comp (fderiv ℝ f y) :=
      (imCLM.hasFDerivAt.comp y (hfd y).hasFDerivAt).fderiv
    rw [hu', hw']
    simp [dbarDir] at h
    simp
    linarith
  let ω₀ : ComplexModel n → ComplexModel n [⋀^Fin 0]→L[ℝ] ℝ := fun y ↦
    ContinuousAlternatingMap.constOfIsEmpty ℝ (ComplexModel n) (Fin 0) (u y)
  have hω₀ : ContDiff ℝ ∞ ω₀ :=
    (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (ComplexModel n) ℝ (Fin 0)).contDiff.comp
      hudiff
  let R := extDeriv ω₀
  have hR : ContDiff ℝ ∞ R := by
    have h :=
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ).contDiff.comp
        (hω₀.fderiv_right (m := ∞) le_rfl)
    convert h using 1
    funext y
    simp [R, extDeriv, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
  have hRapply (y : ComplexModel n) (v : ComplexModel n) : R y ![v] = fderiv ℝ u y v := by
    simp [R, ω₀, extDeriv_constOfIsEmpty]
  refine ⟨W, fun y ↦ 4 * Real.pi * w y, hzW, hW, hWball.trans hεU,
    contDiff_const.mul hwdiff, fun x hx ↦ ?_⟩
  have hdc :
      smoothDc (fun y ↦ 4 * Real.pi * w y) =ᶠ[𝓝 x] fun y ↦ S y + (-1 : ℝ) • R y := by
    filter_upwards [hW.mem_nhds hx] with y hy
    ext v
    have hv : v = ![v 0] := by ext i; fin_cases i; rfl
    have hρ : fderiv ℝ (fun y ↦ 4 * Real.pi * w y) y = (4 * Real.pi) • fderiv ℝ w y :=
      fderiv_const_mul (hwdiff.differentiable (by simp) y) _
    rw [smoothDc_apply, hρ]
    rw [hv]
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      hRapply, hre y hy]
    simp
    field_simp [Real.pi_ne_zero]
    ring
  change extDeriv (smoothDc _) x = a x
  have hRd : DifferentiableAt ℝ (fun y ↦ (-1 : ℝ) • R y) x :=
    ((hR.differentiable (by simp) x).const_smul (-1 : ℝ) :)
  rw [hdc.extDeriv_eq, extDeriv_fun_add (hSd x) hRd]
  change extDeriv S x + extDeriv ((-1 : ℝ) • R) x = a x
  rw [extDeriv_smul, extDeriv_extDeriv_apply hω₀.contDiffAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top),
    hSa x (hWball hx)]
  simp

end

end SGPT.Foundations.Analysis.Pending.LocalPotentials
