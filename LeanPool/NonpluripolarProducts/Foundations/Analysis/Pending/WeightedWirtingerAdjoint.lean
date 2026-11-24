/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.WirtingerIntegrationByParts

/-!
# The weighted formal adjoint of `∂bar` and its commutator

For a real weight `φ` put `δ_v a = ∂_v a - (∂_v φ) a`, so that `δ_v a · e^{-φ} = ∂_v (a e^{-φ})`.
Then `-δ_v` is the formal adjoint of `∂bar_v` in `L²(e^{-φ})`:

  `∫ δ_v a · conj b · e^{-φ} = - ∫ a · conj (∂bar_v b) · e^{-φ}`

for `C¹` functions one of which has compact support, and for `C²` data

  `∂bar_u (δ_v a) = δ_v (∂bar_u a) - (∂bar_u ∂_v φ) a`.
-/

@[expose] public section

open MeasureTheory Set Filter Complex
open scoped Topology ContDiff ComplexConjugate

namespace SGPT.Foundations.Analysis.Pending.CauchyGreen

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `δ_v a = ∂_v a - (∂_v φ) a`, the weighted `∂_v`. -/
def deltaDir (v : E) (φ : E → ℝ) (a : E → ℂ) (x : E) : ℂ :=
  dDir v a x - dDir v (fun y ↦ (φ y : ℂ)) x * a x

/-- The weight `e^{-φ}` as a complex function. -/
def cweight (φ : E → ℝ) (x : E) : ℂ := ((Real.exp (-φ x) : ℝ) : ℂ)

theorem dDir_mul {v : E} {f g : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    dDir v (fun y ↦ f y * g y) x = dDir v f x * g x + f x * dDir v g x := by
  simp only [dDir, fderiv_fun_mul hf hg, add_apply,
    smul_apply, smul_eq_mul]
  ring

theorem dbarDir_mul {v : E} {f g : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    dbarDir v (fun y ↦ f y * g y) x = dbarDir v f x * g x + f x * dbarDir v g x := by
  simp only [dbarDir, fderiv_fun_mul hf hg, add_apply,
    smul_apply, smul_eq_mul]
  ring

theorem dDir_sub {v : E} {f g : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    dDir v (fun y ↦ f y - g y) x = dDir v f x - dDir v g x := by
  simp only [dDir, fderiv_fun_sub hf hg, sub_apply]
  ring

theorem differentiableAt_ofReal_comp {φ : E → ℝ} {x : E} (hφ : DifferentiableAt ℝ φ x) :
    DifferentiableAt ℝ (fun y ↦ (φ y : ℂ)) x :=
  (Complex.ofRealCLM.differentiableAt).comp x hφ

theorem differentiableAt_cweight {φ : E → ℝ} {x : E} (hφ : DifferentiableAt ℝ φ x) :
    DifferentiableAt ℝ (cweight φ) x :=
  differentiableAt_ofReal_comp (hφ.neg.exp)

theorem dDir_cweight {v : E} {φ : E → ℝ} {x : E} (hφ : DifferentiableAt ℝ φ x) :
    dDir v (cweight φ) x = - cweight φ x * dDir v (fun y ↦ (φ y : ℂ)) x := by
  have h1 : HasFDerivAt (fun y ↦ Real.exp (-φ y))
      (Real.exp (-φ x) • (-(fderiv ℝ φ x))) x :=
    (hφ.hasFDerivAt.neg).exp
  have h2 : fderiv ℝ (cweight φ) x =
      Complex.ofRealCLM.comp (Real.exp (-φ x) • (-(fderiv ℝ φ x))) :=
    ((Complex.ofRealCLM.hasFDerivAt).comp x h1).fderiv
  have h3 : fderiv ℝ (fun y ↦ (φ y : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ φ x) :=
    ((Complex.ofRealCLM.hasFDerivAt).comp x hφ.hasFDerivAt).fderiv
  simp only [dDir, h2, h3, cweight, ContinuousLinearMap.comp_apply,
    smul_apply, neg_apply, smul_eq_mul,
    Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- `δ_v a · e^{-φ} = ∂_v (a e^{-φ})`. -/
theorem deltaDir_mul_cweight {v : E} {φ : E → ℝ} {a : E → ℂ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (ha : DifferentiableAt ℝ a x) :
    deltaDir v φ a x * cweight φ x = dDir v (fun y ↦ a y * cweight φ y) x := by
  rw [dDir_mul ha (differentiableAt_cweight hφ), dDir_cweight hφ, deltaDir]
  ring

theorem contDiff_cweight {φ : E → ℝ} {k : WithTop ℕ∞} (hφ : ContDiff ℝ k φ) :
    ContDiff ℝ k (cweight φ) :=
  Complex.ofRealCLM.contDiff.comp hφ.neg.exp

theorem contDiff_ofReal_comp {φ : E → ℝ} {k : WithTop ℕ∞} (hφ : ContDiff ℝ k φ) :
    ContDiff ℝ k (fun y ↦ (φ y : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hφ

theorem contDiff_dDir {v : E} {f : E → ℂ} {k : ℕ} (hf : ContDiff ℝ (k + 1) f) :
    ContDiff ℝ k (dDir v f) := by
  have h : ContDiff ℝ k (fun x ↦ fderiv ℝ f x) := hf.fderiv_right (by norm_cast)
  unfold dDir
  fun_prop

theorem contDiff_dbarDir {v : E} {f : E → ℂ} {k : ℕ} (hf : ContDiff ℝ (k + 1) f) :
    ContDiff ℝ k (dbarDir v f) := by
  have h : ContDiff ℝ k (fun x ↦ fderiv ℝ f x) := hf.fderiv_right (by norm_cast)
  unfold dbarDir
  fun_prop

theorem contDiff_deltaDir {v : E} {φ : E → ℝ} {a : E → ℂ} {k : ℕ}
    (hφ : ContDiff ℝ (k + 1) φ) (ha : ContDiff ℝ (k + 1) a) :
    ContDiff ℝ k (deltaDir v φ a) := by
  have h1 := contDiff_dDir (v := v) ha
  have h2 := contDiff_dDir (v := v) (contDiff_ofReal_comp hφ)
  have h3 : ContDiff ℝ k a := ha.of_le (by norm_cast; omega)
  unfold deltaDir
  exact h1.sub (h2.mul h3)

theorem hasCompactSupport_deltaDir {v : E} {φ : E → ℝ} {a : E → ℂ}
    (ha : HasCompactSupport a) : HasCompactSupport (deltaDir v φ a) := by
  have h1 : HasCompactSupport (dDir v a) := by
    have hf := ha.fderiv (𝕜 := ℝ)
    refine hf.mono' fun x hx ↦ subset_tsupport _ ?_
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h0; apply hx; simp [dDir, h0]
  exact h1.sub ha.mul_left

theorem hasCompactSupport_dbarDir {v : E} {a : E → ℂ}
    (ha : HasCompactSupport a) : HasCompactSupport (dbarDir v a) := by
  have hf := ha.fderiv (𝕜 := ℝ)
  refine hf.mono' fun x hx ↦ subset_tsupport _ ?_
  simp only [Function.mem_support, ne_eq] at hx ⊢
  intro h0; apply hx; simp [dbarDir, h0]

variable [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **`-δ_v` is the formal adjoint of `∂bar_v` in `L²(e^{-φ})`.** -/
theorem integral_deltaDir_mul_conj {v : E} {φ : E → ℝ} {a b : E → ℂ}
    (hφ : ContDiff ℝ 1 φ) (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hab : HasCompactSupport a ∨ HasCompactSupport b) :
    ∫ x, deltaDir v φ a x * conj (b x) * cweight φ x ∂μ =
      - ∫ x, a x * conj (dbarDir v b x) * cweight φ x ∂μ := by
  have hF : ContDiff ℝ 1 (fun y ↦ a y * cweight φ y) := ha.mul (contDiff_cweight hφ)
  have hbc : ContDiff ℝ 1 (fun y ↦ conj (b y)) := Complex.conjCLE.contDiff.comp hb
  have hsupp : HasCompactSupport (fun y ↦ a y * cweight φ y) ∨
      HasCompactSupport (fun y ↦ conj (b y)) := by
    refine hab.imp (fun h ↦ h.mul_right) (fun h ↦ ?_)
    exact h.comp_left (g := conj) (map_zero _)
  have key := integral_mul_dDir_eq_neg (μ := μ) hF hbc hsupp v
  have e1 : (fun x ↦ deltaDir v φ a x * conj (b x) * cweight φ x) =
      fun x ↦ dDir v (fun y ↦ a y * cweight φ y) x * conj (b x) := by
    funext x
    rw [← deltaDir_mul_cweight (hφ.differentiable one_ne_zero x) (ha.differentiable one_ne_zero x)]
    ring
  have e2 : (fun x ↦ a x * conj (dbarDir v b x) * cweight φ x) =
      fun x ↦ a x * cweight φ x * dDir v (fun y ↦ conj (b y)) x := by
    funext x
    rw [dDir_conj (hb.differentiable one_ne_zero x)]
    ring
  rw [e1, e2, key, neg_neg]

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
theorem fderiv_fderiv_apply_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F}
    {x : E} (hg : ContDiffAt ℝ 2 g x) (a w : E) :
    fderiv ℝ (fun y ↦ fderiv ℝ g y w) x a = fderiv ℝ (fderiv ℝ g) x a w := by
  have hDD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have := (hDD.hasFDerivAt).clm_apply (hasFDerivAt_const w x)
  rw [this.fderiv]
  simp

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
theorem fderiv_dDir_apply {g : E → ℂ} {x : E} (hg : ContDiffAt ℝ 2 g x) (v a : E) :
    fderiv ℝ (dDir v g) x a =
      (fderiv ℝ (fderiv ℝ g) x a v - I * fderiv ℝ (fderiv ℝ g) x a (I • v)) / 2 := by
  have hDD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hA : ∀ w, HasFDerivAt (fun y ↦ fderiv ℝ g y w) ((fderiv ℝ (fderiv ℝ g) x).flip w) x :=
    fun w ↦ by simpa using (hDD.hasFDerivAt).clm_apply (hasFDerivAt_const w x)
  have h : HasFDerivAt (fun y ↦ (2 : ℂ)⁻¹ * (fderiv ℝ g y v - I * fderiv ℝ g y (I • v)))
      ((2 : ℂ)⁻¹ • ((fderiv ℝ (fderiv ℝ g) x).flip v -
        I • (fderiv ℝ (fderiv ℝ g) x).flip (I • v))) x :=
    (((hA v).sub ((hA (I • v)).const_mul I)).const_mul (2 : ℂ)⁻¹)
  have e : dDir v g = fun y ↦ (2 : ℂ)⁻¹ * (fderiv ℝ g y v - I * fderiv ℝ g y (I • v)) := by
    funext y; simp only [dDir]; ring
  rw [e, h.fderiv]
  simp only [smul_apply, sub_apply, smul_eq_mul, ContinuousLinearMap.flip_apply]
  ring

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
theorem fderiv_dbarDir_apply {g : E → ℂ} {x : E} (hg : ContDiffAt ℝ 2 g x) (v a : E) :
    fderiv ℝ (dbarDir v g) x a =
      (fderiv ℝ (fderiv ℝ g) x a v + I * fderiv ℝ (fderiv ℝ g) x a (I • v)) / 2 := by
  have hDD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hA : ∀ w, HasFDerivAt (fun y ↦ fderiv ℝ g y w) ((fderiv ℝ (fderiv ℝ g) x).flip w) x :=
    fun w ↦ by simpa using (hDD.hasFDerivAt).clm_apply (hasFDerivAt_const w x)
  have h : HasFDerivAt (fun y ↦ (2 : ℂ)⁻¹ * (fderiv ℝ g y v + I * fderiv ℝ g y (I • v)))
      ((2 : ℂ)⁻¹ • ((fderiv ℝ (fderiv ℝ g) x).flip v +
        I • (fderiv ℝ (fderiv ℝ g) x).flip (I • v))) x :=
    (((hA v).add ((hA (I • v)).const_mul I)).const_mul (2 : ℂ)⁻¹)
  have e : dbarDir v g = fun y ↦ (2 : ℂ)⁻¹ * (fderiv ℝ g y v + I * fderiv ℝ g y (I • v)) := by
    funext y; simp only [dbarDir]; ring
  rw [e, h.fderiv]
  simp only [smul_apply, add_apply, smul_eq_mul, ContinuousLinearMap.flip_apply]
  ring

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
/-- `∂bar_u` and `∂_v` commute on `C²` functions. -/
theorem dbarDir_dDir_comm {u v : E} {g : E → ℂ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    dbarDir u (dDir v g) x = dDir v (dbarDir u g) x := by
  have hsymm := ContDiffAt.isSymmSndFDerivAt hg (by simp)
  simp only [dbarDir, dDir, fderiv_dDir_apply hg, fderiv_dbarDir_apply hg] at *
  rw [hsymm u v, hsymm u (I • v), hsymm (I • u) v, hsymm (I • u) (I • v)]
  ring

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The commutator** `∂bar_u δ_v a = δ_v ∂bar_u a - (∂bar_u ∂_v φ) a`. -/
theorem dbarDir_deltaDir {u v : E} {φ : E → ℝ} {a : E → ℂ} {x : E}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a) :
    dbarDir u (deltaDir v φ a) x =
      deltaDir v φ (dbarDir u a) x - dbarDir u (dDir v (fun y ↦ (φ y : ℂ))) x * a x := by
  have hφc : ContDiff ℝ 2 (fun y ↦ (φ y : ℂ)) := contDiff_ofReal_comp hφ
  have hP : DifferentiableAt ℝ (dDir v (fun y ↦ (φ y : ℂ))) x :=
    (contDiff_dDir (k := 1) hφc).differentiable one_ne_zero x
  have hda : DifferentiableAt ℝ (dDir v a) x :=
    (contDiff_dDir (k := 1) ha).differentiable one_ne_zero x
  have hax : DifferentiableAt ℝ a x := ha.differentiable (by norm_num) x
  have e : deltaDir v φ a = fun y ↦ dDir v a y - dDir v (fun y ↦ (φ y : ℂ)) y * a y := rfl
  rw [e, dbarDir_sub (g := fun y ↦ dDir v (fun y ↦ (φ y : ℂ)) y * a y) hda (hP.mul hax),
    dbarDir_mul hP hax,
    dbarDir_dDir_comm ha.contDiffAt, deltaDir]
  ring

end

end SGPT.Foundations.Analysis.Pending.CauchyGreen
