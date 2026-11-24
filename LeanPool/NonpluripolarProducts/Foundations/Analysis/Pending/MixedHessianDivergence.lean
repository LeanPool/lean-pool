/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.MixedMongeAmpere
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.WirtingerCalculus
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Integration by parts for mixed complex Hessian determinants

For smooth real functions `a, b, g₂, …, gₙ` on `ℂⁿ`, one of `a, b` compactly
supported,
`∫ a · MA(b, g₂, …, gₙ) = ∫ b · MA(a, g₂, …, gₙ)`.
This is the closedness of `ddᶜg₂ ∧ ⋯ ∧ ddᶜgₙ`: expanding the mixed coefficient
in the first slot, its cofactor field is divergence free in both the `∂` and the
`∂bar` directions, because third derivatives are symmetric while the mixed
coefficient is alternating in row and column indices.
-/

@[expose] public section

open Set Filter Complex MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.MixedHessian

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

noncomputable section

variable {n : ℕ}

/-- The mixed coefficient as a double permutation sum, symmetric in rows,
columns and slots. -/
theorem mixedCoefficient_eq_sum_sum (H : Fin n → Matrix (Fin n) (Fin n) ℂ) :
    mixedCoefficient H = ∑ π : Equiv.Perm (Fin n), ∑ ρ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign π : ℂ) * Equiv.Perm.sign ρ) * ∏ i, H i (π i) (ρ i) := by
  have h1 : mixedCoefficient H = ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign τ : ℂ) * ∏ j, H (σ (τ j)) (τ j) j := by
    rw [mixedCoefficient]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    change Matrix.det (Matrix.of fun j k ↦ H (σ j) j k) = _
    rw [Matrix.det_apply]
    simp [Units.smul_def, zsmul_eq_mul]
  rw [h1]
  symm
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [← Equiv.sum_comp ((Equiv.mulLeft σ).trans (Equiv.inv _))]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [← Equiv.prod_comp (σ * τ)]
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Equiv.trans_apply, Equiv.coe_mulLeft,
    mul_inv_rev, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, Equiv.Perm.coe_mul,
    Function.comp_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_apply, mul_eq_mul_right_iff]
  left
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

section Cofactor

variable {m : ℕ}

/-- The cofactor of the first slot of the mixed coefficient: the coefficient of
the `(j, k)` entry of the first matrix. -/
def cofactor (K : Fin m → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (j k : Fin (m + 1)) : ℂ :=
  ∑ π : Equiv.Perm (Fin (m + 1)), ∑ ρ : Equiv.Perm (Fin (m + 1)),
    if π 0 = j ∧ ρ 0 = k then
      ((Equiv.Perm.sign π : ℂ) * Equiv.Perm.sign ρ) * ∏ i, K i (π i.succ) (ρ i.succ)
    else 0

theorem mixedCoefficient_cons (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (K : Fin m → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    mixedCoefficient (Fin.cons A K : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      ∑ j : Fin (m + 1), ∑ k : Fin (m + 1), A j k * cofactor K j k := by
  rw [mixedCoefficient_eq_sum_sum]
  have hterm (π ρ : Equiv.Perm (Fin (m + 1))) :
      ((Equiv.Perm.sign π : ℂ) * Equiv.Perm.sign ρ) *
          ∏ i, (Fin.cons A K : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i (π i) (ρ i) =
        ∑ j : Fin (m + 1), ∑ k : Fin (m + 1), A j k *
          (if π 0 = j ∧ ρ 0 = k then
            ((Equiv.Perm.sign π : ℂ) * Equiv.Perm.sign ρ) * ∏ i, K i (π i.succ) (ρ i.succ)
          else 0) := by
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_ite, mul_zero]
    rw [Finset.sum_eq_single (π 0), Finset.sum_eq_single (ρ 0)]
    · simp only [and_self, ite_true]; ring
    · intro k _ hk; simp [Ne.symm hk]
    · simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      simp [Ne.symm hj]
    · simp
  simp only [hterm, cofactor, Finset.mul_sum]
  calc _ = ∑ π : Equiv.Perm (Fin (m + 1)), ∑ j : Fin (m + 1), ∑ ρ : Equiv.Perm (Fin (m + 1)),
        ∑ k : Fin (m + 1), A j k * (if π 0 = j ∧ ρ 0 = k then
            ((Equiv.Perm.sign π : ℂ) * Equiv.Perm.sign ρ) * ∏ i, K i (π i.succ) (ρ i.succ)
          else 0) := by
          refine Finset.sum_congr rfl fun π _ ↦ ?_
          rw [Finset.sum_comm]
    _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          symm
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun π _ ↦ ?_
          rw [Finset.sum_comm]

/-- Row antisymmetry of the cofactor against a tensor symmetric in its first
two indices. -/
theorem sum_sign_row_symm_eq_zero (K : Fin m → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (T : Fin m → Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → ℂ)
    (hT : ∀ l a b c, T l a b c = T l b a c) (ρ : Equiv.Perm (Fin (m + 1))) (l : Fin m) :
    ∑ π : Equiv.Perm (Fin (m + 1)), (Equiv.Perm.sign π : ℂ) *
      (T l (π 0) (π l.succ) (ρ l.succ) *
        ∏ i ∈ Finset.univ.erase l, K i (π i.succ) (ρ i.succ)) = 0 := by
  set S := ∑ π : Equiv.Perm (Fin (m + 1)), (Equiv.Perm.sign π : ℂ) *
      (T l (π 0) (π l.succ) (ρ l.succ) *
        ∏ i ∈ Finset.univ.erase l, K i (π i.succ) (ρ i.succ)) with hS
  have hne : (0 : Fin (m + 1)) ≠ l.succ := (Fin.succ_ne_zero l).symm
  have h : S = -S := by
    conv_lhs => rw [hS, ← Equiv.sum_comp (Equiv.mulRight (Equiv.swap 0 l.succ))]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun π _ ↦ ?_
    have hprod : ∏ i ∈ Finset.univ.erase l, K i (π (Equiv.swap 0 l.succ i.succ)) (ρ i.succ) =
        ∏ i ∈ Finset.univ.erase l, K i (π i.succ) (ρ i.succ) := by
      refine Finset.prod_congr rfl fun i hi ↦ ?_
      have hil : i ≠ l := Finset.ne_of_mem_erase hi
      rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i)
        (fun h ↦ hil (Fin.succ_injective _ h))]
    simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne,
      Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [hprod, hT]
    push_cast
    ring
  have h2 : (2 : ℂ) * S = 0 := by linear_combination h
  simpa using h2

/-- Column antisymmetry of the cofactor against a tensor symmetric in its first
and third indices. -/
theorem sum_sign_col_symm_eq_zero (K : Fin m → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (T : Fin m → Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → ℂ)
    (hT : ∀ l a b c, T l a b c = T l c b a) (π : Equiv.Perm (Fin (m + 1))) (l : Fin m) :
    ∑ ρ : Equiv.Perm (Fin (m + 1)), (Equiv.Perm.sign ρ : ℂ) *
      (T l (ρ 0) (π l.succ) (ρ l.succ) *
        ∏ i ∈ Finset.univ.erase l, K i (π i.succ) (ρ i.succ)) = 0 :=
  sum_sign_row_symm_eq_zero (fun i ↦ (K i).transpose) (fun l a b c ↦ T l a c b)
    (fun l a b c ↦ hT l a c b) π l

end Cofactor

section Wirtinger

open CauchyGreen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A directional first-order operator `(Df(v) + c·Df(Iv))/2`; `c = -i` gives
`∂/∂w` and `c = i` gives `∂/∂wBar` along the complex line spanned by `v`. -/
def wirt (c : ℂ) (v : E) (f : E → ℂ) (x : E) : ℂ :=
  (fderiv ℝ f x v + c * fderiv ℝ f x (I • v)) / 2

/-- The Wirtinger derivative `∂/∂w` along the complex line spanned by `v`. -/
abbrev dDir (v : E) (f : E → ℂ) (x : E) : ℂ := wirt (-I) v f x

theorem dbarDir_eq_wirt (v : E) (f : E → ℂ) (x : E) : dbarDir v f x = wirt I v f x := rfl

theorem contDiff_wirt {c : ℂ} {v : E} {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (wirt c v f) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) le_rfl
  unfold wirt
  fun_prop

theorem wirt_add {c : ℂ} {v : E} {f g : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    wirt c v (fun y ↦ f y + g y) x = wirt c v f x + wirt c v g x := by
  simp only [wirt, fderiv_fun_add hf hg, add_apply]
  ring

theorem wirt_mul {c : ℂ} {v : E} {f g : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    wirt c v (fun y ↦ f y * g y) x = wirt c v f x * g x + f x * wirt c v g x := by
  simp only [wirt, fderiv_fun_mul hf hg, add_apply,
    smul_apply, smul_eq_mul]
  ring

theorem wirt_const_mul {c : ℂ} {v : E} (a : ℂ) {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    wirt c v (fun y ↦ a * f y) x = a * wirt c v f x := by
  simp only [wirt, fderiv_const_mul hf, smul_apply, smul_eq_mul]
  ring

theorem wirt_sum {ι : Type*} (s : Finset ι) {c : ℂ} {v : E} {f : ι → E → ℂ} {x : E}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    wirt c v (fun y ↦ ∑ i ∈ s, f i y) x = ∑ i ∈ s, wirt c v (f i) x := by
  simp only [wirt, fderiv_fun_sum hf, sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]

theorem wirt_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {c : ℂ} {v : E}
    {f : ι → E → ℂ} {x : E} (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    wirt c v (fun y ↦ ∏ i ∈ s, f i y) x =
      ∑ l ∈ s, wirt c v (f l) x * ∏ i ∈ s.erase l, f i x := by
  have h := (HasFDerivAt.finsetProd fun i hi ↦ (hf i hi).hasFDerivAt).fderiv
  simp only [wirt, h, sum_apply, smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

/-- Two directional operators commute on a `C²` function. -/
theorem wirt_wirt_comm {c d : ℂ} {u v : E} {g : E → ℂ} {x : E}
    (hg : ContDiffAt ℝ 2 g x) :
    wirt c u (wirt d v g) x = wirt d v (wirt c u g) x := by
  have hsymm := ContDiffAt.isSymmSndFDerivAt hg (by simp)
  have hDD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have happ (w : E) : HasFDerivAt (fun y ↦ fderiv ℝ g y w)
      ((fderiv ℝ (fderiv ℝ g) x).flip w) x := by
    have := (hDD.hasFDerivAt).clm_apply (hasFDerivAt_const w x)
    simpa using this
  have hdir (e : ℂ) (w : E) : HasFDerivAt (wirt e w g)
      ((2 : ℂ)⁻¹ • ((fderiv ℝ (fderiv ℝ g) x).flip w +
        e • (fderiv ℝ (fderiv ℝ g) x).flip (I • w))) x := by
    have h := ((happ w).add ((happ (I • w)).const_smul e)).const_smul (2 : ℂ)⁻¹
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
    simp only [wirt, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  simp only [wirt, (hdir d v).fderiv, (hdir c u).fderiv]
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  rw [hsymm u v, hsymm u (I • v), hsymm (I • u) v, hsymm (I • u) (I • v)]
  ring

theorem integral_mul_fderiv_eq_neg_of_hasCompactSupport [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] {f g : E → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport f) (v : E) :
    ∫ x, f x * fderiv ℝ g x v ∂μ = -∫ x, fderiv ℝ f x v * g x ∂μ := by
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous g := hg.continuous
  have hf' : Continuous fun x ↦ fderiv ℝ f x v :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hg' : Continuous fun x ↦ fderiv ℝ g x v :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ ↦ hf.differentiable one_ne_zero x) (fun x _ ↦ hg.differentiable one_ne_zero x)
  · exact (hf'.mul hgc).integrable_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) v).mul_right
  · exact (hfc.mul hg').integrable_of_hasCompactSupport hc.mul_right
  · exact (hfc.mul hgc).integrable_of_hasCompactSupport hc.mul_right

/-- Integration by parts for a directional operator, the first factor having
compact support. -/
theorem integral_mul_wirt_eq_neg [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] {f g : E → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport f) (c : ℂ) (v : E) :
    ∫ x, f x * wirt c v g x ∂μ = -∫ x, wirt c v f x * g x ∂μ := by
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous g := hg.continuous
  have hf' (w : E) : Continuous fun x ↦ fderiv ℝ f x w :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hg' (w : E) : Continuous fun x ↦ fderiv ℝ g x w :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have i1 (w : E) : Integrable (fun x ↦ f x * fderiv ℝ g x w) μ :=
    (hfc.mul (hg' w)).integrable_of_hasCompactSupport hc.mul_right
  have i2 (w : E) : Integrable (fun x ↦ fderiv ℝ f x w * g x) μ :=
    ((hf' w).mul hgc).integrable_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) w).mul_right
  have e1 : (fun x ↦ f x * wirt c v g x) =
      fun x ↦ (2 : ℂ)⁻¹ * (f x * fderiv ℝ g x v + c * (f x * fderiv ℝ g x (I • v))) := by
    funext x; simp only [wirt]; ring
  have e2 : (fun x ↦ wirt c v f x * g x) =
      fun x ↦ (2 : ℂ)⁻¹ * (fderiv ℝ f x v * g x + c * (fderiv ℝ f x (I • v) * g x)) := by
    funext x; simp only [wirt]; ring
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_add (i1 v) ((i1 _).const_mul c),
    integral_add (i2 v) ((i2 _).const_mul c), integral_const_mul, integral_const_mul,
    integral_mul_fderiv_eq_neg_of_hasCompactSupport μ hf hg hc,
    integral_mul_fderiv_eq_neg_of_hasCompactSupport μ hf hg hc]
  ring

/-- Two directional operators applied to a real `C²` function, in terms of its
real Hessian. -/
theorem wirt_wirt_ofReal {c d : ℂ} {v w : E} {g : E → ℝ} {z : E} (hg : ContDiffAt ℝ 2 g z) :
    wirt c v (wirt d w (fun y ↦ (g y : ℂ))) z =
      ((realHessian g z v w : ℂ) + d * realHessian g z v (I • w) +
        c * realHessian g z (I • v) w + c * d * realHessian g z (I • v) (I • w)) / 4 := by
  have hD : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hDD : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have happ (u : E) : HasFDerivAt (fun y ↦ ((fderiv ℝ g y u : ℝ) : ℂ))
      (ofRealCLM.comp ((fderiv ℝ (fderiv ℝ g) z).flip u)) z := by
    have := (hDD.hasFDerivAt).clm_apply (hasFDerivAt_const u z)
    exact ofRealCLM.hasFDerivAt.comp z (by simpa using this)
  have hev : wirt d w (fun y ↦ (g y : ℂ)) =ᶠ[𝓝 z]
      fun y ↦ (2 : ℂ)⁻¹ * (((fderiv ℝ g y w : ℝ) : ℂ) + d * ((fderiv ℝ g y (I • w) : ℝ) : ℂ)) := by
    filter_upwards [hD] with y hy
    have hc : fderiv ℝ (fun y ↦ (g y : ℂ)) y = ofRealCLM.comp (fderiv ℝ g y) :=
      (ofRealCLM.hasFDerivAt.comp y hy.hasFDerivAt).fderiv
    simp only [wirt, hc, ContinuousLinearMap.comp_apply, ofRealCLM_apply]
    ring
  have hder : HasFDerivAt (wirt d w (fun y ↦ (g y : ℂ)))
      ((2 : ℂ)⁻¹ • (ofRealCLM.comp ((fderiv ℝ (fderiv ℝ g) z).flip w) +
        d • ofRealCLM.comp ((fderiv ℝ (fderiv ℝ g) z).flip (I • w)))) z := by
    have h := ((happ w).add ((happ (I • w)).const_mul d)).const_mul (2 : ℂ)⁻¹
    refine (h.congr_of_eventuallyEq hev).congr_fderiv ?_
    ext u
    simp
  simp only [wirt, hder.fderiv, realHessian_eq_fderiv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ofRealCLM_apply, smul_eq_mul]
  ring

theorem integral_wirt_eq_zero [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {F : E → ℂ} (hF : ContDiff ℝ 1 F)
    (hc : HasCompactSupport F) (c : ℂ) (v : E) : ∫ x, wirt c v F x ∂μ = 0 := by
  have h := integral_mul_wirt_eq_neg μ hF (contDiff_const (c := (1 : ℂ))) hc c v
  have h0 : ∀ x, wirt c v (fun _ : E ↦ (1 : ℂ)) x = 0 := fun x ↦ by simp [wirt]
  simp only [h0, mul_zero, integral_zero, mul_one] at h
  linear_combination h

theorem HasCompactSupport.wirt {F : E → ℂ} (hc : HasCompactSupport F) (c : ℂ) (v : E) :
    HasCompactSupport (wirt c v F) := by
  refine hc.mono' fun x hx ↦ ?_
  by_contra h
  have h0 : fderiv ℝ F x = 0 := by
    by_contra h'
    exact h (support_fderiv_subset ℝ (Function.mem_support.mpr h'))
  exact hx (by simp [SGPT.Foundations.Analysis.Pending.MixedHessian.wirt, h0])

end Wirtinger

section Hessian

/-- The complex Hessian entry is `∂ⱼ ∂barₖ g`. -/
theorem complexHessian_eq_wirt {g : ComplexModel n → ℝ} {z : ComplexModel n}
    (hg : ContDiffAt ℝ 2 g z) (j k : Fin n) :
    complexHessian g z j k =
      wirt (-I) (coordinateVector j) (wirt I (coordinateVector k) (fun y ↦ (g y : ℂ))) z := by
  rw [wirt_wirt_ofReal hg, complexHessian]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- The complex Hessian entry is also `∂barₖ ∂ⱼ g`. -/
theorem complexHessian_eq_wirt' {g : ComplexModel n → ℝ} {z : ComplexModel n}
    (hg : ContDiffAt ℝ 2 g z) (j k : Fin n) :
    complexHessian g z j k =
      wirt I (coordinateVector k) (wirt (-I) (coordinateVector j) (fun y ↦ (g y : ℂ))) z := by
  rw [complexHessian_eq_wirt hg, wirt_wirt_comm]
  exact ofRealCLM.contDiff.contDiffAt.comp z hg

theorem contDiff_complexHessian_apply {g : ComplexModel n → ℝ} (hg : ContDiff ℝ ∞ g)
    (j k : Fin n) : ContDiff ℝ ∞ (fun z ↦ complexHessian g z j k) := by
  have hG : ContDiff ℝ ∞ (fun y ↦ (g y : ℂ)) := ofRealCLM.contDiff.comp hg
  have h := contDiff_wirt (c := -I) (v := coordinateVector j) (contDiff_wirt (c := I)
    (v := coordinateVector k) hG)
  have e : (fun z ↦ complexHessian g z j k) = wirt (-I) (coordinateVector j)
      (wirt I (coordinateVector k) (fun y ↦ (g y : ℂ))) :=
    funext fun z ↦ complexHessian_eq_wirt (hg.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) j k
  rw [e]
  exact h

end Hessian

section Divergence

variable {m : ℕ} (g : Fin m → ComplexModel (m + 1) → ℝ)

/-- The cofactor field of `(ddᶜ g₁, …, ddᶜ gₘ)` in the first slot. -/
def cofactorField (j k : Fin (m + 1)) (z : ComplexModel (m + 1)) : ℂ :=
  cofactor (fun i ↦ complexHessian (g i) z) j k

theorem wirt_ite_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (P : Prop)
    [Decidable P] {c : ℂ} {v : E} {f : E → ℂ} {x : E} :
    wirt c v (fun y ↦ if P then f y else 0) x = if P then wirt c v f x else 0 := by
  by_cases h : P <;> simp [h, wirt]

variable {g}

theorem wirt_cofactorField (hg : ∀ i, ContDiff ℝ ∞ (g i)) (c : ℂ) (v : ComplexModel (m + 1))
    (j k : Fin (m + 1)) (z : ComplexModel (m + 1)) :
    wirt c v (cofactorField g j k) z =
      ∑ π : Equiv.Perm (Fin (m + 1)), ∑ ρ : Equiv.Perm (Fin (m + 1)),
        if π 0 = j ∧ ρ 0 = k then
          ((Equiv.Perm.sign π : ℂ) * Equiv.Perm.sign ρ) *
            ∑ l, wirt c v (fun y ↦ complexHessian (g l) y (π l.succ) (ρ l.succ)) z *
              ∏ i ∈ Finset.univ.erase l, complexHessian (g i) z (π i.succ) (ρ i.succ)
        else 0 := by
  have hH (i : Fin m) (a b : Fin (m + 1)) :
      Differentiable ℝ (fun y ↦ complexHessian (g i) y a b) :=
    (contDiff_complexHessian_apply (hg i) a b).differentiable (by simp)
  have hprod (π ρ : Equiv.Perm (Fin (m + 1))) :
      Differentiable ℝ (fun y ↦ ∏ i, complexHessian (g i) y (π i.succ) (ρ i.succ)) :=
    fun y ↦ (HasFDerivAt.finsetProd fun i _ ↦ (hH i _ _ y).hasFDerivAt).differentiableAt
  unfold cofactorField cofactor
  rw [wirt_sum _ fun π _ ↦ ?_]
  · refine Finset.sum_congr rfl fun π _ ↦ ?_
    rw [wirt_sum _ fun ρ _ ↦ ?_]
    · refine Finset.sum_congr rfl fun ρ _ ↦ ?_
      rw [wirt_ite_zero]
      split_ifs
      · rw [wirt_const_mul _ (hprod π ρ z), wirt_prod _ fun i _ ↦ hH i _ _ z]
      · rfl
    · split_ifs
      · exact (hprod π ρ z).const_mul _
      · exact differentiableAt_const _
  · refine DifferentiableAt.fun_sum fun ρ _ ↦ ?_
    split_ifs
    · exact (hprod π ρ z).const_mul _
    · exact differentiableAt_const _

theorem hessianEntry_eq_wirt (hg : ∀ i, ContDiff ℝ ∞ (g i)) (l : Fin m) (b c : Fin (m + 1)) :
    (fun y ↦ complexHessian (g l) y b c) = wirt (-I) (coordinateVector b)
      (wirt I (coordinateVector c) (fun y ↦ (g l y : ℂ))) :=
  funext fun _ ↦ complexHessian_eq_wirt ((hg l).contDiffAt.of_le
    (WithTop.coe_le_coe.mpr le_top)) b c

theorem hessianEntry_eq_wirt' (hg : ∀ i, ContDiff ℝ ∞ (g i)) (l : Fin m) (b c : Fin (m + 1)) :
    (fun y ↦ complexHessian (g l) y b c) = wirt I (coordinateVector c)
      (wirt (-I) (coordinateVector b) (fun y ↦ (g l y : ℂ))) :=
  funext fun _ ↦ complexHessian_eq_wirt' ((hg l).contDiffAt.of_le
    (WithTop.coe_le_coe.mpr le_top)) b c

/-- The cofactor field is `∂`-divergence free in its row index. -/
theorem sum_dDir_cofactorField (hg : ∀ i, ContDiff ℝ ∞ (g i)) (k : Fin (m + 1))
    (z : ComplexModel (m + 1)) :
    ∑ j, wirt (-I) (coordinateVector j) (cofactorField g j k) z = 0 := by
  set T : Fin m → Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → ℂ := fun l a b c ↦
    wirt (-I) (coordinateVector a) (fun y ↦ complexHessian (g l) y b c) z with hTdef
  have hT : ∀ l a b c, T l a b c = T l b a c := by
    intro l a b c
    have hG : ContDiff ℝ ∞ (wirt I (coordinateVector c) (fun y ↦ (g l y : ℂ))) :=
      contDiff_wirt (ofRealCLM.contDiff.comp (hg l))
    simp only [hTdef, hessianEntry_eq_wirt hg]
    exact wirt_wirt_comm (hG.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  simp_rw [wirt_cofactorField hg, ite_and]
  rw [Finset.sum_comm]
  have hstep (π : Equiv.Perm (Fin (m + 1))) :=
    Finset.sum_comm (s := (Finset.univ : Finset (Fin (m + 1))))
    (t := (Finset.univ : Finset (Equiv.Perm (Fin (m + 1)))))
    (f := fun j ρ ↦ if π 0 = j then (if ρ 0 = k then
          ((Equiv.Perm.sign π : ℂ) * Equiv.Perm.sign ρ) *
            ∑ l, wirt (-I) (coordinateVector j)
              (fun y ↦ complexHessian (g l) y (π l.succ) (ρ l.succ)) z *
              ∏ i ∈ Finset.univ.erase l, complexHessian (g i) z (π i.succ) (ρ i.succ)
        else 0) else 0)
  simp only [hstep, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun ρ _ ↦ ?_
  split_ifs
  · have hrow (l : Fin m) :=
      sum_sign_row_symm_eq_zero (fun i ↦ complexHessian (g i) z) T hT ρ l
    calc _ = ∑ π : Equiv.Perm (Fin (m + 1)), ∑ l, (Equiv.Perm.sign ρ : ℂ) *
          ((Equiv.Perm.sign π : ℂ) * (T l (π 0) (π l.succ) (ρ l.succ) *
            ∏ i ∈ Finset.univ.erase l, complexHessian (g i) z (π i.succ) (ρ i.succ))) := by
          refine Finset.sum_congr rfl fun π _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ ↦ ?_
          simp only [hTdef]
          ring
      _ = 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_eq_zero fun l _ ↦ ?_
          rw [← Finset.mul_sum, hrow l, mul_zero]
  · simp

/-- The cofactor field is `∂bar`-divergence free in its column index. -/
theorem sum_dbarDir_cofactorField (hg : ∀ i, ContDiff ℝ ∞ (g i)) (j : Fin (m + 1))
    (z : ComplexModel (m + 1)) :
    ∑ k, wirt I (coordinateVector k) (cofactorField g j k) z = 0 := by
  set T : Fin m → Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → ℂ := fun l a b c ↦
    wirt I (coordinateVector a) (fun y ↦ complexHessian (g l) y b c) z with hTdef
  have hT : ∀ l a b c, T l a b c = T l c b a := by
    intro l a b c
    have hG : ContDiff ℝ ∞ (wirt (-I) (coordinateVector b) (fun y ↦ (g l y : ℂ))) :=
      contDiff_wirt (ofRealCLM.contDiff.comp (hg l))
    simp only [hTdef, hessianEntry_eq_wirt' hg]
    exact wirt_wirt_comm (hG.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  simp_rw [wirt_cofactorField hg, ite_and]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun π _ ↦ ?_
  by_cases hπ : π 0 = j
  · simp only [hπ, ite_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hcol (l : Fin m) :=
      sum_sign_col_symm_eq_zero (fun i ↦ complexHessian (g i) z) T hT π l
    calc _ = ∑ ρ : Equiv.Perm (Fin (m + 1)), ∑ l, (Equiv.Perm.sign π : ℂ) *
          ((Equiv.Perm.sign ρ : ℂ) * (T l (ρ 0) (π l.succ) (ρ l.succ) *
            ∏ i ∈ Finset.univ.erase l, complexHessian (g i) z (π i.succ) (ρ i.succ))) := by
          refine Finset.sum_congr rfl fun ρ _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ ↦ ?_
          simp only [hTdef]
          ring
      _ = 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_eq_zero fun l _ ↦ ?_
          rw [← Finset.mul_sum, hcol l, mul_zero]
  · simp [hπ]

theorem contDiff_cofactorField (hg : ∀ i, ContDiff ℝ ∞ (g i)) (j k : Fin (m + 1)) :
    ContDiff ℝ ∞ (cofactorField g j k) := by
  have hH (i : Fin m) (a b : Fin (m + 1)) :
      ContDiff ℝ ∞ (fun y ↦ complexHessian (g i) y a b) :=
    contDiff_complexHessian_apply (hg i) a b
  unfold cofactorField cofactor
  refine ContDiff.sum fun π _ ↦ ContDiff.sum fun ρ _ ↦ ?_
  split_ifs
  · exact contDiff_const.mul (contDiff_prod fun i _ ↦ hH i _ _)
  · exact contDiff_const

theorem complexHessian_eq_zero_of_notMem_tsupport {a : ComplexModel n → ℝ}
    {z : ComplexModel n} (hz : z ∉ tsupport a) : complexHessian a z = 0 := by
  have h : iteratedFDeriv ℝ 2 a z = 0 := by
    by_contra h
    exact hz (support_iteratedFDeriv_subset 2 (Function.mem_support.mpr h))
  ext j k
  simp [complexHessian, realHessian, h]

/-- Pointwise divergence form of the symmetric difference of the two
integrands. -/
theorem mixedCoefficient_swap_eq_sum_wirt (hg : ∀ i, ContDiff ℝ ∞ (g i))
    {a b : ComplexModel (m + 1) → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (z : ComplexModel (m + 1)) :
    (a z : ℂ) * mixedCoefficient (Fin.cons (complexHessian b z) (fun i ↦ complexHessian (g i) z) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) -
      (b z : ℂ) * mixedCoefficient (Fin.cons (complexHessian a z) (fun i ↦ complexHessian (g i) z)
        :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      ∑ j, ∑ k, (wirt (-I) (coordinateVector j) (fun y ↦ (a y : ℂ) *
          (wirt I (coordinateVector k) (fun y ↦ (b y : ℂ)) y * cofactorField g j k y)) z -
        wirt I (coordinateVector k) (fun y ↦ wirt (-I) (coordinateVector j) (fun y ↦ (a y : ℂ)) y *
          (cofactorField g j k y * (b y : ℂ))) z) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hA : ContDiff ℝ ∞ (fun y ↦ (a y : ℂ)) := ofRealCLM.contDiff.comp ha
  have hB : ContDiff ℝ ∞ (fun y ↦ (b y : ℂ)) := ofRealCLM.contDiff.comp hb
  have hd {F : ComplexModel (m + 1) → ℂ} (hF : ContDiff ℝ ∞ F) : DifferentiableAt ℝ F z :=
    hF.differentiable (by simp) z
  have hterm (j k : Fin (m + 1)) :
      wirt (-I) (coordinateVector j) (fun y ↦ (a y : ℂ) *
          (wirt I (coordinateVector k) (fun y ↦ (b y : ℂ)) y * cofactorField g j k y)) z -
        wirt I (coordinateVector k) (fun y ↦ wirt (-I) (coordinateVector j) (fun y ↦ (a y : ℂ)) y *
          (cofactorField g j k y * (b y : ℂ))) z =
      ((a z : ℂ) * complexHessian b z j k * cofactorField g j k z -
          (b z : ℂ) * complexHessian a z j k * cofactorField g j k z) +
        (a z : ℂ) * wirt I (coordinateVector k) (fun y ↦ (b y : ℂ)) z *
          wirt (-I) (coordinateVector j) (cofactorField g j k) z -
        wirt (-I) (coordinateVector j) (fun y ↦ (a y : ℂ)) z * (b z : ℂ) *
          wirt I (coordinateVector k) (cofactorField g j k) z := by
    have hW := contDiff_wirt (c := I) (v := coordinateVector k) hB
    have hDA := contDiff_wirt (c := -I) (v := coordinateVector j) hA
    have hC := contDiff_cofactorField hg j k
    rw [wirt_mul (hd hA) (hd (hW.mul hC)), wirt_mul (hd hW) (hd hC),
      wirt_mul (hd hDA) (hd (hC.mul hB)), wirt_mul (hd hC) (hd hB),
      complexHessian_eq_wirt ((hb.contDiffAt).of_le h2),
      complexHessian_eq_wirt' ((ha.contDiffAt).of_le h2)]
    ring
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, mixedCoefficient_cons,
    Finset.mul_sum]
  have e1 : ∑ j, ∑ k, (a z : ℂ) * wirt I (coordinateVector k) (fun y ↦ (b y : ℂ)) z *
      wirt (-I) (coordinateVector j) (cofactorField g j k) z = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [← Finset.mul_sum, sum_dDir_cofactorField hg, mul_zero]
  have e2 : ∑ j, ∑ k, wirt (-I) (coordinateVector j) (fun y ↦ (a y : ℂ)) z * (b z : ℂ) *
      wirt I (coordinateVector k) (cofactorField g j k) z = 0 := by
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [← Finset.mul_sum, sum_dbarDir_cofactorField hg, mul_zero]
  rw [e1, e2]
  simp only [add_zero, sub_zero]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_ <;>
    simp only [cofactorField] <;> ring

theorem continuous_mixedCoefficient_cons (hg : ∀ i, ContDiff ℝ ∞ (g i))
    {a : ComplexModel (m + 1) → ℝ} (ha : ContDiff ℝ ∞ a) :
    Continuous fun z ↦ mixedCoefficient (Fin.cons (complexHessian a z)
      (fun i ↦ complexHessian (g i) z) : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
  simp only [mixedCoefficient_cons]
  refine continuous_finsetSum _ fun j _ ↦ continuous_finsetSum _ fun k _ ↦ ?_
  exact (contDiff_complexHessian_apply ha j k).continuous.mul
    ((contDiff_cofactorField hg j k).continuous)

theorem mixedCoefficient_cons_eq_zero_of_notMem_tsupport
    {a : ComplexModel (m + 1) → ℝ} {z : ComplexModel (m + 1)} (hz : z ∉ tsupport a) :
    mixedCoefficient (Fin.cons (complexHessian a z) (fun i ↦ complexHessian (g i) z) :
      Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = 0 := by
  rw [mixedCoefficient_cons, complexHessian_eq_zero_of_notMem_tsupport hz]
  simp only [Matrix.zero_apply, zero_mul, Finset.sum_const_zero]

/-- **Integration by parts for mixed complex Hessians.** For smooth real
functions with `a` compactly supported,
`∫ a · C(ddᶜb, ddᶜg₁, …) = ∫ b · C(ddᶜa, ddᶜg₁, …)`. -/
theorem integral_mul_mixedCoefficient_swap (hg : ∀ i, ContDiff ℝ ∞ (g i))
    {a b : ComplexModel (m + 1) → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hac : HasCompactSupport a) :
    ∫ z, (a z : ℂ) * mixedCoefficient (Fin.cons (complexHessian b z)
        (fun i ↦ complexHessian (g i) z) : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      ∫ z, (b z : ℂ) * mixedCoefficient (Fin.cons (complexHessian a z)
        (fun i ↦ complexHessian (g i) z) :
          Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
  have hA : ContDiff ℝ ∞ (fun y ↦ (a y : ℂ)) := ofRealCLM.contDiff.comp ha
  have hB : ContDiff ℝ ∞ (fun y ↦ (b y : ℂ)) := ofRealCLM.contDiff.comp hb
  have hAc : HasCompactSupport (fun y ↦ (a y : ℂ)) := hac.comp_left Complex.ofReal_zero
  have hint1 : Integrable (fun z ↦ (a z : ℂ) * mixedCoefficient (Fin.cons (complexHessian b z)
      (fun i ↦ complexHessian (g i) z) : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) :=
    (hA.continuous.mul (continuous_mixedCoefficient_cons hg hb)).integrable_of_hasCompactSupport
      hAc.mul_right
  have hint2 : Integrable (fun z ↦ (b z : ℂ) * mixedCoefficient (Fin.cons (complexHessian a z)
      (fun i ↦ complexHessian (g i) z) : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) := by
    refine (hB.continuous.mul
      (continuous_mixedCoefficient_cons hg ha)).integrable_of_hasCompactSupport
        (hac.mono' fun z hz ↦ ?_)
    by_contra h
    rw [Function.mem_support, Pi.mul_apply, mixedCoefficient_cons_eq_zero_of_notMem_tsupport h,
      mul_zero] at hz
    exact hz rfl
  have hW (k : Fin (m + 1)) := contDiff_wirt (c := I) (v := coordinateVector k) hB
  have hDA (j : Fin (m + 1)) := contDiff_wirt (c := -I) (v := coordinateVector j) hA
  have hC (j k : Fin (m + 1)) := contDiff_cofactorField hg j k
  have hF1 (j k : Fin (m + 1)) :
      HasCompactSupport (fun y ↦ (a y : ℂ) *
        (wirt I (coordinateVector k) (fun y ↦ (b y : ℂ)) y * cofactorField g j k y)) :=
    hAc.mul_right
  have hF2 (j k : Fin (m + 1)) :
      HasCompactSupport (fun y ↦ wirt (-I) (coordinateVector j) (fun y ↦ (a y : ℂ)) y *
        (cofactorField g j k y * (b y : ℂ))) :=
    (HasCompactSupport.wirt hAc _ _).mul_right
  have hsm1 (j k : Fin (m + 1)) : ContDiff ℝ ∞ (fun y ↦ (a y : ℂ) *
      (wirt I (coordinateVector k) (fun y ↦ (b y : ℂ)) y * cofactorField g j k y)) :=
    hA.mul ((hW k).mul (hC j k))
  have hsm2 (j k : Fin (m + 1)) : ContDiff ℝ ∞ (fun y ↦
      wirt (-I) (coordinateVector j) (fun y ↦ (a y : ℂ)) y *
        (cofactorField g j k y * (b y : ℂ))) :=
    (hDA j).mul ((hC j k).mul hB)
  have hzero : ∫ z, ((a z : ℂ) * mixedCoefficient (Fin.cons (complexHessian b z)
        (fun i ↦ complexHessian (g i) z) : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) -
      (b z : ℂ) * mixedCoefficient (Fin.cons (complexHessian a z)
        (fun i ↦ complexHessian (g i) z) :
          Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) = 0 := by
    simp_rw [mixedCoefficient_swap_eq_sum_wirt hg ha hb]
    have hi (j k : Fin (m + 1)) (c : ℂ) (v : ComplexModel (m + 1)) {F : ComplexModel (m + 1) → ℂ}
        (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) : Integrable (wirt c v F) :=
      (contDiff_wirt hF).continuous.integrable_of_hasCompactSupport (HasCompactSupport.wirt hFc c
        v)
    have hik (j k : Fin (m + 1)) : Integrable (fun z ↦
        wirt (-I) (coordinateVector j) (fun y ↦ (a y : ℂ) *
          (wirt I (coordinateVector k) (fun y ↦ (b y : ℂ)) y * cofactorField g j k y)) z -
        wirt I (coordinateVector k) (fun y ↦ wirt (-I) (coordinateVector j) (fun y ↦ (a y : ℂ)) y *
          (cofactorField g j k y * (b y : ℂ))) z) :=
      (hi j k _ _ (hsm1 j k) (hF1 j k)).sub (hi j k _ _ (hsm2 j k) (hF2 j k))
    rw [integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦ hik j k]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [integral_finsetSum _ fun k _ ↦ hik j k]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [integral_sub (hi j k _ _ (hsm1 j k) (hF1 j k)) (hi j k _ _ (hsm2 j k) (hF2 j k)),
      integral_wirt_eq_zero _ ((hsm1 j k).of_le (by simp)) (hF1 j k),
      integral_wirt_eq_zero _ ((hsm2 j k).of_le (by simp)) (hF2 j k), sub_zero]
  rw [integral_sub hint1 hint2] at hzero
  exact sub_eq_zero.mp hzero

end Divergence

end

end SGPT.Foundations.Analysis.Pending.MixedHessian
