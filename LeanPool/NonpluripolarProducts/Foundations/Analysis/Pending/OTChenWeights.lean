/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HormanderInterface
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HormanderCutoffWeights

/-!
# Chen's weights for the Ohsawa--Takegoshi theorem

One-variable calculus behind B.-Y. Chen's proof of the Ohsawa--Takegoshi theorem from
Hörmander's estimate (arXiv:1105.2430).

* Functions of `s = |z_i|²`: their Levi form is `(G'(s) + s G''(s)) |ξ_i|²` and their
  `∂bar_{e_j}` derivative is `G'(s) z_i` for `j = i` and `0` otherwise.
* Chen's functions of `s`, for parameters `R, ε`: `L = 1 + log (2R²) - log (s + ε²)`
  (this is `-ρ`), `η = L + log L`, `ψ = -log η`, and the algebraic inequalities between
  `ψ'`, the Levi coefficient `a = ψ' + s ψ''` and `L`.
-/

@[expose] public section

open Set Filter Complex
open scoped Topology ContDiff ComplexConjugate

namespace SGPT.Foundations.Analysis.Pending.OTChen

noncomputable section

open FirstPass CauchyGreen Hormander

variable {n : ℕ}

/-! ### Functions of `|z_i|²` -/

/-- The squared modulus of the `i`-th coordinate. -/
def coordSq (i : Fin n) (z : ComplexModel n) : ℝ := ‖z i‖ ^ 2

/-- The `i`-th coordinate as a real continuous linear map. -/
def coordCLM (i : Fin n) : ComplexModel n →L[ℝ] ℂ :=
  ((EuclideanSpace.proj (𝕜 := ℂ) i : ComplexModel n →L[ℂ] ℂ)).restrictScalars ℝ

@[simp] theorem coordCLM_apply (i : Fin n) (z : ComplexModel n) : coordCLM i z = z i := rfl

theorem coordSq_eq (i : Fin n) : coordSq i = fun z ↦ ‖(0 : ℂ) + coordCLM i z‖ ^ 2 := by
  funext z; simp [coordSq]

theorem contDiff_coordSq (i : Fin n) : ContDiff ℝ ∞ (coordSq i) := by
  rw [coordSq_eq]
  exact (contDiff_norm_sq ℝ).comp (contDiff_const.add (coordCLM i).contDiff)

theorem fderiv_coordSq_apply (i : Fin n) (x a : ComplexModel n) :
    fderiv ℝ (coordSq i) x a = 2 * inner ℝ (x i) (a i) := by
  have h := (hasStrictFDerivAt_norm_sq (x i)).hasFDerivAt.comp x (coordCLM i).hasFDerivAt
  have he : coordSq i = (fun w : ℂ ↦ ‖w‖ ^ 2) ∘ coordCLM i := rfl
  rw [he, h.fderiv]
  simp
  ring

theorem realHessian_coordSq (i : Fin n) (x a b : ComplexModel n) :
    realHessian (coordSq i) x a b = 2 * inner ℝ (a i) (b i) := by
  rw [coordSq_eq]
  rw [realHessian_comp_affine (contDiff_norm_sq ℝ) (coordCLM i) 0 x a b]
  simp [realHessian_norm_sq]

theorem inner_sq_add_inner_I_sq (w a : ℂ) :
    inner ℝ w a ^ 2 + inner ℝ w (I • a) ^ 2 = ‖w‖ ^ 2 * ‖a‖ ^ 2 := by
  simp only [Complex.inner, smul_eq_mul, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- **Levi form of a function of `|z_i|²`.** -/
theorem leviForm_comp_coordSq {G : ℝ → ℝ} {x : ComplexModel n} (i : Fin n)
    (hG : ContDiffAt ℝ 2 G (coordSq i x)) (ξ : ComplexModel n) :
    leviForm (fun z ↦ G (coordSq i z)) x ξ =
      (deriv G (coordSq i x) + coordSq i x * deriv (deriv G) (coordSq i x)) * ‖ξ i‖ ^ 2 := by
  have hq : ContDiffAt ℝ 2 (coordSq i) x := (contDiff_coordSq i).contDiffAt.of_le
    (WithTop.coe_le_coe.mpr le_top)
  simp only [leviForm, realHessian_comp_real hG hq, realHessian_coordSq, fderiv_coordSq_apply]
  have h1 := inner_sq_add_inner_I_sq (x i) (ξ i)
  have h2 : (I • ξ) i = I • ξ i := rfl
  rw [h2]
  simp only [coordSq]
  have h3 : inner ℝ (I • ξ i) (I • ξ i) = ‖ξ i‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
  rw [real_inner_self_eq_norm_sq, h3]
  linear_combination (deriv (deriv G) (‖x i‖ ^ 2)) * h1

theorem fderiv_comp_coordSq_apply {G : ℝ → ℝ} {x : ComplexModel n} (i : Fin n)
    (hG : DifferentiableAt ℝ G (coordSq i x)) (a : ComplexModel n) :
    fderiv ℝ (fun z ↦ G (coordSq i z)) x a = deriv G (coordSq i x) * (2 * inner ℝ (x i) (a i))
      := by
  have hq : HasFDerivAt (coordSq i) (fderiv ℝ (coordSq i) x) x :=
    ((contDiff_coordSq i).differentiable (by simp) x).hasFDerivAt
  have h := hG.hasDerivAt.comp_hasFDerivAt x hq
  change fderiv ℝ (G ∘ coordSq i) x a = _
  rw [h.fderiv]
  simp [fderiv_coordSq_apply]

/-- **`∂bar` of a function of `|z_i|²`.** -/
theorem dbarDir_comp_coordSq {G : ℝ → ℝ} {x : ComplexModel n} (i j : Fin n)
    (hG : DifferentiableAt ℝ G (coordSq i x)) :
    dbarDir (coordVec j) (fun z ↦ ((G (coordSq i z) : ℝ) : ℂ)) x =
      if j = i then ((deriv G (coordSq i x) : ℝ) : ℂ) * x i else 0 := by
  have hd : DifferentiableAt ℝ (fun z ↦ G (coordSq i z)) x :=
    hG.comp x ((contDiff_coordSq i).differentiable (by simp) x)
  simp only [dbarDir, fderiv_ofReal_comp_apply hd, fderiv_comp_coordSq_apply i hG]
  by_cases hji : j = i
  · subst hji
    simp only [ite_true]
    have e1 : (coordVec j : ComplexModel n) j = 1 := by simp [coordVec]
    have e2 : (I • coordVec j : ComplexModel n) j = I := by simp [coordVec]
    rw [e1, e2]
    apply Complex.ext <;> simp [Complex.inner] <;> ring
  · simp only [hji, ite_false]
    have e1 : (coordVec j : ComplexModel n) i = 0 := by simp [coordVec, Ne.symm hji]
    have e2 : (I • coordVec j : ComplexModel n) i = 0 := by simp [coordVec, Ne.symm hji]
    rw [e1, e2]
    simp

/-! ### Chen's functions of `s = |z_n|²` -/

/-- `L = -ρ = 1 + log (2R²) - log (s + ε²)`. -/
def chenL (R ε s : ℝ) : ℝ := 1 + Real.log (2 * R ^ 2) - Real.log (s + ε ^ 2)

/-- `η = L + log L`. -/
def chenEta (R ε s : ℝ) : ℝ := chenL R ε s + Real.log (chenL R ε s)

/-- `ψ = -log η`. -/
def chenPsi (R ε s : ℝ) : ℝ := -Real.log (chenEta R ε s)

/-- The derivative `ψ' = (1 + 1/L) / ((s + ε²) η)`. -/
def chenPsiD (R ε s : ℝ) : ℝ :=
  (1 + (chenL R ε s)⁻¹) / ((s + ε ^ 2) * chenEta R ε s)

/-- The second derivative `ψ''`. -/
def chenPsiDD (R ε s : ℝ) : ℝ :=
  (chenEta R ε s / chenL R ε s ^ 2 - (1 + (chenL R ε s)⁻¹) * chenEta R ε s +
    (1 + (chenL R ε s)⁻¹) ^ 2) / ((s + ε ^ 2) ^ 2 * chenEta R ε s ^ 2)

/-- The Levi coefficient `ψ' + s ψ''` of `ψ(|z_n|²)`. -/
def chenLevi (R ε s : ℝ) : ℝ := chenPsiD R ε s + s * chenPsiDD R ε s

theorem hasDerivAt_chenL (R ε : ℝ) {s : ℝ} (hP : 0 < s + ε ^ 2) :
    HasDerivAt (chenL R ε) (-(s + ε ^ 2)⁻¹) s := by
  have h := ((hasDerivAt_id s).add_const (ε ^ 2)).log hP.ne'
  have h2 := h.const_sub (1 + Real.log (2 * R ^ 2))
  exact h2.congr_deriv (by simp)

theorem hasDerivAt_chenEta (R ε : ℝ) {s : ℝ} (hP : 0 < s + ε ^ 2) (hL : 0 < chenL R ε s) :
    HasDerivAt (chenEta R ε) (-(1 + (chenL R ε s)⁻¹) / (s + ε ^ 2)) s := by
  have h1 := hasDerivAt_chenL R ε hP
  have h2 := h1.add (h1.log hL.ne')
  exact h2.congr_deriv (by field_simp; ring)

theorem hasDerivAt_chenPsi (R ε : ℝ) {s : ℝ} (hP : 0 < s + ε ^ 2) (hL : 0 < chenL R ε s)
    (hη : 0 < chenEta R ε s) : HasDerivAt (chenPsi R ε) (chenPsiD R ε s) s := by
  have h := ((hasDerivAt_chenEta R ε hP hL).log hη.ne').neg
  exact h.congr_deriv (by simp only [chenPsiD]; field_simp)

theorem hasDerivAt_chenPsiD (R ε : ℝ) {s : ℝ} (hP : 0 < s + ε ^ 2) (hL : 0 < chenL R ε s)
    (hη : 0 < chenEta R ε s) : HasDerivAt (chenPsiD R ε) (chenPsiDD R ε s) s := by
  have hB := ((hasDerivAt_chenL R ε hP).inv hL.ne').const_add 1
  have hPη := ((hasDerivAt_id s).add_const (ε ^ 2)).mul (hasDerivAt_chenEta R ε hP hL)
  have h := hB.div hPη (mul_pos hP hη).ne'
  exact h.congr_deriv (by simp only [chenPsiDD, id, Pi.mul_apply, Pi.inv_apply]; field_simp; ring)

/-- The open region where Chen's functions are defined. -/
theorem eventually_chen_good (R ε : ℝ) {s : ℝ} (hP : 0 < s + ε ^ 2) (hL : 0 < chenL R ε s)
    (hη : 0 < chenEta R ε s) :
    ∀ᶠ t in 𝓝 s, 0 < t + ε ^ 2 ∧ 0 < chenL R ε t ∧ 0 < chenEta R ε t := by
  have c1 : ContinuousAt (fun t : ℝ ↦ t + ε ^ 2) s := by fun_prop
  have c2 := (hasDerivAt_chenL R ε hP).continuousAt
  have c3 := (hasDerivAt_chenEta R ε hP hL).continuousAt
  exact (c1.eventually (lt_mem_nhds hP)).and
    ((c2.eventually (lt_mem_nhds hL)).and (c3.eventually (lt_mem_nhds hη)))

theorem contDiffAt_chenPsi (R ε : ℝ) {s : ℝ} (hP : 0 < s + ε ^ 2) (hL : 0 < chenL R ε s)
    (hη : 0 < chenEta R ε s) {k : WithTop ℕ∞} : ContDiffAt ℝ k (chenPsi R ε) s := by
  have hP' : ContDiffAt ℝ k (fun t : ℝ ↦ t + ε ^ 2) s := by fun_prop
  have hlogP := hP'.log hP.ne'
  have hL' : ContDiffAt ℝ k (chenL R ε) s := contDiffAt_const.sub hlogP
  have hη' : ContDiffAt ℝ k (chenEta R ε) s := hL'.add (hL'.log hL.ne')
  exact (hη'.log hη.ne').neg

theorem deriv_chenPsi_eventuallyEq (R ε : ℝ) {s : ℝ} (hP : 0 < s + ε ^ 2)
    (hL : 0 < chenL R ε s) (hη : 0 < chenEta R ε s) :
    deriv (chenPsi R ε) =ᶠ[𝓝 s] chenPsiD R ε := by
  filter_upwards [eventually_chen_good R ε hP hL hη] with t ht
  exact (hasDerivAt_chenPsi R ε ht.1 ht.2.1 ht.2.2).deriv

theorem deriv_chenPsi (R ε : ℝ) {s : ℝ} (hP : 0 < s + ε ^ 2) (hL : 0 < chenL R ε s)
    (hη : 0 < chenEta R ε s) : deriv (chenPsi R ε) s = chenPsiD R ε s :=
  (hasDerivAt_chenPsi R ε hP hL hη).deriv

theorem deriv_deriv_chenPsi (R ε : ℝ) {s : ℝ} (hP : 0 < s + ε ^ 2) (hL : 0 < chenL R ε s)
    (hη : 0 < chenEta R ε s) : deriv (deriv (chenPsi R ε)) s = chenPsiDD R ε s := by
  rw [(deriv_chenPsi_eventuallyEq R ε hP hL hη).deriv_eq]
  exact (hasDerivAt_chenPsiD R ε hP hL hη).deriv

/-! ### Bounds on the region `0 ≤ s`, `s + ε² ≤ 2R²` -/

section Bounds

variable {R ε s : ℝ}

theorem one_le_chenL (hε : 0 < ε) (hs : 0 ≤ s) (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) :
    1 ≤ chenL R ε s := by
  have hP : 0 < s + ε ^ 2 := by positivity
  have := Real.log_le_log hP hsR
  simp only [chenL]
  linarith

theorem chenL_le_chenEta (hε : 0 < ε) (hs : 0 ≤ s) (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) :
    chenL R ε s ≤ chenEta R ε s := by
  have := Real.log_nonneg (one_le_chenL hε hs hsR)
  simp only [chenEta]
  linarith

theorem chenEta_le_two_mul (hε : 0 < ε) (hs : 0 ≤ s) (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) :
    chenEta R ε s ≤ 2 * chenL R ε s := by
  have hL := one_le_chenL hε hs hsR
  have := Real.log_le_sub_one_of_pos (by linarith : 0 < chenL R ε s)
  simp only [chenEta]
  linarith

theorem chenL_le_chenL_zero (hε : 0 < ε) (hs : 0 ≤ s) : chenL R ε s ≤ chenL R ε 0 := by
  have := Real.log_le_log (by positivity : 0 < 0 + ε ^ 2) (by linarith : 0 + ε ^ 2 ≤ s + ε ^ 2)
  simp only [chenL]
  linarith

theorem chenL_sq_mul_le (hε : 0 < ε) (hR : 0 < R) (hs : 0 ≤ s)
    (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) :
    chenL R ε s ^ 2 * (s + ε ^ 2) ≤ 4 * R ^ 2 := by
  have hP : 0 < s + ε ^ 2 := by positivity
  set x := Real.log (2 * R ^ 2) - Real.log (s + ε ^ 2) with hx
  have hx0 : 0 ≤ x := by have := Real.log_le_log hP hsR; linarith
  have hPx : s + ε ^ 2 = 2 * R ^ 2 * Real.exp (-x) := by
    rw [hx, neg_sub, Real.exp_sub, Real.exp_log hP, Real.exp_log (by positivity)]
    field_simp
  have hq := Real.quadratic_le_exp_of_nonneg hx0
  have hL : chenL R ε s = 1 + x := by simp only [chenL, hx]; ring
  rw [hL, hPx]
  have he : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hepos := Real.exp_pos (-x)
  nlinarith [mul_le_mul_of_nonneg_left hq hepos.le, sq_nonneg R]

end Bounds

/-! ### Chen's inequalities -/

section Algebra

variable {s e L η : ℝ}

theorem chen_levi_eq (hP : 0 < s + e) (hL : 0 < L) (hη : 0 < η) :
    (1 + L⁻¹) / ((s + e) * η) +
        s * ((η / L ^ 2 - (1 + L⁻¹) * η + (1 + L⁻¹) ^ 2) / ((s + e) ^ 2 * η ^ 2)) =
      ((1 + L⁻¹) * η * e + s * η / L ^ 2 + s * (1 + L⁻¹) ^ 2) / ((s + e) ^ 2 * η ^ 2) := by
  field_simp
  ring

theorem chen_psi_sq_le (hs : 0 ≤ s) (he : 0 < e) (hL : 1 ≤ L) (hLη : L ≤ η) :
    s * ((1 + L⁻¹) / ((s + e) * η)) ^ 2 ≤ (1 - 1 / (6 * L)) *
      (((1 + L⁻¹) * η * e + s * η / L ^ 2 + s * (1 + L⁻¹) ^ 2) / ((s + e) ^ 2 * η ^ 2)) := by
  have hP : 0 < s + e := by linarith
  have hL0 : 0 < L := by linarith
  have hη : 0 < η := by linarith
  set l := L⁻¹ with hl
  have hl0 : 0 < l := inv_pos.mpr hL0
  have hl1 : l ≤ 1 := inv_le_one_of_one_le₀ hL
  have hηl : 1 ≤ η * l := by rw [hl, ← div_eq_mul_inv, le_div_iff₀ hL0]; linarith
  have e1 : 1 / (6 * L) = l / 6 := by rw [hl]; field_simp
  have e2 : s * η / L ^ 2 = s * η * l ^ 2 := by rw [hl]; field_simp
  have hD : 0 < (s + e) ^ 2 * η ^ 2 := by positivity
  rw [e1, e2]
  have eL : s * ((1 + l) / ((s + e) * η)) ^ 2 = s * (1 + l) ^ 2 / ((s + e) ^ 2 * η ^ 2) := by
    rw [div_pow, mul_pow]; ring
  rw [eL, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ hD.le
  have k1 : s * l ≤ s * η * l ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hηl (mul_nonneg hs
    hl0.le)]
  have k2 : s * (1 + l) ^ 2 ≤ 4 * s := by
    have h4 : (1 + l) ^ 2 ≤ 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hs]
  have k3 : 0 ≤ (1 + l) * η * e := by positivity
  have k4 : 5 / 6 ≤ 1 - l / 6 := by linarith
  have k5 : 5 / 6 * (s * η * l ^ 2) ≤ (1 - l / 6) * (s * η * l ^ 2) :=
    mul_le_mul_of_nonneg_right k4 (by positivity)
  have k6 : 0 ≤ (1 - l / 6) * ((1 + l) * η * e) := mul_nonneg (by linarith) k3
  have k7 : l / 6 * (s * (1 + l) ^ 2) ≤ l / 6 * (4 * s) := mul_le_mul_of_nonneg_left k2 (by
    positivity)
  nlinarith

theorem chen_psi_sq_le_of_le (hs : 0 ≤ s) (hse : s ≤ e) (hL : 1 ≤ L) (hLη : L ≤ η) :
    s * ((1 + L⁻¹) / ((s + e) * η)) ^ 2 ≤ (2 / L) *
      (((1 + L⁻¹) * η * e + s * η / L ^ 2 + s * (1 + L⁻¹) ^ 2) / ((s + e) ^ 2 * η ^ 2)) := by
  have hL0 : 0 < L := by linarith
  have hη : 0 < η := by linarith
  set l := L⁻¹ with hl
  have hl0 : 0 < l := inv_pos.mpr hL0
  have hl1 : l ≤ 1 := inv_le_one_of_one_le₀ hL
  have hηl : 1 ≤ η * l := by rw [hl, ← div_eq_mul_inv, le_div_iff₀ hL0]; linarith
  have e1 : 2 / L = 2 * l := by rw [hl]; field_simp
  have e2 : s * η / L ^ 2 = s * η * l ^ 2 := by rw [hl]; field_simp
  rw [e1, e2]
  have eL : s * ((1 + l) / ((s + e) * η)) ^ 2 = s * (1 + l) ^ 2 / ((s + e) ^ 2 * η ^ 2) := by
    rw [div_pow, mul_pow]; ring
  rw [eL, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have he : 0 ≤ e := hs.trans hse
  have k1 : 2 * l * ((1 + l) * η * e) = 2 * (1 + l) * e * (η * l) := by ring
  have k2 : 2 * (1 + l) * e ≤ 2 * (1 + l) * e * (η * l) := by
    have : 0 ≤ 2 * (1 + l) * e := by positivity
    nlinarith
  have k3 : s * (1 + l) ^ 2 ≤ 2 * (1 + l) * e := by
    have h4 : s * (1 + l) ≤ 2 * e := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4 (by linarith : (0:ℝ) ≤ 1 + l)]
  have k4 : 0 ≤ 2 * l * (s * η * l ^ 2 + s * (1 + l) ^ 2) := by positivity
  nlinarith

theorem chen_le_levi (hs : 0 ≤ s) (he : 0 < e) (hL : 1 ≤ L) (hLη : L ≤ η) :
    e / ((s + e) ^ 2 * η) ≤
      ((1 + L⁻¹) * η * e + s * η / L ^ 2 + s * (1 + L⁻¹) ^ 2) / ((s + e) ^ 2 * η ^ 2) := by
  have hP : 0 < s + e := by linarith
  have hL0 : 0 < L := by linarith
  have hη : 0 < η := by linarith
  have hl0 : 0 < L⁻¹ := inv_pos.mpr hL0
  have e1 : e / ((s + e) ^ 2 * η) = (e * η) / ((s + e) ^ 2 * η ^ 2) := by
    field_simp
  rw [e1]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have h3 : 0 ≤ s * η / L ^ 2 + s * (1 + L⁻¹) ^ 2 := by positivity
  have : e * η ≤ (1 + L⁻¹) * η * e := by nlinarith [mul_pos hη he]
  linarith

/-- **The pointwise Levi estimate for the twisted form.** -/
theorem chen_norm_sq_le {V U Z : ℂ} {ψ' a P : ℝ} (hs : s = ‖Z‖ ^ 2) (hL : 1 ≤ L)
    (hP : 0 < P) (hη : 0 < η) (he : 0 < e)
    (h1 : s * ψ' ^ 2 ≤ (1 - 1 / (6 * L)) * a) (h2 : V ≠ 0 → s * ψ' ^ 2 ≤ (2 / L) * a)
    (h3 : e / (P ^ 2 * η) ≤ a) :
    ‖V + U * ψ' * Z‖ ^ 2 ≤ (25 * ‖V‖ ^ 2 * P ^ 2 * η / e + (1 - 1 / (12 * L)) * ‖U‖ ^ 2) * a := by
  have hL0 : 0 < L := by linarith
  have ha : 0 < a := lt_of_lt_of_le (by positivity) h3
  have hb : ‖U * ψ' * Z‖ ^ 2 = ‖U‖ ^ 2 * (s * ψ' ^ 2) := by
    rw [hs, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
    ring
  have hU0 : 0 ≤ ‖U‖ ^ 2 := by positivity
  have hsψ : 0 ≤ s * ψ' ^ 2 := by rw [hs]; positivity
  set l := 1 / (12 * L) with hl
  have hl0 : 0 < l := by positivity
  have e6 : 1 / (6 * L) = 2 * l := by rw [hl]; field_simp; ring
  have e2 : 2 / L = 24 * l := by rw [hl]; field_simp; ring
  rw [e6] at h1
  have hVa : 0 ≤ 25 * ‖V‖ ^ 2 * P ^ 2 * η / e * a := by positivity
  by_cases hV0 : V = 0
  · subst hV0
    simp only [zero_add, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_mul, zero_div]
    rw [hb]
    have : s * ψ' ^ 2 ≤ (1 - l) * a := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hU0]
  · have h2' := h2 hV0
    rw [e2] at h2'
    have hyoung : ‖V + U * ψ' * Z‖ ^ 2 ≤ 25 * ‖V‖ ^ 2 + (25 / 24) * ‖U * ψ' * Z‖ ^ 2 := by
      have := norm_add_le V (U * ψ' * Z)
      have h0 := norm_nonneg (V + U * ψ' * Z)
      nlinarith [sq_nonneg (24 * ‖V‖ - ‖U * ψ' * Z‖), norm_nonneg V, norm_nonneg (U * ψ' * Z)]
    have hV : 25 * ‖V‖ ^ 2 ≤ 25 * ‖V‖ ^ 2 * P ^ 2 * η / e * a := by
      have h3' : e ≤ a * (P ^ 2 * η) := (div_le_iff₀ (by positivity)).mp h3
      have : 1 ≤ P ^ 2 * η / e * a := by
        rw [div_mul_eq_mul_div, le_div_iff₀ he]
        linarith
      have h0 : 0 ≤ 25 * ‖V‖ ^ 2 := by positivity
      calc 25 * ‖V‖ ^ 2 = 25 * ‖V‖ ^ 2 * 1 := by ring
        _ ≤ 25 * ‖V‖ ^ 2 * (P ^ 2 * η / e * a) := mul_le_mul_of_nonneg_left this h0
        _ = _ := by ring
    have hk : (25 / 24) * (s * ψ' ^ 2) ≤ (1 - l) * a := by nlinarith
    rw [hb] at hyoung
    nlinarith [mul_le_mul_of_nonneg_left hk hU0]

/-- The coefficient left after absorbing the twisted term. -/
theorem chen_coeff_ge {t : ℝ} (hL : 1 ≤ L) (ht0 : 0 ≤ t) (ht : t ≤ 1 / (24 * L)) :
    1 / (24 * L) ≤ 1 - (1 + t) * (1 - 1 / (12 * L)) := by
  have hL0 : 0 < L := by linarith
  have e1 : 1 / (12 * L) = 2 * (1 / (24 * L)) := by field_simp; ring
  rw [e1]
  have hx : 0 ≤ 1 / (24 * L) := by positivity
  nlinarith

end Algebra

/-! ### Chen's inequalities for the functions themselves -/

section ChenFunctions

variable {R ε s : ℝ}

theorem chen_good (hε : 0 < ε) (hs : 0 ≤ s) (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) :
    0 < s + ε ^ 2 ∧ 0 < chenL R ε s ∧ 0 < chenEta R ε s := by
  have h1 := one_le_chenL hε hs hsR
  have h2 := chenL_le_chenEta hε hs hsR
  exact ⟨by positivity, by linarith, by linarith⟩

theorem chenLevi_eq (hε : 0 < ε) (hs : 0 ≤ s) (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) :
    chenLevi R ε s = ((1 + (chenL R ε s)⁻¹) * chenEta R ε s * ε ^ 2 +
      s * chenEta R ε s / chenL R ε s ^ 2 + s * (1 + (chenL R ε s)⁻¹) ^ 2) /
        ((s + ε ^ 2) ^ 2 * chenEta R ε s ^ 2) := by
  obtain ⟨hP, hL, hη⟩ := chen_good hε hs hsR
  exact chen_levi_eq hP hL hη

theorem sq_chenPsiD_le (hε : 0 < ε) (hs : 0 ≤ s) (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) :
    s * chenPsiD R ε s ^ 2 ≤ (1 - 1 / (6 * chenL R ε s)) * chenLevi R ε s := by
  rw [chenLevi_eq hε hs hsR]
  exact chen_psi_sq_le hs (by positivity) (one_le_chenL hε hs hsR) (chenL_le_chenEta hε hs hsR)

theorem sq_chenPsiD_le_of_le (hε : 0 < ε) (hs : 0 ≤ s) (hsR : s + ε ^ 2 ≤ 2 * R ^ 2)
    (hse : s ≤ ε ^ 2) :
    s * chenPsiD R ε s ^ 2 ≤ (2 / chenL R ε s) * chenLevi R ε s := by
  rw [chenLevi_eq hε hs hsR]
  exact chen_psi_sq_le_of_le hs hse (one_le_chenL hε hs hsR) (chenL_le_chenEta hε hs hsR)

theorem le_chenLevi (hε : 0 < ε) (hs : 0 ≤ s) (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) :
    ε ^ 2 / ((s + ε ^ 2) ^ 2 * chenEta R ε s) ≤ chenLevi R ε s := by
  rw [chenLevi_eq hε hs hsR]
  exact chen_le_levi hs (by positivity) (one_le_chenL hε hs hsR) (chenL_le_chenEta hε hs hsR)

theorem chenLevi_pos (hε : 0 < ε) (hs : 0 ≤ s) (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) :
    0 < chenLevi R ε s := by
  obtain ⟨hP, hL, hη⟩ := chen_good hε hs hsR
  exact lt_of_lt_of_le (by positivity) (le_chenLevi hε hs hsR)

theorem chenPsi_nonpos (hε : 0 < ε) (hs : 0 ≤ s) (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) :
    chenPsi R ε s ≤ 0 := by
  have h1 := one_le_chenL hε hs hsR
  have h2 := chenL_le_chenEta hε hs hsR
  simp only [chenPsi, neg_nonpos]
  exact Real.log_nonneg (by linarith)

theorem exp_chenPsi (hε : 0 < ε) (hs : 0 ≤ s) (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) :
    Real.exp (chenPsi R ε s) = (chenEta R ε s)⁻¹ := by
  obtain ⟨-, -, hη⟩ := chen_good hε hs hsR
  rw [chenPsi, Real.exp_neg, Real.exp_log hη]

theorem chenPsiD_nonneg (hε : 0 < ε) (hs : 0 ≤ s) (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) :
    0 ≤ chenPsiD R ε s := by
  obtain ⟨hP, hL, hη⟩ := chen_good hε hs hsR
  unfold chenPsiD
  positivity

theorem chenPsiD_le (hε : 0 < ε) (hs : 0 ≤ s) (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) :
    chenPsiD R ε s ≤ 2 / ε ^ 2 := by
  obtain ⟨hP, hL, hη⟩ := chen_good hε hs hsR
  have h1 := one_le_chenL hε hs hsR
  have h2 := chenL_le_chenEta hε hs hsR
  have hB : 1 + (chenL R ε s)⁻¹ ≤ 2 := by
    have : (chenL R ε s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    linarith
  unfold chenPsiD
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hPη : ε ^ 2 ≤ (s + ε ^ 2) * chenEta R ε s := by nlinarith
  nlinarith

end ChenFunctions

/-! ### The weight `log (s + δ²)` -/

theorem hasDerivAt_log_add_sq {δ s : ℝ} (hP : 0 < s + δ ^ 2) :
    HasDerivAt (fun t : ℝ ↦ Real.log (t + δ ^ 2)) (s + δ ^ 2)⁻¹ s := by
  have h := ((hasDerivAt_id s).add_const (δ ^ 2)).log hP.ne'
  exact h.congr_deriv (by simp [div_eq_mul_inv])

theorem deriv_log_add_sq {δ s : ℝ} (hP : 0 < s + δ ^ 2) :
    deriv (fun t : ℝ ↦ Real.log (t + δ ^ 2)) s = (s + δ ^ 2)⁻¹ :=
  (hasDerivAt_log_add_sq hP).deriv

theorem deriv_deriv_log_add_sq {δ s : ℝ} (hP : 0 < s + δ ^ 2) :
    deriv (deriv fun t : ℝ ↦ Real.log (t + δ ^ 2)) s = -((s + δ ^ 2) ^ 2)⁻¹ := by
  have hev : deriv (fun t : ℝ ↦ Real.log (t + δ ^ 2)) =ᶠ[𝓝 s] fun t ↦ (t + δ ^ 2)⁻¹ := by
    have c1 : ContinuousAt (fun t : ℝ ↦ t + δ ^ 2) s := by fun_prop
    filter_upwards [c1.eventually (lt_mem_nhds hP)] with t ht
    exact deriv_log_add_sq ht
  rw [hev.deriv_eq]
  have h : HasDerivAt (fun t : ℝ ↦ (t + δ ^ 2)⁻¹) (-((s + δ ^ 2) ^ 2)⁻¹) s := by
    have h0 := ((hasDerivAt_id s).add_const (δ ^ 2)).inv hP.ne'
    exact h0.congr_deriv (by simp [div_eq_mul_inv])
  exact h.deriv

theorem contDiffAt_log_add_sq {δ s : ℝ} (hP : 0 < s + δ ^ 2) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (fun t : ℝ ↦ Real.log (t + δ ^ 2)) s := by
  have hP' : ContDiffAt ℝ k (fun t : ℝ ↦ t + δ ^ 2) s := by fun_prop
  exact hP'.log hP.ne'

theorem levi_log_add_sq {δ s : ℝ} (hP : 0 < s + δ ^ 2) :
    deriv (fun t : ℝ ↦ Real.log (t + δ ^ 2)) s +
        s * deriv (deriv fun t : ℝ ↦ Real.log (t + δ ^ 2)) s = δ ^ 2 / (s + δ ^ 2) ^ 2 := by
  rw [deriv_log_add_sq hP, deriv_deriv_log_add_sq hP]
  field_simp
  ring

/-! ### The cutoff -/

/-- A smooth cutoff equal to `1` on `(-∞, 1/2]` and to `0` on `[1, ∞)`. -/
def chenCutoff (x : ℝ) : ℝ := Real.smoothTransition (2 - 2 * x)

theorem contDiff_chenCutoff {k : ℕ∞} : ContDiff ℝ k chenCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))

theorem chenCutoff_of_le {x : ℝ} (hx : x ≤ 1 / 2) : chenCutoff x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem chenCutoff_of_ge {x : ℝ} (hx : 1 ≤ x) : chenCutoff x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem chenCutoff_nonneg (x : ℝ) : 0 ≤ chenCutoff x := Real.smoothTransition.nonneg _

theorem chenCutoff_le_one (x : ℝ) : chenCutoff x ≤ 1 := Real.smoothTransition.le_one _

theorem deriv_chenCutoff_of_lt {x : ℝ} (hx : 1 < x) : deriv chenCutoff x = 0 := by
  have : chenCutoff =ᶠ[𝓝 x] fun _ ↦ 0 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using chenCutoff_of_ge hy.le
  rw [this.deriv_eq]
  simp

theorem exists_abs_deriv_chenCutoff_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv chenCutoff x| ≤ M := by
  obtain ⟨M, hM⟩ := exists_abs_deriv_smoothTransition_le
  refine ⟨2 * M, by nlinarith [hM 0, abs_nonneg (deriv Real.smoothTransition 0)], fun x ↦ ?_⟩
  have hd : HasDerivAt chenCutoff (deriv Real.smoothTransition (2 - 2 * x) * (-2)) x := by
    have h1 : HasDerivAt (fun y : ℝ ↦ 2 - 2 * y) (-2) x := by
      simpa using ((hasDerivAt_id x).const_mul 2).const_sub 2
    exact ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt.comp
      x h1
  rw [hd.deriv, abs_mul]
  have := hM (2 - 2 * x)
  norm_num
  linarith

end

end SGPT.Foundations.Analysis.Pending.OTChen
