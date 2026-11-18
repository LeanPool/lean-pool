/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Gaussian derivatives and lattice sampling

Derived from the corresponding part of the upstream triangular Hilbert form proof.

The lattice-sampling argument adapts `TwoCommuting/Auto/Sec2ElementaryPreparation.lean`.
Joris Roos’s `lean-twocommuting` revision `33b69ccacc013c703a151421658187ea4d2029fb`
credits these Apache-2.0 Lean proofs to Claude.
-/

@[expose] public section
namespace Triangular.Auto

open MeasureTheory Filter Topology Set

open scoped ContDiff ENNReal NNReal symmDiff

noncomputable section

section GaussianCalculus

open Real

/-- The unnormalized standard Gaussian profile. -/
def gaussProfile (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2)

/-- The `j`th derivative of the unnormalized Gaussian profile. -/
def gaussProfileD (j : ℕ) : ℝ → ℝ := iteratedDeriv j gaussProfile

lemma contDiff_gaussProfile : ContDiff ℝ ∞ gaussProfile := by
  unfold gaussProfile
  fun_prop

lemma contDiff_gaussProfileD (j : ℕ) : ContDiff ℝ ∞ (gaussProfileD j) := by
  unfold gaussProfileD
  rw [iteratedDeriv_eq_iterate]
  exact contDiff_gaussProfile.iterate_deriv j

lemma differentiable_gaussProfileD (j : ℕ) :
    Differentiable ℝ (gaussProfileD j) := (contDiff_gaussProfileD j).differentiable (by simp)

lemma deriv_gaussProfileD (j : ℕ) : deriv (gaussProfileD j) = gaussProfileD (j + 1) := by
  unfold gaussProfileD
  rw [iteratedDeriv_succ]

lemma hasDerivAt_gaussProfileD (j : ℕ) (x : ℝ) :
    HasDerivAt (gaussProfileD j) (gaussProfileD (j + 1) x) x := by
  rw [← deriv_gaussProfileD]
  exact (differentiable_gaussProfileD j x).hasDerivAt

lemma gaussProfileD_zero : gaussProfileD 0 = gaussProfile := by simp [gaussProfileD]

lemma gaussProfileD_one (x : ℝ) : gaussProfileD 1 x = -x * gaussProfile x := by
  have h : HasDerivAt gaussProfile (-x * gaussProfile x) x := by
    unfold gaussProfile
    have := ((hasDerivAt_pow 2 x).neg.div_const 2).exp
    convert this using 1
    simp; ring
  rw [← h.deriv, ← deriv_gaussProfileD, gaussProfileD_zero]

lemma gaussProfileD_succ_succ (j : ℕ) (x : ℝ) :
    gaussProfileD (j + 2) x = -((j : ℝ) + 1) * gaussProfileD j x - x * gaussProfileD (j + 1) x := by
  induction j generalizing x with
  | zero =>
    have h1 : gaussProfileD 1 = fun x => -x * gaussProfileD 0 x := by
      funext y; rw [gaussProfileD_one, gaussProfileD_zero]
    have : HasDerivAt (fun x => -x * gaussProfileD 0 x) (-1 * gaussProfileD 0 x + -x * gaussProfileD
        1 x) x := (hasDerivAt_id x).neg.mul (hasDerivAt_gaussProfileD 0 x)
    rw [← h1] at this
    rw [← (hasDerivAt_gaussProfileD 1 x).deriv, this.deriv]
    push_cast; ring
  | succ j ih =>
    have h2 : gaussProfileD (j + 2) = fun x =>
        -((j : ℝ) + 1) * gaussProfileD j x - x * gaussProfileD (j + 1) x := funext ih
    have : HasDerivAt (fun x => -((j : ℝ) + 1) * gaussProfileD j x - x * gaussProfileD (j + 1) x)
        (-((j : ℝ) + 1) * gaussProfileD (j + 1) x - (1 * gaussProfileD (j + 1) x + x * gaussProfileD
        (j + 2) x)) x := ((hasDerivAt_gaussProfileD j x).const_mul _).sub ((hasDerivAt_id x).mul
        (hasDerivAt_gaussProfileD (j + 1) x))
    rw [← h2] at this
    rw [← (hasDerivAt_gaussProfileD (j + 2) x).deriv, this.deriv]
    push_cast; ring

lemma gaussProfile_pos (x : ℝ) : 0 < gaussProfile x := Real.exp_pos _

lemma abs_gaussProfileD_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |gaussProfileD j x| ≤ C * (1 + |x|) ^ j * gaussProfile x := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => exact ⟨1, zero_le_one, fun x => by
        simp [gaussProfileD_zero, abs_of_pos (gaussProfile_pos x)]⟩
    | 1, _ => exact ⟨1, zero_le_one, fun x => by
        rw [gaussProfileD_one, abs_mul, abs_neg, abs_of_pos (gaussProfile_pos x)]
        have := gaussProfile_pos x
        nlinarith [abs_nonneg x]⟩
    | j + 2, ih =>
      obtain ⟨C0, hC0, h0⟩ := ih j (by omega)
      obtain ⟨C1, hC1, h1⟩ := ih (j + 1) (by omega)
      refine ⟨((j : ℝ) + 1) * C0 + C1, by positivity, fun x => ?_⟩
      rw [gaussProfileD_succ_succ]
      have hx : (1 : ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
      have hp := gaussProfile_pos x
      have e0 := h0 x
      have e1 := h1 x
      calc |-((j : ℝ) + 1) * gaussProfileD j x - x * gaussProfileD (j + 1) x|
          ≤ ((j : ℝ) + 1) * |gaussProfileD j x| + |x| * |gaussProfileD (j + 1) x| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (j : ℝ) + 1)]
        _ ≤ ((j : ℝ) + 1) * (C0 * (1 + |x|) ^ j * gaussProfile x) + (1 + |x|) * (C1 * (1 + |x|) ^ (j
            + 1) * gaussProfile x) := by
            gcongr
            linarith
        _ ≤ (((j : ℝ) + 1) * C0 + C1) * (1 + |x|) ^ (j + 2) * gaussProfile x := by
            have hpow : (1 + |x|) ^ j ≤ (1 + |x|) ^ (j + 2) :=
              pow_le_pow_right₀ hx (by omega)
            have : (1 + |x|) * (C1 * (1 + |x|) ^ (j + 1) * gaussProfile x) =
                C1 * (1 + |x|) ^ (j + 2) * gaussProfile x := by ring
            rw [this]
            have : ((j : ℝ) + 1) * (C0 * (1 + |x|) ^ j * gaussProfile x) ≤ ((j : ℝ) + 1) * (C0 * (1
                + |x|) ^ (j + 2) * gaussProfile x) := by
              gcongr
            nlinarith

lemma one_add_abs_pow_mul_gaussProfile_le (n : ℕ) (x : ℝ) :
    (1 + |x|) ^ n * gaussProfile x ≤ n.factorial * Real.exp 2 * Real.exp (-(x ^ 2) / 4) := by
  have hy : 0 ≤ 1 + |x| := by positivity
  have h1 : (1 + |x|) ^ n ≤ n.factorial * Real.exp (1 + |x|) := by
    have := Real.pow_div_factorial_le_exp _ hy n
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h2 : Real.exp (1 + |x|) * gaussProfile x ≤ Real.exp 2 * Real.exp (-(x ^ 2) / 4) := by
    unfold gaussProfile
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith [sq_nonneg (|x| / 2 - 1)]
  calc (1 + |x|) ^ n * gaussProfile x ≤ n.factorial * Real.exp (1 + |x|) * gaussProfile x := by
        gcongr; exact (gaussProfile_pos x).le
    _ = n.factorial * (Real.exp (1 + |x|) * gaussProfile x) := by ring
    _ ≤ n.factorial * (Real.exp 2 * Real.exp (-(x ^ 2) / 4)) := by gcongr
    _ = _ := by ring

lemma abs_pow_mul_gaussProfileD_le (j m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |x| ^ m * |gaussProfileD j x| ≤ C * Real.exp (-(x ^ 2) / 4) := by
  obtain ⟨C, hC, h⟩ := abs_gaussProfileD_le j
  refine ⟨C * (m + j).factorial * Real.exp 2, by positivity, fun x => ?_⟩
  have hx : |x| ^ m ≤ (1 + |x|) ^ m := by gcongr; linarith
  calc |x| ^ m * |gaussProfileD j x| ≤ (1 + |x|) ^ m * (C * (1 + |x|) ^ j * gaussProfile x) := by
        gcongr; exact h x
    _ = C * ((1 + |x|) ^ (m + j) * gaussProfile x) := by ring
    _ ≤ C * ((m + j).factorial * Real.exp 2 * Real.exp (-(x ^ 2) / 4)) := by
        exact mul_le_mul_of_nonneg_left (one_add_abs_pow_mul_gaussProfile_le _ x) hC
    _ = _ := by ring

/-- The normalized one-dimensional Gaussian of variance `σ` for positive `σ`. -/
def gaussian (σ t : ℝ) : ℝ := (√(2 * π * σ))⁻¹ * Real.exp (-(t ^ 2) / (2 * σ))

/-- The `j`th derivative with respect to the spatial coordinate of `gaussian σ`. -/
def gaussianD (j : ℕ) (σ : ℝ) : ℝ → ℝ := iteratedDeriv j (gaussian σ)

lemma contDiff_gaussian (σ : ℝ) : ContDiff ℝ ∞ (gaussian σ) := by
  unfold gaussian
  fun_prop

lemma gaussianD_zero (σ : ℝ) : gaussianD 0 σ = gaussian σ := by simp [gaussianD]

lemma hasDerivAt_gaussianD (j : ℕ) (σ t : ℝ) :
    HasDerivAt (gaussianD j σ) (gaussianD (j + 1) σ t) t := by
  have hd : Differentiable ℝ (gaussianD j σ) := (contDiff_gaussian σ).differentiable_iteratedDeriv j
      (by exact_mod_cast WithTop.coe_lt_top _)
  have : deriv (gaussianD j σ) = gaussianD (j + 1) σ := by
    unfold gaussianD; rw [iteratedDeriv_succ]
  rw [← this]
  exact (hd t).hasDerivAt

lemma continuous_gaussianD (j : ℕ) (σ : ℝ) : Continuous (gaussianD j σ) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_gaussianD j σ t).continuousAt

lemma gaussian_eq_profile {σ : ℝ} (hσ : 0 < σ) :
    gaussian σ = fun t => (√(2 * π))⁻¹ * (√σ)⁻¹ * gaussProfile ((√σ)⁻¹ * t) := by
  funext t
  unfold gaussian gaussProfile
  have hs : 0 < √σ := Real.sqrt_pos.2 hσ
  rw [show (2 * π * σ) = (2 * π) * σ by ring, Real.sqrt_mul (by positivity), mul_inv]
  congr 2
  rw [mul_pow, inv_pow, Real.sq_sqrt hσ.le]
  field_simp

lemma gaussianD_eq_profile (j : ℕ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    gaussianD j σ t = (√(2 * π))⁻¹ * (√σ)⁻¹ ^ (j + 1) * gaussProfileD j ((√σ)⁻¹ * t) := by
  unfold gaussianD
  rw [gaussian_eq_profile hσ]
  have hcd : ContDiff ℝ j (fun t => gaussProfile ((√σ)⁻¹ * t)) := (contDiff_gaussProfile.of_le (by
      exact_mod_cast le_top)).comp (by fun_prop)
  rw [iteratedDeriv_const_mul (f := fun t => gaussProfile ((√σ)⁻¹ * t)) _ hcd.contDiffAt]
  rw [iteratedDeriv_comp_const_mul (contDiff_gaussProfile.of_le (by exact_mod_cast le_top))
      ((√σ)⁻¹)]
  simp only [gaussProfileD]
  ring

theorem integral_gaussian_eq_one {σ : ℝ} (hσ : 0 < σ) : ∫ t, gaussian σ t = 1 := by
  unfold gaussian
  rw [integral_const_mul]
  have : (fun t : ℝ => Real.exp (-(t ^ 2) / (2 * σ))) =
      fun t => Real.exp (-(1 / (2 * σ)) * t ^ 2) := by
    funext t; congr 1; ring
  rw [this, integral_gaussian, div_div_eq_mul_div, div_one]
  rw [show (π * (2 * σ)) = 2 * π * σ by ring]
  exact inv_mul_cancel₀ (Real.sqrt_pos.2 (by positivity)).ne'

theorem gaussianD_scale (j : ℕ) {a s : ℝ} (ha : 0 < a) (hs : 0 < s) (t : ℝ) :
    gaussianD j (a * s) t = (√s)⁻¹ ^ (j + 1) * gaussianD j a ((√s)⁻¹ * t) := by
  rw [gaussianD_eq_profile j (mul_pos ha hs), gaussianD_eq_profile j ha,
    Real.sqrt_mul ha.le, mul_inv]
  rw [show (√a)⁻¹ * ((√s)⁻¹ * t) = (√a)⁻¹ * (√s)⁻¹ * t by ring]
  ring

theorem hasDerivAt_gaussianD_variance (j : ℕ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    HasDerivAt (fun τ => gaussianD j τ t) (gaussianD (j + 2) σ t / 2) σ := by
  set c := (√(2 * π))⁻¹
  have hs : 0 < √σ := Real.sqrt_pos.2 hσ
  have hr : HasDerivAt (fun τ => (√τ)⁻¹) (-(1 / 2) * (√σ)⁻¹ ^ 3) σ := by
    have h1 := (Real.hasDerivAt_sqrt hσ.ne').inv hs.ne'
    convert h1 using 1
    have : (√σ) ^ 2 = σ := Real.sq_sqrt hσ.le
    field_simp
  have hF : HasDerivAt (fun τ => c * (√τ)⁻¹ ^ (j + 1) * gaussProfileD j ((√τ)⁻¹ * t)) (c * (((j + 1
      : ℕ) : ℝ) * (√σ)⁻¹ ^ j * (-(1 / 2) * (√σ)⁻¹ ^ 3)) *
          gaussProfileD j ((√σ)⁻¹ * t) +
        c * (√σ)⁻¹ ^ (j + 1) * (gaussProfileD (j + 1) ((√σ)⁻¹ * t) * (-(1 / 2) * (√σ)⁻¹ ^ 3 * t))) σ
            := by
    have h1 := (hr.pow (j + 1)).const_mul c
    have h2 := (hasDerivAt_gaussProfileD j ((√σ)⁻¹ * t)).comp σ (hr.mul_const t)
    convert h1.mul h2 using 1
    · funext τ; simp [Function.comp]
    · simp [Function.comp]
  have hev : (fun τ => gaussianD j τ t) =ᶠ[𝓝 σ]
      fun τ => c * (√τ)⁻¹ ^ (j + 1) * gaussProfileD j ((√τ)⁻¹ * t) := by
    filter_upwards [lt_mem_nhds hσ] with τ hτ
    exact gaussianD_eq_profile j hτ t
  refine (hF.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [gaussianD_eq_profile (j + 2) hσ, gaussProfileD_succ_succ]
  push_cast
  ring

theorem abs_pow_mul_gaussianD_le (j m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 0 < σ → ∀ t : ℝ, |t| ^ m * |gaussianD j σ t| ≤ C * (√σ) ^ m *
      (√σ)⁻¹ ^ (j + 1) * Real.exp (-(t ^ 2) / (4 * σ)) := by
  obtain ⟨C, hC, h⟩ := abs_pow_mul_gaussProfileD_le j m
  refine ⟨(√(2 * π))⁻¹ * C, by positivity, fun σ hσ t => ?_⟩
  have hs : 0 < √σ := Real.sqrt_pos.2 hσ
  set x := (√σ)⁻¹ * t with hx
  have ht : t = √σ * x := by rw [hx]; field_simp
  have hx2 : -(x ^ 2) / 4 = -(t ^ 2) / (4 * σ) := by
    simp only [hx]; rw [mul_pow, inv_pow, Real.sq_sqrt hσ.le]; field_simp
  rw [gaussianD_eq_profile j hσ, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0:ℝ) < (√(2 * π))⁻¹),
    abs_of_pos (by positivity : (0:ℝ) < (√σ)⁻¹ ^ (j + 1)), ← hx, ← hx2]
  have hxt : |t| ^ m = (√σ) ^ m * |x| ^ m := by
    rw [ht, abs_mul, abs_of_pos hs, mul_pow]
  rw [hxt]
  have := h x
  calc (√σ) ^ m * |x| ^ m * ((√(2 * π))⁻¹ * (√σ)⁻¹ ^ (j + 1) * |gaussProfileD j x|)
      = (√(2 * π))⁻¹ * (√σ) ^ m * (√σ)⁻¹ ^ (j + 1) * (|x| ^ m * |gaussProfileD j x|) := by ring
    _ ≤ (√(2 * π))⁻¹ * (√σ) ^ m * (√σ)⁻¹ ^ (j + 1) * (C * Real.exp (-(x ^ 2) / 4)) := by
        gcongr
    _ = _ := by ring

lemma integrable_exp_neg_sq_div {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / (4 * σ))) := by
  have : (fun t : ℝ => Real.exp (-(t ^ 2) / (4 * σ))) =
      fun t => Real.exp (-(1 / (4 * σ)) * t ^ 2) := by
    funext t; congr 1; ring
  rw [this]
  exact integrable_exp_neg_mul_sq (by positivity)

theorem integrable_pow_mul_gaussianD (j m : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun t => t ^ m * gaussianD j σ t) := by
  obtain ⟨C, hC, h⟩ := abs_pow_mul_gaussianD_le j m
  refine ((integrable_exp_neg_sq_div hσ).const_mul (C * (√σ) ^ m * (√σ)⁻¹ ^ (j + 1))).mono'
      ((continuous_pow m).mul (continuous_gaussianD j σ)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact h σ hσ t

theorem integrable_gaussianD (j : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (gaussianD j σ) := by
  simpa using integrable_pow_mul_gaussianD j 0 hσ

lemma abs_gaussianD_le_const (j : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ M : ℝ, ∀ t, |gaussianD j σ t| ≤ M := by
  obtain ⟨C, hC, h⟩ := abs_pow_mul_gaussianD_le j 0
  refine ⟨C * (√σ) ^ 0 * (√σ)⁻¹ ^ (j + 1), fun t => ?_⟩
  have := h σ hσ t
  rw [pow_zero, one_mul] at this
  refine this.trans ?_
  have : Real.exp (-(t ^ 2) / (4 * σ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ t ^ 2 / (4 * σ) := by positivity
    rw [neg_div]; linarith
  have : 0 ≤ C * (√σ) ^ 0 * (√σ)⁻¹ ^ (j + 1) := by positivity
  nlinarith [Real.exp_pos (-(t ^ 2) / (4 * σ))]

lemma hasDerivAt_gaussianD_conv (i : ℕ) {σ : ℝ} (hσ : 0 < σ) {G : ℝ → ℝ} (hG : Integrable G)
    (t : ℝ) :
    HasDerivAt (fun t => ∫ d, gaussianD i σ (t - d) * G d) (∫ d, gaussianD (i + 1) σ (t - d) * G
      d) t := by
  obtain ⟨M0, hM0⟩ := abs_gaussianD_le_const i hσ
  obtain ⟨M1, hM1⟩ := abs_gaussianD_le_const (i + 1) hσ
  have hint : ∀ (k : ℕ) (M : ℝ), (∀ t, |gaussianD k σ t| ≤ M) → ∀ x : ℝ,
      Integrable (fun d => gaussianD k σ (x - d) * G d) := by
    intro k M hM x
    refine (hG.norm.const_mul M).mono' ?_ ?_
    · exact ((continuous_gaussianD k σ).comp (continuous_const.sub continuous_id)
        ).aestronglyMeasurable.mul hG.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun d => ?_
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun d => M1 * |G d|) (F := fun
      t d => gaussianD i σ (t - d) * G d) (F' := fun t d => gaussianD (i + 1) σ (t - d) * G d) (s :=
      Set.univ)
    Filter.univ_mem ?_ (hint i M0 hM0 t) ?_ ?_ (hG.norm.const_mul M1) ?_).2
  · exact Filter.Eventually.of_forall fun x => (hint i M0 hM0 x).aestronglyMeasurable
  · exact (hint (i + 1) M1 hM1 t).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun d x _ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hM1 _) (abs_nonneg _)
  · refine Filter.Eventually.of_forall fun d x _ => ?_
    have := ((hasDerivAt_gaussianD i σ (x - d)).comp x ((hasDerivAt_id x).sub_const d)).mul_const (G
        d)
    simpa using this

lemma iteratedDeriv_gaussian_conv (i : ℕ) {σ : ℝ} (hσ : 0 < σ) {G : ℝ → ℝ} (hG : Integrable G) :
    iteratedDeriv i (fun t => ∫ d, gaussian σ (t - d) * G d) = fun t => ∫ d, gaussianD i σ (t -
      d) * G d := by
  induction i with
  | zero => simp [gaussianD_zero]
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hasDerivAt_gaussianD_conv i hσ hG t).deriv

lemma gaussian_conv_gaussian {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (t : ℝ) :
    ∫ d, gaussian σ (t - d) * gaussian τ d = gaussian (σ + τ) t := by
  set b := (σ + τ) / (2 * σ * τ) with hb
  have hb0 : 0 < b := by positivity
  set c := τ / (σ + τ)
  have hsq : ∀ d : ℝ, gaussian σ (t - d) * gaussian τ d = ((√(2 * π * σ))⁻¹ * (√(2 * π * τ))⁻¹ *
      Real.exp (-(t ^ 2) / (2 * (σ + τ)))) *
        Real.exp (-b * (d - c * t) ^ 2) := by
    intro d
    unfold gaussian
    have : Real.exp (-((t - d) ^ 2) / (2 * σ)) * Real.exp (-(d ^ 2) / (2 * τ)) =
        Real.exp (-(t ^ 2) / (2 * (σ + τ))) * Real.exp (-b * (d - c * t) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [hb, c]
      field_simp
      ring
    calc
      _ = (√(2 * π * σ))⁻¹ * (√(2 * π * τ))⁻¹ *
          (Real.exp (-((t - d) ^ 2) / (2 * σ)) * Real.exp (-(d ^ 2) / (2 * τ))) := by ring
      _ = _ := by rw [this]; ring
  simp_rw [hsq]
  rw [integral_const_mul]
  have hshift : ∫ d : ℝ, Real.exp (-b * (d - c * t) ^ 2) = √(π / b) := by
    rw [integral_sub_right_eq_self (fun d => Real.exp (-b * d ^ 2)) (c * t), integral_gaussian]
  rw [hshift]
  unfold gaussian
  rw [show ∀ x y z w : ℝ, x * y * z * w = (x * y * w) * z by intros; ring]
  congr 1
  rw [← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity),
    ← Real.sqrt_mul (by positivity)]
  congr 1
  simp only [hb]
  field_simp

theorem gaussianD_conv_gaussianD (i j : ℕ) {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (t : ℝ) :
    ∫ d, gaussianD i σ (t - d) * gaussianD j τ d = gaussianD (i + j) (σ + τ) t := by
  have h0 : ∀ x, ∫ d, gaussian σ (x - d) * gaussianD j τ d = gaussianD j (σ + τ) x := by
    intro x
    have e1 : ∫ d, gaussian σ (x - d) * gaussianD j τ d =
        ∫ d, gaussianD j τ (x - d) * gaussian σ d := by
      rw [← integral_sub_left_eq_self (fun d => gaussian σ (x - d) * gaussianD j τ d) (μ := volume)
          x]
      simp only [sub_sub_cancel]
      congr 1; funext d; ring
    rw [e1]
    have hgi : Integrable (gaussian σ) := by
      simpa [gaussianD_zero] using integrable_gaussianD 0 hσ
    have := congrFun (iteratedDeriv_gaussian_conv j hτ hgi) x
    rw [← this]
    have e2 : (fun t => ∫ d, gaussian τ (t - d) * gaussian σ d) = gaussian (σ + τ) := by
      funext y; rw [gaussian_conv_gaussian hτ hσ, add_comm]
    rw [e2]
    rfl
  have := congrFun (iteratedDeriv_gaussian_conv i hσ (integrable_gaussianD j hτ)) t
  rw [← this]
  have e3 : (fun t => ∫ d, gaussian σ (t - d) * gaussianD j τ d) = gaussianD j (σ + τ) :=
    funext h0
  rw [e3]
  unfold gaussianD
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply]

end GaussianCalculus

section LatticeApproximation

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Round each coordinate down to the grid with spacing `1 / N`. -/
def latticeFloor (N : ℕ) (x : Fin d → ℝ) : Fin d → ℝ := fun i => (⌊(N : ℝ) * x i⌋ : ℝ) / N

/-- The half-open grid cube with lower corner `k / N`. -/
def latticeCube (N : ℕ) (k : Fin d → ℤ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ fun i => Set.Ico ((k i : ℝ) / N) (((k i : ℝ) + 1) / N)

lemma mem_latticeCube {N : ℕ} (hN : 0 < N) {k : Fin d → ℤ} {x : Fin d → ℝ} :
    x ∈ latticeCube N k ↔ ∀ i, ⌊(N : ℝ) * x i⌋ = k i := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [latticeCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico, Int.floor_eq_iff]
  refine forall_congr' fun i => ?_
  rw [div_le_iff₀ hN', lt_div_iff₀ hN']
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma volume_latticeCube {N : ℕ} (hN : 0 < N) (k : Fin d → ℤ) :
    volume (latticeCube N k) = ENNReal.ofReal ((N : ℝ)⁻¹) ^ d := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [latticeCube, Real.volume_pi_Ico]
  have : ∀ i, ((k i : ℝ) + 1) / N - (k i : ℝ) / N = (N : ℝ)⁻¹ := by
    intro i; field_simp; ring
  simp_rw [this]
  simp

lemma abs_sub_latticeFloor_le {N : ℕ} (hN : 0 < N) (x : Fin d → ℝ) (i : Fin d) :
    |x i - latticeFloor N x i| ≤ (N : ℝ)⁻¹ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := Int.floor_le ((N : ℝ) * x i)
  have h2 := Int.lt_floor_add_one ((N : ℝ) * x i)
  simp only [latticeFloor]
  have key : x i - (⌊(N : ℝ) * x i⌋ : ℝ) / N = ((N : ℝ) * x i - ⌊(N : ℝ) * x i⌋) / N := by
    field_simp
  rw [key, abs_div, abs_of_pos hN', div_le_iff₀ hN', inv_mul_cancel₀ hN'.ne', abs_le]
  constructor <;> linarith

lemma tendsto_latticeFloor (x : Fin d → ℝ) :
    Tendsto (fun N : ℕ => latticeFloor N x) atTop (𝓝 x) := by
  rw [tendsto_pi_nhds]
  intro i
  have h0 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have : Tendsto (fun N : ℕ => x i - latticeFloor N x i) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.norm_eq_abs]
    exact abs_sub_latticeFloor_le hN x i
  have := (tendsto_const_nhds (x := x i)).sub this
  simpa using this

lemma volume_coord_hyperplane (i : Fin d) (a : ℝ) : volume {x : Fin d → ℝ | x i = a} = 0 := by
  have : {x : Fin d → ℝ | x i = a} = (Function.eval i : (Fin d → ℝ) → ℝ) ⁻¹' ({a} : Set ℝ) := rfl
  rw [this, volume_pi]
  exact Measure.pi_eval_preimage_null _ (Real.volume_singleton)

theorem lattice_sampling_dominated_convergence (H : (Fin d → ℝ) → E) (hHb : ∃ M, ∀ x, ‖H x‖ ≤ M)
    (hHs : ∃ R, ∀ x, R < ‖x‖ → H x = 0) (S : Finset (Fin d × ℝ))
    (hHc : ∀ x, (∀ p ∈ S, x p.1 ≠ p.2) → ContinuousAt H x) :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹) ^ d • ∑' k : Fin d → ℤ, H (fun i => (k i : ℝ) / N)) atTop
      (𝓝 (∫ x, H x)) := by
  classical
  obtain ⟨M, hM⟩ := hHb
  obtain ⟨R0, hR0⟩ := hHs
  set R := max R0 0
  have hR : ∀ x, R < ‖x‖ → H x = 0 := fun x hx => hR0 x (lt_of_le_of_lt (le_max_left _ _) hx)
  set O : Set (Fin d → ℝ) := {x | ∀ p ∈ S, x p.1 ≠ p.2}
  have hO : ∀ᵐ x, x ∈ O := by
    have : (Oᶜ) ⊆ ⋃ p ∈ S, {x : Fin d → ℝ | x p.1 = p.2} := by
      intro x hx
      simp only [O, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not] at hx
      obtain ⟨p, hp, hxp⟩ := hx
      exact Set.mem_biUnion hp hxp
    rw [ae_iff]
    refine measure_mono_null (fun x hx => this hx) ?_
    exact (measure_biUnion_null_iff (Finset.countable_toSet S)).2
      fun p _ => volume_coord_hyperplane p.1 p.2
  set F : ℕ → Finset (Fin d → ℤ) := fun N =>
    Fintype.piFinset fun _ => Finset.Icc (-(⌈R * N⌉ + 1)) (⌈R * N⌉ + 1)
  have hF : ∀ N : ℕ, 0 < N → ∀ k : Fin d → ℤ, k ∉ F N → H (fun i => (k i : ℝ) / N) = 0 := by
    intro N hN k hk
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [F, Fintype.mem_piFinset, Finset.mem_Icc, not_forall] at hk
    obtain ⟨i, hi⟩ := hk
    apply hR
    have hki : R * N < |(k i : ℝ)| := by
      have h1 := Int.le_ceil (R * N)
      rcases not_and_or.1 hi with h | h
      · push Not at h
        have : (k i : ℝ) < -(⌈R * N⌉ + 1) := by exact_mod_cast h
        rw [abs_of_neg (by linarith [mul_nonneg (le_max_right R0 0) hN'.le])]
        linarith
      · push Not at h
        have : (⌈R * N⌉ + 1 : ℝ) < (k i : ℝ) := by exact_mod_cast h
        rw [abs_of_pos (by linarith [mul_nonneg (le_max_right R0 0) hN'.le])]
        linarith
    calc R < |(k i : ℝ) / N| := by
          rw [abs_div, Nat.abs_cast, lt_div_iff₀ hN']; exact hki
      _ = ‖(fun i => (k i : ℝ) / N) i‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖fun i => (k i : ℝ) / N‖ := norm_le_pi_norm (fun i => (k i : ℝ) / N) i
  have hrep : ∀ N : ℕ, 0 < N → ∀ x, H (latticeFloor N x) =
      ∑ k ∈ F N, (latticeCube N k).indicator (fun _ => H (fun i => (k i : ℝ) / N)) x := by
    intro N hN x
    set k0 : Fin d → ℤ := fun i => ⌊(N : ℝ) * x i⌋
    have hmem : ∀ k, x ∈ latticeCube N k ↔ k = k0 := by
      intro k
      rw [mem_latticeCube hN]
      constructor
      · intro h; funext i; exact (h i).symm
      · rintro rfl i; rfl
    have hk0 : latticeFloor N x = fun i => (k0 i : ℝ) / N := rfl
    by_cases hk : k0 ∈ F N
    · rw [Finset.sum_eq_single k0]
      · rw [Set.indicator_of_mem ((hmem k0).2 rfl), hk0]
      · intro k _ hkk
        exact Set.indicator_of_notMem (fun h => hkk ((hmem k).1 h)) _
      · intro h; exact absurd hk h
    · rw [hk0, hF N hN k0 hk]
      refine (Finset.sum_eq_zero fun k hkF => ?_).symm
      exact Set.indicator_of_notMem (fun h => hk ((hmem k).1 h ▸ hkF)) _
  have hcube_meas : ∀ N k, MeasurableSet (latticeCube (d := d) N k) := fun N k =>
    MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hsum : ∀ N : ℕ, 0 < N → ((N : ℝ)⁻¹) ^ d • ∑' k : Fin d → ℤ, H (fun i => (k i : ℝ) / N) =
      ∫ x, H (latticeFloor N x) := by
    intro N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [tsum_eq_sum (s := F N) (fun k hk => hF N hN k hk)]
    simp_rw [hrep N hN]
    rw [integral_finsetSum]
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_indicator_const _ (hcube_meas N k), measureReal_def, volume_latticeCube hN,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
    · intro k _
      refine IntegrableOn.integrable_indicator (integrableOn_const ?_) (hcube_meas N k)
      rw [volume_latticeCube hN]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hlim : Tendsto (fun N : ℕ => ∫ x, H (latticeFloor N x)) atTop (𝓝 (∫ x, H x)) := by
    refine tendsto_integral_filter_of_dominated_convergence ((Metric.closedBall (0 : Fin d → ℝ) (R +
        1)).indicator fun _ => M) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with N hN
      rw [show (fun x => H (latticeFloor N x)) = fun x => ∑ k ∈ F N, (latticeCube N k).indicator
          (fun _ => H (fun i => (k i : ℝ) / N)) x from
        funext (hrep N hN)]
      exact Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
        aestronglyMeasurable_const.indicator (hcube_meas N k)
    · filter_upwards [eventually_gt_atTop 0] with N hN
      refine Filter.Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ Metric.closedBall (0 : Fin d → ℝ) (R + 1)
      · rw [Set.indicator_of_mem hx]; exact hM _
      · rw [Set.indicator_of_notMem hx, hR, norm_zero]
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
        have hd : ‖x - latticeFloor N x‖ ≤ 1 := by
          refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
          rw [Pi.sub_apply, Real.norm_eq_abs]
          refine (abs_sub_latticeFloor_le hN x i).trans ?_
          exact inv_le_one_of_one_le₀ (by exact_mod_cast hN)
        have := norm_sub_norm_le x (latticeFloor N x)
        linarith
    · exact IntegrableOn.integrable_indicator (integrableOn_const measure_closedBall_lt_top.ne)
        Metric.isClosed_closedBall.measurableSet
    · filter_upwards [hO] with x hx
      exact (hHc x hx).tendsto.comp (tendsto_latticeFloor x)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (hsum N hN).symm

end LatticeApproximation

end

end Triangular.Auto
