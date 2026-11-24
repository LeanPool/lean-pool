/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.LeviForm
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexManifold

/-!
# Cutoffs and weights for Hörmander's three-weight `L²` method

The cutoffs and weights used in Hörmander's three-weight `L²` method on a bounded convex domain
`L ⊆ ℂⁿ` (Hörmander, *An Introduction to Complex Analysis in Several Variables*, §4.1–4.2), in
purely real-analytic terms.

* `exists_smooth_convex_majorant`: a one-variable smooth convex nondecreasing function on
  `(-∞, c)`, vanishing on `(-∞, a]`, whose value and derivative dominate a given locally bounded
  function near `c`.  It is a locally finite sum of rescaled integrated smooth transitions.
* `realHessian_comp_real`, `le_leviForm_comp_real`: the Hessian chain rule for `f ∘ s` with
  `f : ℝ → ℝ`, and `f'(s) Levi(s) ≤ Levi(f ∘ s)` when `f'' ≥ 0`.
* `exists_smooth_convex_exhaustion`: a smooth convex `s` with `{s ≤ 1} ⊆ L`, `s ≤ 1/2` on a
  compact `K ⊆ L`, and `Levi(s)(v) ≥ ε ‖v‖²`.  It is a sum of exponentials of affine functions
  cutting out a polytope inside `L` (found by Hahn–Banach separation and compactness of the
  frontier), plus `ε ‖x - p‖²`.  No mollification is needed.
* `exists_hormanderCutoffData`: the main statement.  With `L' = {s < 1}` and `U₀ = {s < 3/5}`,
  the cutoffs are `η_k = θ_k ∘ s`, and the weights are `ψ₀ = φ ∘ s`, `χ = χ₀ ∘ s` for
  one-variable profiles `φ, χ₀` produced by `exists_smooth_convex_majorant`.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending

noncomputable section

section OneVariable

theorem deriv_smoothTransition_of_neg {u : ℝ} (hu : u < 0) :
    deriv Real.smoothTransition u = 0 := by
  have : Real.smoothTransition =ᶠ[𝓝 u] fun _ ↦ 0 := by
    filter_upwards [Iio_mem_nhds hu] with v hv using Real.smoothTransition.zero_of_nonpos hv.le
  rw [this.deriv_eq]
  simp

theorem deriv_smoothTransition_of_one_lt {u : ℝ} (hu : 1 < u) :
    deriv Real.smoothTransition u = 0 := by
  have : Real.smoothTransition =ᶠ[𝓝 u] fun _ ↦ 1 := by
    filter_upwards [Ioi_mem_nhds hu] with v hv using Real.smoothTransition.one_of_one_le hv.le
  rw [this.deriv_eq]
  simp

/-- The derivative of the smooth transition function is bounded. -/
theorem exists_abs_deriv_smoothTransition_le :
    ∃ M : ℝ, ∀ u, |deriv Real.smoothTransition u| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun u hu ↦ ?_
    simp only [mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · exact deriv_smoothTransition_of_neg hu
    · exact deriv_smoothTransition_of_one_lt hu
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C, fun u ↦ by simpa using hC u⟩

theorem deriv_smoothTransition_nonneg (u : ℝ) : 0 ≤ deriv Real.smoothTransition u :=
  Real.smoothTransition.monotone.deriv_nonneg

/-- The integrated smooth transition, a smooth convex function vanishing on `(-∞, 0]`. -/
def smoothRamp (u : ℝ) : ℝ := ∫ x in (0 : ℝ)..u, Real.smoothTransition x

theorem hasDerivAt_smoothRamp (u : ℝ) :
    HasDerivAt smoothRamp (Real.smoothTransition u) u :=
  (Real.smoothTransition.continuous.integral_hasStrictDerivAt 0 u).hasDerivAt

theorem deriv_smoothRamp : deriv smoothRamp = Real.smoothTransition :=
  funext fun u ↦ (hasDerivAt_smoothRamp u).deriv

theorem contDiff_smoothRamp : ContDiff ℝ ∞ smoothRamp :=
  contDiff_infty_iff_deriv.mpr ⟨fun u ↦ (hasDerivAt_smoothRamp u).differentiableAt,
    deriv_smoothRamp ▸ Real.smoothTransition.contDiff⟩

theorem smoothRamp_of_nonpos {u : ℝ} (hu : u ≤ 0) : smoothRamp u = 0 := by
  rw [smoothRamp, intervalIntegral.integral_symm, neg_eq_zero,
    intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ))]
  · simp
  intro x hx
  rw [uIcc_of_le hu] at hx
  exact Real.smoothTransition.zero_of_nonpos hx.2

theorem smoothRamp_nonneg (u : ℝ) : 0 ≤ smoothRamp u := by
  rcases le_total u 0 with hu | hu
  · exact (smoothRamp_of_nonpos hu).ge
  · exact intervalIntegral.integral_nonneg hu fun x _ ↦ Real.smoothTransition.nonneg x

theorem one_le_smoothRamp {u : ℝ} (hu : 2 ≤ u) : 1 ≤ smoothRamp u := by
  have hi : ∀ a b : ℝ, IntervalIntegrable Real.smoothTransition MeasureTheory.volume a b :=
    fun a b ↦ Real.smoothTransition.continuous.intervalIntegrable a b
  have h := intervalIntegral.integral_add_adjacent_intervals (hi 0 1) (hi 1 u)
  have h1 : ∫ x in (1 : ℝ)..u, Real.smoothTransition x = u - 1 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (1 : ℝ))]
    · simp
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact Real.smoothTransition.one_of_one_le hx.1
  have h0 := smoothRamp_nonneg 1
  rw [smoothRamp] at h0 ⊢
  linarith

/-- A smooth convex nondecreasing function on `(-∞, c)` vanishing on `(-∞, a]` whose value and
derivative dominate a given function on `[(a + c) / 2, c)`, provided that function is bounded
above on each `[(a + c) / 2, t]` with `t < c`. -/
theorem exists_smooth_convex_majorant {a c : ℝ} (hac : a < c) (g : ℝ → ℝ)
    (hg : ∀ t < c, BddAbove (g '' Icc ((a + c) / 2) t)) :
    ∃ F : ℝ → ℝ, ContDiffOn ℝ ∞ F (Iio c) ∧ (∀ t, 0 ≤ F t) ∧ (∀ t ≤ a, F t = 0) ∧
      (∀ t < c, 0 ≤ deriv F t ∧ 0 ≤ deriv (deriv F) t) ∧
      ∀ t ∈ Ico ((a + c) / 2) c, g t ≤ F t ∧ g t ≤ deriv F t := by
  set τ : ℕ → ℝ := fun j ↦ c - (c - a) * (1 / 2) ^ j with hτ
  set Δ : ℕ → ℝ := fun j ↦ (c - a) * (1 / 2) ^ (j + 1) with hΔ
  have hΔpos : ∀ j, 0 < Δ j := fun j ↦ mul_pos (sub_pos.mpr hac) (by positivity)
  have hτΔ : ∀ j, τ (j + 1) = τ j + Δ j := fun j ↦ by simp only [hτ, hΔ]; ring
  have hτlt : ∀ j, τ j < c := fun j ↦ by
    simp only [hτ]; have := mul_pos (sub_pos.mpr hac) (by positivity : (0 : ℝ) < (1 / 2) ^ j)
    linarith
  have hτmono : Monotone τ := monotone_nat_of_le_succ fun j ↦ by
    rw [hτΔ]; exact le_add_of_nonneg_right (hΔpos j).le
  have hτ0 : τ 0 = a := by simp [hτ]
  have hτ1 : τ 1 = (a + c) / 2 := by simp only [hτ]; ring
  have hτex : ∀ t < c, ∃ N, t < τ N := fun t ht ↦ by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (sub_pos.mpr ht) (sub_pos.mpr hac))
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨N, ?_⟩
    rw [lt_div_iff₀ (sub_pos.mpr hac)] at hN
    simp only [hτ]; linarith
  have hB : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Icc ((a + c) / 2) (τ (j + 2)), g u ≤ B := fun j ↦ by
    obtain ⟨B, hB⟩ := hg _ (hτlt (j + 2))
    exact ⟨max B 0, le_max_right _ _, fun u hu ↦ (hB ⟨u, hu, rfl⟩).trans (le_max_left _ _)⟩
  choose B hB0 hB using hB
  set α : ℕ → ℝ := fun j ↦ B j * (1 + Δ j) with hα
  have hα0 : ∀ j, 0 ≤ α j := fun j ↦ mul_nonneg (hB0 j) (by linarith [hΔpos j])
  set T := Real.smoothTransition
  set term : ℕ → ℝ → ℝ := fun j t ↦ α j * smoothRamp (2 * (t - τ j) / Δ j) with hterm
  set d1 : ℕ → ℝ → ℝ := fun j t ↦ α j * (T (2 * (t - τ j) / Δ j) * (2 / Δ j)) with hd1
  set d2 : ℕ → ℝ → ℝ := fun j t ↦
    α j * (deriv T (2 * (t - τ j) / Δ j) * (2 / Δ j) * (2 / Δ j)) with hd2
  have harg : ∀ j t, HasDerivAt (fun t ↦ 2 * (t - τ j) / Δ j) (2 / Δ j) t := fun j t ↦ by
    simpa using (((hasDerivAt_id t).sub_const (τ j)).const_mul 2).div_const (Δ j)
  have hterm' : ∀ j t, HasDerivAt (term j) (d1 j t) t := fun j t ↦
    ((hasDerivAt_smoothRamp _).comp t (harg j t)).const_mul (α j)
  have hd1' : ∀ j t, HasDerivAt (d1 j) (d2 j t) t := fun j t ↦ by
    have hT : HasDerivAt T (deriv T (2 * (t - τ j) / Δ j)) (2 * (t - τ j) / Δ j) :=
      ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) _).hasDerivAt
    exact ((hT.comp t (harg j t)).mul_const (2 / Δ j)).const_mul (α j)
  have hterm0 : ∀ j t, t ≤ τ j → term j t = 0 := fun j t ht ↦ by
    simp only [hterm]
    rw [smoothRamp_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (hΔpos j).le),
      mul_zero]
  have hterm_nn : ∀ j t, 0 ≤ term j t := fun j t ↦ mul_nonneg (hα0 j) (smoothRamp_nonneg _)
  set G : ℕ → ℝ → ℝ := fun N t ↦ ∑ j ∈ Finset.range N, term j t with hG
  set F : ℝ → ℝ := fun t ↦ ∑' j, term j t with hF
  have hFG : ∀ N t, t ≤ τ N → F t = G N t := fun N t ht ↦ by
    refine tsum_eq_sum fun j hj ↦ hterm0 j t (ht.trans (hτmono ?_))
    simpa using hj
  have hFGev : ∀ N t, t < τ N → F =ᶠ[𝓝 t] G N := fun N t ht ↦ by
    filter_upwards [Iio_mem_nhds ht] with u hu using hFG N u hu.le
  have hGd : ∀ N, deriv (G N) = fun t ↦ ∑ j ∈ Finset.range N, d1 j t := fun N ↦
    funext fun t ↦ (HasDerivAt.fun_sum fun j _ ↦ hterm' j t).deriv
  have hGdd : ∀ N t, deriv (deriv (G N)) t = ∑ j ∈ Finset.range N, d2 j t := fun N t ↦ by
    rw [hGd]; exact (HasDerivAt.fun_sum fun j _ ↦ hd1' j t).deriv
  have hGcd : ∀ N, ContDiff ℝ ∞ (G N) := fun N ↦ by
    refine ContDiff.sum fun j _ ↦ contDiff_const.mul (contDiff_smoothRamp.comp ?_)
    fun_prop
  refine ⟨F, fun t ht ↦ ?_, fun t ↦ tsum_nonneg fun j ↦ hterm_nn j t, fun t ht ↦ ?_,
    fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨N, hN⟩ := hτex t ht
    exact ((hGcd N).contDiffAt.congr_of_eventuallyEq (hFGev N t hN)).contDiffWithinAt
  · simp only [hF]
    exact (tsum_congr fun j ↦ hterm0 j t (ht.trans (hτ0 ▸ hτmono (Nat.zero_le j)))).trans
      tsum_zero
  · obtain ⟨N, hN⟩ := hτex t ht
    rw [(hFGev N t hN).deriv_eq, ((hFGev N t hN).deriv).deriv_eq, hGdd, hGd]
    refine ⟨Finset.sum_nonneg fun j _ ↦ ?_, Finset.sum_nonneg fun j _ ↦ ?_⟩
    · exact mul_nonneg (hα0 j) (mul_nonneg (Real.smoothTransition.nonneg _)
        (div_nonneg zero_le_two (hΔpos j).le))
    · exact mul_nonneg (hα0 j) (mul_nonneg (mul_nonneg (deriv_smoothTransition_nonneg _)
        (div_nonneg zero_le_two (hΔpos j).le)) (div_nonneg zero_le_two (hΔpos j).le))
  · classical
    let N₀ := Nat.find (hτex t ht.2)
    have hN₀ : t < τ N₀ := Nat.find_spec (hτex t ht.2)
    have hN₀2 : 2 ≤ N₀ := by
      by_contra h
      have : N₀ ≤ 1 := by omega
      have := hτmono this
      rw [hτ1] at this
      linarith [ht.1]
    obtain ⟨j, hj⟩ : ∃ j, N₀ = j + 2 := ⟨N₀ - 2, by omega⟩
    have hj1 : τ (j + 1) ≤ t := by
      have := Nat.find_min (hτex t ht.2) (show j + 1 < N₀ by omega)
      exact not_lt.mp this
    have hgt : g t ≤ B j := hB j t ⟨ht.1, hj ▸ hN₀.le⟩
    have harg2 : 2 ≤ 2 * (t - τ j) / Δ j := by
      rw [le_div_iff₀ (hΔpos j)]
      rw [hτΔ] at hj1
      linarith
    have hjN : j ∈ Finset.range N₀ := by simp; omega
    refine ⟨?_, ?_⟩
    · rw [hFG N₀ t hN₀.le]
      refine le_trans ?_ (Finset.single_le_sum (fun i _ ↦ hterm_nn i t) hjN)
      have h1 := one_le_smoothRamp harg2
      have : B j ≤ α j := le_mul_of_one_le_right (hB0 j) (by linarith [hΔpos j])
      simp only [hterm]
      nlinarith [hα0 j]
    · rw [(hFGev N₀ t hN₀).deriv_eq, hGd]
      refine le_trans ?_ (Finset.single_le_sum (f := fun i ↦ d1 i t)
        (fun i _ ↦ mul_nonneg (hα0 i) (mul_nonneg (Real.smoothTransition.nonneg _)
          (div_nonneg zero_le_two (hΔpos i).le))) hjN)
      simp only [hd1, T, Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ _),
        one_mul, hα]
      have hD := hΔpos j
      have h2 : 1 ≤ (1 + Δ j) * (2 / Δ j) := by
        rw [mul_div_assoc', le_div_iff₀ hD]; nlinarith
      calc g t ≤ B j := hgt
        _ ≤ B j * ((1 + Δ j) * (2 / Δ j)) := le_mul_of_one_le_right (hB0 j) h2
        _ = _ := by ring

end OneVariable

section Hessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem differentiableAt_deriv_of_contDiffAt {f : ℝ → ℝ} {t : ℝ} (hf : ContDiffAt ℝ 2 f t) :
    DifferentiableAt ℝ (deriv f) t := by
  have h := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : deriv f = fun u ↦ fderiv ℝ f u 1 := funext fun u ↦ (fderiv_apply_one_eq_deriv).symm
  rw [heq]
  exact h.clm_apply (differentiableAt_const _)

/-- The Hessian chain rule for a real function of a real-valued function. -/
theorem realHessian_comp_real {f : ℝ → ℝ} {s : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f (s x)) (hs : ContDiffAt ℝ 2 s x) (v w : E) :
    realHessian (fun y ↦ f (s y)) x v w =
      deriv f (s x) * realHessian s x v w +
        deriv (deriv f) (s x) * (fderiv ℝ s x v * fderiv ℝ s x w) := by
  have hs' : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ s y :=
    (hs.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by norm_num)
  have hf' : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f (s y) :=
    hs.continuousAt.eventually
      ((hf.eventually (by simp)).mono fun t ht ↦ ht.differentiableAt (by norm_num))
  have heq : fderiv ℝ (fun y ↦ f (s y)) =ᶠ[𝓝 x] fun y ↦ deriv f (s y) • fderiv ℝ s y := by
    filter_upwards [hs', hf'] with y hy1 hy2
    rw [fderiv_fun_comp y hy2 hy1]
    ext v
    simp [mul_comm]
  have hd1 := differentiableAt_deriv_of_contDiffAt hf
  have hd2 : DifferentiableAt ℝ (fderiv ℝ s) x :=
    (hs.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH := (hd1.hasDerivAt.comp_hasFDerivAt x hs'.self_of_nhds.hasFDerivAt).smul
    hd2.hasFDerivAt
  rw [realHessian_eq_fderiv, heq.fderiv_eq]
  change fderiv ℝ (deriv f ∘ s • fderiv ℝ s) x v w = _
  rw [hH.fderiv]
  simp [realHessian_eq_fderiv]
  ring

/-- The norm of the derivative of a composition with a real function. -/
theorem norm_fderiv_comp_real_le {f : ℝ → ℝ} {s : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (s x)) (hs : DifferentiableAt ℝ s x) :
    ‖fderiv ℝ (fun y ↦ f (s y)) x‖ ≤ |deriv f (s x)| * ‖fderiv ℝ s x‖ := by
  rw [fderiv_fun_comp x hf hs]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq ?_
  rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]

end Hessian

section Levi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]

/-- The Levi form of a convex nondecreasing function of `s` dominates `f' ∘ s` times the Levi
form of `s`. -/
theorem le_leviForm_comp_real {f : ℝ → ℝ} {s : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f (s x)) (hs : ContDiffAt ℝ 2 s x)
    (hf2 : 0 ≤ deriv (deriv f) (s x)) (v : E) :
    deriv f (s x) * leviForm s x v ≤ leviForm (fun y ↦ f (s y)) x v := by
  simp only [leviForm, realHessian_comp_real hf hs]
  have h1 := mul_nonneg hf2 (mul_self_nonneg (fderiv ℝ s x v))
  have h2 := mul_nonneg hf2 (mul_self_nonneg (fderiv ℝ s x (Complex.I • v)))
  linarith

end Levi

section Exhaustion

open FirstPass

theorem realHessian_exp_affine_self_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : StrongDual ℝ E) (N b : ℝ) (x v : E) :
    0 ≤ realHessian (fun y ↦ Real.exp (N * (ℓ y - b))) x v v := by
  have ha : ContDiff ℝ 2 (fun y : E ↦ N * (ℓ y - b)) := by fun_prop
  rw [realHessian_comp_real (f := Real.exp) (s := fun y ↦ N * (ℓ y - b))
    Real.contDiff_exp.contDiffAt ha.contDiffAt]
  have h0 : realHessian (fun y : E ↦ N * (ℓ y - b)) x v v = 0 := by
    rw [realHessian_eq_fderiv]
    have : fderiv ℝ (fun y : E ↦ N * (ℓ y - b)) = fun _ ↦ N • ℓ := by
      funext y
      exact ((ℓ.hasFDerivAt.sub_const b).const_mul N).fderiv
    rw [this]
    simp
  rw [h0, Real.deriv_exp, Real.deriv_exp, mul_zero, zero_add]
  exact mul_nonneg (Real.exp_pos _).le (mul_self_nonneg _)

theorem realHessian_norm_sub_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p x a b : H) :
    realHessian (fun y : H ↦ ‖y - p‖ ^ 2) x a b = 2 * inner ℝ a b := by
  have h := realHessian_comp_affine (u := fun y : H ↦ ‖y‖ ^ 2) (contDiff_norm_sq ℝ)
    (ContinuousLinearMap.id ℝ H) (-p) x a b
  simp only [ContinuousLinearMap.id_apply, neg_add_eq_sub] at h
  rw [h, realHessian_norm_sq]

/-- A bounded open convex set `L` containing a nonempty compact set `K` carries a smooth convex
function `s ≥ 0` with `{s ≤ 1} ⊆ L`, `s ≤ 1/2` on `K`, and Levi form bounded below by
`ε ‖v‖²`.  It is a sum of exponentials of affine functions (a smoothed polytope contained in
`L`) plus `ε ‖x - p‖²`. -/
theorem exists_smooth_convex_exhaustion {n : ℕ} {L K : Set (ComplexModel n)}
    (hLo : IsOpen L) (hLc : Convex ℝ L) (hLb : Bornology.IsBounded L)
    (hK : IsCompact K) (hKL : K ⊆ L) (hKne : K.Nonempty) :
    ∃ (s : ComplexModel n → ℝ) (ε : ℝ), 0 < ε ∧ ContDiff ℝ ∞ s ∧ ConvexOn ℝ univ s ∧
      (∀ x, 0 ≤ s x) ∧ {x | s x ≤ 1} ⊆ L ∧ (∀ x ∈ K, s x ≤ 1 / 2) ∧
      ∀ x v, ε * ‖v‖ ^ 2 ≤ leviForm s x v := by
  obtain ⟨p, hp⟩ := hKne
  have hsep : ∀ y ∈ frontier L, ∃ (ℓ : StrongDual ℝ (ComplexModel n)) (b δ : ℝ), 0 < δ ∧
      (∀ x ∈ K, ℓ x ≤ b - δ) ∧ b < ℓ y := by
    intro y hy
    have hyL : y ∉ L := fun h ↦ by
      have := hLo.inter_frontier_eq.subset ⟨h, hy⟩
      simp at this
    obtain ⟨ℓ, hℓ⟩ := geometric_hahn_banach_open_point hLc hLo hyL
    obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn ⟨p, hp⟩ ℓ.continuous.continuousOn
    have hlt := hℓ x₀ (hKL hx₀)
    refine ⟨ℓ, (ℓ x₀ + ℓ y) / 2, (ℓ y - ℓ x₀) / 2, by linarith, fun x hx ↦ ?_, by linarith⟩
    have : ℓ x ≤ ℓ x₀ := hmax hx
    linarith
  choose! ℓ b δ hδ hℓK hℓy using hsep
  have hfc : IsCompact (frontier L) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hLb.closure.subset frontier_subset_closure)
  obtain ⟨I, hIfr, hIcov⟩ := hfc.elim_nhds_subcover (fun y ↦ {x | b y < ℓ y x}) fun y hy ↦
    (isOpen_lt continuous_const (ℓ y).continuous).mem_nhds (hℓy y hy)
  set m : ℝ := (I.card : ℝ) with hm
  set κ : ℝ := Real.log (4 * (m + 1)) with hκ
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hκ0 : 0 < κ := Real.log_pos (by linarith)
  set N : ComplexModel n → ℝ := fun y ↦ κ / δ y with hN
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall p
  set D : ℝ := max r 0 with hD
  set ε : ℝ := 1 / (4 * (D ^ 2 + 1)) with hε
  have hε0 : 0 < ε := by positivity
  set e : ComplexModel n → ComplexModel n → ℝ := fun y x ↦ Real.exp (N y * (ℓ y x - b y))
    with he
  set s : ComplexModel n → ℝ := fun x ↦ ∑ y ∈ I, e y x + ε * ‖x - p‖ ^ 2 with hs
  have hecd : ∀ y, ContDiff ℝ ∞ (e y) := fun y ↦ by simp only [he]; fun_prop
  have hqcd : ContDiff ℝ ∞ (fun x : ComplexModel n ↦ ε * ‖x - p‖ ^ 2) :=
    contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  have hscd : ContDiff ℝ ∞ s := (ContDiff.sum fun y _ ↦ hecd y).add hqcd
  refine ⟨s, ε, hε0, hscd, ?_, fun x ↦ ?_, ?_, fun x hx ↦ ?_, fun x v ↦ ?_⟩
  · -- convexity
    have hsum : ConvexOn ℝ univ (fun x ↦ ∑ y ∈ I, e y x) := by
      refine ⟨convex_univ, fun x _ z _ a c ha hc hac ↦ ?_⟩
      simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun y _ ↦ ?_
      have h := convexOn_exp.2 (mem_univ (N y * (ℓ y x - b y))) (mem_univ (N y * (ℓ y z - b y)))
        ha hc hac
      simp only [smul_eq_mul] at h
      convert h using 2
      simp only [map_add, map_smul, smul_eq_mul]
      have : b y = a * b y + c * b y := by rw [← add_mul, hac, one_mul]
      conv_lhs => rw [this]
      ring
    have hq : ConvexOn ℝ univ (fun x : ComplexModel n ↦ ε * ‖x - p‖ ^ 2) := by
      have h := ((convexOn_dist p convex_univ).pow (fun _ _ ↦ dist_nonneg) 2).smul hε0.le
      simpa [dist_eq_norm] using h
    exact hsum.add hq
  · exact add_nonneg (Finset.sum_nonneg fun y _ ↦ (Real.exp_pos _).le) (by positivity)
  · -- the sublevel set lies in `L`
    intro x hx
    set P : Set (ComplexModel n) := {x | ∀ y ∈ I, ℓ y x ≤ b y} with hP
    have hPc : Convex ℝ P := by
      intro u hu w hw a c ha hc hac y hy
      simp only [map_add, map_smul, smul_eq_mul]
      have h1 := mul_le_mul_of_nonneg_left (hu y hy) ha
      have h2 := mul_le_mul_of_nonneg_left (hw y hy) hc
      have h3 : a * b y + c * b y = b y := by rw [← add_mul, hac, one_mul]
      linarith
    have hpP : p ∈ P := fun y hy ↦ by linarith [hℓK y (hIfr y hy) p hp, hδ y (hIfr y hy)]
    have hPL : P ⊆ L := by
      refine hPc.isPreconnected.subset_of_closure_inter_subset hLo ⟨p, hpP, hKL hp⟩ ?_
      rintro z ⟨hz, hzP⟩
      rw [closure_eq_self_union_frontier] at hz
      rcases hz with hz | hz
      · exact hz
      · obtain ⟨y, hyI, hy⟩ := mem_iUnion₂.mp (hIcov hz)
        exact absurd (hzP y hyI) (not_le.mpr hy)
    refine hPL fun y hy ↦ ?_
    have hNy : 0 < N y := div_pos hκ0 (hδ y (hIfr y hy))
    by_contra hlt
    push Not at hlt
    have h1 : 1 < e y x := Real.one_lt_exp_iff.mpr (mul_pos hNy (by linarith))
    have h2 : e y x ≤ ∑ y ∈ I, e y x :=
      Finset.single_le_sum (f := fun y ↦ e y x) (fun y _ ↦ (Real.exp_pos _).le) hy
    have h3 : 0 ≤ ε * ‖x - p‖ ^ 2 := by positivity
    have : s x ≤ 1 := hx
    simp only [hs] at this
    linarith
  · -- the bound on `K`
    have he : ∀ y ∈ I, e y x ≤ 1 / (4 * (m + 1)) := fun y hy ↦ by
      have hδy := hδ y (hIfr y hy)
      have h1 : N y * (ℓ y x - b y) ≤ -κ := by
        have := hℓK y (hIfr y hy) x hx
        have h2 : N y * (ℓ y x - b y) ≤ N y * (-δ y) :=
          mul_le_mul_of_nonneg_left (by linarith) (div_pos hκ0 hδy).le
        rw [mul_neg, hN, div_mul_cancel₀ _ hδy.ne'] at h2
        exact h2
      calc e y x ≤ Real.exp (-κ) := Real.exp_le_exp.mpr h1
        _ = 1 / (4 * (m + 1)) := by
          rw [Real.exp_neg, hκ, Real.exp_log (by positivity), one_div]
    have hsum : ∑ y ∈ I, e y x ≤ 1 / 4 := by
      calc ∑ y ∈ I, e y x ≤ ∑ _y ∈ I, 1 / (4 * (m + 1)) := Finset.sum_le_sum he
        _ = m / (4 * (m + 1)) := by simp [hm, div_eq_mul_inv]
        _ ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
    have hxD : ‖x - p‖ ≤ D := by
      have := hr hx
      rw [mem_closedBall, dist_eq_norm] at this
      exact this.trans (le_max_left _ _)
    have hq : ε * ‖x - p‖ ^ 2 ≤ 1 / 4 := by
      have h1 : ‖x - p‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxD 2
      rw [hε, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    simp only [hs]
    linarith
  · -- the Levi form bound
    have hH : ∀ w : ComplexModel n, 2 * ε * ‖w‖ ^ 2 ≤ realHessian s x w w := fun w ↦ by
      have hsplit : realHessian s x w w =
          realHessian (fun x ↦ ∑ y ∈ I, e y x) x w w +
            ε * realHessian (fun x : ComplexModel n ↦ ‖x - p‖ ^ 2) x w w := by
        rw [show s = (fun x ↦ ∑ y ∈ I, e y x) + (fun x : ComplexModel n ↦ ε * ‖x - p‖ ^ 2)
          from rfl, realHessian_add ((ContDiff.sum fun y _ ↦ hecd y).of_le (by
            norm_cast)).contDiffAt
          (hqcd.of_le (by norm_cast)).contDiffAt]
        congr 1
        exact realHessian_smul (u := fun x : ComplexModel n ↦ ‖x - p‖ ^ 2)
          (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).of_le
            (by norm_cast)).contDiffAt ε w w
      have hsum : 0 ≤ realHessian (fun x ↦ ∑ y ∈ I, e y x) x w w := by
        rw [realHessian, iteratedFDeriv_fun_sum_apply fun y _ ↦
          ((hecd y).of_le (by norm_cast)).contDiffAt, _root_.sum_apply]
        exact Finset.sum_nonneg fun y _ ↦ realHessian_exp_affine_self_nonneg _ _ _ x w
      rw [hsplit, realHessian_norm_sub_sq, real_inner_self_eq_norm_sq]
      nlinarith
    have h1 := hH v
    have h2 := hH (Complex.I • v)
    rw [norm_smul, Complex.norm_I, one_mul] at h2
    simp only [leviForm]
    linarith

end Exhaustion

section Cutoff

/-- Width of the `k`-th transition layer of the cutoffs. -/
def cutoffWidth (k : ℕ) : ℝ := 1 / (20 * ((k : ℝ) + 1))

theorem cutoffWidth_pos (k : ℕ) : 0 < cutoffWidth k := by
  unfold cutoffWidth; positivity

theorem two_mul_cutoffWidth_le (k : ℕ) : 2 * cutoffWidth k ≤ 1 / 10 := by
  unfold cutoffWidth
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ k := k.cast_nonneg
  nlinarith

theorem exists_two_mul_cutoffWidth_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, 2 * cutoffWidth k < δ := by
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / δ)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hk' : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  unfold cutoffWidth
  rw [mul_one_div, div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hδ] at hk₀
  nlinarith

/-- The `k`-th one-variable cutoff: `1` on `(-∞, 1 - 2 w_k]` and `0` on `[1 - w_k, ∞)`. -/
def cutoffProfile (k : ℕ) (t : ℝ) : ℝ :=
  1 - Real.smoothTransition ((t - (1 - 2 * cutoffWidth k)) / cutoffWidth k)

theorem contDiff_cutoffProfile (k : ℕ) : ContDiff ℝ ∞ (cutoffProfile k) := by
  unfold cutoffProfile
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem cutoffProfile_of_le {k : ℕ} {t : ℝ} (ht : t ≤ 1 - 2 * cutoffWidth k) :
    cutoffProfile k t = 1 := by
  rw [cutoffProfile, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (cutoffWidth_pos k).le), sub_zero]

theorem cutoffProfile_of_ge {k : ℕ} {t : ℝ} (ht : 1 - cutoffWidth k ≤ t) :
    cutoffProfile k t = 0 := by
  rw [cutoffProfile, Real.smoothTransition.one_of_one_le, sub_self]
  rw [le_div_iff₀ (cutoffWidth_pos k)]
  linarith

theorem cutoffProfile_nonneg (k : ℕ) (t : ℝ) : 0 ≤ cutoffProfile k t :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem cutoffProfile_le_one (k : ℕ) (t : ℝ) : cutoffProfile k t ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

theorem deriv_cutoffProfile (k : ℕ) (t : ℝ) :
    deriv (cutoffProfile k) t =
      -(deriv Real.smoothTransition ((t - (1 - 2 * cutoffWidth k)) / cutoffWidth k) /
        cutoffWidth k) := by
  have hT : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((t - (1 - 2 * cutoffWidth k)) / cutoffWidth k))
      ((t - (1 - 2 * cutoffWidth k)) / cutoffWidth k) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) _).hasDerivAt
  have harg : HasDerivAt (fun t ↦ (t - (1 - 2 * cutoffWidth k)) / cutoffWidth k)
      (1 / cutoffWidth k) t := by
    simpa using ((hasDerivAt_id t).sub_const (1 - 2 * cutoffWidth k)).div_const (cutoffWidth k)
  have h : HasDerivAt (cutoffProfile k) (-(deriv Real.smoothTransition
      ((t - (1 - 2 * cutoffWidth k)) / cutoffWidth k) * (1 / cutoffWidth k))) t := by
    have h1 := hT.comp t harg
    have h2 := h1.const_sub 1
    exact h2
  rw [h.deriv]
  ring

theorem deriv_cutoffProfile_of_lt {k : ℕ} {t : ℝ} (ht : t < 1 - 2 * cutoffWidth k) :
    deriv (cutoffProfile k) t = 0 := by
  rw [deriv_cutoffProfile, deriv_smoothTransition_of_neg
    (div_neg_of_neg_of_pos (by linarith) (cutoffWidth_pos k))]
  simp

theorem abs_deriv_cutoffProfile_le {M : ℝ} (hM : ∀ u, |deriv Real.smoothTransition u| ≤ M)
    (k : ℕ) {t : ℝ} (ht : t < 1) :
    |deriv (cutoffProfile k) t| ≤ 2 * M / (1 - t) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rcases lt_or_ge t (1 - 2 * cutoffWidth k) with h | h
  · rw [deriv_cutoffProfile_of_lt h, abs_zero]
    exact div_nonneg (by positivity) (by linarith)
  · have hw := cutoffWidth_pos k
    rw [deriv_cutoffProfile, abs_neg, abs_div, abs_of_pos hw]
    calc |deriv Real.smoothTransition ((t - (1 - 2 * cutoffWidth k)) / cutoffWidth k)| /
          cutoffWidth k ≤ M / cutoffWidth k := by gcongr; exact hM _
      _ ≤ 2 * M / (1 - t) := by
        rw [div_le_div_iff₀ hw (by linarith)]
        nlinarith

end Cutoff

section Main

open FirstPass

/-- **Cutoff and weight data for Hörmander's three-weight `L²` method** on a bounded convex
domain `L ⊆ ℂⁿ` (Hörmander, *An Introduction to Complex Analysis in Several Variables*,
§4.1–4.2).  There are a convex open `L' ⋐ L`, an open `U₀` with `K ⊆ U₀ ⊆ L'`, cutoffs `η k`
compactly supported in `L'` and eventually `1` near each point of `L'`, and weights `ψ₀ ≥ 0`,
`χ`, vanishing on `U₀`, with `|∇η_k|² ≤ e^{ψ₀}`, `2ψ₀ ≤ χ`, and
`A |∇ψ₀|² |ξ|² ≤ Levi(χ)(ξ)` on `L'`. -/
theorem exists_hormanderCutoffData {n : ℕ} {L : Set (ComplexModel n)} (hLo : IsOpen L)
    (hLc : Convex ℝ L) (hLb : Bornology.IsBounded L) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKL : K ⊆ L) (A : ℝ) :
    ∃ (L' : Set (ComplexModel n)) (U₀ : Set (ComplexModel n)) (η : ℕ → ComplexModel n → ℝ)
      (ψ₀ χ : ComplexModel n → ℝ),
      IsOpen L' ∧ Convex ℝ L' ∧ closure L' ⊆ L ∧ IsOpen U₀ ∧ K ⊆ U₀ ∧ U₀ ⊆ L' ∧
      (∀ k, ContDiff ℝ ∞ (η k) ∧ HasCompactSupport (η k) ∧ tsupport (η k) ⊆ L' ∧
        ∀ x, 0 ≤ η k x ∧ η k x ≤ 1) ∧
      (∀ x ∈ L', ∀ᶠ k in Filter.atTop, η k =ᶠ[𝓝 x] fun _ ↦ 1) ∧
      ContDiffOn ℝ ∞ ψ₀ L' ∧ ContDiffOn ℝ ∞ χ L' ∧
      (∀ k, ∀ x ∈ L', ‖fderiv ℝ (η k) x‖ ^ 2 ≤ Real.exp (ψ₀ x)) ∧
      (∀ x, 0 ≤ ψ₀ x) ∧ (∀ x ∈ U₀, ψ₀ x = 0 ∧ χ x = 0) ∧
      (∀ x ∈ L', 2 * ψ₀ x ≤ χ x) ∧
      (∀ x ∈ L', ∀ ξ, A * ‖fderiv ℝ ψ₀ x‖ ^ 2 * ‖ξ‖ ^ 2 ≤ leviForm χ x ξ) ∧
      (∀ x ∈ L', ∀ ξ, 0 ≤ leviForm χ x ξ) := by
  rcases L.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · obtain rfl : K = ∅ := subset_empty_iff.mp hKL
    refine ⟨∅, ∅, fun _ _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, ?_⟩
    simp [HasCompactSupport, contDiff_const, convex_empty]
  obtain ⟨s, ε, hε, hscd, hsconv, -, hsL, hsK, hslevi⟩ :=
    exists_smooth_convex_exhaustion hLo hLc hLb (hK.insert p) (insert_subset hp hKL)
      (insert_nonempty p K)
  have hsc : Continuous s := hscd.continuous
  have hScpt : IsCompact {x | s x ≤ 1} :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_le hsc continuous_const) (hLb.subset hsL)
  obtain ⟨G₀, hG₀⟩ := hScpt.exists_bound_of_continuousOn
    (hscd.continuous_fderiv (by norm_cast)).continuousOn
  set G : ℝ := max G₀ 0 with hGdef
  have hG0 : 0 ≤ G := le_max_right _ _
  have hG : ∀ x, s x < 1 → ‖fderiv ℝ s x‖ ≤ G := fun x hx ↦
    (hG₀ x (show s x ≤ 1 from hx.le)).trans (le_max_left _ _)
  obtain ⟨M, hM⟩ := exists_abs_deriv_smoothTransition_le
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- the weight profile `φ`
  have hg₁ : ∀ t < (1 : ℝ), BddAbove ((fun t ↦ (2 * M * G) ^ 2 / (1 - t) ^ 2) ''
      Icc ((4 / 5 + 1) / 2) t) := fun t ht ↦ by
    refine isCompact_Icc.bddAbove_image (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
    intro u hu
    have : u < 1 := hu.2.trans_lt ht
    exact pow_ne_zero 2 (by linarith)
  obtain ⟨φ, hφcd, hφ0, hφzero, -, hφbig⟩ :=
    exists_smooth_convex_majorant (by norm_num : (4 / 5 : ℝ) < 1) _ hg₁
  have hφd0 : ∀ t < (4 / 5 : ℝ), deriv φ t = 0 := fun t ht ↦ by
    have : φ =ᶠ[𝓝 t] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds ht] with u hu using hφzero u hu.le
    rw [this.deriv_eq]
    simp
  -- the convex profile `χ₀`
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hg₂ : ∀ t < (1 : ℝ), BddAbove ((fun t ↦ max (2 * φ t) (A' * G ^ 2 * deriv φ t ^ 2 / ε)) ''
      Icc ((3 / 5 + 1) / 2) t) := fun t ht ↦ by
    have hsub : Icc ((3 / 5 + 1) / 2) t ⊆ Iio 1 := fun u hu ↦ hu.2.trans_lt ht
    have h1 := (hφcd.continuousOn).mono hsub
    have h2 := (hφcd.continuousOn_deriv_of_isOpen isOpen_Iio (by norm_cast)).mono hsub
    have h3 : ContinuousOn (fun t ↦ 2 * φ t) (Icc ((3 / 5 + 1) / 2) t) :=
      continuousOn_const.mul h1
    have h4 : ContinuousOn (fun t ↦ A' * G ^ 2 * deriv φ t ^ 2 / ε) (Icc ((3 / 5 + 1) / 2) t) :=
      (continuousOn_const.mul (h2.pow 2)).div_const ε
    exact isCompact_Icc.bddAbove_image (h3.sup h4)
  obtain ⟨χ₀, hχcd, hχ0, hχzero, hχd, hχbig⟩ :=
    exists_smooth_convex_majorant (by norm_num : (3 / 5 : ℝ) < 1) _ hg₂
  have hχat : ∀ t < (1 : ℝ), ContDiffAt ℝ 2 χ₀ t := fun t ht ↦
    (hχcd.contDiffAt (Iio_mem_nhds ht)).of_le (by norm_cast)
  have hsat : ∀ x, ContDiffAt ℝ 2 s x := fun x ↦ (hscd.of_le (by norm_cast)).contDiffAt
  have hlevi : ∀ x, s x < 1 → ∀ ξ,
      deriv χ₀ (s x) * (ε * ‖ξ‖ ^ 2) ≤ leviForm (fun y ↦ χ₀ (s y)) x ξ := fun x hx ξ ↦
    (mul_le_mul_of_nonneg_left (hslevi x ξ) (hχd _ hx).1).trans
      (le_leviForm_comp_real (hχat _ hx) (hsat x) (hχd _ hx).2 ξ)
  refine ⟨{x | s x < 1}, {x | s x < 3 / 5}, fun k x ↦ cutoffProfile k (s x),
    fun x ↦ φ (s x), fun x ↦ χ₀ (s x), isOpen_lt hsc continuous_const, ?_,
    (closure_lt_subset_le hsc continuous_const).trans hsL, isOpen_lt hsc continuous_const,
    fun x hx ↦ (hsK x (mem_insert_of_mem p hx)).trans_lt (by norm_num),
    fun x (hx : s x < 3 / 5) ↦ show s x < 1 by linarith, fun k ↦ ?_, fun x hx ↦ ?_,
    hφcd.comp hscd.contDiffOn fun x hx ↦ hx, hχcd.comp hscd.contDiffOn fun x hx ↦ hx,
    fun k x hx ↦ ?_, fun x ↦ hφ0 _, fun x (hx : s x < 3 / 5) ↦
      ⟨hφzero _ (by linarith), hχzero _ hx.le⟩, fun x hx ↦ ?_, fun x hx ξ ↦ ?_,
    fun x hx ξ ↦ ?_⟩
  · simpa using hsconv.convex_lt 1
  · -- the cutoffs
    have hw := cutoffWidth_pos k
    have hsupp : tsupport (fun x ↦ cutoffProfile k (s x)) ⊆ {x | s x ≤ 1 - cutoffWidth k} := by
      refine closure_minimal (fun x hx ↦ ?_) (isClosed_le hsc continuous_const)
      by_contra h
      exact hx (cutoffProfile_of_ge (not_le.mp h).le)
    refine ⟨(contDiff_cutoffProfile k).comp hscd,
      hScpt.of_isClosed_subset (isClosed_tsupport _) fun x hx ↦ ?_, fun x hx ↦ ?_,
      fun x ↦ ⟨cutoffProfile_nonneg _ _, cutoffProfile_le_one _ _⟩⟩
    · exact (show s x ≤ 1 - cutoffWidth k from hsupp hx).trans (by linarith)
    · exact (show s x ≤ 1 - cutoffWidth k from hsupp hx).trans_lt (by linarith)
  · -- the cutoffs are eventually `1` near each point
    have hx' : s x < 1 := hx
    obtain ⟨k₀, hk₀⟩ := exists_two_mul_cutoffWidth_lt (sub_pos.mpr hx')
    filter_upwards [eventually_ge_atTop k₀] with k hk
    have hlt : s x < 1 - 2 * cutoffWidth k := by linarith [hk₀ k hk]
    filter_upwards [(isOpen_lt hsc continuous_const).mem_nhds hlt] with y hy
    exact cutoffProfile_of_le (le_of_lt hy)
  · -- the gradient bound for the cutoffs
    have hx' : s x < 1 := hx
    have hn : ‖fderiv ℝ (fun y ↦ cutoffProfile k (s y)) x‖ ≤
        |deriv (cutoffProfile k) (s x)| * G :=
      (norm_fderiv_comp_real_le (((contDiff_cutoffProfile k).differentiable
        (by norm_num)) _) (hscd.differentiable (by norm_num) x)).trans
        (mul_le_mul_of_nonneg_left (hG x hx') (abs_nonneg _))
    rcases lt_or_ge (s x) ((4 / 5 + 1) / 2) with h | h
    · rw [deriv_cutoffProfile_of_lt (by linarith [two_mul_cutoffWidth_le k]), abs_zero,
        zero_mul] at hn
      have : ‖fderiv ℝ (fun y ↦ cutoffProfile k (s y)) x‖ = 0 :=
        le_antisymm hn (norm_nonneg _)
      rw [this]
      simpa using (Real.exp_pos _).le
    · have hb := abs_deriv_cutoffProfile_le hM k hx'
      have h1 : 0 < 1 - s x := sub_pos.mpr hx'
      have hsq : ‖fderiv ℝ (fun y ↦ cutoffProfile k (s y)) x‖ ^ 2 ≤
          (2 * M * G) ^ 2 / (1 - s x) ^ 2 := by
        have h2 : ‖fderiv ℝ (fun y ↦ cutoffProfile k (s y)) x‖ ≤ 2 * M / (1 - s x) * G :=
          hn.trans (mul_le_mul_of_nonneg_right hb hG0)
        calc _ ≤ (2 * M / (1 - s x) * G) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
          _ = _ := by field_simp
      have := (hφbig (s x) ⟨h, hx'⟩).1
      linarith [Real.add_one_le_exp (φ (s x))]
  · -- `2 ψ₀ ≤ χ`
    have hx' : s x < 1 := hx
    rcases lt_or_ge (s x) ((3 / 5 + 1) / 2) with h | h
    · change 2 * φ (s x) ≤ χ₀ (s x)
      rw [hφzero _ (by linarith), mul_zero]
      exact hχ0 _
    · exact (le_max_left _ _).trans (hχbig (s x) ⟨h, hx'⟩).1
  · -- the Levi form bound
    have hx' : s x < 1 := hx
    have hn : ‖fderiv ℝ (fun y ↦ φ (s y)) x‖ ≤ |deriv φ (s x)| * G :=
      (norm_fderiv_comp_real_le ((hφcd.differentiableOn (by norm_num)).differentiableAt
        (Iio_mem_nhds hx')) (hscd.differentiable (by norm_num) x)).trans
        (mul_le_mul_of_nonneg_left (hG x hx') (abs_nonneg _))
    have hn2 : ‖fderiv ℝ (fun y ↦ φ (s y)) x‖ ^ 2 ≤ deriv φ (s x) ^ 2 * G ^ 2 := by
      calc _ ≤ (|deriv φ (s x)| * G) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
        _ = _ := by rw [mul_pow, sq_abs]
    have hkey : A' * (deriv φ (s x) ^ 2 * G ^ 2) ≤ deriv χ₀ (s x) * ε := by
      rcases lt_or_ge (s x) ((3 / 5 + 1) / 2) with h | h
      · rw [hφd0 _ (by linarith)]
        simpa using mul_nonneg (hχd _ hx').1 hε.le
      · have := (le_max_right _ _).trans (hχbig (s x) ⟨h, hx'⟩).2
        rw [div_le_iff₀ hε] at this
        linarith
    have hA : A * ‖fderiv ℝ (fun y ↦ φ (s y)) x‖ ^ 2 ≤ A' * (deriv φ (s x) ^ 2 * G ^ 2) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hn2 hA'0)
    calc A * ‖fderiv ℝ (fun y ↦ φ (s y)) x‖ ^ 2 * ‖ξ‖ ^ 2
        ≤ deriv χ₀ (s x) * ε * ‖ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hA.trans hkey) (by positivity)
      _ = deriv χ₀ (s x) * (ε * ‖ξ‖ ^ 2) := by ring
      _ ≤ _ := hlevi x hx' ξ
  · exact (mul_nonneg (hχd _ hx).1 (by positivity)).trans (hlevi x hx ξ)

end Main

end

end SGPT.Foundations.Analysis.Pending
