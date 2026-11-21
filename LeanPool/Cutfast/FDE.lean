/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Barenblatt
public import LeanPool.Cutfast.PDE
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The solution of `∂ₜu = Δ(uᵐ)`, the time change, initial and long-time behavior
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace BoundedContinuousFunction MatrixOrder

namespace Cutfast

namespace FDE

open Barenblatt PDE

variable {d : ℕ} {m : ℝ}

/-- The base `c + κ₀ (τ^α)^{-2} ‖y - x₀‖²` of the explicit solution `u`. -/
noncomputable def fdeBase (d : ℕ) (m : ℝ) (x₀ : E d) (τ : ℝ) (y : E d) : ℝ :=
  barenblattConst d m + alpha d m * (1 - m) / (2 * m) *
    ((τ ^ alpha d m)⁻¹) ^ 2 * ‖y - x₀‖ ^ 2

/-- The explicit solution `u` in terms of `fdeBase`. -/
theorem fdeSolution_eq_max (d : ℕ) (m : ℝ) (x₀ : E d) (τ : ℝ) (y : E d) :
    fdeSolution d m x₀ τ y = (τ ^ (alpha d m * d))⁻¹ *
      (max (fdeBase d m x₀ τ y) 0) ^ (1 / (m - 1)) := by
  simp only [fdeSolution, barenblatt, barenblattWith, fdeBase, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, mul_assoc]

/-- Time derivative of the base. -/
theorem hasDerivAt_fdeBase {α : ℝ} (hαd : α = alpha d m) (x₀ : E d) {t : ℝ} (ht : 0 < t)
    (x : E d) :
    HasDerivAt (fun τ => fdeBase d m x₀ τ x)
      (α * (1 - m) / (2 * m) * (-2 * (1 * α * t ^ (α - 1)) / (t ^ α) ^ 3) * ‖x - x₀‖ ^ 2) t := by
  subst hαd
  have ha : HasDerivAt (fun τ => (τ ^ alpha d m)⁻¹ ^ 2) _ t :=
    (((hasDerivAt_id t).rpow_const (p := alpha d m) (Or.inl ht.ne')).inv
      (rpow_pos_of_pos ht _).ne').pow 2
  have := ((ha.const_mul (alpha d m * (1 - m) / (2 * m))).mul_const (‖x - x₀‖ ^ 2)).const_add
    (barenblattConst d m)
  refine this.congr_deriv ?_
  have hpos := (rpow_pos_of_pos ht (alpha d m)).ne'
  simp only [id, Nat.reduceSub, pow_one, Nat.cast_ofNat, Pi.inv_apply]
  generalize t ^ alpha d m = A at hpos ⊢
  field_simp

/-- `u(t,·)` is the rescaling `A^{-d} B(A⁻¹(x - x₀))`, `A = t^α`. -/
theorem fdeSolution_eq_scaled (x₀ : E d) {t : ℝ} (ht : 0 < t) (x : E d) :
    fdeSolution d m x₀ t x =
      ((t ^ alpha d m) ^ d)⁻¹ * barenblatt d m ((t ^ alpha d m)⁻¹ • (x - x₀)) := by
  rw [fdeSolution, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]

/-- The Barenblatt profile is nonnegative. -/
theorem barenblatt_nonneg (x : E d) : 0 ≤ barenblatt d m x :=
  Real.rpow_nonneg (le_max_right _ _) _

/-- Weak convergence of the image of a probability density `f` under `y ↦ a y + h`, as
`a → 0` and `h → x₀`. -/
theorem tendsto_integral_affine {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : E d → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f) (hf1 : ∫ x, f x = 1)
    {a : ι → ℝ} {h : ι → E d} {x₀ : E d} (ha : Tendsto a l (𝓝 0)) (hh : Tendsto h l (𝓝 x₀))
    (φ : E d →ᵇ ℝ) :
    Tendsto (fun i => ∫ y, φ (a i • y + h i) * f y) l (𝓝 (φ x₀)) := by
  have key := tendsto_integral_filter_of_dominated_convergence (l := l)
    (F := fun i y => φ (a i • y + h i) * f y) (f := fun y => φ x₀ * f y)
    (fun y => ‖φ‖ * f y) (Eventually.of_forall fun i => by fun_prop)
    (Eventually.of_forall fun i => ae_of_all _ fun y => by
      rw [norm_mul, Real.norm_of_nonneg (hf0 y)]
      exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm _) (hf0 y))
    (hfi.const_mul _) (ae_of_all _ fun y => by
      refine ((φ.continuous.tendsto x₀).comp ?_).mul_const _
      simpa using (ha.smul_const y).add hh)
  rwa [integral_const_mul, hf1, mul_one] at key

end FDE

open Barenblatt PDE FDE

/-- `u` solves `∂ₜu = Δ(uᵐ)` (eq. (FDE)) at every point `(t,x)`, `t > 0`, of positivity of `u`. -/
theorem fdeSolution_hasDerivAt' {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) {t : ℝ} (ht : 0 < t) {x : E d}
    (hx : 0 < fdeSolution d m x₀ t x) :
    HasDerivAt (fun s => fdeSolution d m x₀ s x)
      (Laplacian.laplacian (fun y => fdeSolution d m x₀ t y ^ m) x) t := by
  have h : Admissible d m := ⟨hd, hm0, hm1, hmd⟩
  have hm1' : m - 1 ≠ 0 := sub_ne_zero.mpr hm1
  have hαpos : 0 < alpha d m := alpha_pos h
  have hα1 : alpha d m * (2 - d * (1 - m)) = 1 := alpha_mul h
  set α := alpha d m with hαdef
  set c := barenblattConst d m with hcdef
  set q : ℝ := 1 / (m - 1) with hqdef
  set a := t ^ α with hadef
  have ha : 0 < a := rpow_pos_of_pos ht _
  set S := t ^ (α * d) with hSdef
  have hS : 0 < S := rpow_pos_of_pos ht _
  set r0 := ‖x - x₀‖ ^ 2 with hr0
  set B0 := fdeBase d m x₀ t x with hB0def
  have hB0 : 0 < B0 := by
    by_contra hle
    rw [fdeSolution_eq_max, max_eq_right (not_lt.mp hle), zero_rpow (one_div_ne_zero hm1'),
      mul_zero] at hx
    exact lt_irrefl _ hx
  set K := α * (1 - m) / (2 * m) * (a⁻¹) ^ 2 with hKdef
  -- time derivative
  have hb := hasDerivAt_fdeBase hαdef x₀ ht x
  have hT := (((hasDerivAt_id t).rpow_const (p := α * d) (Or.inl ht.ne')).inv hS.ne').mul
    (hb.rpow_const (p := q) (Or.inl hB0.ne'))
  have hT' := hT.congr_of_eventuallyEq (f₁ := fun τ => fdeSolution d m x₀ τ x) (by
    filter_upwards [hb.continuousAt.eventually (lt_mem_nhds hB0)] with τ hτ
    rw [fdeSolution_eq_max, max_eq_left hτ.le]
    rfl)
  -- Laplacian
  have hlap : Laplacian.laplacian (fun y => fdeSolution d m x₀ t y ^ m) x =
      4 * r0 * ((S⁻¹) ^ m * (K * (q * m) * (K * (q * m - 1) * B0 ^ (q * m - 1 - 1)))) +
        2 * d * ((S⁻¹) ^ m * (K * (q * m) * B0 ^ (q * m - 1))) := by
    simp_rw [fdeSolution_eq_max]
    exact laplacian_clippedRadialAffine_rpow (inv_nonneg.2 hS.le) c K q m x₀ x hB0
  -- algebra
  rw [hlap]
  refine hT'.congr_deriv ?_
  simp only [Pi.inv_apply, id]
  have hS1 : t ^ (α * d - 1) = S / t := rpow_sub_one ht.ne' _
  have ha1 : t ^ (α - 1) = a / t := rpow_sub_one ht.ne' _
  have hB1 : B0 ^ (q - 1) = B0 ^ q / B0 := rpow_sub_one hB0.ne' _
  have hqm : q * m - 1 = q := by rw [hqdef]; field_simp; ring
  have hAm : S⁻¹ ^ m = a ^ 2 / (t * S) := inverse_scale_rpow ht hα1
  rw [hS1, ha1, hqm, hB1, hAm]
  rw [show t ^ (α * d) = S from rfl, show t ^ α = a from rfl,
    show fdeBase d m x₀ t x = B0 from rfl, show ‖x - x₀‖ ^ 2 = r0 from rfl, hKdef, hqdef]
  generalize B0 ^ q = P
  clear_value a S B0 r0 α
  field_simp
  ring

/-- For every `t > 0`, `u(t,·)` is a probability density function (positivity and mass are
preserved). -/
theorem fdeSolution_isProbabilityDensity' {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m)
    (hm1 : m ≠ 1) (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) {t : ℝ} (ht : 0 < t) :
    (∀ x, 0 ≤ fdeSolution d m x₀ t x) ∧
      IsProbabilityMeasure (densityMeasure (fdeSolution d m x₀ t)) := by
  have hB := barenblattConst_spec' hd hm0 hm1 hmd
  have hA : 0 < t ^ alpha d m := rpow_pos_of_pos ht _
  have hfun : fdeSolution d m x₀ t =
      fun x => ((t ^ alpha d m) ^ d)⁻¹ * barenblatt d m ((t ^ alpha d m)⁻¹ • (x - x₀)) :=
    funext (fdeSolution_eq_scaled x₀ ht)
  have h0 : ∀ x, 0 ≤ fdeSolution d m x₀ t x := fun x => by
    rw [hfun]
    exact mul_nonneg (by positivity) (barenblatt_nonneg _)
  refine ⟨h0, isProbabilityMeasure_densityMeasure h0 ?_ ?_⟩
  · rw [hfun]
    exact integrable_scaled hB.2.1 hA x₀
  · rw [hfun, integral_scaled _ hA x₀]
    exact hB.2.2.1

/-- The time change (eqs. (uv) and (FDEFPv)): `v(t,x) = e^{dt} u(α(e^{t/α} - 1), eᵗx)`. -/
theorem solution_eq_fdeSolution' {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) {t : ℝ} (ht : 0 < t) (x : E d) :
    solution d m x₀ t x =
      exp (d * t) * fdeSolution d m x₀ (alpha d m * (exp (t / alpha d m) - 1)) (exp t • x) := by
  have h : Admissible d m := ⟨hd, hm0, hm1, hmd⟩
  have hα := alpha_pos h
  set α := alpha d m with hαdef
  have hτ : 0 < α * (exp (t / α) - 1) :=
    mul_pos hα (sub_pos.2 (one_lt_exp_iff.2 (div_pos ht hα)))
  set τ := α * (exp (t / α) - 1) with hτdef
  have hs : α * (1 - exp (-t / α)) = τ * exp (-t / α) := by
    rw [hτdef, neg_div, exp_neg]
    field_simp
  have hpow : ∀ p : ℝ, (α * (1 - exp (-t / α))) ^ p = τ ^ p * exp (-(t * (p / α))) := by
    intro p
    rw [hs, mul_rpow hτ.le (exp_pos _).le, ← exp_mul]
    congr 2
    ring
  unfold solution fdeSolution
  rw [← hαdef, hpow, hpow, div_self hα.ne', mul_one,
    show α * ↑d / α = d by field_simp, mul_inv, mul_inv, ← exp_neg, ← exp_neg, neg_neg, neg_neg,
    smul_sub, smul_sub, smul_smul, smul_smul, mul_assoc ((τ ^ α)⁻¹), ← exp_add, add_neg_cancel,
    exp_zero, mul_one, mul_comm t]
  ring

/-- Initial condition: `u(t,·) → δ_{x₀}` weakly as `t → 0⁺`. -/
theorem tendsto_fdeSolution_zero' {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) (φ : E d →ᵇ ℝ) :
    Tendsto (fun t => ∫ x, φ x * fdeSolution d m x₀ t x) (𝓝[>] 0) (𝓝 (φ x₀)) := by
  have h : Admissible d m := ⟨hd, hm0, hm1, hmd⟩
  have hB := barenblattConst_spec' hd hm0 hm1 hmd
  have hα := alpha_pos h
  have hlim : Tendsto (fun t : ℝ => t ^ alpha d m) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (alpha d m) (Or.inr hα.le)).tendsto
    rw [zero_rpow hα.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine (tendsto_integral_affine (fun x => barenblatt_nonneg x) hB.2.1 hB.2.2.1 hlim
    tendsto_const_nhds φ).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hA : 0 < t ^ alpha d m := rpow_pos_of_pos ht _
  have e := integral_comp_affine (fun x => φ x * fdeSolution d m x₀ t x) hA x₀
  have e' : ∀ y, φ (t ^ alpha d m • y + x₀) * fdeSolution d m x₀ t (t ^ alpha d m • y + x₀) =
      ((t ^ alpha d m) ^ d)⁻¹ * (φ (t ^ alpha d m • y + x₀) * barenblatt d m y) := fun y => by
    rw [fdeSolution_eq_scaled x₀ ht, add_sub_cancel_right, inv_smul_smul₀ hA.ne']
    ring
  simp only [e', integral_const_mul] at e
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero d hA.ne')) e

/-- Initial condition: `v(t,·) → δ_{x₀}` weakly as `t → 0⁺`. -/
theorem tendsto_solution_zero' {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) (φ : E d →ᵇ ℝ) :
    Tendsto (fun t => ∫ x, φ x * solution d m x₀ t x) (𝓝[>] 0) (𝓝 (φ x₀)) := by
  have h : Admissible d m := ⟨hd, hm0, hm1, hmd⟩
  have hα := alpha_pos h
  have hlim : Tendsto (scaleFactor d m) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Continuous fun t : ℝ => 1 - exp (-t / alpha d m) := by fun_prop
    have := (h1.tendsto 0).rpow_const (p := alpha d m) (Or.inr hα.le)
    simp only [neg_zero, zero_div, exp_zero, sub_self, zero_rpow hα.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hh : Tendsto (fun t : ℝ => exp (-t) • x₀) (𝓝[>] 0) (𝓝 x₀) := by
    have : Continuous fun t : ℝ => exp (-t) • x₀ := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine (tendsto_integral_affine (equilibrium_nonneg h) (integrable_equilibrium h)
    (integral_equilibrium h) hlim hh φ).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (integral_mul_solution h x₀ ht φ).symm

/-- Long-time behavior (eq. (vinf)): `v(t,x) → v_∞(x)` as `t → ∞`, and
`v_∞(x) = (C + (1-m)/(2m)|x|²)₊^{1/(m-1)}` for some constant `C > 0`. -/
theorem tendsto_solution_atTop' {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) :
    (∀ x, Tendsto (fun t => solution d m x₀ t x) atTop (𝓝 (equilibrium d m x))) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ x, equilibrium d m x = (max (C + (1 - m) / (2 * m) * ‖x‖ ^ 2) 0) ^ (1 / (m -
      1)) := by
  have h : Admissible d m := ⟨hd, hm0, hm1, hmd⟩
  have hα := alpha_pos h
  refine ⟨fun x => ?_, equilibriumConst d m, equilibriumConst_pos h, equilibrium_eq h⟩
  -- continuity of the equilibrium
  have hcont : Continuous (equilibrium d m) := by
    rw [show equilibrium d m = _ from funext (equilibrium_eq h)]
    refine Continuous.rpow_const (by fun_prop) fun y => ?_
    rcases lt_or_gt_of_ne hm1 with hm | hm
    · left
      have : 0 ≤ (1 - m) / (2 * m) * ‖y‖ ^ 2 := by
        have : 0 < 1 - m := by linarith
        positivity
      have := equilibriumConst_pos h
      exact (lt_max_of_lt_left (by linarith)).ne'
    · right
      exact (p_compact_pos hm).le
  have hexp : Tendsto (fun t : ℝ => exp (-t / alpha d m)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (by
      simpa only [neg_div, Function.comp_def, id] using
        tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const hα))
  have ha : Tendsto (scaleFactor d m) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).rpow_const (p := alpha d m)
      (Or.inr hα.le)
    simp only [sub_zero, one_rpow] at this
    exact this
  have hh : Tendsto (fun t : ℝ => exp (-t) • x₀) atTop (𝓝 0) := by
    simpa using (tendsto_exp_neg_atTop_nhds_zero).smul_const x₀
  have hlim : Tendsto (fun t => (scaleFactor d m t ^ d)⁻¹ *
      equilibrium d m ((scaleFactor d m t)⁻¹ • (x - exp (-t) • x₀))) atTop
      (𝓝 ((1 ^ d)⁻¹ * equilibrium d m ((1 : ℝ)⁻¹ • (x - 0)))) :=
    ((ha.pow d).inv₀ (by simp)).mul ((hcont.tendsto _).comp
      ((ha.inv₀ one_ne_zero).smul (tendsto_const_nhds.sub hh)))
  simp only [one_pow, inv_one, one_mul, one_smul, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact (solution_eq h x₀ ht x).symm

/-- `u` solves `∂ₜu = Δ(uᵐ)` (eq. (FDE)) at every point `(t,x)`, `t > 0`, of positivity of `u`. -/
alias fdeSolution_hasDerivAt := fdeSolution_hasDerivAt'

/-- For every `t > 0`, `u(t,·)` is a probability density function (positivity and mass are
preserved). -/
alias fdeSolution_isProbabilityDensity := fdeSolution_isProbabilityDensity'

/-- The time change (eqs. (uv) and (FDEFPv)): `v(t,x) = e^{dt} u(α(e^{t/α} - 1), eᵗx)`. -/
alias solution_eq_fdeSolution := solution_eq_fdeSolution'

/-- Initial condition: `u(t,·) → δ_{x₀}` weakly as `t → 0⁺`. -/
alias tendsto_fdeSolution_zero := tendsto_fdeSolution_zero'

/-- Initial condition: `v(t,·) → δ_{x₀}` weakly as `t → 0⁺`. -/
alias tendsto_solution_zero := tendsto_solution_zero'

/-- Long-time behavior (eq. (vinf)): `v(t,x) → v_∞(x)` as `t → ∞`, and
`v_∞(x) = (C + (1-m)/(2m)|x|²)₊^{1/(m-1)}` for some constant `C > 0`. -/
alias tendsto_solution_atTop := tendsto_solution_atTop'

end Cutfast
