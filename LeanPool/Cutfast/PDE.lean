/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.Cutfast.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen


/-!
# The explicit solution solves the Fokker–Planck equation (eq. (FDEFP))

Near a point where `v(t, x) > 0`, the base of the Barenblatt profile is positive, so
`v(τ, y) = s(τ)^{-αd} (c + κ₀ s(τ)^{-2α} ‖y - e^{-τ}x₀‖²)^{1/(m-1)}` is smooth there. The
Laplacian of `vᵐ` is computed with the radial formula
`Δ[G(‖y - h‖²)] = 4‖y - h‖² G''(‖y - h‖²) + 2d G'(‖y - h‖²)`
(`Cutfast.PDE.laplacian_comp_normSq_sub`), and the identity reduces to an algebraic one.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace

namespace Cutfast

namespace PDE

/-! ### Helpers -/

/-- `s(τ) = α(1 - e^{-τ/α})`. -/
noncomputable def sFun (α τ : ℝ) : ℝ := α * (1 - exp (-τ / α))

/-- The base `c + κ₀ s(τ)^{-2α} ‖y - e^{-τ}x₀‖²` of the explicit solution. -/
noncomputable def baseFun (d : ℕ) (m : ℝ) (x₀ : E d) (τ : ℝ) (y : E d) : ℝ :=
  barenblattConst d m + alpha d m * (1 - m) / (2 * m) *
    ((sFun (alpha d m) τ ^ alpha d m)⁻¹) ^ 2 * ‖y - exp (-τ) • x₀‖ ^ 2

/-- The explicit solution in terms of `sFun` and `baseFun`. -/
theorem solution_eq_max (d : ℕ) (m : ℝ) (x₀ : E d) (τ : ℝ) (y : E d) :
    solution d m x₀ τ y = (sFun (alpha d m) τ ^ (alpha d m * d))⁻¹ *
      (max (baseFun d m x₀ τ y) 0) ^ (1 / (m - 1)) := by
  simp only [solution, barenblatt, barenblattWith, baseFun, sFun, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, mul_assoc]

/-- `s'(t) = e^{-t/α}`. -/
theorem hasDerivAt_sFun {α : ℝ} (hα : α ≠ 0) (t : ℝ) :
    HasDerivAt (sFun α) (exp (-t / α)) t := by
  have h1 : HasDerivAt (fun τ => -τ / α) (-1 / α) t := by
    simpa using ((hasDerivAt_id t).neg).div_const α
  exact ((h1.exp.const_sub 1).const_mul α).congr_deriv (by field_simp)

/-- Time derivative of `s(τ)^p`. -/
theorem hasDerivAt_sFun_rpow {α : ℝ} (hα : α ≠ 0) {t : ℝ} (hs : 0 < sFun α t) (p : ℝ) :
    HasDerivAt (fun τ => sFun α τ ^ p) (exp (-t / α) * p * sFun α t ^ (p - 1)) t :=
  (hasDerivAt_sFun hα t).rpow_const (Or.inl hs.ne')

/-- The Laplacian of a radial function `y ↦ G(‖y - h‖²)`. -/
theorem laplacian_comp_normSq_sub {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (G G' : ℝ → ℝ) (g2 : ℝ) (h x : F)
    (hG : ∀ᶠ r in 𝓝 (‖x - h‖ ^ 2), HasDerivAt G (G' r) r)
    (hG' : HasDerivAt G' g2 (‖x - h‖ ^ 2)) :
    Laplacian.laplacian (fun y => G (‖y - h‖ ^ 2)) x =
      4 * ‖x - h‖ ^ 2 * g2 + 2 * Module.finrank ℝ F * G' (‖x - h‖ ^ 2) := by
  have hφ : ∀ y : F, HasFDerivAt (fun y => ‖y - h‖ ^ 2) (2 • innerSL ℝ (y - h)) y := by
    intro y
    have := ((hasFDerivAt_id y).sub_const h).norm_sq
    simpa using this
  set D : F → F →L[ℝ] ℝ := fun y => G' (‖y - h‖ ^ 2) • (2 • innerSL ℝ (y - h)) with hD
  have hcont : Tendsto (fun y : F => ‖y - h‖ ^ 2) (𝓝 x) (𝓝 (‖x - h‖ ^ 2)) :=
    ((continuous_id.sub continuous_const).norm.pow 2).tendsto x
  have hfd : fderiv ℝ (fun y => G (‖y - h‖ ^ 2)) =ᶠ[𝓝 x] D := by
    filter_upwards [hcont.eventually hG] with y hy
    exact (hy.comp_hasFDerivAt y (hφ y)).fderiv
  have hD' : HasFDerivAt D
      ((G' (‖x - h‖ ^ 2)) • (2 • innerSL ℝ) +
        ((g2 • (2 • innerSL ℝ (x - h)))).smulRight (2 • innerSL ℝ (x - h))) x := by
    have h1 : HasFDerivAt (fun y : F => G' (‖y - h‖ ^ 2)) (g2 • (2 • innerSL ℝ (x - h))) x :=
      hG'.comp_hasFDerivAt x (hφ x)
    have h2 : HasFDerivAt (fun y : F => (2 • innerSL ℝ (y - h) : F →L[ℝ] ℝ))
        (2 • innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) x := by
      have := ((2 • innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ).hasFDerivAt (x := x - h)).comp x
        ((hasFDerivAt_id x).sub_const h)
      exact this
    exact h1.smul h2
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ F)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hfd.fderiv_eq, hD'.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hb := (stdOrthonormalBasis ℝ F).sum_inner_mul_inner (x - h) (x - h)
  set b := stdOrthonormalBasis ℝ F
  have e1 : ∑ i, 2 • ((innerSL ℝ) (b i)) (b i) = 2 * (Module.finrank ℝ F : ℝ) := by
    simp [innerSL_apply_apply, mul_comm]
  have e2 : ∑ i, g2 * 2 • ⟪x - h, b i⟫_ℝ * 2 • ⟪x - h, b i⟫_ℝ = 4 * ‖x - h‖ ^ 2 * g2 := by
    rw [← real_inner_self_eq_norm_sq, ← hb, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (b i)]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [e1, e2]
  ring

/-- Time derivative of the base `c + κ₀ (s^α)^{-2} ‖x - e^{-τ}x₀‖²`. -/
theorem hasDerivAt_baseFun {d : ℕ} {m : ℝ} (hm : m ≠ 0) (hα : alpha d m ≠ 0) (x₀ : E d) {t : ℝ}
    (hs : 0 < sFun (alpha d m) t) (x : E d) :
    HasDerivAt (fun τ => baseFun d m x₀ τ x)
      (alpha d m * (1 - m) / (2 * m) *
        (-2 * (exp (-t / alpha d m) * alpha d m * sFun (alpha d m) t ^ (alpha d m - 1)) /
          (sFun (alpha d m) t ^ alpha d m) ^ 3) * ‖x - exp (-t) • x₀‖ ^ 2 +
       alpha d m * (1 - m) / (2 * m) * ((sFun (alpha d m) t ^ alpha d m)⁻¹) ^ 2 *
        (2 * ⟪x - exp (-t) • x₀, exp (-t) • x₀⟫_ℝ)) t := by
  have ha : HasDerivAt (fun τ => (sFun (alpha d m) τ ^ alpha d m)⁻¹ ^ 2) _ t :=
    ((hasDerivAt_sFun_rpow hα hs (alpha d m)).inv (rpow_pos_of_pos hs _).ne').pow 2
  have hh : HasDerivAt (fun τ => ‖x - exp (-τ) • x₀‖ ^ 2) _ t :=
    ((((hasDerivAt_neg t).exp).smul_const x₀).const_sub x).norm_sq
  have := ((ha.const_mul (alpha d m * (1 - m) / (2 * m))).mul hh).const_add (barenblattConst d m)
  refine this.congr_deriv ?_
  have hpos := (rpow_pos_of_pos hs (alpha d m)).ne'
  simp only [inner_neg_right, inner_smul_right, Pi.inv_apply, Nat.reduceSub, pow_one,
    Nat.cast_ofNat]
  generalize sFun (alpha d m) t ^ alpha d m = A at hpos ⊢
  field_simp
end PDE

open PDE in
/-- The explicit solution satisfies `∂ₜv = Δ(vᵐ) + d v + ⟨x, ∇v⟩ = Δ(vᵐ) + div(x v)` at every
point where it is positive (eq. (FDEFP)). -/
theorem solution_hasDerivAt' {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) {t : ℝ} (ht : 0 < t) {x : E d}
    (hx : 0 < solution d m x₀ t x) :
    HasDerivAt (fun s => solution d m x₀ s x)
      (Laplacian.laplacian (fun y => solution d m x₀ t y ^ m) x +
        d * solution d m x₀ t x + ⟪x, gradient (solution d m x₀ t) x⟫_ℝ) t := by
  -- parameters
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hm1' : m - 1 ≠ 0 := sub_ne_zero.mpr hm1
  have hden : 0 < 2 - (d : ℝ) * (1 - m) := by
    rw [div_lt_iff₀ hdpos] at hmd
    nlinarith
  have hαpos : 0 < alpha d m := by unfold alpha; positivity
  have hα1 : alpha d m * (2 - d * (1 - m)) = 1 := by
    unfold alpha; field_simp
  set α := alpha d m with hαdef
  set c := barenblattConst d m with hcdef
  set q : ℝ := 1 / (m - 1) with hqdef
  set E0 := exp (-t / α) with hE0
  have hE0lt : E0 < 1 := by
    rw [hE0, Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos ht) hαpos
  set s := sFun α t with hsdef
  have hs : 0 < s := mul_pos hαpos (by linarith)
  set a := s ^ α with hadef
  have ha : 0 < a := rpow_pos_of_pos hs _
  set S := s ^ (α * d) with hSdef
  have hS : 0 < S := rpow_pos_of_pos hs _
  set h := exp (-t) • x₀ with hhdef
  set r0 := ‖x - h‖ ^ 2 with hr0
  set B0 := baseFun d m x₀ t x with hB0def
  have hB0 : 0 < B0 := by
    by_contra hle
    rw [solution_eq_max, max_eq_right (not_lt.mp hle), zero_rpow (one_div_ne_zero hm1'),
      mul_zero] at hx
    exact lt_irrefl _ hx
  set K := α * (1 - m) / (2 * m) * (a⁻¹) ^ 2 with hKdef
  -- time derivative
  have hb := hasDerivAt_baseFun hm0.ne' hαpos.ne' x₀ hs x
  have hT := ((hasDerivAt_sFun_rpow hαpos.ne' hs (α * d)).inv hS.ne').mul
    (hb.rpow_const (p := q) (Or.inl hB0.ne'))
  have hT' := hT.congr_of_eventuallyEq (f₁ := fun τ => solution d m x₀ τ x) (by
    filter_upwards [hb.continuousAt.eventually (lt_mem_nhds hB0)] with τ hτ
    rw [solution_eq_max, max_eq_left hτ.le]
    rfl)
  -- spatial structure
  have hcont : Continuous fun y => baseFun d m x₀ t y := by unfold baseFun; fun_prop
  have hev : ∀ᶠ y in 𝓝 x, 0 < baseFun d m x₀ t y := hcont.continuousAt.eventually (lt_mem_nhds hB0)
  have hbase : ∀ y, baseFun d m x₀ t y = c + K * ‖y - h‖ ^ 2 := fun y => rfl
  have hφ : ∀ y : E d, HasFDerivAt (fun y => ‖y - h‖ ^ 2) (2 • innerSL ℝ (y - h)) y := by
    intro y
    simpa using ((hasFDerivAt_id y).sub_const h).norm_sq
  -- gradient
  have hF : HasDerivAt (fun r => S⁻¹ * (c + K * r) ^ q) (S⁻¹ * (K * q * B0 ^ (q - 1))) r0 := by
    have := ((((hasDerivAt_id r0).const_mul K).const_add c).rpow_const (p := q)
      (Or.inl hB0.ne')).const_mul S⁻¹
    refine this.congr_deriv ?_
    simp only [id, mul_one]
    rfl
  have hgrad : ⟪x, gradient (solution d m x₀ t) x⟫_ℝ =
      S⁻¹ * (K * q * B0 ^ (q - 1)) * (2 * ⟪x - h, x⟫_ℝ) := by
    have hfd := (hF.comp_hasFDerivAt x (hφ x)).congr_of_eventuallyEq
      (f₁ := solution d m x₀ t) (by
        filter_upwards [hev] with y hy
        rw [solution_eq_max, max_eq_left hy.le]
        rfl)
    rw [gradient, hfd.fderiv, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    simp only [_root_.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  -- Laplacian
  have hlap : Laplacian.laplacian (fun y => solution d m x₀ t y ^ m) x =
      4 * r0 * ((S⁻¹) ^ m * (K * (q * m) * (K * (q * m - 1) * B0 ^ (q * m - 1 - 1)))) +
        2 * d * ((S⁻¹) ^ m * (K * (q * m) * B0 ^ (q * m - 1))) := by
    have hcongr : (fun y => solution d m x₀ t y ^ m) =ᶠ[𝓝 x]
        fun y => (fun r => (S⁻¹) ^ m * (c + K * r) ^ (q * m)) (‖y - h‖ ^ 2) := by
      filter_upwards [hev] with y hy
      rw [solution_eq_max, max_eq_left hy.le, mul_rpow (by positivity) (by positivity),
        ← rpow_mul hy.le]
      rfl
    rw [(InnerProductSpace.laplacian_congr_nhds hcongr).eq_of_nhds]
    have hr : ∀ᶠ r in 𝓝 r0, 0 < c + K * r :=
      ((continuous_const.add (continuous_const.mul continuous_id)).continuousAt (x
        := r0)).eventually
        (lt_mem_nhds hB0)
    refine (laplacian_comp_normSq_sub (F := E d) (fun r => (S⁻¹) ^ m * (c + K * r) ^ (q * m))
      (fun r => (S⁻¹) ^ m * (K * (q * m) * (c + K * r) ^ (q * m - 1)))
      ((S⁻¹) ^ m * (K * (q * m) * (K * (q * m - 1) * B0 ^ (q * m - 1 - 1)))) h x ?_ ?_).trans ?_
    · filter_upwards [hr] with r hr
      have := ((((hasDerivAt_id r).const_mul K).const_add c).rpow_const (p := q * m)
        (Or.inl hr.ne')).const_mul ((S⁻¹) ^ m)
      refine this.congr_deriv ?_
      simp
    · have := ((((hasDerivAt_id r0).const_mul K).const_add c).rpow_const (p := q * m - 1)
        (Or.inl hB0.ne')).const_mul (K * (q * m)) |>.const_mul ((S⁻¹) ^ m)
      refine this.congr_deriv ?_
      simp only [id, mul_one]
      rfl
    · rw [finrank_euclideanSpace_fin]
      rfl
  -- algebra
  have hval : solution d m x₀ t x = S⁻¹ * B0 ^ q := by
    rw [solution_eq_max, max_eq_left hB0.le]
  rw [hlap, hgrad, hval]
  refine hT'.congr_deriv ?_
  simp only [Pi.inv_apply]
  rw [← hαdef]
  have hS1 : s ^ (α * d - 1) = S / s := rpow_sub_one hs.ne' _
  have ha1 : s ^ (α - 1) = a / s := rpow_sub_one hs.ne' _
  have hB1 : B0 ^ (q - 1) = B0 ^ q / B0 := rpow_sub_one hB0.ne' _
  have hqm : q * m - 1 = q := by rw [hqdef]; field_simp; ring
  have hAm : S⁻¹ ^ m = a ^ 2 / (s * S) := by
    have : S⁻¹ ^ m = s ^ (2 * α - 1 - α * d) := by
      rw [inv_rpow hS.le, ← rpow_mul hs.le, ← rpow_neg hs.le]
      congr 1
      linear_combination (-1 : ℝ) * hα1
    rw [this, rpow_sub hs, rpow_sub hs, rpow_one, two_mul, rpow_add hs]
    ring
  have hin : ⟪x - h, x⟫_ℝ = r0 + ⟪x - h, h⟫_ℝ := by
    rw [hr0, ← real_inner_self_eq_norm_sq, ← inner_add_right, sub_add_cancel]
  rw [hS1, ha1, hqm, hB1, hAm, hin]
  rw [show sFun α t ^ (α * d) = S from rfl, show sFun α t ^ α = a from rfl,
    show baseFun d m x₀ t x = B0 from rfl, show ‖x - rexp (-t) • x₀‖ ^ 2 = r0 from rfl,
    show ⟪x - rexp (-t) • x₀, rexp (-t) • x₀⟫_ℝ = ⟪x - h, h⟫_ℝ from rfl,
    show rexp (-t / α) = E0 from rfl, hKdef, hqdef]
  have hsE : s = α * (1 - E0) := rfl
  generalize B0 ^ q = P
  generalize ⟪x - h, h⟫_ℝ = u
  clear_value s a S B0 r0 E0 α
  subst hsE
  have h1E : 1 - E0 ≠ 0 := (sub_pos.mpr hE0lt).ne'
  field_simp
  ring
end Cutfast
