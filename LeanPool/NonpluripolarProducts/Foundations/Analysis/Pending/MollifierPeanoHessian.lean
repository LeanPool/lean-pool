/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SemiconcaveTaylor
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicPullback

/-!
# Hessians of radial mollifications at points of second-order differentiability

If `u` admits a second-order Peano expansion at `z₀` with symmetric quadratic part `A`, then
the real Hessians at `z₀` of the mollifications `u ∗ ρ_j` converge to `A`.

The proof subtracts the Taylor polynomial `q` of `u` at `z₀`: the mollification of a quadratic
polynomial differs from it by a constant (the kernel is even and has integral one), so the
Hessian of `q ∗ ρ_j` is exactly `A`; and the error term is estimated by the exact dilation
relation `ρ_j(x) = (j+1)^d ρ_0((j+1) x)` between the kernels, which converts the `o(‖x - z₀‖²)`
Peano remainder into an arbitrarily small contribution.

The related determinant convergence uses local `L¹` convergence for Sobolev PSH data in
[Błocki, Proposition 2.1.6](https://gamma.im.uj.edu.pl/~blocki/publ/ln/wykl.pdf#page=37).
The proof of [Theorem 2.3.1](https://gamma.im.uj.edu.pl/~blocki/publ/ln/wykl.pdf#page=52)
uses the Taylor expansion of a `C¹,¹` potential at a point of twice differentiability.
Here the separate pointwise lemma assumes a Peano expansion and proves convergence
of each Hessian pairing.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory Module
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.SemiconcaveHessian

open FirstPass FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending.HolomorphicPullback

variable {n : ℕ}

/-! ### Elementary transformation rules for the real Hessian -/

theorem realHessian_const_mul {f : ComplexModel n → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ)
    (x v w : ComplexModel n) :
    realHessian (fun z ↦ c * f z) x v w = c * realHessian f x v w := by
  have h := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (i := 2) (a := c) (f := f) (x := x)
    hf.contDiffAt
  simp only [realHessian, smul_eq_mul] at h ⊢
  rw [h]
  simp

theorem realHessian_comp_const_smul {f : ComplexModel n → ℝ} (hf : ContDiff ℝ 2 f) (a : ℝ)
    (x v w : ComplexModel n) :
    realHessian (fun z ↦ f (a • z)) x v w = a ^ 2 * realHessian f (a • x) v w := by
  have h := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := 2) (f := f) a hf
  simp only [realHessian]
  rw [show (fun z ↦ f (a • z)) = fun z ↦ f (a • z) from rfl, h]
  simp

theorem abs_realHessian_le {f : ComplexModel n → ℝ} (x v w : ComplexModel n) :
    |realHessian f x v w| ≤ ‖iteratedFDeriv ℝ 2 f x‖ * (‖v‖ * ‖w‖) := by
  have h := (iteratedFDeriv ℝ 2 f x).le_opNorm ![v, w]
  simp only [realHessian, Real.norm_eq_abs] at h ⊢
  calc |iteratedFDeriv ℝ 2 f x ![v, w]| ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ∏ i, ‖(![v, w]) i‖ := h
    _ = ‖iteratedFDeriv ℝ 2 f x‖ * (‖v‖ * ‖w‖) := by
        congr 1
        simp [Fin.prod_univ_two]

/-! ### Moments of an even kernel -/

theorem integral_linear_mul_of_even {ℓ : ComplexModel n →L[ℝ] ℝ} {κ : ComplexModel n → ℝ}
    (hκeven : ∀ y, κ (-y) = κ y) : ∫ y, ℓ y * κ y = 0 := by
  have h1 : (∫ y : ComplexModel n, ℓ (-y) * κ (-y)) = ∫ y : ComplexModel n, ℓ y * κ y :=
    integral_neg_eq_self (fun y ↦ ℓ y * κ y) volume
  have h2 : (∫ y : ComplexModel n, ℓ (-y) * κ (-y)) = -∫ y : ComplexModel n, ℓ y * κ y := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [hκeven, map_neg]
    ring
  linarith [h1, h2]

/-- Mollifying a quadratic polynomial with an even kernel of integral one shifts it by a
constant. -/
theorem translationPairing_quadratic {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {L : ComplexModel n →L[ℝ] ℝ} {a : ℝ} {z₀ : ComplexModel n} {κ : ComplexModel n → ℝ}
    (hκs : HasCompactSupport κ) (hκc : Continuous κ) (hκ1 : ∫ y, κ y = 1)
    (hκeven : ∀ y, κ (-y) = κ y) (z : ComplexModel n) :
    translationPairing volume (fun x ↦ a + L (x - z₀) + A (x - z₀) (x - z₀) / 2) κ z =
      (a + L (z - z₀) + A (z - z₀) (z - z₀) / 2) + ∫ y, A y y * κ y / 2 := by
  classical
  set q : ComplexModel n → ℝ := fun x ↦ a + L (x - z₀) + A (x - z₀) (x - z₀) / 2 with hq
  set ℓ : ComplexModel n →L[ℝ] ℝ :=
    L + (2⁻¹ : ℝ) • (A (z - z₀) + A.flip (z - z₀)) with hℓ
  have hshift : translationPairing volume q κ z = ∫ y, q (y + z) * κ y := by
    rw [translationPairing]
    rw [← integral_add_right_eq_self (fun x : ComplexModel n ↦ q x * κ (x - z)) z]
    simp
  have hexp : ∀ y : ComplexModel n, q (y + z) * κ y =
      q z * κ y + ℓ y * κ y + A y y * κ y / 2 := by
    intro y
    have hyz : y + z - z₀ = (z - z₀) + y := by abel
    simp only [hq, hℓ, hyz, map_add, _root_.add_apply,
      _root_.smul_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  have hint1 : Integrable (fun y : ComplexModel n ↦ q z * κ y) volume :=
    (hκc.integrable_of_hasCompactSupport hκs).const_mul _
  have hint2 : Integrable (fun y : ComplexModel n ↦ ℓ y * κ y) volume := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact hκs.mono (by
      intro x hx
      simp only [Function.mem_support, ne_eq] at hx ⊢
      intro h
      exact hx (by simp [h]))
  have hint3 : Integrable (fun y : ComplexModel n ↦ A y y * κ y / 2) volume := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact hκs.mono (by
      intro x hx
      simp only [Function.mem_support, ne_eq] at hx ⊢
      intro h
      exact hx (by simp [h]))
  have e1 : (∫ y : ComplexModel n, (q z * κ y + ℓ y * κ y + A y y * κ y / 2))
      = (∫ y : ComplexModel n, (q z * κ y + ℓ y * κ y)) +
        ∫ y : ComplexModel n, A y y * κ y / 2 :=
    integral_add (hint1.add hint2) hint3
  have e2 : (∫ y : ComplexModel n, (q z * κ y + ℓ y * κ y))
      = (∫ y : ComplexModel n, q z * κ y) + ∫ y : ComplexModel n, ℓ y * κ y :=
    integral_add hint1 hint2
  rw [hshift, integral_congr_ae (Eventually.of_forall hexp), e1, e2,
    integral_linear_mul_of_even hκeven, integral_const_mul, hκ1]
  simp [hq]

/-- The real Hessian of a quadratic polynomial is its (symmetric) quadratic coefficient. -/
theorem realHessian_quadratic {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hsymm : ∀ v w, A v w = A w v) {L : ComplexModel n →L[ℝ] ℝ} {a c : ℝ}
    {z₀ : ComplexModel n} (x v w : ComplexModel n) :
    realHessian (fun z ↦ (a + L (z - z₀) + A (z - z₀) (z - z₀) / 2) + c) x v w = A v w := by
  set f : ComplexModel n → ℝ := fun z ↦ (a + L (z - z₀) + A (z - z₀) (z - z₀) / 2) + c with hf
  have hlin : ∀ y : ComplexModel n, HasFDerivAt (fun z : ComplexModel n ↦ z - z₀)
      (ContinuousLinearMap.id ℝ (ComplexModel n)) y := fun y ↦ (hasFDerivAt_id y).sub_const z₀
  have hquad : ∀ y : ComplexModel n,
      HasFDerivAt (fun z : ComplexModel n ↦ A (z - z₀) (z - z₀))
        (A (y - z₀) + A.flip (y - z₀)) y := by
    intro y
    have h2 : HasFDerivAt (fun z : ComplexModel n ↦ A (z - z₀))
        (A.comp (ContinuousLinearMap.id ℝ (ComplexModel n))) y := A.hasFDerivAt.comp y (hlin y)
    simpa using h2.clm_apply (hlin y)
  have hf1 : ∀ y : ComplexModel n,
      HasFDerivAt f (L + (2⁻¹ : ℝ) • (A (y - z₀) + A.flip (y - z₀))) y := by
    intro y
    have h1 : HasFDerivAt (fun z : ComplexModel n ↦ a + L (z - z₀)) L y := by
      have := (L.hasFDerivAt.comp y (hlin y)).const_add a
      simpa using this
    have hrw : (fun z : ComplexModel n ↦ A (z - z₀) (z - z₀) / 2)
        = fun z : ComplexModel n ↦ 2⁻¹ * (A (z - z₀) (z - z₀)) := by
      funext z; ring
    have h2 : HasFDerivAt (fun z : ComplexModel n ↦ A (z - z₀) (z - z₀) / 2)
        ((2⁻¹ : ℝ) • (A (y - z₀) + A.flip (y - z₀))) y := by
      rw [hrw]
      simpa using (hquad y).const_mul (2⁻¹ : ℝ)
    simpa [hf] using (h1.add h2).add_const c
  have hfd : fderiv ℝ f = fun y ↦ L + (2⁻¹ : ℝ) • (A (y - z₀) + A.flip (y - z₀)) :=
    funext fun y ↦ (hf1 y).fderiv
  have hf2 : HasFDerivAt (fun y : ComplexModel n ↦ L + (2⁻¹ : ℝ) • (A (y - z₀) + A.flip (y - z₀)))
      ((2⁻¹ : ℝ) • (A + A.flip)) x := by
    have hA : HasFDerivAt (fun y : ComplexModel n ↦ A (y - z₀)) A x := by
      have h := A.hasFDerivAt.comp x (hlin x)
      simp only [Function.comp_def, ContinuousLinearMap.comp_id] at h
      exact h
    have hAf : HasFDerivAt (fun y : ComplexModel n ↦ A.flip (y - z₀)) A.flip x := by
      have h := A.flip.hasFDerivAt.comp x (hlin x)
      simp only [Function.comp_def, ContinuousLinearMap.comp_id] at h
      exact h
    have h := ((hA.add hAf).const_smul (2⁻¹ : ℝ)).const_add L
    rw [smul_add] at h
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ by simp [smul_add])
  rw [realHessian_eq_fderiv, hfd, hf2.fderiv]
  have hval : ((2⁻¹ : ℝ) • (A + A.flip)) v w = 2⁻¹ * (A v w + A w v) := by
    simp [ContinuousLinearMap.flip_apply]
    ring
  rw [hval, ← hsymm v w]
  ring

/-- **Hessians of radial mollifications converge at a point of second-order differentiability.**
-/
theorem tendsto_realHessian_translationPairing_of_hasPeanoExpansion
    {R : ℝ} (hR : 0 < R) {g u : ComplexModel n → ℝ} (hg : LocallyIntegrable g volume)
    {z₀ : ComplexModel n} {L : ComplexModel n →L[ℝ] ℝ}
    {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ} (hsymm : ∀ v w, A v w = A w v)
    (hpeano : HasPeanoExpansionAt u z₀ L A)
    (hgu : ∀ x ∈ closedBall z₀ R, g x = u x) (v w : ComplexModel n) :
    Tendsto (fun j ↦ realHessian
        (translationPairing volume g (explicitRadialKernel R hR j)) z₀ v w)
      atTop (𝓝 (A v w)) := by
  classical
  set d := finrank ℝ (ComplexModel n) with hd
  set κ : ℕ → ComplexModel n → ℝ := fun j ↦ explicitRadialKernel R hR j with hκdef
  have hκ2 : ∀ j, ContDiff ℝ 2 (κ j) := fun j ↦
    (explicitRadialKernel_contDiff R hR j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hκs : ∀ j, HasCompactSupport (κ j) := fun j ↦ explicitRadialKernel_hasCompactSupport R hR j
  have hκc : ∀ j, Continuous (κ j) := fun j ↦ (hκ2 j).continuous
  have hκ1 : ∀ j, ∫ y, κ j y = 1 := fun j ↦ explicitRadialKernel_integral_one R hR j
  have hκeven : ∀ j, ∀ y, κ j (-y) = κ j y := fun j y ↦ explicitRadialKernel_neg R hR j y
  set q : ComplexModel n → ℝ := fun x ↦ u z₀ + L (x - z₀) + A (x - z₀) (x - z₀) / 2 with hq
  have hqc : Continuous q := by
    have : Continuous fun x : ComplexModel n ↦ A (x - z₀) (x - z₀) :=
      (A.continuous₂).comp₂ (continuous_id.sub continuous_const) (continuous_id.sub
        continuous_const)
    fun_prop
  have hqloc : LocallyIntegrable q volume := hqc.locallyIntegrable
  -- the mollification of the Taylor polynomial has Hessian `A`
  have hstep1 : ∀ j, realHessian (translationPairing volume q (κ j)) z₀ v w = A v w := by
    intro j
    have hfun : translationPairing volume q (κ j)
        = fun z ↦ (u z₀ + L (z - z₀) + A (z - z₀) (z - z₀) / 2) + ∫ y, A y y * κ j y / 2 :=
      funext fun z ↦ translationPairing_quadratic (hκs j) (hκc j) (hκ1 j) (hκeven j) z
    rw [hfun]
    exact realHessian_quadratic hsymm z₀ v w
  -- splitting off the Taylor polynomial
  have hstep2 : ∀ j, realHessian (translationPairing volume g (κ j)) z₀ v w - A v w
      = ∫ x, (g x - q x) * realHessian (κ j) (x - z₀) v w := by
    intro j
    rw [realHessian_translationPairing hg (hκs j) (hκ2 j), ← hstep1 j,
      realHessian_translationPairing hqloc (hκs j) (hκ2 j),
      ← integral_sub (integrable_translationPairing_realHessian hg (hκs j) (hκ2 j) z₀ v w)
        (integrable_translationPairing_realHessian hqloc (hκs j) (hκ2 j) z₀ v w)]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    ring
  -- a uniform bound for the second derivative of the base kernel
  obtain ⟨N, hN⟩ := ((hκs 0).iteratedFDeriv 2).exists_bound_of_continuous
    ((hκ2 0).continuous_iteratedFDeriv (by norm_num))
  have hN0 : 0 ≤ N := le_trans (norm_nonneg _) (hN 0)
  -- the exact dilation relation between the kernels
  have hscale : ∀ (j : ℕ) (y : ComplexModel n),
      realHessian (κ j) y v w = ((j : ℝ) + 1) ^ d *
        (((j : ℝ) + 1) ^ 2 * realHessian (κ 0) (((j : ℝ) + 1) • y) v w) := by
    intro j y
    have hfun : κ j = fun x ↦ ((j : ℝ) + 1) ^ d * κ 0 (((j : ℝ) + 1) • x) := by
      funext x
      have h := explicitRadialKernel_scale R hR 0 j x
      simpa [hκdef, hd] using h
    have hcd : ContDiff ℝ 2 fun z : ComplexModel n ↦ κ 0 (((j : ℝ) + 1) • z) :=
      (hκ2 0).comp (contDiff_id.const_smul _)
    rw [hfun, realHessian_const_mul hcd, realHessian_comp_const_smul (hκ2 0)]
  have hbound : ∀ (j : ℕ) (y : ComplexModel n),
      |realHessian (κ j) y v w| ≤ ((j : ℝ) + 1) ^ d * (((j : ℝ) + 1) ^ 2 * (N * (‖v‖ * ‖w‖))) := by
    intro j y
    rw [hscale j y, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((j : ℝ) + 1) ^ d),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ((j : ℝ) + 1) ^ 2)]
    have h1 : |realHessian (κ 0) (((j : ℝ) + 1) • y) v w| ≤ N * (‖v‖ * ‖w‖) := by
      refine le_trans (abs_realHessian_le _ v w) ?_
      exact mul_le_mul_of_nonneg_right (hN _) (by positivity)
    have h2 : (0:ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by positivity
    have h3 : (0:ℝ) ≤ ((j : ℝ) + 1) ^ d := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h2) h3
  -- outside the kernel support the integrand vanishes
  have hsupp : ∀ (j : ℕ) (x : ComplexModel n), x ∉ closedBall z₀ (R / ((j : ℝ) + 1)) →
      (g x - q x) * realHessian (κ j) (x - z₀) v w = 0 := by
    intro j x hx
    have hxt : x - z₀ ∉ tsupport (κ j) := by
      rw [hκdef]
      simp only [explicitRadialKernel_tsupport R hR j]
      simpa [mem_closedBall, dist_eq_norm] using hx
    have hzero : iteratedFDeriv ℝ 2 (κ j) (x - z₀) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h ↦ hxt (tsupport_iteratedFDeriv_subset 2 h))
    simp [realHessian, hzero]
  -- the main estimate
  set V := (volume : Measure (ComplexModel n)).real (ball 0 1) with hV
  have hV0 : 0 ≤ V := by positivity
  set Const := R ^ (d + 2) * N * (‖v‖ * ‖w‖) * V with hConst
  have hConst0 : 0 ≤ Const := by positivity
  have key : ∀ ε > 0, ∀ᶠ j in atTop,
      |realHessian (translationPairing volume g (κ j)) z₀ v w - A v w| ≤ ε * Const := by
    intro ε hε
    obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff_ball.mp (hpeano ε hε)
    obtain ⟨jN, hjN⟩ := exists_nat_gt (R / ρ)
    filter_upwards [eventually_ge_atTop jN] with j hj
    set s : ℝ := (j : ℝ) + 1 with hs
    have hs0 : 0 < s := by positivity
    have hsR : R / s < ρ := by
      have hjR : R / ρ < s := by
        have : (jN : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hj
        linarith
      rw [div_lt_iff₀ hs0]
      rw [div_lt_iff₀ hρ] at hjR
      linarith [hjR]
    have hsRle : R / s ≤ R := by
      rw [div_le_iff₀ hs0]
      nlinarith [hR.le, Nat.cast_nonneg (α := ℝ) j]
    have hrpos : 0 < R / s := by positivity
    -- pointwise bound on the ball of radius `R / s`
    have hptwise : ∀ x ∈ closedBall z₀ (R / s),
        ‖(g x - q x) * realHessian (κ j) (x - z₀) v w‖ ≤
          (ε * (R / s) ^ 2) * (s ^ d * (s ^ 2 * (N * (‖v‖ * ‖w‖)))) := by
      intro x hx
      have hxnorm : ‖x - z₀‖ ≤ R / s := by simpa [mem_closedBall, dist_eq_norm] using hx
      have hxR : x ∈ closedBall z₀ R := by
        simp only [mem_closedBall, dist_eq_norm]
        exact le_trans hxnorm hsRle
      have hxball : x - z₀ ∈ ball (0 : ComplexModel n) ρ := by
        simp only [mem_ball, dist_zero_right]
        exact lt_of_le_of_lt hxnorm hsR
      have hpe := hρball _ hxball
      have hxz : z₀ + (x - z₀) = x := by abel
      have hgq : |g x - q x| ≤ ε * (R / s) ^ 2 := by
        have heq : u x - q x =
            u (z₀ + (x - z₀)) - u z₀ - L (x - z₀) - A (x - z₀) (x - z₀) / 2 := by
          rw [hxz, hq]
          ring
        rw [hgu x hxR, heq]
        refine le_trans hpe ?_
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxnorm 2) hε.le
      rw [Real.norm_eq_abs, abs_mul]
      have := hbound j (x - z₀)
      exact mul_le_mul hgq this (abs_nonneg _) (by positivity)
    have hcompl : ∀ x ∉ closedBall z₀ (R / s), (g x - q x) * realHessian (κ j) (x - z₀) v w = 0 :=
      fun x hx ↦ hsupp j x (by simpa [hs] using hx)
    have hsetint : (∫ x, (g x - q x) * realHessian (κ j) (x - z₀) v w)
        = ∫ x in closedBall z₀ (R / s), (g x - q x) * realHessian (κ j) (x - z₀) v w :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hcompl).symm
    have hmeas : (volume : Measure (ComplexModel n)) (closedBall z₀ (R / s)) < ⊤ :=
      measure_closedBall_lt_top
    have hnorm := norm_setIntegral_le_of_norm_le_const hmeas hptwise
    have hvol : (volume : Measure (ComplexModel n)).real (closedBall z₀ (R / s))
        = (R / s) ^ d * V := by
      rw [hV, hd]
      exact Measure.addHaar_real_closedBall volume z₀ hrpos.le
    rw [hstep2 j, ← Real.norm_eq_abs, hsetint]
    refine le_trans hnorm ?_
    rw [hvol]
    have hsne : s ≠ 0 := ne_of_gt hs0
    have h1 : (R / s) ^ 2 * s ^ 2 = R ^ 2 := by
      rw [div_pow]
      field_simp
    have h2 : (R / s) ^ d * s ^ d = R ^ d := by
      rw [div_pow]
      field_simp
    have halg : (ε * (R / s) ^ 2) * (s ^ d * (s ^ 2 * (N * (‖v‖ * ‖w‖)))) * ((R / s) ^ d * V)
        = ε * Const := by
      calc (ε * (R / s) ^ 2) * (s ^ d * (s ^ 2 * (N * (‖v‖ * ‖w‖)))) * ((R / s) ^ d * V)
          = ε * ((R / s) ^ 2 * s ^ 2) * ((R / s) ^ d * s ^ d) * (N * (‖v‖ * ‖w‖) * V) := by
            ring
        _ = ε * R ^ 2 * R ^ d * (N * (‖v‖ * ‖w‖) * V) := by rw [h1, h2]
        _ = ε * Const := by rw [hConst, pow_add]; ring
    exact le_of_eq halg
  -- conclude
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hCpos : 0 < Const + 1 := by positivity
  obtain ⟨jN, hjN⟩ := (key (δ / (2 * (Const + 1))) (by positivity)).exists_forall_of_atTop
  refine ⟨jN, fun j hj ↦ ?_⟩
  have h := hjN j hj
  rw [Real.dist_eq]
  have hb : δ / (2 * (Const + 1)) * Const ≤ δ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
    nlinarith [hConst0, hδ.le]
  linarith [h, hb, hδ]

end SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
