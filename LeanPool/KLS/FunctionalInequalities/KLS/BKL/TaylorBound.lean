/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Suspension.Density
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Suspension.Cumulant
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Suspension.Derivatives
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Suspension.Moments
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Regular.Basic
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable
public import LeanPool.KLS.FunctionalInequalities.L2.AffineDecomposition
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Suspension.Law

/-!
# BKL Proposition 7.1: the Taylor-coefficient bound from cumulant bounds

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Proposition 7.1, pp. 28–30. Under the hypothesis
`CumulantBound d b` (`R^ν_{d+1} ≤ b Id` for every isotropic log-concave `ν` in every dimension),
every isotropic regular law `μ` satisfies (113), `|T_d f|² ≤ b/(d!)²`, for `f ∈ C² ∩ L²(μ)` with
bounded Hessian normalized by (108) — proved through the suspension `(S, X₁, …, X_N)` with `N`
chosen by (110) for each `β`, then `β → ∞`. Then (113) extends by density to every `f ∈ L²(μ)`
orthogonal to the affine
functions (`norm_coordTensor_taylorTensor_sq_le_of_orthogonal`). Finally the assembly (107),
`norm_coordTensor_taylorTensor_sq_le_two_mul`, is Proposition 7.1 in the source form (conditional on
its hypothesis `CumulantBound`). Nothing here is Theorem 4.1 or Theorem 1.1.

The proof uses the law, density, cumulant, moment and derivative interfaces of `Suspension/`.
-/

@[expose] public section

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.Suspension

/-! The scalar beta-limit argument uses the integrated sigma identity. The suspension law,
its density and cumulants, the chosen-copy derivative formula (112), and the finite-coordinate
comparison supply the Taylor estimate below. -/

private theorem source_energy_bound_of_sigma_bounds {T b : ℝ} {d : ℕ} (hb : 0 < b) (hd : 2 ≤ d)
    (hβbound : ∀ β : ℝ, 0 < β → T ≤ (sigma β) ^ 2 * b / (d.factorial : ℝ) ^ 2) :
    T ≤ b / (d.factorial : ℝ) ^ 2 := by
  have hfac_nat : 2 ≤ d.factorial := by simpa using Nat.factorial_le hd
  have hfac : (2 : ℝ) ≤ (d.factorial : ℝ) := by exact_mod_cast hfac_nat
  have hα : 0 < b / (d.factorial : ℝ) ^ 2 := div_pos hb (pow_pos (by linarith) 2)
  let α : ℝ := b / (d.factorial : ℝ) ^ 2
  by_contra hnot
  have hgap : 0 < T - α := sub_pos.mpr (lt_of_not_ge hnot)
  let β : ℝ := Real.sqrt (4 * α / (T - α))
  have hratio : 0 < 4 * α / (T - α) := by
    change 0 < 4 * (b / (d.factorial : ℝ) ^ 2) / (T - α);
    positivity
  have hβ : 0 < β := Real.sqrt_pos.mpr hratio
  have hβsq : β ^ 2 = 4 * α / (T - α) := Real.sq_sqrt hratio.le
  have hproduct : β ^ 2 * (T - α) = 4 * α := (eq_div_iff hgap.ne').mp hβsq
  have hextra : 2 * α / β ^ 2 < T - α := by
    apply (div_lt_iff₀ (pow_pos hβ 2)).2
    nlinarith [hproduct]
  have hbβ : T ≤ sigma β ^ 2 * α := by simpa only [α, mul_div_assoc] using hβbound β hβ
  rw [sigma_sq hβ] at hbβ
  have heq : (1 + 2 / β ^ 2) * α = α + 2 * α / β ^ 2 := by ring
  rw [heq] at hbβ
  linarith

private theorem joint_cumulant_sum_sq_le {n N d : ℕ} {b : ℝ} (hcb : CumulantBound d b)
    (hN : 0 < N) (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') (hiso : KLS.Isotropic hV.law)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ} (hβ : 0 < β) (hf : ContDiff ℝ 2 f)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (h110 : β / Real.sqrt N * M ≤ a)
    (hf2 : MemLp f 2 (hV.law : Measure _))
    (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0) (hf1 : ∫ x, f x ^ 2 ∂(hV.law : Measure _) = 1)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) :
    (∑ K : Fin d → Option (Fin N × Fin n),
      cumulant (jointLaw (hV.law : Measure _) f β (sigma β) N) (d + 1)
        (Fin.cons (EuclideanSpace.single none 1) fun k => EuclideanSpace.single (K k) 1) ^ 2) ≤ b := by
  classical
  let ν : ProbabilityMeasure (JointSpace N n) :=
    ⟨jointLaw (hV.law : Measure _) f β (sigma β) N,
      isProbabilityMeasure_jointLaw_of_pos (hV.law : Measure _) hf.continuous.measurable hβ
        (sigma β) N⟩
  have hisoν : KLS.Isotropic ν :=
    isotropic_jointLaw hN (hV.law : Measure _) hiso.memLp_two hiso.mean_zero
      hiso.integral_inner_mul_inner hf.continuous.measurable hf2 hf0 hf1 hfx hβ
  have hV2 : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hlcν : KLS.LogConcave ν :=
    logConcave_jointLaw V f hβ hV2 hf hV.lower hfM h110 hV.integrable_exp_neg ν.prop
  simpa only [ν, ProbabilityMeasure.coe_mk, EuclideanSpace.basisFun_apply, PiLp.norm_single,
    norm_one, one_pow, mul_one] using
    cumulantBound_jointSpace hcb hisoν hlcν (EuclideanSpace.single none 1)

private theorem le_mul_div_of_div_mul_le {a s t b : ℝ} (ha : 0 < a) (hs : 0 < s)
    (h : a / s * t ≤ b) : t ≤ s * b / a := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hs] at h
  apply (le_div_iff₀ ha).mpr
  simpa only [mul_comm] using h

private theorem taylor_energy_le_sigma_sq_mul_cumulant_bound {d : ℕ} (hd : 1 ≤ d) {b : ℝ}
    (hcb : CumulantBound d b) {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') (hiso : KLS.Isotropic hV.law)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ} (hf : ContDiff ℝ 2 f)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hf2 : MemLp f 2 (hV.law : Measure _))
    (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0) (hf1 : ∫ x, f x ^ 2 ∂(hV.law : Measure _) = 1)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) {β : ℝ} (hβ : 0 < β) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^
        2 ≤
      sigma β ^ 2 * b / (d.factorial : ℝ) ^ 2 := by
  classical
  have hM : 0 ≤ M := (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (hfM 0)
  obtain ⟨N, hN, h110⟩ := exists_copies hV.pos hβ.le hM
  have hσ : 0 < sigma β := Real.sqrt_pos.mpr (by positivity)
  have hentries := cumulant_jointLaw_none_entries hN V hV hβ hf hfM h110 hd
  have hlow := sum_sq_cumulant_ge_of_entries hN (jointLaw (hV.law : Measure _) f β (sigma β) N)
    (hV.law : Measure _) f hσ hd hentries
  have hhigh := joint_cumulant_sum_sq_le hcb hN V hV hiso hβ hf hfM h110 hf2 hf0 hf1 hfx
  have hfac : 0 < (d.factorial : ℝ) ^ 2 := by positivity
  exact le_mul_div_of_div_mul_le hfac (pow_pos hσ 2) (hlow.trans hhigh)

/--
**BKL (113) for `f ∈ C²` with bounded Hessian satisfying (108)**: under `CumulantBound d b`, for an
isotropic regular law, `|T_d f|² ≤ b/(d!)²`. For each `β > 0` a copy number `N` is chosen by (110);
the
joint law is isotropic and log-concave, (112) and the Hilbert–Schmidt step give
`(d!)²/σ_β² |T_d f|² ≤ b`, and `β → ∞`. -/
theorem norm_coordTensor_taylorTensor_sq_le_of_cumulantBound {d : ℕ} (hd : 2 ≤ d) {b : ℝ}
    (hb : 0 < b) (hcb : CumulantBound d b) {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') (hiso : KLS.Isotropic hV.law)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ} (hf : ContDiff ℝ 2 f)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hf2 : MemLp f 2 (hV.law : Measure _))
    (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0) (hf1 : ∫ x, f x ^ 2 ∂(hV.law : Measure _) = 1)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^
        2 ≤
      b / (d.factorial : ℝ) ^ 2 := by
  apply source_energy_bound_of_sigma_bounds hb hd
  intro β hβ
  exact
    taylor_energy_le_sigma_sq_mul_cumulant_bound (by omega) hcb V hV hiso hf hfM hf2 hf0 hf1 hfx
      hβ

/-! ### The density step (BKL p. 30) -/

open scoped ContDiff

section NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem compact_c2_hessian_bounded
    {g : E → F} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) :
    ∃ M : ℝ, ∀ x : E, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M := by
  have hd : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hcontinuous : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    hd.continuous_fderiv one_ne_zero
  have hnorm : Continuous (fun x : E => ‖fderiv ℝ (fderiv ℝ g) x‖) :=
    Continuous.norm (E := E →L[ℝ] E →L[ℝ] F) hcontinuous
  obtain ⟨M, hM⟩ := hc.isCompact.exists_bound_of_continuousOn hnorm.continuousOn
  refine ⟨max M 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport g
  · have hbound : ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ g) x))]
        using hM x hx
    exact hbound.trans (le_max_left M 0)
  · have hx1 : x ∉ tsupport (fderiv ℝ g) :=
      fun h => hx (tsupport_fderiv_subset ℝ h)
    rw [fderiv_of_notMem_tsupport ℝ hx1, ContinuousLinearMap.opNorm_zero]
    exact le_max_right M 0

private theorem smooth_compact_hessian_bounded
    {g : E → F} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ M : ℝ, ∀ x : E, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M := by
  have hg2 : ContDiff ℝ 2 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  exact compact_c2_hessian_bounded hg2 hc

end NormedSpace

/-! Smooth affine-orthogonal approximants for BKL p. 30. The approximation is derived
from Mathlib smooth compact-support density, not assumed as a field. -/

open MeasureTheory FunctionalInequalities.L2
open scoped ContDiff RealInnerProductSpace

private theorem smooth_affineOrthPart {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (affineOrthPart μ ψ) := by
  unfold affineOrthPart
  apply (hψ.sub contDiff_const).sub
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).contDiff

/-- Genuine smooth compact-support inputs yield projected L2 approximants in the actual
affine-orthogonal subspace. The projected function itself need not have compact support. -/
private theorem exists_projected_smooth_approx {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport ψ ∧ ContDiff ℝ ∞ ψ ∧
      MemLp ψ 2 μ ∧ ContDiff ℝ ∞ (affineOrthPart μ ψ) ∧
      MemLp (affineOrthPart μ ψ) 2 μ ∧
      (∫ x, affineOrthPart μ ψ x ∂μ) = 0 ∧
      (∀ u, ∫ x, ⟪u, x⟫ * affineOrthPart μ ψ x ∂μ = 0) ∧
      eLpNorm (f - affineOrthPart μ ψ) 2 μ ≤ ENNReal.ofReal ε := by
  obtain ⟨ψ, hψsupp, hψsmooth, hψapprox⟩ :=
    hf.exist_eLpNorm_sub_le (by norm_num : (2 : ENNReal) ≠ ⊤) one_le_two hε
  have hψ2 : MemLp ψ 2 μ := hψsmooth.continuous.memLp_of_hasCompactSupport hψsupp
  refine ⟨ψ, hψsupp, hψsmooth, hψ2, smooth_affineOrthPart μ hψsmooth,
    memLp_affineOrthPart μ hμ2 hψ2, integral_affineOrthPart μ hμ2 hμ0 hψ2,
    integral_inner_mul_affineOrthPart μ hμ2 hμ0 hμcov hψ2, ?_⟩
  exact (eLpNorm_sub_affineOrthPart_le μ hμ2 hμ0 hμcov hf hf0 hfx hψ2).trans hψapprox

/-- Actual smooth-infinity bounded-Hessian affine-orthogonal tests are dense in the original
affine-orthogonal L2 subspace. Compact support is used before affine projection. -/
private theorem exists_smooth_bounded_hessian_approx {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ g ∧
      (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M) ∧ MemLp g 2 μ ∧
      (∫ x, g x ∂μ) = 0 ∧ (∀ u, ∫ x, ⟪u, x⟫ * g x ∂μ = 0) ∧
      eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε := by
  obtain ⟨ψ, hψsupp, hψsmooth, _, hgsmooth, hg2, hg0, hgorth, happrox⟩ :=
    exists_projected_smooth_approx μ hμ2 hμ0 hμcov hf hf0 hfx hε
  obtain ⟨M, hM⟩ := smooth_compact_hessian_bounded hψsmooth hψsupp
  have hψC2 : ContDiff ℝ 2 ψ := hψsmooth.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨affineOrthPart μ ψ, hgsmooth, ⟨M, ?_⟩, hg2, hg0, hgorth, happrox⟩
  intro x
  rw [(contDiff_affineOrthPart μ hψC2).2 x]
  exact hM x

private theorem hessian_const_mul {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ContDiff ℝ ∞ g) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (fun y => c * g y)) x = c • fderiv ℝ (fderiv ℝ g) x := by
  have hdg : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have heq : fderiv ℝ (fun y => c * g y) = fun y => c • fderiv ℝ g y := by
    funext y
    have heqf : (fun y => c * g y) = c • g := rfl
    rw [heqf]
    exact (((hg.differentiable (by simp)).differentiableAt.hasFDerivAt).const_smul c).fderiv
  rw [heq]
  exact (((hdg.differentiable (by simp)).differentiableAt.hasFDerivAt).const_smul c).fderiv

/-- A genuine nonzero smooth affine-orthogonal L2 test can be normalized to all of (108),
retaining smooth infinity and an actual Hessian bound. -/
private theorem normalize_smooth_test {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hM : ∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M)
    (hg2 : MemLp g 2 μ) (hg0 : ∫ x, g x ∂μ = 0)
    (hgorth : ∀ u, ∫ x, ⟪u, x⟫ * g x ∂μ = 0)
    (hpos : 0 < ∫ x, g x ^ 2 ∂μ) :
    let s : ℝ := Real.sqrt (∫ x, g x ^ 2 ∂μ)
    let q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => g x / s
    ContDiff ℝ ∞ q ∧ (∃ B : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ q) x‖ ≤ B) ∧
      MemLp q 2 μ ∧ (∫ x, q x ∂μ) = 0 ∧ (∫ x, q x ^ 2 ∂μ) = 1 ∧
      (∀ u, ∫ x, ⟪u, x⟫ * q x ∂μ = 0) := by
  dsimp only
  let s : ℝ := Real.sqrt (∫ x, g x ^ 2 ∂μ)
  have hs : 0 < s := Real.sqrt_pos.2 hpos
  have hs2 : s ^ 2 = ∫ x, g x ^ 2 ∂μ := Real.sq_sqrt hpos.le
  obtain ⟨M, hM⟩ := hM
  have hq2 : MemLp (fun x => g x / s) 2 μ := by
    simpa only [div_eq_mul_inv] using hg2.mul_const s⁻¹
  refine ⟨hg.div_const s, ⟨|s⁻¹| * M, ?_⟩, hq2, ?_, ?_, ?_⟩
  · intro x
    have heq : (fun x => g x / s) = fun x => s⁻¹ * g x := by
      funext x
      simp only [div_eq_mul_inv, mul_comm]
    rw [heq, hessian_const_mul hg]
    exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
      (by simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_left (hM x) (abs_nonneg s⁻¹))
  · rw [integral_div, hg0, zero_div]
  · simp only [div_pow]
    rw [integral_div, hs2, div_self hpos.ne']
  · intro u
    have heq : (fun x => ⟪u, x⟫ * (g x / s)) = fun x => (⟪u, x⟫ * g x) / s := by
      funext x
      ring
    rw [heq, integral_div, hgorth u, zero_div]

open FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor

section MeasurableSpace

variable {A : Type*}
  [MeasurableSpace A]

private theorem integral_sq_eq_norm_sq
    (μ : Measure A) {g : A → ℝ} (hg : MemLp g 2 μ) :
    (∫ x, g x ^ 2 ∂μ) = (eLpNorm g 2 μ).toReal ^ 2 := by
  let G : Lp ℝ 2 μ := hg.toLp g
  have hG : G =ᵐ[μ] g := hg.coeFn_toLp
  calc
    (∫ x, g x ^ 2 ∂μ) = ∫ x, (G x) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hG] with x hx
      rw [hx]
    _ = ∫ x, ⟪G x, G x⟫ ∂μ := by
      congr 1
      funext x
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = ⟪G, G⟫ := (MeasureTheory.L2.inner_def G G).symm
    _ = ‖G‖ ^ 2 := real_inner_self_eq_norm_sq G
    _ = (eLpNorm g 2 μ).toReal ^ 2 := by rw [Lp.norm_toLp]

private theorem norm_error_le (μ : Measure A)
    {f g : A → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε) :
    (eLpNorm (f - g) 2 μ).toReal ≤ ε ∧
      (eLpNorm g 2 μ).toReal ≤ (eLpNorm f 2 μ).toReal + ε := by
  have hfg : MemLp (f - g) 2 μ := hf.sub hg
  have herr : (eLpNorm (f - g) 2 μ).toReal ≤ ε := by
    simpa only [ENNReal.toReal_ofReal hε] using
      (ENNReal.toReal_le_toReal hfg.eLpNorm_ne_top ENNReal.ofReal_ne_top).2 happrox
  refine ⟨herr, ?_⟩
  have htri := eLpNorm_sub_le (f := f) (g := f - g) (μ := μ) one_le_two
  have heq : f - (f - g) = g := by funext x; simp
  rw [heq] at htri
  have ht := (ENNReal.toReal_le_toReal hg.eLpNorm_ne_top
    (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hfg.eLpNorm_ne_top⟩)).2 htri
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top hfg.eLpNorm_ne_top] at ht
  linarith

end MeasurableSpace

private theorem coeffs_const_mul {n d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (c : ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ (fun x => c * g x) d) =
      c • coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ g d) := by
  rw [taylorTensor_const_mul]
  ext J
  simp [coordTensor_apply]

private theorem coeffs_add {n d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ (fun x => f x + g x) d) =
      coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ f d) +
        coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ g d) := by
  rw [taylorTensor_add μ hexp hf hg]
  ext J
  simp [coordTensor_apply]

private theorem smooth_homogeneous_bound {n d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (B : ℝ)
    (hunit : ∀ q : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 q →
      (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ q) x‖ ≤ M) → MemLp q 2 μ →
      (∫ x, q x ∂μ) = 0 → (∫ x, q x ^ 2 ∂μ) = 1 →
      (∀ u, ∫ x, ⟪u, x⟫ * q x ∂μ = 0) →
      ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ q d)‖ ^ 2 ≤ B)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hM : ∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M)
    (hg2 : MemLp g 2 μ) (hg0 : ∫ x, g x ∂μ = 0)
    (hgorth : ∀ u, ∫ x, ⟪u, x⟫ * g x ∂μ = 0) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ g d)‖ ^ 2 ≤
      B * (eLpNorm g 2 μ).toReal ^ 2 := by
  let s : ℝ := (eLpNorm g 2 μ).toReal
  have hsnonneg : 0 ≤ s := ENNReal.toReal_nonneg
  by_cases hs0 : s = 0
  · obtain ⟨C, hC⟩ := exists_norm_coordTensor_taylorTensor_le μ hexp
      (EuclideanSpace.basisFun (Fin n) ℝ) d
    have hs0' : (eLpNorm g 2 μ).toReal = 0 := hs0
    have hnormle : ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ g d)‖ ≤ 0 := by
      simpa only [hs0', mul_zero] using hC g hg2
    have hnzero := le_antisymm hnormle (norm_nonneg _)
    simp only [hnzero, hs0', zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
  · have hs : 0 < s := lt_of_le_of_ne hsnonneg (Ne.symm hs0)
    have hpos : 0 < ∫ x, g x ^ 2 ∂μ := by
      rw [integral_sq_eq_norm_sq μ hg2]
      exact sq_pos_of_pos hs
    have hsqrt : Real.sqrt (∫ x, g x ^ 2 ∂μ) = s := by
      rw [integral_sq_eq_norm_sq μ hg2]
      exact Real.sqrt_sq hsnonneg
    have hnorm := normalize_smooth_test μ hg hM hg2 hg0 hgorth hpos
    dsimp only at hnorm
    rw [hsqrt] at hnorm
    obtain ⟨hq, hqM, hq2, hq0, hq1, hqorth⟩ := hnorm
    have hqbound := hunit (fun x => g x / s)
      (hq.of_le (WithTop.coe_le_coe.mpr le_top)) hqM hq2 hq0 hq1 hqorth
    have hnormscale :
        ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
            (taylorTensor μ (fun x => g x / s) d)‖ =
          ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ g d)‖ / s := by
      have heq : (fun x => g x / s) = fun x => s⁻¹ * g x := by funext x; ring
      rw [heq, coeffs_const_mul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
      ring
    rw [hnormscale, div_pow] at hqbound
    exact (div_le_iff₀ (sq_pos_of_pos hs)).1 hqbound

/--
Exact source affine-orthogonal density extension endpoint: the normalized smooth estimate extends to
the full affine-
orthogonal L2 subspace by actual smooth bounded-Hessian density and actual Taylor continuity. -/
theorem norm_coordTensor_taylorTensor_sq_le_of_smooth {d : ℕ} {b : ℝ} (hb : 0 ≤ b) {n : ℕ}
    (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b')
    (hiso : KLS.Isotropic hV.law)
    (h113 :
      ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 2 g →
          (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M) →
            MemLp g 2 (hV.law : Measure _) →
              ∫ x, g x ∂(hV.law : Measure _) = 0 →
                ∫ x, g x ^ 2 ∂(hV.law : Measure _) = 1 →
                  (∀ u, ∫ x, ⟪u, x⟫ * g x ∂(hV.law : Measure _) = 0) →
                    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                            (taylorTensor (hV.law : Measure _) g d)‖ ^
                        2 ≤
                      b / (d.factorial : ℝ) ^ 2)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 (hV.law : Measure _))
    (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^
        2 ≤
      b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 (hV.law : Measure _)).toReal ^ 2 := by
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := hV.law
  let B : ℝ := b / (d.factorial : ℝ) ^ 2
  let A : (EuclideanSpace ℝ (Fin n) → ℝ) → Coord n d := fun g =>
    coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ g d)
  have hB : 0 ≤ B := div_nonneg hb (sq_nonneg _)
  have hroot : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  have hrootsq : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
  have hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ := hV.integrable_exp_mul_norm
  obtain ⟨C, hC⟩ :=
    exists_norm_coordTensor_taylorTensor_le μ hexp (EuclideanSpace.basisFun (Fin n) ℝ) d
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right C 0
  have hcont (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : MemLp g 2 μ) :
    ‖A g‖ ≤ C0 * (eLpNorm g 2 μ).toReal :=
    (hC g hg).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) ENNReal.toReal_nonneg)
  have hnorm : ‖A f‖ ≤ Real.sqrt B * (eLpNorm f 2 μ).toReal := by
    apply le_of_forall_pos_le_add
    intro η hη
    let K : ℝ := C0 + Real.sqrt B
    have hK : 0 ≤ K := add_nonneg hC0 hroot
    let ε : ℝ := η / (K + 1)
    have hden : 0 < K + 1 := by linarith
    have hε : 0 < ε := div_pos hη hden
    have hεeq : ε * (K + 1) = η := (div_mul_cancel₀ _ hden.ne')
    have hKε : K * ε ≤ η := by nlinarith [hε.le]
    obtain ⟨g, hgSmooth, hgM, hg2, hg0, hgorth, happrox⟩ :=
      exists_smooth_bounded_hessian_approx μ hiso.memLp_two hiso.mean_zero
        hiso.integral_inner_mul_inner hf hf0 hfx hε
    obtain ⟨herr, hgnorm⟩ := norm_error_le μ hf hg2 hε.le happrox
    have hgBound : ‖A g‖ ^ 2 ≤ B * (eLpNorm g 2 μ).toReal ^ 2 :=
      smooth_homogeneous_bound μ hexp B h113 hgSmooth hgM hg2 hg0 hgorth
    have hgBoundNorm : ‖A g‖ ≤ Real.sqrt B * (eLpNorm g 2 μ).toReal := by
      have hrnonneg : 0 ≤ Real.sqrt B * (eLpNorm g 2 μ).toReal :=
        mul_nonneg hroot ENNReal.toReal_nonneg
      have hsq : (Real.sqrt B * (eLpNorm g 2 μ).toReal) ^ 2 = B * (eLpNorm g 2 μ).toReal ^ 2 := by
        rw [mul_pow, hrootsq]
      nlinarith [sq_nonneg (‖A g‖ - Real.sqrt B * (eLpNorm g 2 μ).toReal), norm_nonneg (A g)]
    have hfg2 : MemLp (f - g) 2 μ := hf.sub hg2
    have heq : (fun x => (f - g) x + g x) = f := by funext x; simp
    have hadd : A f = A (f - g) + A g := by
      have ht := coeffs_add μ hexp hfg2 hg2 (d := d)
      rw [heq] at ht
      exact ht
    calc
      ‖A f‖ = ‖A (f - g) + A g‖ := congrArg norm hadd
      _ ≤ ‖A (f - g)‖ + ‖A g‖ := norm_add_le _ _
      _ ≤ C0 * (eLpNorm (f - g) 2 μ).toReal + Real.sqrt B * (eLpNorm g 2 μ).toReal :=
        add_le_add (hcont (f - g) hfg2) hgBoundNorm
      _ ≤ C0 * ε + Real.sqrt B * ((eLpNorm f 2 μ).toReal + ε) :=
        add_le_add (mul_le_mul_of_nonneg_left herr hC0) (mul_le_mul_of_nonneg_left hgnorm hroot)
      _ = Real.sqrt B * (eLpNorm f 2 μ).toReal + K * ε := by dsimp [K]; ring
      _ ≤ Real.sqrt B * (eLpNorm f 2 μ).toReal + η := add_le_add le_rfl hKε
  change ‖A f‖ ^ 2 ≤ B * (eLpNorm f 2 μ).toReal ^ 2
  have hsq : (Real.sqrt B * (eLpNorm f 2 μ).toReal) ^ 2 = B * (eLpNorm f 2 μ).toReal ^ 2 := by
    rw [mul_pow, hrootsq]
  nlinarith [norm_nonneg (A f), mul_nonneg hroot (ENNReal.toReal_nonneg (a := eLpNorm f 2 μ))]


/--
**BKL (113) for every `f ∈ L²(μ)` orthogonal to the affine functions**, under `CumulantBound d b`:
the smooth case `norm_coordTensor_taylorTensor_sq_le_of_cumulantBound` extended by density. -/
theorem norm_coordTensor_taylorTensor_sq_le_of_orthogonal {d : ℕ} (hd : 2 ≤ d) {b : ℝ}
    (hb : 0 < b) (hcb : CumulantBound d b) {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') (hiso : KLS.Isotropic hV.law)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 (hV.law : Measure _))
    (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^
        2 ≤
      b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 (hV.law : Measure _)).toReal ^ 2 :=
  norm_coordTensor_taylorTensor_sq_le_of_smooth hb.le V hV hiso
    (fun _g hg ⟨_M, hM⟩ hg2 hg0 hg1 hgx =>
      norm_coordTensor_taylorTensor_sq_le_of_cumulantBound hd hb hcb V hV hiso hg hM hg2 hg0 hg1
        hgx)
    hf hf0 hfx

/-! ### The assembly (107) -/

open FunctionalInequalities.Analysis.Tensor FunctionalInequalities.L2
open FunctionalInequalities.KLS.LogConcave.Suspension

private theorem taylorTensor_constant_zero {n d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (c : ℝ) (hd : 1 ≤ d) : taylorTensor μ (fun _ => c) d = 0 := by
  have hprob (z : EuclideanSpace ℝ (Fin n)) : IsProbabilityMeasure (expTilt μ z) := by
    have hint : Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
      refine (hexp ‖z‖).mono'
        ((by fun_prop : Continuous (fun x => Real.exp ⟪z, x⟫)).aestronglyMeasurable) ?_
      filter_upwards [] with x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
    exact isProbabilityMeasure_tilted hint
  have hAvg : tiltAverage μ (fun _ => c) = fun _ => c := by
    funext z
    let _ : IsProbabilityMeasure (expTilt μ z) := hprob z
    simp [tiltAverage]
  unfold taylorTensor
  rw [hAvg, iteratedFDeriv_const_of_ne (by omega : d ≠ 0)]
  ext h
  simp

/-- **BKL Proposition 7.1, (107).** Exact original mathematical header. -/
theorem norm_coordTensor_taylorTensor_sq_le_two_mul {d : ℕ} (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b)
    (hcb : CumulantBound d b) {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') (hiso : KLS.Isotropic hV.law)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemLp f 2 (hV.law : Measure _)) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^
        2 ≤
      2 * b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 (hV.law : Measure _)).toReal ^ 2 := by
  classical
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := hV.law
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let c : ℝ := ∫ x, f x ∂μ
  let co : Fin n → ℝ := fun j => ∫ x, ⟪e j, x⟫ * f x ∂μ
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 co
  let l : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ⟪v, x⟫
  let q : EuclideanSpace ℝ (Fin n) → ℝ := affineOrthPart μ f
  let A : (EuclideanSpace ℝ (Fin n) → ℝ) → Coord n d := fun g =>
    coordTensor e (taylorTensor μ g d)
  let B : ℝ := b / (d.factorial : ℝ) ^ 2
  have hB : 0 ≤ B := div_nonneg hb.le (sq_nonneg _)
  have hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ := hV.integrable_exp_mul_norm
  have hq2 : MemLp q 2 μ := memLp_affineOrthPart μ hiso.memLp_two hf
  have hq0 : ∫ x, q x ∂μ = 0 := integral_affineOrthPart μ hiso.memLp_two hiso.mean_zero hf
  have hqorth : ∀ u, ∫ x, ⟪u, x⟫ * q x ∂μ = 0 :=
    integral_inner_mul_affineOrthPart μ hiso.memLp_two hiso.mean_zero
      hiso.integral_inner_mul_inner hf
  have hqbound : ‖A q‖ ^ 2 ≤ B * (eLpNorm q 2 μ).toReal ^ 2 :=
    norm_coordTensor_taylorTensor_sq_le_of_orthogonal hd hb hcb V hV hiso hq2 hq0 hqorth
  have hl2 : MemLp l 2 μ := by
    simpa only [l, μ, Function.comp_def, id_eq, innerSL_apply_apply] using
      (innerSL ℝ v).comp_memLp' hiso.memLp_two
  have hlbound : ‖A l‖ ^ 2 ≤ B * ‖v‖ ^ 2 :=
    norm_coordTensor_taylorTensor_inner_sq_le_of_basis μ hexp e
      (hcb n hV.law hiso hV.logConcave_law) v
  have hvnorm : ‖v‖ ^ 2 = ∑ j, co j ^ 2 := EuclideanSpace.real_norm_sq_eq v
  have hrepr (x : EuclideanSpace ℝ (Fin n)) : ⟪v, x⟫ = ∑ j, co j * ⟪e j, x⟫ := by
    simpa only [e, EuclideanSpace.basisFun_inner, EuclideanSpace.inner_basisFun_real, v] using
      (e.sum_inner_mul_inner v x).symm
  have hdecomp : (fun x => (c + l x) + q x) = f := by
    funext x
    simp only [q, l, hrepr, c, co, affineOrthPart, e]
    ring
  have hc2 : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => c) 2 μ := memLp_const c
  have hcl2 : MemLp (fun x => c + l x) 2 μ := hc2.add hl2
  have hconst : A (fun _ => c) = 0 := by
    dsimp [A]
    rw [taylorTensor_constant_zero μ hexp c (by omega)]
    ext J
    simp [coordTensor_apply]
  have hAl : A (fun x => c + l x) = A l := by
    have ht := coeffs_add μ hexp hc2 hl2 (d := d)
    change A (fun x => c + l x) = A (fun _ => c) + A l at ht
    rw [hconst, zero_add] at ht
    exact ht
  have hAf : A f = A l + A q := by
    have ht := coeffs_add μ hexp hcl2 hq2 (d := d)
    rw [hdecomp] at ht
    change A f = A (fun x => c + l x) + A q at ht
    rw [hAl] at ht
    exact ht
  have hpyth :=
    integral_sq_eq_affine_decomposition μ hiso.memLp_two hiso.mean_zero
      hiso.integral_inner_mul_inner hf
  have henergy : ‖v‖ ^ 2 + ∫ x, q x ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂μ := by
    change ‖v‖ ^ 2 + ∫ x, affineOrthPart μ f x ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂μ
    rw [hvnorm]
    dsimp [co, e]
    linarith [sq_nonneg (∫ x, f x ∂μ)]
  have hqnorm : (eLpNorm q 2 μ).toReal ^ 2 = ∫ x, q x ^ 2 ∂μ :=
    (integral_sq_eq_norm_sq μ hq2).symm
  have hfnorm : (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ :=
    (integral_sq_eq_norm_sq μ hf).symm
  have htri : ‖A f‖ ≤ ‖A l‖ + ‖A q‖ := by rw [hAf]; exact norm_add_le _ _
  have htwonorm : ‖A f‖ ^ 2 ≤ 2 * (‖A l‖ ^ 2 + ‖A q‖ ^ 2) := by
    nlinarith [norm_nonneg (A f), norm_nonneg (A l), norm_nonneg (A q),
      sq_nonneg (‖A l‖ - ‖A q‖)]
  rw [hqnorm] at hqbound
  change ‖A f‖ ^ 2 ≤ 2 * b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 μ).toReal ^ 2
  rw [hfnorm]
  calc
    ‖A f‖ ^ 2 ≤ 2 * (‖A l‖ ^ 2 + ‖A q‖ ^ 2) := htwonorm
    _ ≤ 2 * (B * ‖v‖ ^ 2 + B * ∫ x, q x ^ 2 ∂μ) := by gcongr
    _ = 2 * B * (‖v‖ ^ 2 + ∫ x, q x ^ 2 ∂μ) := by ring
    _ ≤ 2 * B * (∫ x, f x ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left henergy (mul_nonneg (by norm_num) hB)
    _ = _ := by dsimp [B]; ring

end FunctionalInequalities.KLS.LogConcave.Suspension
