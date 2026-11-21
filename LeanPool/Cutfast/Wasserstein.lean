/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.Tactic.Lemma
public import Mathlib.Tactic.Monotonicity.Lemmas

/-!
# Wasserstein distance for position-scale transformations (Lemma 2.1)

We prove that `W₂²` is symmetric, and Lemma 2.1 of the paper: if `T x = A x + h` with `A`
a positive (symmetric, positive semidefinite) operator, then `T` is an optimal transport map
from `μ` to `T_#μ`, so that `W₂²(μ, T_#μ) = ∫ ‖T x - x‖² dμ`.

The proof does not use Brenier's theorem. The upper bound uses the coupling `(id, T)_#μ`.
For the lower bound, we regularize `A` into `B = A + δ • 1`, which is invertible, and use the
Fenchel–Young inequality `2⟪x, B w⟫ ≤ ⟪B x, x⟫ + ⟪B w, w⟫` (with `B w = y - h`) to bound
`‖x - y‖²` from below by a sum `f₁ x + f₂ y` of integrable functions, whose integral against
any coupling only depends on the marginals. Letting `δ → 0` gives the result.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace

namespace Cutfast

namespace Wasserstein

variable {d : ℕ}

lemma edist_sq_eq (x y : E d) : edist x y ^ 2 = ENNReal.ofReal (‖x - y‖ ^ 2) := by
  rw [edist_dist, dist_eq_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

lemma measurable_cost : Measurable (fun p : E d × E d => edist p.1 p.2 ^ 2) :=
  (measurable_fst.edist measurable_snd).pow_const 2

variable {α : Type*} [MeasurableSpace α] {ρ : Measure α}

/-- The inner product of two square-integrable functions is integrable. -/
lemma integrable_inner {f g : α → E d} (hf : AEStronglyMeasurable f ρ)
    (hg : AEStronglyMeasurable g ρ) (hf2 : Integrable (fun a => ‖f a‖ ^ 2) ρ)
    (hg2 : Integrable (fun a => ‖g a‖ ^ 2) ρ) :
    Integrable (fun a => ⟪f a, g a⟫_ℝ) ρ := by
  refine (hf2.add hg2).mono' (hf.inner hg) (ae_of_all _ fun a => ?_)
  have h1 := abs_real_inner_le_norm (f a) (g a)
  rw [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [norm_nonneg (f a), norm_nonneg (g a), sq_nonneg (‖f a‖ - ‖g a‖)]

/-- An affine image of a square-integrable function is square-integrable. -/
lemma integrable_sq_clm [IsFiniteMeasure ρ] {f : α → E d} (hf : AEStronglyMeasurable f ρ)
    (hf2 : Integrable (fun a => ‖f a‖ ^ 2) ρ) (L : E d →L[ℝ] E d) (c : E d) :
    Integrable (fun a => ‖L (f a) + c‖ ^ 2) ρ := by
  refine ((hf2.const_mul (2 * ‖L‖ ^ 2)).add (integrable_const (2 * ‖c‖ ^ 2))).mono'
    (((L.continuous.comp_aestronglyMeasurable hf).add aestronglyMeasurable_const).norm.pow 2)
    (ae_of_all _ fun a => ?_)
  have h1 := norm_add_le (L (f a)) c
  have h2 := L.le_opNorm (f a)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h3 : ‖L (f a) + c‖ ≤ ‖L‖ * ‖f a‖ + ‖c‖ := by linarith
  have h4 : 0 ≤ ‖L (f a) + c‖ := norm_nonneg _
  rw [Pi.add_apply]
  nlinarith [sq_nonneg (‖L‖ * ‖f a‖ - ‖c‖), norm_nonneg c, mul_nonneg (norm_nonneg L)
    (norm_nonneg (f a))]

/-- A function with integrable squared norm on a finite measure space is integrable. -/
lemma integrable_of_sq [IsFiniteMeasure ρ] {f : α → E d} (hf : AEStronglyMeasurable f ρ)
    (hf2 : Integrable (fun a => ‖f a‖ ^ 2) ρ) : Integrable f ρ := by
  refine (hf2.add (integrable_const 1)).mono' hf (ae_of_all _ fun a => ?_)
  rw [Pi.add_apply]
  nlinarith [sq_nonneg (‖f a‖ - 1)]

/-- Fenchel–Young type inequality for a positive operator `P`:
`2⟪x, P w⟫ ≤ ⟪P x, x⟫ + ⟪P w, w⟫`. -/
lemma two_inner_le {P : E d →L[ℝ] E d} (hP : P.IsPositive) (x w : E d) :
    2 * ⟪x, P w⟫_ℝ ≤ ⟪P x, x⟫_ℝ + ⟪P w, w⟫_ℝ := by
  have h := hP.re_inner_nonneg_left (x - w)
  have hs := hP.inner_left_eq_inner_right w x
  simp only [RCLike.re_to_real, map_sub, inner_sub_left, inner_sub_right] at h
  have e1 : ⟪P x, w⟫_ℝ = ⟪w, P x⟫_ℝ := real_inner_comm _ _
  have e2 : ⟪P w, x⟫_ℝ = ⟪x, P w⟫_ℝ := real_inner_comm _ _
  linarith

/-- If `(A + δ • 1) w = A z` with `A` positive and `δ ≥ 0`, then
`⟪(A + δ • 1) w, w⟫ ≤ ⟪A z, z⟫`. -/
lemma inner_reg_le {A : E d →L[ℝ] E d} (hA : A.IsPositive) {δ : ℝ} (hδ : 0 ≤ δ)
    {w z : E d} (hwz : (A + δ • (1 : E d →L[ℝ] E d)) w = A z) :
    ⟪(A + δ • (1 : E d →L[ℝ] E d)) w, w⟫_ℝ ≤ ⟪A z, z⟫_ℝ := by
  have h := two_inner_le hA z w
  have hs := hA.inner_left_eq_inner_right z w
  have hB : ⟪(A + δ • (1 : E d →L[ℝ] E d)) w, w⟫_ℝ = ⟪A w, w⟫_ℝ + δ * ⟪w, w⟫_ℝ := by
    simp [inner_add_left, inner_smul_left]
  have hw : 0 ≤ ⟪w, w⟫_ℝ := real_inner_self_nonneg
  have hzw : ⟪A z, w⟫_ℝ = ⟪A w, w⟫_ℝ + δ * ⟪w, w⟫_ℝ := by rw [← hwz, hB]
  have e : ⟪A z, w⟫_ℝ = ⟪w, A z⟫_ℝ := real_inner_comm _ _
  rw [hB]
  nlinarith [mul_nonneg hδ hw]

/-- The key lower bound: for every coupling `γ` of `μ` and `T_#μ` and every `δ > 0`,
`∫ ‖x - T x‖² dμ - δ ∫ ‖x‖² dμ ≤ ∫ ‖x - y‖² dγ`. -/
lemma lower_bound (μ : Measure (E d)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ‖x‖ ^ 2) μ) {A : E d →L[ℝ] E d} (hA : A.IsPositive) (h : E d)
    (γ : Measure (E d × E d)) (h1 : γ.map Prod.fst = μ)
    (h2 : γ.map Prod.snd = μ.map fun x => A x + h) {δ : ℝ} (hδ : 0 < δ) :
    ∫ x, ‖x - (A x + h)‖ ^ 2 ∂μ - δ * ∫ x, ‖x‖ ^ 2 ∂μ ≤ ∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ := by
  set T : E d → E d := fun x => A x + h with hT
  set ν := μ.map T with hν
  have hTc : Continuous T := A.continuous.add continuous_const
  have hTm : Measurable T := hTc.measurable
  have hid : AEStronglyMeasurable (fun x : E d => x) μ := aestronglyMeasurable_id
  have hν2 : Integrable (fun y => ‖y‖ ^ 2) ν :=
    (integrable_map_measure (by fun_prop) hTm.aemeasurable).2 (integrable_sq_clm hid hμ A h)
  -- second moments of the marginals of `γ`
  have hγ1 : Integrable (fun p : E d × E d => ‖p.1‖ ^ 2) γ := by
    have : Integrable (fun x : E d => ‖x‖ ^ 2) (γ.map Prod.fst) := h1 ▸ hμ
    exact (integrable_map_measure (by fun_prop) measurable_fst.aemeasurable).1 this
  have hγ2 : Integrable (fun p : E d × E d => ‖p.2‖ ^ 2) γ := by
    have : Integrable (fun x : E d => ‖x‖ ^ 2) (γ.map Prod.snd) := h2 ▸ hν2
    exact (integrable_map_measure (by fun_prop) measurable_snd.aemeasurable).1 this
  -- the regularized operator and its inverse
  set B : E d →L[ℝ] E d := A + δ • (1 : E d →L[ℝ] E d) with hBdef
  have hBinner : ∀ x, ⟪B x, x⟫_ℝ = ⟪A x, x⟫_ℝ + δ * ‖x‖ ^ 2 := fun x => by
    simp [hBdef, inner_add_left, inner_smul_left]
  have hBpos : B.IsPositive := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · simp only [hBdef, ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
        LinearMap.add_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
        one_apply_eq_self, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right]
      rw [hA.inner_left_eq_inner_right]
      simp
    · simp only [ContinuousLinearMap.reApplyInnerSelf, RCLike.re_to_real, hBinner]
      have := hA.re_inner_nonneg_left x
      simp only [RCLike.re_to_real] at this
      positivity
  have hBinj : Function.Injective (B : E d →ₗ[ℝ] E d) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 := hBinner x
    have hx' : B x = 0 := hx
    rw [hx', inner_zero_left] at h0
    have := hA.re_inner_nonneg_left x
    simp only [RCLike.re_to_real] at this
    have : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x‖]
    simpa using this
  set e := LinearEquiv.ofInjectiveEndo (B : E d →ₗ[ℝ] E d) hBinj
  set C : E d →L[ℝ] E d := LinearMap.toContinuousLinearMap (e.symm : E d →ₗ[ℝ] E d)
  have hBC : ∀ y, B (C y) = y := fun y => e.apply_symm_apply y
  -- the two potentials
  set f₁ : E d → ℝ := fun x => ‖x‖ ^ 2 - ⟪B x, x⟫_ℝ - 2 * ⟪x, h⟫_ℝ with hf₁
  set f₂ : E d → ℝ := fun y => ‖y‖ ^ 2 - ⟪y - h, C (y - h)⟫_ℝ with hf₂
  have hf₁c : Continuous f₁ := by fun_prop
  have hf₂c : Continuous f₂ := by fun_prop
  have key : ∀ x y, f₁ x + f₂ y ≤ ‖x - y‖ ^ 2 := fun x y => by
    have := two_inner_le hBpos x (C (y - h))
    rw [hBC] at this
    simp only [hf₁, hf₂, inner_sub_right] at this ⊢
    rw [norm_sub_sq_real]
    linarith
  have key₂ : ∀ x, ‖T x‖ ^ 2 - ⟪A x, x⟫_ℝ ≤ f₂ (T x) := fun x => by
    have hw : B (C (A x)) = A x := hBC _
    have := inner_reg_le hA hδ.le hw
    rw [hw] at this
    have e : ⟪x, A x⟫_ℝ = ⟪A x, x⟫_ℝ := real_inner_comm _ _
    simp only [hf₂, hT, add_sub_cancel_right]
    linarith
  have key₁ : ∀ x, f₁ x + (‖T x‖ ^ 2 - ⟪A x, x⟫_ℝ) = ‖x - T x‖ ^ 2 - δ * ‖x‖ ^ 2 := fun x => by
    simp only [hf₁, hT, hBinner, norm_sub_sq_real, inner_add_right]
    rw [real_inner_comm (A x) x]
    ring
  -- integrability
  have hf₁i : Integrable f₁ μ := by
    refine (hμ.sub (integrable_inner (B.continuous.aestronglyMeasurable) hid ?_ hμ)).sub
      ((integrable_inner hid aestronglyMeasurable_const hμ (integrable_const _)).const_mul 2)
    simpa using integrable_sq_clm hid hμ B 0
  have hf₂i : Integrable f₂ ν := by
    have hidν : AEStronglyMeasurable (fun y : E d => y) ν := aestronglyMeasurable_id
    have h3 : Integrable (fun y => ‖y - h‖ ^ 2) ν := by
      simpa [sub_eq_add_neg] using integrable_sq_clm hidν hν2 1 (-h)
    have h4 : Integrable (fun y => ‖C (y - h)‖ ^ 2) ν := by
      simpa [sub_eq_add_neg] using integrable_sq_clm hidν hν2 C (-C h)
    exact hν2.sub (integrable_inner (by fun_prop) (by fun_prop) h3 h4)
  have hf₂Ti : Integrable (fun x => f₂ (T x)) μ :=
    (integrable_map_measure hf₂c.aestronglyMeasurable hTm.aemeasurable).1 hf₂i
  have hf₁γ : Integrable (fun p : E d × E d => f₁ p.1) γ := by
    have : Integrable f₁ (γ.map Prod.fst) := by rw [h1]; exact hf₁i
    exact this.comp_measurable measurable_fst
  have hf₂γ : Integrable (fun p : E d × E d => f₂ p.2) γ := by
    have : Integrable f₂ (γ.map Prod.snd) := by rw [h2]; exact hf₂i
    exact this.comp_measurable measurable_snd
  have hcost : Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) γ := by
    refine ((hγ1.add hγ2).const_mul 2).mono' (by fun_prop) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Pi.add_apply]
    have := norm_sub_le p.1 p.2
    nlinarith [norm_nonneg (p.1 - p.2), sq_nonneg (‖p.1‖ - ‖p.2‖)]
  have hI : Integrable (fun x => ‖x - T x‖ ^ 2) μ := by
    have := integrable_sq_clm hid hμ (1 - A) (-h)
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [hT, sub_apply, one_apply_eq_self]
    congr 2
    abel
  have hTsq : Integrable (fun x => ‖T x‖ ^ 2 - ⟪A x, x⟫_ℝ) μ :=
    (integrable_sq_clm hid hμ A h).sub (integrable_inner (by fun_prop) hid
      (by simpa using integrable_sq_clm hid hμ A 0) hμ)
  -- integrate
  have e₁ : ∫ p, f₁ p.1 ∂γ = ∫ x, f₁ x ∂μ := by
    rw [← h1, integral_map measurable_fst.aemeasurable (h1 ▸ hf₁c.aestronglyMeasurable)]
  have e₂ : ∫ p, f₂ p.2 ∂γ = ∫ x, f₂ (T x) ∂μ := by
    have : ∫ x, f₂ (T x) ∂μ = ∫ y, f₂ y ∂ν :=
      (integral_map hTm.aemeasurable hf₂c.aestronglyMeasurable).symm
    rw [this, ← h2, integral_map measurable_snd.aemeasurable (h2 ▸ hf₂c.aestronglyMeasurable)]
  calc ∫ x, ‖x - (A x + h)‖ ^ 2 ∂μ - δ * ∫ x, ‖x‖ ^ 2 ∂μ
      = ∫ x, (f₁ x + (‖T x‖ ^ 2 - ⟪A x, x⟫_ℝ)) ∂μ := by
        simp_rw [key₁]
        rw [integral_sub hI (hμ.const_mul δ), integral_const_mul]
    _ ≤ ∫ x, (f₁ x + f₂ (T x)) ∂μ :=
        integral_mono (hf₁i.add hTsq) (hf₁i.add hf₂Ti) fun x => by
          simp only; linarith [key₂ x]
    _ = ∫ p, (f₁ p.1 + f₂ p.2) ∂γ := by
        rw [integral_add hf₁i hf₂Ti, integral_add hf₁γ hf₂γ, e₁, e₂]
    _ ≤ ∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ :=
        integral_mono (hf₁γ.add hf₂γ) hcost fun p => key p.1 p.2

end Wasserstein

open Wasserstein in
/-- The squared Wasserstein distance is symmetric. -/
theorem wassersteinSq_comm {d : ℕ} (μ ν : Measure (E d)) :
    wassersteinSq μ ν = wassersteinSq ν μ := by
  have key : ∀ μ ν : Measure (E d), wassersteinSq ν μ ≤ wassersteinSq μ ν := by
    intro μ ν
    refine le_iInf fun γ => le_iInf fun hγ => le_iInf fun h1 => le_iInf fun h2 => ?_
    have := hγ
    have hs : Measurable (Prod.swap : E d × E d → E d × E d) := measurable_swap
    refine iInf_le_of_le (γ.map Prod.swap) <| iInf_le_of_le inferInstance <|
      iInf_le_of_le ?_ <| iInf_le_of_le ?_ ?_
    · rw [Measure.map_map measurable_fst hs]; exact h2
    · rw [Measure.map_map measurable_snd hs]; exact h1
    · rw [lintegral_map measurable_cost hs]
      simp [edist_comm]
  exact le_antisymm (key ν μ) (key μ ν)

open Wasserstein in
/-- Lemma 2.1: for a positive operator `A` and `h ∈ ℝᵈ`, the affine map `x ↦ A x + h` is
optimal, and `W₂²(μ, (A · + h)_#μ) = ∫ ‖(A - 1) x‖² dμ + 2⟪(A - 1) 𝔼 X, h⟫ + ‖h‖²`. -/
theorem wassersteinSq_map_affine' {d : ℕ} (μ : Measure (E d)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ‖x‖ ^ 2) μ) (A : E d →L[ℝ] E d) (hA : A.IsPositive) (h : E d) :
    wassersteinSq μ (μ.map fun x => A x + h) =
      ENNReal.ofReal (∫ x, ‖(A - 1) x‖ ^ 2 ∂μ + 2 * ⟪(A - 1) (∫ x, x ∂μ), h⟫_ℝ + ‖h‖ ^ 2) := by
  set T : E d → E d := fun x => A x + h with hT
  have hTc : Continuous T := A.continuous.add continuous_const
  have hTm : Measurable T := hTc.measurable
  have hid : AEStronglyMeasurable (fun x : E d => x) μ := aestronglyMeasurable_id
  have hI : Integrable (fun x => ‖x - T x‖ ^ 2) μ := by
    have := integrable_sq_clm hid hμ (1 - A) (-h)
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [hT, sub_apply, one_apply_eq_self]
    congr 2
    abel
  have hRHS : ∫ x, ‖(A - 1) x‖ ^ 2 ∂μ + 2 * ⟪(A - 1) (∫ x, x ∂μ), h⟫_ℝ + ‖h‖ ^ 2 =
      ∫ x, ‖x - T x‖ ^ 2 ∂μ := by
    have hx : Integrable (fun x : E d => x) μ := integrable_of_sq hid hμ
    have h1 : Integrable (fun x => ‖(A - 1) x‖ ^ 2) μ := by
      simpa using integrable_sq_clm hid hμ (A - 1) 0
    have h2 : Integrable (fun x => ⟪(A - 1) x, h⟫_ℝ) μ :=
      integrable_inner (by fun_prop) aestronglyMeasurable_const h1 (integrable_const _)
    have e : ∀ x, ‖x - T x‖ ^ 2 = ‖(A - 1) x‖ ^ 2 + 2 * ⟪(A - 1) x, h⟫_ℝ + ‖h‖ ^ 2 := by
      intro x
      rw [← norm_add_sq_real, ← norm_neg]
      congr 1
      simp only [hT, sub_apply, one_apply_eq_self]
      abel_nf
    have hlin : ∫ x, ⟪(A - 1) x, h⟫_ℝ ∂μ = ⟪(A - 1) (∫ x, x ∂μ), h⟫_ℝ := by
      have := ((innerSL ℝ h).comp (A - 1)).integral_comp_comm hx
      calc ∫ x, ⟪(A - 1) x, h⟫_ℝ ∂μ = ∫ x, ((innerSL ℝ h).comp (A - 1)) x ∂μ :=
            integral_congr_ae (ae_of_all _ fun x => by simp [real_inner_comm, inner_sub_right])
        _ = _ := this
        _ = _ := by simp [real_inner_comm, inner_sub_right]
    have h3 : Integrable (fun x => ‖(A - 1) x‖ ^ 2 + 2 * ⟪(A - 1) x, h⟫_ℝ) μ :=
      h1.add (h2.const_mul 2)
    simp_rw [e]
    rw [integral_add h3 (integrable_const _), integral_add h1 (h2.const_mul 2),
      integral_const_mul, hlin]
    simp
  rw [hRHS]
  apply le_antisymm
  · -- upper bound: the coupling `(id, T)₊μ`
    have hg : Measurable fun x : E d => (x, T x) := measurable_id.prodMk hTm
    refine iInf_le_of_le (μ.map fun x => (x, T x)) <| iInf_le_of_le inferInstance <|
      iInf_le_of_le ?_ <| iInf_le_of_le ?_ ?_
    · rw [Measure.map_map measurable_fst hg]; exact Measure.map_id
    · rw [Measure.map_map measurable_snd hg]; rfl
    · rw [lintegral_map measurable_cost hg, ofReal_integral_eq_lintegral_ofReal hI
        (ae_of_all _ fun x => by positivity)]
      simp only [edist_sq_eq, le_refl]
  · -- lower bound
    refine le_iInf fun γ => le_iInf fun _ => le_iInf fun h1 => le_iInf fun h2 => ?_
    have hγ1 : Integrable (fun p : E d × E d => ‖p.1‖ ^ 2) γ := by
      have : Integrable (fun x : E d => ‖x‖ ^ 2) (γ.map Prod.fst) := h1 ▸ hμ
      exact (integrable_map_measure (by fun_prop) measurable_fst.aemeasurable).1 this
    have hγ2 : Integrable (fun p : E d × E d => ‖p.2‖ ^ 2) γ := by
      have hν2 : Integrable (fun y => ‖y‖ ^ 2) (μ.map T) :=
        (integrable_map_measure (by fun_prop) hTm.aemeasurable).2 (integrable_sq_clm hid hμ A h)
      have : Integrable (fun x : E d => ‖x‖ ^ 2) (γ.map Prod.snd) := h2 ▸ hν2
      exact (integrable_map_measure (by fun_prop) measurable_snd.aemeasurable).1 this
    have hcost : Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) γ := by
      refine ((hγ1.add hγ2).const_mul 2).mono' (by fun_prop) (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Pi.add_apply]
      have := norm_sub_le p.1 p.2
      nlinarith [norm_nonneg (p.1 - p.2), sq_nonneg (‖p.1‖ - ‖p.2‖)]
    have hlin : ∫⁻ p, edist p.1 p.2 ^ 2 ∂γ = ENNReal.ofReal (∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hcost (ae_of_all _ fun x => by positivity)]
      simp only [edist_sq_eq]
    rw [hlin]
    refine ENNReal.ofReal_le_ofReal (le_of_forall_pos_le_add fun ε hε => ?_)
    set M := ∫ x, ‖x‖ ^ 2 ∂μ
    have hM : 0 ≤ M := integral_nonneg fun x => by positivity
    have hδ : 0 < ε / (M + 1) := by positivity
    have := lower_bound μ hμ hA h γ h1 h2 hδ
    have hδM : ε / (M + 1) * M ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    simp only [hT] at *
    linarith

end Cutfast
