/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.GrowthBound

/-!
# Restriction, isometric transport, and monotonicity of the growth bound

Three elementary constructions on `FastDynamo.StronglyContinuousSemigroup` that the
assembly of the growth rate on a distinguished closed subspace needs, and that involve
no analysis beyond the definitions.

* `StronglyContinuousSemigroup.restrict`: a semigroup that leaves a submodule `W`
  invariant restricts to a semigroup on `W`.  The evolution operator is
  `(S t).comp W.subtypeL` corestricted to `W` by `ContinuousLinearMap.codRestrict`, so
  the three semigroup laws are the ambient ones read through the subtype coercion, and
  strong continuity of the restricted orbit is continuity of the ambient orbit followed
  by `Continuous.subtype_mk`.  No closedness of `W` is needed for the construction
  itself; closedness enters only where the invariance hypothesis is *produced* (by a
  limit argument), not here.  The quantitative content is
  `norm_restrict_le`, `‖S|_W t‖ ≤ ‖S t‖`, from `ContinuousLinearMap.le_opNorm`.

* `StronglyContinuousSemigroup.congr`: transport of a semigroup along a surjective
  linear isometry `e : X ≃ₗᵢ[ℂ] Y`, by conjugation `e ∘ S t ∘ e.symm`.  Because `e` and
  `e.symm` preserve norms, `norm_congr` is an exact equality of operator norms and not
  merely a bound, and hence `growthBound_congr` is an exact equality of growth bounds.
  This is what makes the growth rate independent of the chosen isometric model of the
  state space.

* `StronglyContinuousSemigroup.growthBound_mono_of_norm_le`: a pointwise comparison of
  operator norms, `‖S t‖ ≤ ‖T t‖` for every nonnegative time, propagates to the growth
  bounds, `S.growthBound ≤ T.growthBound`.  The two semigroups are allowed to live on
  different spaces, since only their operator norms enter the definition of
  `FastDynamo.StronglyContinuousSemigroup.growthBound`.  The comparison is a
  `Filter.limsup_le_limsup`: at the times where `‖S t‖` vanishes the integrand is `⊥`
  and there is nothing to prove, and elsewhere `0 < ‖S t‖ ≤ ‖T t‖` makes `Real.log`
  monotone, the factor `t⁻¹` being nonnegative along `atTop`.

Together, `growthBound_restrict_le` says that passing to an invariant subspace can only
decrease the growth bound; the reverse inequality is false in general and is not claimed.
-/

@[expose] public section

namespace FastDynamo

universe u v

namespace StronglyContinuousSemigroup

variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-!
## Comparison of growth bounds
-/

/--
Monotonicity of the growth bound in the operator norm: if `‖S t‖ ≤ ‖T t‖` at every
nonnegative time then `S.growthBound ≤ T.growthBound`.

The two semigroups may live on different spaces, since
`FastDynamo.StronglyContinuousSemigroup.growthBound` depends on the semigroup only
through the real numbers `‖S t‖`.

At a time where `‖S t‖ = 0` the integrand of `growthBound` is `⊥`, so the inequality is
trivial there; elsewhere `0 < ‖S t‖ ≤ ‖T t‖` forces `‖T t‖ ≠ 0` as well, and
`Real.log_le_log` together with `0 ≤ t⁻¹` — valid eventually along `atTop` — gives the
pointwise comparison of the two integrands.
-/
theorem growthBound_mono_of_norm_le {S : StronglyContinuousSemigroup X}
    {T : StronglyContinuousSemigroup Y}
    (h : ∀ t : NNReal, ‖S.operator t‖ ≤ ‖T.operator t‖) :
    S.growthBound ≤ T.growthBound := by
  refine Filter.limsup_le_limsup ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  by_cases hzero : ‖S.operator (Real.toNNReal t)‖ = 0
  · rw [ite_eq_left hzero]
    exact bot_le
  have hS : 0 < ‖S.operator (Real.toNNReal t)‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  have hT : 0 < ‖T.operator (Real.toNNReal t)‖ :=
    lt_of_lt_of_le hS (h (Real.toNNReal t))
  rw [ite_eq_right hzero, ite_eq_right (ne_of_gt hT), EReal.coe_le_coe_iff]
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hS (h (Real.toNNReal t)))
    (inv_pos.mpr ht).le

/-!
## Restriction to an invariant submodule
-/

/--
The restriction of a strongly continuous semigroup to a submodule `W` that every
evolution operator maps into itself.

The evolution operator at time `t` is `(S t).comp W.subtypeL` corestricted to `W`, i.e.
the ambient operator read as a map `W → W`; the semigroup laws are
`FastDynamo.StronglyContinuousSemigroup.apply_zero` and `apply_add` applied to the
ambient vector, and strong continuity is the ambient strong continuity followed by
`Continuous.subtype_mk`.

The construction needs no topological hypothesis on `W`: `W` carries the subspace norm
whatever it is, and completeness of `W` — which *does* need closedness — is nowhere used
here.
-/
def restrict (S : StronglyContinuousSemigroup X) (W : Submodule ℂ X)
    (hinv : ∀ (t : NNReal) (x : X), x ∈ W → S t x ∈ W) :
    StronglyContinuousSemigroup W where
  operator t := ((S t).comp W.subtypeL).codRestrict W fun x ↦ hinv t x x.2
  operator_zero' := by
    ext x
    exact S.apply_zero (x : X)
  operator_add' s t := by
    ext x
    exact S.apply_add s t (x : X)
  strong_continuous' x := Continuous.subtype_mk (S.orbit_continuous (x : X)) _

/-- The restricted evolution operator is the ambient one, read through the inclusion of
`W` into the ambient space. -/
@[simp] theorem restrict_apply (S : StronglyContinuousSemigroup X) (W : Submodule ℂ X)
    (hinv : ∀ (t : NNReal) (x : X), x ∈ W → S t x ∈ W) (t : NNReal) (x : W) :
    ((S.restrict W hinv) t x : X) = S t x :=
  rfl

/-- Restricting does not increase the operator norm: `‖S|_W t‖ ≤ ‖S t‖`.  The restricted
operator acts on the ambient vectors underlying `W`, whose norms are the ambient ones, so
this is `ContinuousLinearMap.le_opNorm` for the ambient operator. -/
theorem norm_restrict_le (S : StronglyContinuousSemigroup X) (W : Submodule ℂ X)
    (hinv : ∀ (t : NNReal) (x : X), x ∈ W → S t x ∈ W) (t : NNReal) :
    ‖(S.restrict W hinv).operator t‖ ≤ ‖S.operator t‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
  rw [show ‖(S.restrict W hinv).operator t x‖ = ‖S.operator t (x : X)‖ from rfl]
  exact (S.operator t).le_opNorm (x : X)

/-- Passing to an invariant submodule can only decrease the growth bound.  The reverse
inequality is false in general and is not claimed. -/
theorem growthBound_restrict_le (S : StronglyContinuousSemigroup X) (W : Submodule ℂ X)
    (hinv : ∀ (t : NNReal) (x : X), x ∈ W → S t x ∈ W) :
    (S.restrict W hinv).growthBound ≤ S.growthBound :=
  growthBound_mono_of_norm_le (S.norm_restrict_le W hinv)

/-!
## Transport along a surjective linear isometry
-/

/--
Transport of a strongly continuous semigroup along a surjective linear isometry
`e : X ≃ₗᵢ[ℂ] Y`, by conjugation: the evolution operator at time `t` is
`e ∘ S t ∘ e.symm`.

The semigroup laws follow from `LinearIsometryEquiv.symm_apply_apply`, which collapses
the inner pair `e.symm ∘ e` in the composition of two conjugates, and strong continuity
from continuity of `e`.
-/
def congr (S : StronglyContinuousSemigroup X) (e : X ≃ₗᵢ[ℂ] Y) :
    StronglyContinuousSemigroup Y where
  operator t :=
    (e.toLinearIsometry.toContinuousLinearMap.comp (S.operator t)).comp
      e.symm.toLinearIsometry.toContinuousLinearMap
  operator_zero' := by
    ext y
    change e (S.operator 0 (e.symm y)) = y
    rw [S.apply_zero, e.apply_symm_apply]
  operator_add' s t := by
    ext y
    change e (S.operator (s + t) (e.symm y))
      = e (S.operator s (e.symm (e (S.operator t (e.symm y)))))
    rw [e.symm_apply_apply, S.apply_add]
  strong_continuous' y :=
    e.continuous.comp (S.orbit_continuous (e.symm y))

/-- The transported evolution operator is the conjugate of the original one. -/
@[simp] theorem congr_apply (S : StronglyContinuousSemigroup X) (e : X ≃ₗᵢ[ℂ] Y)
    (t : NNReal) (y : Y) :
    (S.congr e) t y = e (S.operator t (e.symm y)) :=
  rfl

/-- Conjugating by a surjective linear isometry preserves the operator norm exactly:
`‖(S.congr e) t‖ = ‖S t‖`.  Both inequalities are
`ContinuousLinearMap.opNorm_le_bound` combined with `LinearIsometryEquiv.norm_map` for
`e` and for `e.symm`. -/
theorem norm_congr (S : StronglyContinuousSemigroup X) (e : X ≃ₗᵢ[ℂ] Y) (t : NNReal) :
    ‖(S.congr e).operator t‖ = ‖S.operator t‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_)
  · rw [show (S.congr e).operator t y = e (S.operator t (e.symm y)) from rfl, e.norm_map]
    calc ‖S.operator t (e.symm y)‖ ≤ ‖S.operator t‖ * ‖e.symm y‖ :=
          (S.operator t).le_opNorm (e.symm y)
      _ = ‖S.operator t‖ * ‖y‖ := by rw [e.symm.norm_map]
  · have hx : S.operator t x = e.symm ((S.congr e).operator t (e x)) := by
      change S.operator t x = e.symm (e (S.operator t (e.symm (e x))))
      rw [e.symm_apply_apply, e.symm_apply_apply]
    rw [hx, e.symm.norm_map]
    calc ‖(S.congr e).operator t (e x)‖ ≤ ‖(S.congr e).operator t‖ * ‖e x‖ :=
          ((S.congr e).operator t).le_opNorm (e x)
      _ = ‖(S.congr e).operator t‖ * ‖x‖ := by rw [e.norm_map]

/-- The growth bound is an isometric invariant: conjugating by a surjective linear
isometry leaves it unchanged.  The integrand of
`FastDynamo.StronglyContinuousSemigroup.growthBound` depends on the semigroup only
through its operator norms, which `norm_congr` shows are unchanged. -/
theorem growthBound_congr (S : StronglyContinuousSemigroup X) (e : X ≃ₗᵢ[ℂ] Y) :
    (S.congr e).growthBound = S.growthBound := by
  simp only [growthBound, norm_congr]

end StronglyContinuousSemigroup

end FastDynamo
