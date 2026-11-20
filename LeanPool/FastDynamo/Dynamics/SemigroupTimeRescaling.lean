/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.GrowthBound

/-!
# Time rescaling of a strongly continuous semigroup

For a `C₀`-semigroup `S` and a positive real `c`, the curve `t ↦ S(c t)` is again a
`C₀`-semigroup.  This module records the three facts about it that the normalisation of the
velocity in Remark 1.6 of the paper (the remark after `rem:scope-intro`) needs:

* `StronglyContinuousSemigroup.timeRescale` — the rescaled semigroup `t ↦ S(c t)`;
* `StronglyContinuousSemigroup.growthBound_timeRescale` — its growth bound is `c` times that
  of `S`: the integrand `t⁻¹ log ‖S(c t)‖` is `c` times the integrand of `S` read at time
  `c t`, and `t ↦ c t` maps `atTop` onto itself;
* `DomainOperatorSemigroupRealization.timeRescale` — if `S` realizes a domain operator `A`,
  then `t ↦ S(c t)` realizes the operator `c A` with the same domain: the domain orbit is
  run at time `c t`, and the chain rule multiplies the derivative by `c`.

With the uniqueness of the realizing semigroup
(`StronglyContinuousSemigroup.eq_of_realization`) the last item identifies the semigroup of
`c A` with the time-rescaled semigroup of `A`; that is how `γ(uNorm, ε) = M⁻¹ γ(u, M ε)` is proved
in `FastDynamo/Dynamics/Assembly/NormalizedGrowthRate.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter

universe u v

namespace StronglyContinuousSemigroup

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The time-rescaled semigroup `t ↦ S(c t)` of a `C₀`-semigroup `S`, for a nonnegative real
`c`. -/
def timeRescale (S : StronglyContinuousSemigroup X) (c : NNReal) :
    StronglyContinuousSemigroup X where
  operator t := S (c * t)
  operator_zero' := by rw [mul_zero, S.operator_zero]
  operator_add' s t := by rw [mul_add, S.operator_add]
  strong_continuous' x := (S.orbit_continuous x).comp (continuous_const.mul continuous_id)

/-- The time-rescaled evolution operator at time `t` is the original one at time `c t`.  This
is definitional. -/
theorem timeRescale_operator (S : StronglyContinuousSemigroup X) (c t : NNReal) :
    (S.timeRescale c).operator t = S.operator (c * t) :=
  rfl

/-- **The growth bound under time rescaling.**  For `c > 0` the growth bound of
`t ↦ S(c t)` is `c` times the growth bound of `S`.

For `t > 0` the integrand of `growthBound` at time `t` is `c` times the integrand of `S` at time
`c t` (the `⊥` branch included, `c · ⊥ = ⊥`), multiplication by the finite positive constant `c`
commutes with `limsup` in `EReal`, and `t ↦ c t` maps the filter `atTop` onto itself. -/
theorem growthBound_timeRescale (S : StronglyContinuousSemigroup X) {c : NNReal}
    (hc : 0 < c) :
    (S.timeRescale c).growthBound = ((c : ℝ) : EReal) * S.growthBound := by
  have hc' : (0 : ℝ) < c := hc
  set f : ℝ → EReal := fun t ↦ if ‖S.operator (Real.toNNReal t)‖ = 0 then (⊥ : EReal)
    else ((t⁻¹ * Real.log ‖S.operator (Real.toNNReal t)‖ : ℝ) : EReal) with hf
  have hev : (fun t : ℝ ↦ if ‖(S.timeRescale c).operator (Real.toNNReal t)‖ = 0 then
        (⊥ : EReal) else
        ((t⁻¹ * Real.log ‖(S.timeRescale c).operator (Real.toNNReal t)‖ : ℝ) : EReal))
      =ᶠ[atTop] fun t ↦ ((c : ℝ) : EReal) * f ((c : ℝ) * t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have htime : c * Real.toNNReal t = Real.toNNReal ((c : ℝ) * t) := by
      rw [Real.toNNReal_mul c.coe_nonneg, Real.toNNReal_coe]
    rw [timeRescale_operator, htime, hf]
    dsimp only
    split_ifs with h
    · exact (EReal.coe_mul_bot_of_pos hc').symm
    · rw [← EReal.coe_mul, EReal.coe_eq_coe_iff]
      field_simp
  have hmap : map (fun t : ℝ ↦ (c : ℝ) * t) atTop = atTop := by
    have h := map_div_atTop_eq ((c : ℝ)⁻¹) (inv_pos.2 hc')
    simpa only [div_inv_eq_mul, mul_comm] using h
  unfold growthBound
  rw [limsup_congr hev, EReal.limsup_const_mul_of_nonneg_of_ne_top
      (EReal.coe_nonneg.2 hc'.le) (EReal.coe_ne_top _)]
  congr 1
  rw [← hf]
  change limsup (f ∘ fun t : ℝ ↦ (c : ℝ) * t) atTop = limsup f atTop
  rw [limsup_comp, hmap]

end StronglyContinuousSemigroup

namespace DomainOperatorSemigroupRealization

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- **Realization under time rescaling.**  If `S` realizes the domain operator `A`, and `A'`
has the same embedding and the action `A'.op = c • A.op`, then the time-rescaled semigroup
`t ↦ S(c t)` realizes `A'`.  The domain orbit of `A'` is that of `A` run at time `c t`; it
solves the equation of `A'` by the chain rule, `t ↦ c t` mapping `[0, ∞)` into itself. -/
def timeRescale {S : StronglyContinuousSemigroup X} {A A' : DomainOperator X D}
    (R : DomainOperatorSemigroupRealization S A) (c : NNReal)
    (hemb : A'.embedding = A.embedding) (hop : A'.op = ((c : ℝ) : ℂ) • A.op) :
    DomainOperatorSemigroupRealization (S.timeRescale c) A' where
  domainOrbit B t := R.domainOrbit B ((c : ℝ) * t)
  domainOrbit_zero B := by
    simp only [mul_zero]
    exact R.domainOrbit_zero B
  domainOrbit_isForwardStrongSolution B t ht := by
    have hct : 0 ≤ (c : ℝ) * t := mul_nonneg c.coe_nonneg ht
    have hinner : HasDerivWithinAt (fun s : ℝ ↦ (c : ℝ) * s) (c : ℝ) (Set.Ici 0) t := by
      simpa using (hasDerivWithinAt_id t (Set.Ici (0 : ℝ))).const_mul (c : ℝ)
    have hmaps : Set.MapsTo (fun s : ℝ ↦ (c : ℝ) * s) (Set.Ici 0) (Set.Ici 0) :=
      fun s hs ↦ mul_nonneg c.coe_nonneg hs
    have h := (R.domainOrbit_isForwardStrongSolution B ((c : ℝ) * t) hct).scomp t hinner hmaps
    rw [hemb, hop]
    refine h.congr_deriv ?_
    change _ = ((c : ℝ) : ℂ) • A.op _
    rw [Complex.coe_smul]
  semigroup_eq_embedding_domainOrbit B t ht := by
    have hct : 0 ≤ (c : ℝ) * t := mul_nonneg c.coe_nonneg ht
    have htime : c * Real.toNNReal t = Real.toNNReal ((c : ℝ) * t) := by
      rw [Real.toNNReal_mul c.coe_nonneg, Real.toNNReal_coe]
    rw [StronglyContinuousSemigroup.timeRescale_operator, htime, hemb]
    exact R.semigroup_eq_embedding_domainOrbit B _ hct

end DomainOperatorSemigroupRealization

end

end FastDynamo
