/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.StronglyContinuousSemigroup
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The exponential growth bound of a semigroup, and the growth floor of strong solutions

The paper defines the maximal growth rate of the induction
equation by

```
  γ(u, ε) := lim_{t → ∞} t⁻¹ · log ‖e^{t L_{ε,u}}‖_{L²_σ → L²_σ}
```

(`eq:semigroup-growth-rate`;
the limit exists there because `t ↦ log ‖e^{tL}‖` is subadditive and every
`C₀`-semigroup is locally bounded, Engel–Nagel Proposition IV.2.2).

This module contributes two things.

* `StronglyContinuousSemigroup.growthBound`, the `EReal`-valued `limsup` version
  of that quantity for an *arbitrary* `StronglyContinuousSemigroup`, together
  with the two bounds that make it usable: an upper bound from a uniform
  exponential majorant, and a lower bound from an eventual exponential
  minorant.  Combined with
  `DomainOperatorSemigroupRealization.exp_re_le_operatorNorm` this gives
  `Re λ ≤ growthBound` for every eigenpair of a realized domain operator.
  **No semigroup is constructed here**: `growthBound` is a statement about a
  given `S`.  Semigroups are constructed elsewhere: the abstract Hille–Yosida
  generation theorem is in `FastDynamo/Dynamics/HilleYosida/`, and from it
  `FastDynamo/Dynamics/Assembly/` builds `e^{t L_{ε,u}}` on the solenoidal space
  `L²_σ(T³)` — the all-frequency semigroup `productInductionSemigroup`, its solenoidal
  restriction `solenoidalInductionSemigroup`, and the isometric transport
  `literalInductionSemigroup` whose growth bound is `FastDynamo.gamma`.

* `DomainOperator.strongSolutionGrowthFloor`, a quantity that requires no
  semigroup at all: the supremum, over forward strong solutions with nonzero
  initial ambient state, of the exponential growth rate of that solution.  It is
  not the paper's `γ`; see its docstring.

The `limsup` is taken in `EReal` so that it is total: no boundedness hypothesis
is needed to make the definition meaningful, and the degenerate value `⊥` is
available.

Note on the real logarithm.  `Real.log 0 = 0` in Mathlib, so the bare real
expression `t⁻¹ · log ‖S t‖` would carry a junk value on the (nilpotent)
semigroups with `S t = 0` for large `t`, and likewise on solutions that die in
finite time, for which the mathematical growth rate is `-∞`.  Both definitions
below therefore branch on the vanishing of the norm and return `⊥` there, so
they are faithful in that degenerate case and no statement needs a positivity
hypothesis to compensate for a junk value.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter

universe u v

namespace StronglyContinuousSemigroup

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

/--
The exponential growth bound of a strongly continuous semigroup: the paper's
growth rate `γ(u, ε)` (`eq:semigroup-growth-rate`), written as a `limsup` in `EReal` rather
than as a
limit, so that it is defined for every semigroup without a preliminary
subadditivity argument.

Nonnegative time is parametrised by `Real.toNNReal`, so on `t ≤ 0` the
integrand takes the irrelevant value `t⁻¹ · log ‖S 0‖`.  On a nontrivial `X`
that value is `0` because `log ‖S 0‖ = log 1 = 0`; the factor `0⁻¹ = 0`
settles only the single time `t = 0`.  On a trivial `X` one has
`‖S 0‖ = ‖id‖ = 0` and the `⊥` branch below is taken there instead.  Either
way only the behaviour along `atTop` enters the `limsup`.

At the times where the operator norm vanishes the integrand is `⊥` rather than
the real logarithm's junk value `Real.log 0 = 0`.  The definition is therefore
faithful on the nilpotent semigroups permitted by the interface (`S t = 0` for
`t ≥ t₀`), whose growth bound is `-∞`, and the bounds below need no positivity
hypothesis.

On a Banach space this `limsup` is the paper's limit: subadditivity of
`t ↦ log ‖S t‖` (from `operator_add` and `ContinuousLinearMap.opNorm_comp_le`)
together with local boundedness (strong continuity and Banach–Steinhaus) makes the
integrand converge to `growthBound`, which is also the infimum of the integrand
over positive times (`tendsto_growthExponent`, `growthBound_eq_iInf` in
`FastDynamo/Dynamics/GrowthBoundLimit.lean`).  The bounds below are proved for the
`limsup` and need no completeness.

This is a definition about a *given* semigroup.  The development constructs one
for the fixed-sector reduced operator `A_{ε,K}`
(`FastDynamo/Dynamics/ReducedInductionHilleYosidaRay.lean`, through the generation
theorem of `FastDynamo/Dynamics/HilleYosida/`) and one for `L_{ε,u}` on
`L²_σ(T³)` (`FastDynamo/Dynamics/Assembly/`), so this definition does give the
paper's `γ(u, ε)` a Lean value: `FastDynamo.gamma`, the growth bound of
`FastDynamo.literalInductionSemigroup`.
-/
def growthBound (S : StronglyContinuousSemigroup X) : EReal :=
  Filter.limsup
    (fun t : ℝ ↦ if ‖S.operator (Real.toNNReal t)‖ = 0 then (⊥ : EReal)
      else ((t⁻¹ * Real.log ‖S.operator (Real.toNNReal t)‖ : ℝ) : EReal))
    Filter.atTop

/--
An exponential majorant `‖S t‖ ≤ C · e^{ω t}` on all of nonnegative time bounds
the growth rate: `S.growthBound ≤ ω`.  This is the elementary half of the
paper's growth-rate discussion (§1.1, around `eq:semigroup-growth-rate`).

No nonvanishing hypothesis is needed: at the times where `S t = 0` the
integrand of `growthBound` is `⊥`, which is below every majorant, so the
degenerate case is handled by the definition rather than by an assumption.
-/
theorem growthBound_le_of_norm_le (S : StronglyContinuousSemigroup X)
    {C ω : ℝ} (hC : 0 < C)
    (hbound : ∀ t : NNReal, ‖S.operator t‖ ≤ C * Real.exp (ω * (t : ℝ))) :
    S.growthBound ≤ (ω : EReal) := by
  have hmajorant : ∀ᶠ t : ℝ in Filter.atTop,
      (if ‖S.operator (Real.toNNReal t)‖ = 0 then (⊥ : EReal)
        else ((t⁻¹ * Real.log ‖S.operator (Real.toNNReal t)‖ : ℝ) : EReal)) ≤
        ((t⁻¹ * Real.log C + ω : ℝ) : EReal) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    by_cases hzero : ‖S.operator (Real.toNNReal t)‖ = 0
    · rw [ite_eq_left hzero]
      exact bot_le
    rw [ite_eq_right hzero, EReal.coe_le_coe_iff]
    have hcoe : ((Real.toNNReal t : NNReal) : ℝ) = t := Real.coe_toNNReal t ht.le
    have hb := hbound (Real.toNNReal t)
    rw [hcoe] at hb
    have hpos : 0 < ‖S.operator (Real.toNNReal t)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    have hlog : Real.log ‖S.operator (Real.toNNReal t)‖ ≤ Real.log C + ω * t := by
      have hmono := Real.log_le_log hpos hb
      rwa [Real.log_mul (ne_of_gt hC) (Real.exp_ne_zero _), Real.log_exp] at hmono
    have hscaled : t⁻¹ * Real.log ‖S.operator (Real.toNNReal t)‖ ≤
        t⁻¹ * (Real.log C + ω * t) :=
      mul_le_mul_of_nonneg_left hlog (le_of_lt (inv_pos.mpr ht))
    calc t⁻¹ * Real.log ‖S.operator (Real.toNNReal t)‖
        ≤ t⁻¹ * (Real.log C + ω * t) := hscaled
      _ = t⁻¹ * Real.log C + ω := by field_simp
  have hlimit : Filter.limsup
      (fun t : ℝ ↦ ((t⁻¹ * Real.log C + ω : ℝ) : EReal)) Filter.atTop = (ω : EReal) := by
    refine Filter.Tendsto.limsup_eq ?_
    refine EReal.tendsto_coe.2 ?_
    simpa using (tendsto_inv_atTop_zero.mul_const (Real.log C)).add_const ω
  calc S.growthBound ≤
      Filter.limsup (fun t : ℝ ↦ ((t⁻¹ * Real.log C + ω : ℝ) : EReal)) Filter.atTop :=
        Filter.limsup_le_limsup hmajorant
    _ = (ω : EReal) := hlimit

/--
An eventual exponential minorant `e^{ω t} ≤ ‖S t‖` forces `ω ≤ S.growthBound`.
This is the lower bound the paper uses for the fast-dynamo conclusion
(in its proof of `thm:main`, in the form `γ(u, ε) ≥ Re λ_ε ≥ γ₀`): only the eventual
behaviour of the operator norm along `atTop` enters.  The hypothesis forces `‖S t‖` to be
positive along `atTop`, so the `⊥` branch of the integrand is not taken there.
-/
theorem le_growthBound_of_norm_ge (S : StronglyContinuousSemigroup X) {ω : ℝ}
    (hbound : ∀ᶠ t : ℝ in Filter.atTop,
      Real.exp (ω * t) ≤ ‖S.operator (Real.toNNReal t)‖) :
    (ω : EReal) ≤ S.growthBound := by
  refine Filter.le_limsup_of_frequently_le (Filter.Eventually.frequently ?_)
  filter_upwards [hbound, Filter.eventually_gt_atTop (0 : ℝ)] with t hle ht
  have hpos : 0 < ‖S.operator (Real.toNNReal t)‖ :=
    lt_of_lt_of_le (Real.exp_pos (ω * t)) hle
  rw [ite_eq_right (ne_of_gt hpos), EReal.coe_le_coe_iff]
  have hlog : ω * t ≤ Real.log ‖S.operator (Real.toNNReal t)‖ := by
    have hmono := Real.log_le_log (Real.exp_pos (ω * t)) hle
    rwa [Real.log_exp] at hmono
  have hscaled : t⁻¹ * (ω * t) ≤ t⁻¹ * Real.log ‖S.operator (Real.toNNReal t)‖ :=
    mul_le_mul_of_nonneg_left hlog (le_of_lt (inv_pos.mpr ht))
  calc ω = t⁻¹ * (ω * t) := by field_simp
    _ ≤ t⁻¹ * Real.log ‖S.operator (Real.toNNReal t)‖ := hscaled

end StronglyContinuousSemigroup

namespace DomainOperatorSemigroupRealization

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {S : StronglyContinuousSemigroup X} {A : DomainOperator X D}

/--
Spectral lower bound for the growth bound: if the semigroup `S` realizes the
domain operator `A`, forward strong solutions of `A` are unique, and `A` has an
eigenpair `(λ, b)`, then `Re λ ≤ S.growthBound`.

This is exactly the inequality the paper uses for the fast-dynamo
conclusion, `γ(u, ε) ≥ Re λ_ε` (the proof of `thm:main`), specialised to the semigroup
interface of this development.  It is obtained from the exact exponential orbit law
`DomainOperatorSemigroupRealization.exp_re_le_operatorNorm` and
`StronglyContinuousSemigroup.le_growthBound_of_norm_ge`.

Both remaining inputs are hypotheses here: the realization `R` (semigroup
generation) and `hunique` (uniqueness of forward strong solutions).  Both are
discharged for the fixed-sector reduced operator `A_{ε,K}` in
`FastDynamo/Dynamics/ReducedInductionHilleYosidaRay.lean`, and for the all-frequency
induction operator with domain `H²` in
`FastDynamo/Dynamics/Assembly/ProductSemigroup.lean`.  For the semigroup on `L²_σ(T³)`,
the restriction of the latter, whose generator is the part of `L_{ε,u}` in `L²_σ`
(`generator_solenoidalInductionSemigroup`), the lower bound is proved from the ambient
realization by `re_le_growthBound_solenoidalInductionSemigroup_of_eigenpair`.
-/
theorem re_le_growthBound_of_eigenpair
    (R : DomainOperatorSemigroupRealization S A)
    (hunique : A.ForwardStrongSolutionsUnique)
    {eigenvalue : ℂ} {b : D} (hpair : A.IsEigenpair eigenvalue b) :
    (eigenvalue.re : EReal) ≤ S.growthBound := by
  refine S.le_growthBound_of_norm_ge ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  have hbound := R.exp_re_le_operatorNorm hunique eigenvalue b hpair (Real.toNNReal t)
  rwa [Real.coe_toNNReal t ht, mul_comm t eigenvalue.re] at hbound

end DomainOperatorSemigroupRealization

namespace DomainOperator

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/--
The growth floor of the initial-value problem for a domain operator: the
supremum, over forward strong solutions `w` of `A` with nonzero initial ambient
state, of the exponential growth rate

```
  limsup_{t → ∞} t⁻¹ · log (‖ι (w t)‖ / ‖ι (w 0)‖)
```

of that single solution, with the convention that a time at which `ι (w t)`
vanishes contributes `⊥` rather than the real logarithm's junk value
`Real.log 0 = 0`.  (Nothing in the interface forbids a forward strong solution
from dying in finite time — that is what a nilpotent semigroup does — so this
branch is needed for the definition to be faithful, exactly as in
`FastDynamo.StronglyContinuousSemigroup.growthBound`.)  The supremum is taken
*outside* the `limsup`, i.e. this is a supremum of limsups; it is therefore at
most the limsup of the suprema, so a lower bound proved for it is the stronger
of the two statements.  When no such solution exists the supremum is `⊥`.

**This is not the paper's `γ(u, ε)`.**  The paper's growth rate
(`eq:semigroup-growth-rate`) is the growth bound of the operator norm of the semigroup
`e^{t L_{ε,u}}` on `L²_σ`, a supremum over *all* `L²` initial data taken inside the norm, whereas
`strongSolutionGrowthFloor` ranges only over data in the operator's domain and
only over curves that happen to solve the equation.  The two coincide only once
a strongly continuous semigroup realizing `A` with locally bounded operator norm
exists — the semigroup-generation problem, which this module does not touch (it is
solved in `FastDynamo/Dynamics/HilleYosida/` and `FastDynamo/Dynamics/Assembly/`, where the
semigroup on `L²_σ` generated by `L_{ε,u}` is constructed).  Given such a semigroup `S`, the
inequality `strongSolutionGrowthFloor ≤ S.growthBound` comes from
`ContinuousLinearMap.le_opNorm` and the reverse from density of the domain
together with the local bound; neither direction is proved here.

The value is meaningful as it stands: it is the exponential growth rate of the
initial-value problem for `A` on its domain, and
`re_le_strongSolutionGrowthFloor_of_eigenpair` bounds it below by the real part
of any eigenvalue, with no semigroup and no uniqueness hypothesis.
-/
def strongSolutionGrowthFloor (A : DomainOperator X D) : EReal :=
  ⨆ w : {w : ℝ → D // A.IsForwardStrongSolution w ∧ A.embedding (w 0) ≠ 0},
    Filter.limsup
      (fun t : ℝ ↦ if ‖A.embedding (w.1 t)‖ = 0 then (⊥ : EReal)
        else ((t⁻¹ *
          Real.log (‖A.embedding (w.1 t)‖ / ‖A.embedding (w.1 0)‖) : ℝ) : EReal))
      Filter.atTop

/--
A uniform exponential majorant along *every* forward strong solution bounds the
growth floor from above: if `‖ι (w t)‖ ≤ e^{M t} ‖ι (w 0)‖` for every forward
strong solution `w` of `A` and every `t ≥ 0`, then
`A.strongSolutionGrowthFloor ≤ M`.

This is the companion of `le_strongSolutionGrowthFloor_of_eventually_exp_le`, and
it is what rules out the degenerate value `⊤`: together with a lower bound it
sandwiches the growth floor between two real numbers, so the definition is
demonstrably non-degenerate.  For the reduced fixed-sector induction operator the
hypothesis is the a priori energy estimate
`FastDynamo.reducedInductionOperator_norm_embedding_le_exp`, with
`M = ‖transverseStretchingCoefficient u‖`; that instance and the resulting
sandwich are in `FastDynamo/Dynamics/MainGrowthFloor.lean`.

No nonvanishing hypothesis is needed: at the times where `ι (w t)` vanishes the
integrand of `strongSolutionGrowthFloor` is `⊥`, which is below every majorant.
-/
theorem strongSolutionGrowthFloor_le_of_norm_le (A : DomainOperator X D) {M : ℝ}
    (hbound : ∀ w : ℝ → D, A.IsForwardStrongSolution w → ∀ t : ℝ, 0 ≤ t →
      ‖A.embedding (w t)‖ ≤ Real.exp (M * t) * ‖A.embedding (w 0)‖) :
    A.strongSolutionGrowthFloor ≤ (M : EReal) := by
  refine iSup_le ?_
  rintro ⟨w, hw, hw0⟩
  refine Filter.limsup_le_of_le Filter.isCobounded_le_of_bot ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  by_cases hzero : ‖A.embedding (w t)‖ = 0
  · rw [ite_eq_left hzero]
    exact bot_le
  rw [ite_eq_right hzero, EReal.coe_le_coe_iff]
  have hn0 : 0 < ‖A.embedding (w 0)‖ := norm_pos_iff.mpr hw0
  have hratio : ‖A.embedding (w t)‖ / ‖A.embedding (w 0)‖ ≤ Real.exp (M * t) :=
    (div_le_iff₀ hn0).2 (hbound w hw t ht.le)
  have hpos : 0 < ‖A.embedding (w t)‖ / ‖A.embedding (w 0)‖ :=
    div_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)) hn0
  have hlog : Real.log (‖A.embedding (w t)‖ / ‖A.embedding (w 0)‖) ≤ M * t := by
    have hmono := Real.log_le_log hpos hratio
    rwa [Real.log_exp] at hmono
  calc t⁻¹ * Real.log (‖A.embedding (w t)‖ / ‖A.embedding (w 0)‖)
      ≤ t⁻¹ * (M * t) := mul_le_mul_of_nonneg_left hlog (inv_pos.mpr ht).le
    _ = M := by field_simp

/--
A single forward strong solution that eventually grows at least like `e^{g t}`
relative to its initial ambient state bounds the growth floor from below by `g`.

The growth hypothesis makes `‖ι (w t)‖` positive along `atTop`, so the `⊥`
branch of the integrand of `strongSolutionGrowthFloor` is not taken there.
-/
theorem le_strongSolutionGrowthFloor_of_eventually_exp_le
    (A : DomainOperator X D) {w : ℝ → D} {g : ℝ}
    (hw : A.IsForwardStrongSolution w) (hw0 : A.embedding (w 0) ≠ 0)
    (hgrowth : ∀ᶠ t : ℝ in Filter.atTop,
      Real.exp (g * t) * ‖A.embedding (w 0)‖ ≤ ‖A.embedding (w t)‖) :
    (g : EReal) ≤ A.strongSolutionGrowthFloor := by
  have hnorm0 : 0 < ‖A.embedding (w 0)‖ := norm_pos_iff.mpr hw0
  have key : (g : EReal) ≤ Filter.limsup
      (fun t : ℝ ↦ if ‖A.embedding (w t)‖ = 0 then (⊥ : EReal)
        else ((t⁻¹ *
          Real.log (‖A.embedding (w t)‖ / ‖A.embedding (w 0)‖) : ℝ) : EReal))
      Filter.atTop := by
    refine Filter.le_limsup_of_frequently_le (Filter.Eventually.frequently ?_)
    filter_upwards [hgrowth, Filter.eventually_gt_atTop (0 : ℝ)] with t hle ht
    have hpos : 0 < ‖A.embedding (w t)‖ :=
      lt_of_lt_of_le (mul_pos (Real.exp_pos (g * t)) hnorm0) hle
    rw [ite_eq_right (ne_of_gt hpos), EReal.coe_le_coe_iff]
    have hratio : Real.exp (g * t) ≤ ‖A.embedding (w t)‖ / ‖A.embedding (w 0)‖ :=
      (le_div_iff₀ hnorm0).2 hle
    have hlog : g * t ≤ Real.log (‖A.embedding (w t)‖ / ‖A.embedding (w 0)‖) := by
      have hmono := Real.log_le_log (Real.exp_pos (g * t)) hratio
      rwa [Real.log_exp] at hmono
    have hscaled := mul_le_mul_of_nonneg_left hlog (le_of_lt (inv_pos.mpr ht))
    calc g = t⁻¹ * (g * t) := by field_simp
      _ ≤ t⁻¹ * Real.log (‖A.embedding (w t)‖ / ‖A.embedding (w 0)‖) := hscaled
  refine le_trans ?_ (le_iSup (α := EReal) _ (⟨w, hw, hw0⟩ :
    {w : ℝ → D // A.IsForwardStrongSolution w ∧ A.embedding (w 0) ≠ 0}))
  exact key

/--
Every eigenpair of `A` bounds the growth floor of the initial-value problem from
below by the real part of its eigenvalue: `Re λ ≤ A.strongSolutionGrowthFloor`.

The witness is the explicit exponential eigen-trajectory
`A.eigenTrajectory λ b`, which is a forward strong solution
(`FastDynamo.DomainOperator.isForwardStrongSolution_eigenTrajectory`) and obeys
the exact norm law `‖ι (e^{tλ} b)‖ = e^{t Re λ} ‖ι b‖`
(`FastDynamo.DomainOperator.norm_embedding_eigenTrajectory`).  Nonvanishing of
`A.embedding b` is part of `DomainOperator.IsEigenpair`.

Unlike `FastDynamo.DomainOperatorSemigroupRealization.re_le_growthBound_of_eigenpair`,
this statement has no hypothesis: no semigroup, no realization and no uniqueness
of forward strong solutions is assumed.  It is, correspondingly, a statement
about the growth floor and not about the paper's `γ(u, ε)`.
-/
theorem re_le_strongSolutionGrowthFloor_of_eigenpair
    (A : DomainOperator X D) {eigenvalue : ℂ} {b : D}
    (hpair : A.IsEigenpair eigenvalue b) :
    (eigenvalue.re : EReal) ≤ A.strongSolutionGrowthFloor := by
  refine A.le_strongSolutionGrowthFloor_of_eventually_exp_le
    (A.isForwardStrongSolution_eigenTrajectory eigenvalue b hpair) ?_ ?_
  · rw [A.eigenTrajectory_zero]
    exact hpair.1
  · filter_upwards with t
    rw [A.eigenTrajectory_zero, A.norm_embedding_eigenTrajectory,
      mul_comm eigenvalue.re t]

end DomainOperator

/-! ## A scalar sanity check

`DomainOperatorSemigroupRealization.re_le_growthBound_of_eigenpair` is conditional
on a realization together with uniqueness of forward strong solutions, and this
module constructs no such data for any induction operator.  The
scalar semigroup `t ↦ e^{tλ}` on `X = D = ℂ`, with generator `λ · id`, carries all
of it, so those hypotheses are jointly satisfiable and the conditional statements
above are not vacuous.  Nothing here
says anything about `L_{ε,u}`: the scalar generator is bounded, and the
generation problem for `L_{ε,u}` on `L²_σ(T³)` is not addressed here (see
`FastDynamo/Dynamics/Assembly/`).
-/

/-- The scalar semigroup `t ↦ e^{tλ}` on `ℂ`, acting by multiplication. -/
def scalarSemigroup (lam : ℂ) : StronglyContinuousSemigroup ℂ where
  operator t := (Complex.exp ((t : ℝ) * lam)) • ContinuousLinearMap.id ℂ ℂ
  operator_zero' := by simp
  operator_add' := by
    intro s t
    ext
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, NNReal.coe_add, Complex.ofReal_add]
    rw [add_mul, Complex.exp_add, mul_assoc]
  strong_continuous' := by
    intro x
    have hc : Continuous fun t : NNReal ↦ Complex.exp ((t : ℝ) * lam) :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp NNReal.continuous_coe).mul continuous_const)
    exact hc.smul continuous_const

/-- The generator `λ · id` of `scalarSemigroup lam`, as a domain operator whose
domain is all of `ℂ` and whose embedding is the identity. -/
def scalarOperator (lam : ℂ) : DomainOperator ℂ ℂ where
  embedding := ContinuousLinearMap.id ℂ ℂ
  embedding_injective := fun _ _ h ↦ h
  op := lam • ContinuousLinearMap.id ℂ ℂ

/-- `(λ, 1)` is an eigenpair of the scalar generator. -/
theorem scalarOperator_isEigenpair (lam : ℂ) :
    (scalarOperator lam).IsEigenpair lam 1 :=
  ⟨by simp [scalarOperator], by simp [scalarOperator]⟩

/-- Forward strong solutions of the scalar generator are unique.  The exponential
multiplier `e^{-tλ}` turns the difference of two solutions into a curve with
vanishing right derivative on `[0, ∞)`, hence into a constant. -/
theorem scalarOperator_forwardStrongSolutionsUnique (lam : ℂ) :
    (scalarOperator lam).ForwardStrongSolutionsUnique := by
  intro w₁ w₂ h₁ h₂ hinit t ht
  have hd : ∀ w : ℝ → ℂ, (scalarOperator lam).IsForwardStrongSolution w →
      ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt w (lam * w s) (Set.Ici s) s := by
    intro w hw s hs
    have h0 : HasDerivWithinAt w (lam * w s) (Set.Ici 0) s := by
      simpa [scalarOperator] using hw s hs
    rcases eq_or_lt_of_le hs with rfl | hpos
    · exact h0
    · exact (h0.hasDerivAt (Ici_mem_nhds hpos)).hasDerivWithinAt
  have hc : ∀ w : ℝ → ℂ, (scalarOperator lam).IsForwardStrongSolution w →
      ContinuousOn w (Set.Ici 0) := fun w hw s hs ↦ by
    simpa [scalarOperator] using (hw s hs).continuousWithinAt
  have key : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt
      (fun r : ℝ ↦ Complex.exp (-lam * r) * (w₁ r - w₂ r)) 0 (Set.Ici s) s := by
    intro s hs
    have hdiff : HasDerivWithinAt (fun r : ℝ ↦ w₁ r - w₂ r)
        (lam * (w₁ s - w₂ s)) (Set.Ici s) s := by
      have hsub := (hd w₁ h₁ s hs).sub (hd w₂ h₂ s hs)
      rwa [← mul_sub] at hsub
    have hexp : HasDerivAt (fun r : ℝ ↦ Complex.exp (-lam * r))
        (Complex.exp (-lam * s) * -lam) s := by
      have hlin : HasDerivAt (fun r : ℝ ↦ -lam * (r : ℂ)) (-lam) s := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (-lam)
      simpa using hlin.cexp
    have heq : (0 : ℂ) = Complex.exp (-lam * s) * -lam * (w₁ s - w₂ s) +
        Complex.exp (-lam * s) * (lam * (w₁ s - w₂ s)) := by ring
    rw [heq]
    exact (hexp.hasDerivWithinAt (s := Set.Ici s)).mul hdiff
  have hcont : ContinuousOn (fun r : ℝ ↦ Complex.exp (-lam * r) * (w₁ r - w₂ r))
      (Set.Icc 0 t) :=
    ((Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).continuousOn).mul
      (((hc w₁ h₁).sub (hc w₂ h₂)).mono Set.Icc_subset_Ici_self)
  have hconst := constant_of_has_deriv_right_zero hcont (fun s hs ↦ key s hs.1) t
    (Set.right_mem_Icc.2 ht)
  have hzero : w₁ 0 - w₂ 0 = 0 :=
    sub_eq_zero.2 (by simpa [scalarOperator] using hinit)
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, hzero,
    mul_eq_zero] at hconst
  simpa [scalarOperator] using
    sub_eq_zero.1 (hconst.resolve_left (Complex.exp_ne_zero _))

/-- The scalar semigroup realizes its own generator: the eigen-trajectory of the
datum `B` is the domain-valued orbit. -/
def scalarRealization (lam : ℂ) :
    DomainOperatorSemigroupRealization (scalarSemigroup lam) (scalarOperator lam) where
  domainOrbit B t := (scalarOperator lam).eigenTrajectory lam B t
  domainOrbit_zero B := by simp
  domainOrbit_isForwardStrongSolution B := fun t _ht ↦
    (DomainOperator.hasDerivAt_embedding_eigenTrajectory (scalarOperator lam) lam B
      t).hasDerivWithinAt
  semigroup_eq_embedding_domainOrbit B t ht := by
    change (Complex.exp (((Real.toNNReal t : NNReal) : ℝ) * lam)) • B
      = Complex.exp ((t : ℂ) * lam) • B
    rw [Real.coe_toNNReal t ht]

/-- Non-vacuity: realization, forward uniqueness and an eigenpair hold
simultaneously, so `re_le_growthBound_of_eigenpair` is a conditional statement
with satisfiable hypotheses. -/
example (lam : ℂ) : (lam.re : EReal) ≤ (scalarSemigroup lam).growthBound :=
  (scalarRealization lam).re_le_growthBound_of_eigenpair
    (scalarOperator_forwardStrongSolutionsUnique lam) (scalarOperator_isEigenpair lam)

end

end FastDynamo
