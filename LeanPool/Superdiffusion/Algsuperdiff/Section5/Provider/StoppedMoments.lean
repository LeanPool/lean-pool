/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.StoppedDirichletHarmonic

/-!
# StoppedMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The stopped mean and the stopped second moment

Fix a conservative Feller process with continuous paths, an open set `U`, a deterministic
horizon `t`, and a starting point `x` of `U`.  Write `theta` for the stopped time
`exitTimeTrunc U t`, so that the stopped position is `omega theta`.

Two observables are treated, and both are treated in the same way: an observable compared with
a function reproduced by the exit distribution of `U`.

* **The stopped mean.**  If `u` is reproduced by the exit distribution of `U`, if
  `|b - u| <= K` everywhere and `b x = 0`, then
    `|E_x[b(X_theta)]| <= 2K` .
  The two summands are the value `u x`, which is within `K` of `b x = 0`, and the expectation
  of `b - u`, which is within `K` because the law is a probability measure.

* **The stopped second moment.**  If `u = h - sigma * w` with `h` reproduced by the exit
  distribution and `w` the expected exit time, if `|q - u| <= K` everywhere and `q x = 0`, then
    `|E_x[q(X_theta)] - sigma * t| <= 2K + sigma * t * P_x[tau <= t]` .
  The second identity of the stopped-Dirichlet file turns `E_x[u(X_theta)]` into
  `u x + sigma E_x[theta]`, and the expected stopped time is the horizon less a shortfall
  supported on the event that the exit has already occurred.

The two conclusions are the displays `e.displacement.squared.stopped` and
`e.second.moment.stopped` of the source, in one direction each: there `b` is a linear function,
`q` a quadratic one, `sigma` is twice the effective diffusivity at the scale of the cube, and
`K` is the uniform distance between the heterogeneous solution and its homogenized counterpart.
Summing over a family of observables is the last section; it produces the displacement bound
and the second moment of the whole displacement vector, with leading term `n * sigma * t` over
`n` directions.

Nothing here refers to a generator, to a coefficient field, or to a cube.  The two inputs that
carry the analytic content are `HasExitMeanValueOn` — the mean-value property of the
observable, supplied by the exit mean-value interface — and the uniform bound `K`, supplied by
the renormalization of the generator.

## Main results

* `ae_eval_exitTimeTrunc_mem_closure` — the stopped position lies in the closure of `U`.
* `integral_eval_exitTimeTrunc_congr_of_eqOn_closure` — only the values on the closure matter.
* `abs_integral_eval_exitTimeTrunc_le_of_hasExitMeanValueOn` — the stopped mean.
* `abs_integral_eval_exitTimeTrunc_sub_mul_le_of_hasExitMeanValueOn` — the stopped second
  moment.
* `abs_integral_sum_eval_exitTimeTrunc_sub_le` — the sum over a family of directions.

## References

* ABK26, Steps 1 and 3 of the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Provider

open MeasureTheory
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open DivergenceFormProcess.StoppedDirichlet
open scoped ENNReal NNReal

noncomputable section

/-! ## 1. Two elementary bounds -/

/-- The absolute value of the expectation of a uniformly bounded observable, under a
probability measure. -/
private theorem abs_integral_le_of_forall_abs_le {Omega : Type*} [MeasurableSpace Omega]
    (nu : Measure Omega) [IsProbabilityMeasure nu] {f : Omega → ℝ} {C : ℝ}
    (hf : ∀ omega, |f omega| ≤ C) :
    |∫ omega, f omega ∂nu| ≤ C := by
  have hbound := norm_integral_le_of_norm_le_const (μ := nu) (f := f) (C := C)
    (Filter.Eventually.of_forall fun omega ↦ by simpa only [Real.norm_eq_abs] using hf omega)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hbound

/-! ## 2. The stopped position -/

section Path

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- The composition of a Borel function with the stopped position is Borel. -/
theorem measurable_eval_exitTimeTrunc {U : Set alpha} (hU : IsOpen U) (t : NNReal)
    {f : alpha → ℝ} (hf : Measurable f) :
    Measurable fun omega : ContinuousPath alpha ↦
      f (omega (ContinuousPath.exitTimeTrunc U t omega)) :=
  hf.comp (ContinuousPath.measurable_eval_stoppingTime_borel _
    (ContinuousPath.isStoppingTime_exitTimeTrunc U hU t))

end Path

section Process

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- A bounded Borel observable of the stopped position is integrable. -/
theorem integrable_eval_exitTimeTrunc {U : Set alpha} (hU : IsOpen U) (t : NNReal)
    {f : alpha → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) (x : alpha) :
    Integrable (fun omega ↦ f (omega (ContinuousPath.exitTimeTrunc U t omega)))
      (IsConservative.continuousProcess P hP x) :=
  Integrable.of_bound
    ((measurable_eval_exitTimeTrunc hU t hf).stronglyMeasurable).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun _ ↦ by simpa only [Real.norm_eq_abs] using hC _)

/-- **The stopped position lies in the closure of the domain.**  Almost every path of the
process started inside `U` starts inside `U`, and a continuous path started inside `U` is in
the closure of `U` at the time at which it either leaves `U` or reaches the horizon. -/
theorem ae_eval_exitTimeTrunc_mem_closure (hK : P.KolmogorovRegular hP) {U : Set alpha}
    (hU : IsOpen U) (t : NNReal) {x : alpha} (hx : x ∈ U) :
    ∀ᵐ omega ∂(IsConservative.continuousProcess P hP x),
      omega (ContinuousPath.exitTimeTrunc U t omega) ∈ closure U := by
  filter_upwards [IsConservative.ae_eval_zero_eq hP hK x] with omega homega
  refine ContinuousPath.stopped_exitTimeTrunc_mem_closure U hU t omega ?_
  rw [homega]
  exact hx

/-- **Only the values on the closure matter.**  Two observables agreeing on the closure of `U`
have the same expectation at the stopped position. -/
theorem integral_eval_exitTimeTrunc_congr_of_eqOn_closure (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) {f g : alpha → ℝ} (hfg : Set.EqOn f g (closure U))
    (t : NNReal) {x : alpha} (hx : x ∈ U) :
    (∫ omega, f (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x)) =
      ∫ omega, g (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x) := by
  refine integral_congr_ae ?_
  filter_upwards [ae_eval_exitTimeTrunc_mem_closure P hP hK hU t hx] with omega homega
  exact hfg homega

/-! ## 3. The shortfall of the stopped time against the horizon -/

/-- The shortfall of the stopped time against the horizon is nonnegative. -/
theorem integral_shortfall_nonneg {U : Set alpha} (t : NNReal) (x : alpha) :
    0 ≤ ∫ omega, Set.indicator (survivalEvent U t)ᶜ
      (fun omega ↦ (t : ℝ) - (ContinuousPath.exitTime U omega).toReal) omega
      ∂(IsConservative.continuousProcess P hP x) := by
  refine integral_nonneg fun omega ↦ Set.indicator_apply_nonneg fun homega ↦ ?_
  have hle : ContinuousPath.exitTime U omega ≤ (t : ℝ≥0∞) := not_lt.mp homega
  have hreal : (ContinuousPath.exitTime U omega).toReal ≤ (t : ℝ) := by
    simpa [ENNReal.coe_toReal] using ENNReal.toReal_mono ENNReal.coe_ne_top hle
  linarith only [hreal]

/-- The shortfall of the stopped time against the horizon is at most the horizon times the
probability that the exit has already occurred. -/
theorem integral_shortfall_le {U : Set alpha} (hU : IsOpen U) (t : NNReal) (x : alpha) :
    (∫ omega, Set.indicator (survivalEvent U t)ᶜ
        (fun omega ↦ (t : ℝ) - (ContinuousPath.exitTime U omega).toReal) omega
        ∂(IsConservative.continuousProcess P hP x)) ≤
      (t : ℝ) * (IsConservative.continuousProcess P hP x (survivalEvent U t)ᶜ).toReal := by
  have hSmeas := measurableSet_survivalEvent (alpha := alpha) hU t
  have hgmeas : Measurable fun omega : ContinuousPath alpha ↦
      Set.indicator (survivalEvent U t)ᶜ
        (fun omega ↦ (t : ℝ) - (ContinuousPath.exitTime U omega).toReal) omega :=
    (measurable_const.sub
      (ENNReal.measurable_toReal.comp (ContinuousPath.measurable_exitTime U hU))).indicator
      hSmeas.compl
  have hpt : ∀ omega : ContinuousPath alpha,
      Set.indicator (survivalEvent U t)ᶜ
          (fun omega ↦ (t : ℝ) - (ContinuousPath.exitTime U omega).toReal) omega ≤
        Set.indicator (survivalEvent U t)ᶜ (fun _ ↦ (t : ℝ)) omega := by
    intro omega
    by_cases homega : omega ∈ (survivalEvent U t)ᶜ
    · rw [Set.indicator_of_mem homega, Set.indicator_of_mem homega]
      have hnn : (0 : ℝ) ≤ (ContinuousPath.exitTime U omega).toReal := ENNReal.toReal_nonneg
      linarith only [hnn]
    · rw [Set.indicator_of_notMem homega, Set.indicator_of_notMem homega]
  have hgint : Integrable (fun omega : ContinuousPath alpha ↦
      Set.indicator (survivalEvent U t)ᶜ
        (fun omega ↦ (t : ℝ) - (ContinuousPath.exitTime U omega).toReal) omega)
      (IsConservative.continuousProcess P hP x) := by
    refine Integrable.of_bound hgmeas.stronglyMeasurable.aestronglyMeasurable (t : ℝ)
      (Filter.Eventually.of_forall fun omega ↦ ?_)
    by_cases homega : omega ∈ (survivalEvent U t)ᶜ
    · have hle : ContinuousPath.exitTime U omega ≤ (t : ℝ≥0∞) := not_lt.mp homega
      have hreal : (ContinuousPath.exitTime U omega).toReal ≤ (t : ℝ) := by
        simpa [ENNReal.coe_toReal] using ENNReal.toReal_mono ENNReal.coe_ne_top hle
      have hnn : (0 : ℝ) ≤ (ContinuousPath.exitTime U omega).toReal := ENNReal.toReal_nonneg
      rw [Set.indicator_of_mem homega, Real.norm_of_nonneg (by linarith only [hreal])]
      linarith only [hnn]
    · rw [Set.indicator_of_notMem homega, norm_zero]
      exact NNReal.zero_le_coe
  have hconstint : Integrable (fun omega : ContinuousPath alpha ↦
      Set.indicator (survivalEvent U t)ᶜ (fun _ ↦ (t : ℝ)) omega)
      (IsConservative.continuousProcess P hP x) :=
    (integrable_const (t : ℝ)).indicator hSmeas.compl
  calc (∫ omega, Set.indicator (survivalEvent U t)ᶜ
          (fun omega ↦ (t : ℝ) - (ContinuousPath.exitTime U omega).toReal) omega
          ∂(IsConservative.continuousProcess P hP x))
      ≤ ∫ omega, Set.indicator (survivalEvent U t)ᶜ (fun _ ↦ (t : ℝ)) omega
          ∂(IsConservative.continuousProcess P hP x) := integral_mono hgint hconstint hpt
    _ = (IsConservative.continuousProcess P hP x (survivalEvent U t)ᶜ).toReal • (t : ℝ) :=
        integral_indicator_const (t : ℝ) hSmeas.compl
    _ = (t : ℝ) * (IsConservative.continuousProcess P hP x (survivalEvent U t)ᶜ).toReal := by
        rw [smul_eq_mul]
        ring

/-! ## 4. Summing over a family of directions -/

/-- **The second moment of the whole displacement.**  If a finite family of observables adds up
on the closure of `U` to a single observable `N`, and each member is within `B` of `sigma * t`
at the stopped position, then `N` is within `n * B` of `n * sigma * t` there.

With `N` the squared norm and `sigma` twice the effective diffusivity, the leading term is
`n * sigma * t`, the source's `2 d shom_m t` over the `d` coordinate directions. -/
theorem abs_integral_sum_eval_exitTimeTrunc_sub_le (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) {n : ℕ} (Q : Fin n → alpha → ℝ) (N : alpha → ℝ)
    (hN : Set.EqOn N (fun y ↦ ∑ i, Q i y) (closure U))
    (hQmeas : ∀ i, Measurable (Q i)) {CQ : ℝ} (hCQ : ∀ i y, |Q i y| ≤ CQ)
    (t : NNReal) {x : alpha} (hx : x ∈ U) {sigma B : ℝ}
    (hQ : ∀ i, |(∫ omega, Q i (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x)) - sigma * (t : ℝ)| ≤ B) :
    |(∫ omega, N (omega (ContinuousPath.exitTimeTrunc U t omega))
          ∂(IsConservative.continuousProcess P hP x)) - (n : ℝ) * (sigma * (t : ℝ))| ≤
      (n : ℝ) * B := by
  have hswap : (∫ omega, N (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x)) =
      ∑ i, ∫ omega, Q i (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x) := by
    rw [integral_eval_exitTimeTrunc_congr_of_eqOn_closure P hP hK hU hN t hx]
    exact integral_finsetSum Finset.univ
      fun i _ ↦ integrable_eval_exitTimeTrunc P hP hU t (hQmeas i) (hCQ i) x
  have hshape : (∫ omega, N (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x)) - (n : ℝ) * (sigma * (t : ℝ)) =
      ∑ i, ((∫ omega, Q i (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x)) - sigma * (t : ℝ)) := by
    rw [hswap, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [hshape]
  calc |∑ i, ((∫ omega, Q i (omega (ContinuousPath.exitTimeTrunc U t omega))
          ∂(IsConservative.continuousProcess P hP x)) - sigma * (t : ℝ))|
      ≤ ∑ i, |(∫ omega, Q i (omega (ContinuousPath.exitTimeTrunc U t omega))
          ∂(IsConservative.continuousProcess P hP x)) - sigma * (t : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ ↦ hQ i
    _ = (n : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Process

section StoppedIdentities

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-! ## 5. The stopped mean -/

/-- **The stopped mean.**  Let `u` be reproduced by the exit distribution of `U` and let `b`
be a Borel observable within `K` of `u` everywhere and vanishing at the starting point.  Then
the expectation of `b` at the stopped position is at most `2K` in absolute value.

This is the display `e.displacement.squared.stopped` of the source before squaring: `b` is the
linear function `e ⬝ x`, `u` is the heterogeneous solution taking those boundary values, and
`K` is the uniform distance between them. -/
theorem abs_integral_eval_exitTimeTrunc_le_of_hasExitMeanValueOn
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) {u b : alpha → ℝ} (hu : Measurable u)
    {Cu : ℝ} (hCu : ∀ y, |u y| ≤ Cu) (hharm : HasExitMeanValueOn P hP U u)
    (hb : Measurable b) {K : ℝ} (hKb : ∀ y, |b y - u y| ≤ K)
    (t : NNReal) {x : alpha} (hx : x ∈ U) (hb0 : b x = 0)
    (hwfin : expectedExitTime P hP U x ≠ ⊤) :
    |∫ omega, b (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x)| ≤ 2 * K := by
  have hbbound : ∀ y, |b y| ≤ K + Cu := by
    intro y
    calc |b y| = |b y - u y + u y| := by rw [show b y - u y + u y = b y by ring]
      _ ≤ |b y - u y| + |u y| := abs_add_le _ _
      _ ≤ K + Cu := add_le_add (hKb y) (hCu y)
  have huint : Integrable (fun omega ↦ u (omega (ContinuousPath.exitTimeTrunc U t omega)))
      (IsConservative.continuousProcess P hP x) :=
    integrable_eval_exitTimeTrunc P hP hU t hu hCu x
  have hbint : Integrable (fun omega ↦ b (omega (ContinuousPath.exitTimeTrunc U t omega)))
      (IsConservative.continuousProcess P hP x) :=
    integrable_eval_exitTimeTrunc P hP hU t hb hbbound x
  have hval : (∫ omega, u (omega (ContinuousPath.exitTimeTrunc U t omega))
      ∂(IsConservative.continuousProcess P hP x)) = u x :=
    integral_eval_exitTimeTrunc_eq_of_hasExitMeanValueOn P hP hFeller hK hU hu Cu
      (fun y ↦ by simpa only [Real.norm_eq_abs] using hCu y) hharm t hx hwfin
  have hsub : (∫ omega, (b (omega (ContinuousPath.exitTimeTrunc U t omega)) -
        u (omega (ContinuousPath.exitTimeTrunc U t omega)))
        ∂(IsConservative.continuousProcess P hP x)) =
      (∫ omega, b (omega (ContinuousPath.exitTimeTrunc U t omega))
          ∂(IsConservative.continuousProcess P hP x)) -
        ∫ omega, u (omega (ContinuousPath.exitTimeTrunc U t omega))
          ∂(IsConservative.continuousProcess P hP x) :=
    integral_sub hbint huint
  have hdiff : |∫ omega, (b (omega (ContinuousPath.exitTimeTrunc U t omega)) -
      u (omega (ContinuousPath.exitTimeTrunc U t omega)))
      ∂(IsConservative.continuousProcess P hP x)| ≤ K :=
    abs_integral_le_of_forall_abs_le (IsConservative.continuousProcess P hP x)
      fun omega ↦ hKb (omega (ContinuousPath.exitTimeTrunc U t omega))
  have hux : |u x| ≤ K := by
    have hzero := hKb x
    rw [hb0, zero_sub, abs_neg] at hzero
    exact hzero
  have hsplit : (∫ omega, b (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x)) =
      u x + ∫ omega, (b (omega (ContinuousPath.exitTimeTrunc U t omega)) -
        u (omega (ContinuousPath.exitTimeTrunc U t omega)))
        ∂(IsConservative.continuousProcess P hP x) := by
    rw [hsub, hval]
    ring
  calc |∫ omega, b (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x)|
      = |u x + ∫ omega, (b (omega (ContinuousPath.exitTimeTrunc U t omega)) -
          u (omega (ContinuousPath.exitTimeTrunc U t omega)))
          ∂(IsConservative.continuousProcess P hP x)| := by rw [hsplit]
    _ ≤ |u x| + |∫ omega, (b (omega (ContinuousPath.exitTimeTrunc U t omega)) -
          u (omega (ContinuousPath.exitTimeTrunc U t omega)))
          ∂(IsConservative.continuousProcess P hP x)| := abs_add_le _ _
    _ ≤ K + K := add_le_add hux hdiff
    _ = 2 * K := by ring

/-! ## 6. The stopped second moment -/

/-- **The stopped second moment.**  Let `h` be reproduced by the exit distribution of `U`, let
`u` be `h` corrected by `sigma` times the expected exit time, and let `q` be a bounded Borel
observable within `K` of `u` everywhere and vanishing at the starting point.  Then the
expectation of `q` at the stopped position is within `2K` of `sigma` times the horizon, up to
the shortfall carried by the event that the exit has already occurred.

This is the display `e.second.moment.stopped` of the source: `q` is the quadratic observable
`(e ⬝ x)^2`, `sigma` is twice the effective diffusivity at the scale of the cube, `u` is the
heterogeneous solution with that constant right-hand side and those boundary values, and `K`
is the uniform distance between `u` and `q`. -/
theorem abs_integral_eval_exitTimeTrunc_sub_mul_le_of_hasExitMeanValueOn
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) {h q u : alpha → ℝ} (hh : Measurable h)
    {Ch : ℝ} (hCh : ∀ y, |h y| ≤ Ch) (hharm : HasExitMeanValueOn P hP U h)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hu : ∀ y, u y = h y - sigma * (expectedExitTime P hP U y).toReal)
    (hq : Measurable q) {Cq : ℝ} (hCq : ∀ y, |q y| ≤ Cq)
    {K : ℝ} (hKb : ∀ y, |q y - u y| ≤ K)
    (t : NNReal) {x : alpha} (hx : x ∈ U) (hq0 : q x = 0)
    (hwfin : expectedExitTime P hP U x ≠ ⊤) :
    |(∫ omega, q (omega (ContinuousPath.exitTimeTrunc U t omega))
          ∂(IsConservative.continuousProcess P hP x)) - sigma * (t : ℝ)| ≤
      2 * K + sigma * ((t : ℝ) *
        (IsConservative.continuousProcess P hP x (survivalEvent U t)ᶜ).toReal) := by
  have hhint : Integrable (fun omega ↦ h (omega (ContinuousPath.exitTimeTrunc U t omega)))
      (IsConservative.continuousProcess P hP x) :=
    integrable_eval_exitTimeTrunc P hP hU t hh hCh x
  have hwint := integrable_expectedExitTime_eval_exitTimeTrunc P hP hFeller hK hU t hx hwfin
  have huint : Integrable (fun omega ↦ u (omega (ContinuousPath.exitTimeTrunc U t omega)))
      (IsConservative.continuousProcess P hP x) := by
    have hshape : (fun omega : ContinuousPath alpha ↦
          u (omega (ContinuousPath.exitTimeTrunc U t omega))) =
        fun omega : ContinuousPath alpha ↦ h (omega (ContinuousPath.exitTimeTrunc U t omega)) -
          sigma * (expectedExitTime P hP U
            (omega (ContinuousPath.exitTimeTrunc U t omega))).toReal := by
      funext omega
      exact hu _
    rw [hshape]
    exact hhint.sub (hwint.const_mul sigma)
  have hqint : Integrable (fun omega ↦ q (omega (ContinuousPath.exitTimeTrunc U t omega)))
      (IsConservative.continuousProcess P hP x) :=
    integrable_eval_exitTimeTrunc P hP hU t hq hCq x
  have hA2 := integral_eval_exitTimeTrunc_eq_add_of_hasExitMeanValueOn P hP hFeller hK hU hh Ch
    (fun y ↦ by simpa only [Real.norm_eq_abs] using hCh y) hharm sigma hu t hx hwfin
  have hsub : (∫ omega, (q (omega (ContinuousPath.exitTimeTrunc U t omega)) -
        u (omega (ContinuousPath.exitTimeTrunc U t omega)))
        ∂(IsConservative.continuousProcess P hP x)) =
      (∫ omega, q (omega (ContinuousPath.exitTimeTrunc U t omega))
          ∂(IsConservative.continuousProcess P hP x)) -
        ∫ omega, u (omega (ContinuousPath.exitTimeTrunc U t omega))
          ∂(IsConservative.continuousProcess P hP x) :=
    integral_sub hqint huint
  have hdiff : |∫ omega, (q (omega (ContinuousPath.exitTimeTrunc U t omega)) -
      u (omega (ContinuousPath.exitTimeTrunc U t omega)))
      ∂(IsConservative.continuousProcess P hP x)| ≤ K :=
    abs_integral_le_of_forall_abs_le (IsConservative.continuousProcess P hP x)
      fun omega ↦ hKb (omega (ContinuousPath.exitTimeTrunc U t omega))
  have hux : |u x| ≤ K := by
    have hzero := hKb x
    rw [hq0, zero_sub, abs_neg] at hzero
    exact hzero
  have htheta := integral_exitTimeTrunc_eq_sub P hP hU t x
  have hI0 := integral_shortfall_nonneg P hP (U := U) t x
  have hIle := integral_shortfall_le P hP hU t x
  have hsplit : (∫ omega, q (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x)) - sigma * (t : ℝ) =
      u x + (∫ omega, (q (omega (ContinuousPath.exitTimeTrunc U t omega)) -
          u (omega (ContinuousPath.exitTimeTrunc U t omega)))
          ∂(IsConservative.continuousProcess P hP x)) -
        sigma * ∫ omega, Set.indicator (survivalEvent U t)ᶜ
          (fun omega ↦ (t : ℝ) - (ContinuousPath.exitTime U omega).toReal) omega
          ∂(IsConservative.continuousProcess P hP x) := by
    rw [hsub, hA2, htheta]
    ring
  have hsigmaI := mul_le_mul_of_nonneg_left hIle hsigma
  have hsigmaI0 := mul_nonneg hsigma hI0
  have habsu := abs_le.1 hux
  have habsd := abs_le.1 hdiff
  rw [hsplit, abs_le]
  constructor
  · linarith only [habsu.1, habsd.1, hsigmaI, hsigmaI0]
  · linarith only [habsu.2, habsd.2, hsigmaI, hsigmaI0]

end StoppedIdentities

end

end Algsuperdiff.Section5.Provider
