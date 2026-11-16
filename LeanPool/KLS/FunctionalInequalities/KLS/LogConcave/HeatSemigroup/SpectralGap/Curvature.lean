/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Decay
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.InteriorRegularity
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.WeightedGradient.Poincare
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Curvature
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Curvature
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Convergence
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.Tilted

/-!
# The heat semigroup of a strongly log-concave law: curvature and the Poincaré bound

Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators* (2014), Corollary 4.8.2:
if `dμ = e^{-W} dx` is a probability measure on `ℝⁿ` with `∇∇W ≥ ρ Id`, `ρ > 0`, then `μ` satisfies
the Poincaré inequality `P(1/ρ)`. The book's proof (Propositions 4.8.1 and 4.8.3) combines the
integrated curvature bound `ρ ∫ Γ(f) dμ ≤ ∫ (ℒf)² dμ` with the heat flow and ergodicity.

For the heat semigroup model of `HeatSemigroup/` (`ν = m.tilted (-U)`, closed unit gradient `Tbar`,
`A = Tbar†Tbar`), this file proves:
* the curvature bound `ρ ‖Tbar y‖² ≤ ‖A y‖²` on `C_c^∞` and then on all of `D(A)`, through the
  operator core `exists_seq_smooth_tendsto_adjointComp`;
* the finite-time Poincaré bound `Var(u) - Var(P_t u) ≤ (1 - e^{-2ρt}) / ρ · ‖Tbar u‖²` on `D(Tbar)`;
* `literatureConstant_le_inv_of_tendsto`, the bound `C_P(ν) ≤ 1/ρ` under an explicit ergodicity
  hypothesis, kept as an interface;
* ergodicity itself: `ker Tbar` is the constants (`closedWeightedOperator_eq_zero_iff`, from
  `WeightedGradient/Kernel.lean`), and `Var(P_t u) → 0` for every `u ∈ L²(ν)`
  (`tendsto_norm_center_apply`, from the abstract `Generated.tendsto_apply_of_inner_eq_zero`);
* Corollary 4.8.2 in the model: `Var(u) ≤ ρ⁻¹ ‖Tbar u‖²` on the whole form domain `D(Tbar)`, the closure
  of `C_c^∞` (`norm_center_sq_le_inv_mul`), and `C_P(ν) ≤ 1/ρ` (`literatureConstant_le_inv`);
* the published form for `ν = volume.tilted (-W)` with `W ∈ C²` and `∇∇W ≥ ρ > 0`, whose
  log-concavity and full support are proved in `Density/Tilted.lean`:
  `literatureConstant_le_inv_of_eq_tilted` and the smooth-test inequality
  `smoothTest_holds_inv_of_eq_tilted`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)

omit [FiniteDimensional ℝ V] in
/-- The squared `L²(ν)` norm of the class of `∇f` is `∫ ‖∇f‖² dν`. -/
theorem norm_toLp_gradient_sq {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ‖(memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc).toLp (gradient f)‖ ^ 2 =
      ∫ x, gamma f f x ∂(ν : Measure V) := by
  let hG := memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc
  change ‖hG.toLp (gradient f)‖ ^ 2 = ∫ x, gamma f f x ∂(ν : Measure V)
  calc
    ‖hG.toLp (gradient f)‖ ^ 2 =
        ⟪hG.toLp (gradient f), hG.toLp (gradient f)⟫_ℝ := by
          rw [real_inner_self_eq_norm_sq]
    _ = ∫ x, ⟪gradient f x, gradient f x⟫_ℝ ∂(ν : Measure V) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hG] with x hx
      rw [hx]
    _ = ∫ x, ‖gradient f x‖ ^ 2 ∂(ν : Measure V) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [real_inner_self_eq_norm_sq]
    _ = ∫ x, gamma f f x ∂(ν : Measure V) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [gamma_self]

include hνU hU in
/-- The curvature bound on smooth compactly supported classes: if `∇∇U ≥ ρ`, then
`ρ ‖Tbar [f]‖² ≤ ‖A [f]‖²`. -/
theorem mul_norm_closedWeightedOperator_toLp_sq_le {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩‖ ^ 2 ≤
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU.of_succ hf hfc⟩‖ ^ 2 := by
  rw [hν.closedWeightedOperator_toLp_eq m hi hf hfc,
    hν.adjointComp_toLp_eq m hi hνU hU.of_succ hf hfc]
  have hneg :
      ‖(memLp_neg_weightedLaplacian (ν := ν) hU.of_succ hf hfc).toLp
          (fun x => -weightedLaplacian U f x)‖ ^ 2 =
        ∫ x, weightedLaplacian U f x ^ 2 ∂(ν : Measure V) := by
    let hL := memLp_neg_weightedLaplacian (ν := ν) hU.of_succ hf hfc
    change ‖hL.toLp (fun x => -weightedLaplacian U f x)‖ ^ 2 =
      ∫ x, weightedLaplacian U f x ^ 2 ∂(ν : Measure V)
    calc
      ‖hL.toLp (fun x => -weightedLaplacian U f x)‖ ^ 2 =
          ⟪hL.toLp (fun x => -weightedLaplacian U f x),
            hL.toLp (fun x => -weightedLaplacian U f x)⟫_ℝ := by
        rw [real_inner_self_eq_norm_sq]
      _ = ∫ x, ⟪-weightedLaplacian U f x,
            -weightedLaplacian U f x⟫_ℝ ∂(ν : Measure V) := by
        rw [MeasureTheory.L2.inner_def]
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hL] with x hx
        rw [hx]
      _ = ∫ x, weightedLaplacian U f x ^ 2 ∂(ν : Measure V) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [real_inner_self_eq_norm_sq, norm_neg, Real.norm_eq_abs,
          sq_abs]
  rw [norm_toLp_gradient_sq (ν := ν) hf hfc, hneg, hνU]
  exact Analysis.BakryEmery.mul_integral_gamma_le m hU
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfc hH

include hνU hU in
/-- The curvature bound on the whole operator domain: if `∇∇U ≥ ρ`, then `ρ ‖Tbar y‖² ≤ ‖A y‖²`
for every `y ∈ D(A)`. -/
theorem mul_norm_closedWeightedOperator_sq_le {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨F, F.2.2⟩‖ ^ 2 ≤
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F‖ ^ 2 := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hinner
      (x : (adjointComp T).domain) :
      ‖T ⟨x, x.2.2⟩‖ ^ 2 = ⟪adjointComp T x, x⟫_ℝ := by
    symm
    exact inner_adjointComp_self_eq m (ContinuousLinearMap.id ℝ V) hν hi x
  obtain ⟨fn, hfn, hfnc, h1, h2⟩ :=
    hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU.of_succ F
  let Fn : ℕ → (adjointComp T).domain := fun n =>
    ⟨(Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport (ν := ν) (hfn n)
        (hfnc n)).toLp (fn n),
      hν.toLp_mem_adjointComp_domain m hi hνU hU.of_succ
        (hfn n) (hfnc n)⟩
  have hle : ∀ n,
      ρ * ⟪adjointComp T (Fn n), Fn n⟫_ℝ ≤
        ‖adjointComp T (Fn n)‖ ^ 2 := by
    intro n
    rw [← hinner (Fn n)]
    exact
      mul_norm_closedWeightedOperator_toLp_sq_le m hν hi hνU hU hH
        (hfn n) (hfnc n)
  have hFn :
      Tendsto
        (fun n =>
          ((Fn n : (adjointComp T).domain) : Lp ℝ 2 (ν : Measure V)))
        atTop
        (𝓝 ((F : (adjointComp T).domain) : Lp ℝ 2 (ν : Measure V))) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa [Fn, T] using h1
  have hAF :
      Tendsto
        (fun n => adjointComp T (Fn n))
        atTop
        (𝓝 (adjointComp T F)) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa [Fn, T] using h2
  have hleft :
      Tendsto
        (fun n =>
          ρ * ⟪adjointComp T (Fn n),
            ((Fn n : (adjointComp T).domain) :
              Lp ℝ 2 (ν : Measure V))⟫_ℝ)
        atTop
        (𝓝
          (ρ * ⟪adjointComp T F,
            ((F : (adjointComp T).domain) :
              Lp ℝ 2 (ν : Measure V))⟫_ℝ)) := by
    simpa using
      (tendsto_const_nhds.mul (hAF.inner hFn))
  have hright :
      Tendsto
        (fun n => ‖adjointComp T (Fn n)‖ ^ 2)
        atTop
        (𝓝 (‖adjointComp T F‖ ^ 2)) := by
    simpa using hAF.norm.pow 2
  have hlim :
      ρ * ⟪adjointComp T F,
        ((F : (adjointComp T).domain) :
          Lp ℝ 2 (ν : Measure V))⟫_ℝ ≤
        ‖adjointComp T F‖ ^ 2 :=
    le_of_tendsto_of_tendsto' hleft hright hle
  change
    ρ * ‖T ⟨F, F.2.2⟩‖ ^ 2 ≤
      ‖adjointComp T F‖ ^ 2
  calc
    ρ * ‖T ⟨F, F.2.2⟩‖ ^ 2 =
        ρ * ⟪adjointComp T F,
          ((F : (adjointComp T).domain) :
            Lp ℝ 2 (ν : Measure V))⟫_ℝ := by
      rw [hinner F]
    _ ≤ ‖adjointComp T F‖ ^ 2 := hlim

/-- Centering stays in the domain of the closed gradient: `center u ∈ D(Tbar)` for `u ∈ D(Tbar)`. -/
theorem center_mem_closedWeightedOperator_domain
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    L2.center ν (u : Lp ℝ 2 (ν : Measure V)) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hconst :
      L2.const ν (L2.mean ν (u : Lp ℝ 2 (ν : Measure V))) ∈ T.domain := by
    have hone :
        L2.const ν 1 ∈ T.domain :=
      one_mem_domain_closedWeightedOperator m
        (ContinuousLinearMap.id ℝ V) hν hi
    have hsmul :
        L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) • L2.const ν 1 ∈ T.domain :=
      T.domain.smul_mem
        (L2.mean ν (u : Lp ℝ 2 (ν : Measure V))) hone
    rw [← mul_one (L2.mean ν (u : Lp ℝ 2 (ν : Measure V))),
      L2.const_smul]
    exact hsmul
  have hsub :
      (u : Lp ℝ 2 (ν : Measure V)) -
          L2.const ν (L2.mean ν (u : Lp ℝ 2 (ν : Measure V))) ∈ T.domain :=
    T.domain.sub_mem u.2 hconst
  simpa [T, L2.center] using hsub

/-- Centering does not change the closed gradient: `Tbar (center u) = Tbar u`. -/
theorem closedWeightedOperator_center
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
          center_mem_closedWeightedOperator_domain m hν hi u⟩ =
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let c := L2.mean ν (u : Lp ℝ 2 (ν : Measure V))
  let o : T.domain :=
    ⟨L2.const ν 1,
      one_mem_domain_closedWeightedOperator m
        (ContinuousLinearMap.id ℝ V) hν hi⟩
  have hu :
      (⟨L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
          center_mem_closedWeightedOperator_domain m hν hi u⟩ : T.domain) =
        u - c • o := by
    apply Subtype.ext
    change
      L2.center ν (u : Lp ℝ 2 (ν : Measure V)) =
        (u : Lp ℝ 2 (ν : Measure V)) -
          c • (L2.const ν 1)
    simp only [L2.center]
    congr 1
    rw [← L2.const_smul, mul_one]
  have ho : T o = 0 := by
    change
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨L2.const ν 1,
            one_mem_domain_closedWeightedOperator m
              (ContinuousLinearMap.id ℝ V) hν hi⟩ = 0
    exact hν.closedWeightedOperator_one_eq_zero m
      (ContinuousLinearMap.id ℝ V) hi
  have hmain :
      T
          ⟨L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
            center_mem_closedWeightedOperator_domain m hν hi u⟩ =
        T u := by
    have h := congrArg (fun x : T.domain => T x) hu
    calc
      T
          ⟨L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
            center_mem_closedWeightedOperator_domain m hν hi u⟩ =
          T (u - c • o) := h
      _ = T u - T (c • o) := by
        exact T.toFun.map_sub u (c • o)
      _ = T u - c • T o := by
        congr 1
        exact T.toFun.map_smul c o
      _ = T u := by
        rw [ho, smul_zero, sub_zero]
  exact hmain

include hνU hU in
/-- The finite-time Poincaré bound: if `∇∇U ≥ ρ > 0`, then for `u ∈ D(Tbar)` and `t ≥ 0`,
`Var(u) - Var(P_t u) ≤ (1 - e^{-2ρt}) / ρ · ‖Tbar u‖²`. -/
theorem norm_center_sq_sub_le {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
        ‖L2.center ν
          (HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht u)‖ ^ 2 ≤
      (1 - Real.exp (-2 * ρ * t)) / ρ *
        ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2 := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let c : T.domain :=
    ⟨L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
      center_mem_closedWeightedOperator_domain m hν hi u⟩
  have hcurv :
      ∀ y : (adjointComp T).domain,
        ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖adjointComp T y‖ ^ 2 := by
    intro y
    exact mul_norm_closedWeightedOperator_sq_le m hν hi hνU hU hH y
  have hkey :=
    Generated.norm_sq_sub_norm_apply_sq_le T hT hd hρ hcurv c ht
  have hcenter :
      L2.center ν
          (HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht
            (u : Lp ℝ 2 (ν : Measure V))) =
        HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          (L2.center ν (u : Lp ℝ 2 (ν : Measure V))) := by
    exact HeatSemigroup.center_operator m (ContinuousLinearMap.id ℝ V) hν hi ht
      (u : Lp ℝ 2 (ν : Measure V))
  rw [hcenter]
  change
    ‖(c : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
        ‖Generated.apply T hT hd t c‖ ^ 2 ≤
      (1 - Real.exp (-2 * ρ * t)) / ρ *
        ‖T u‖ ^ 2
  have hTc :
      T c = T u := by
    simpa [c, T] using
      (closedWeightedOperator_center m hν hi u)
  rw [hTc] at hkey
  exact hkey

/-- A form-domain gap `Var(u) ≤ C ‖Tbar u‖²` bounds the literature Poincaré constant by `C`
(the converse of `closedWeightedOperator_id_gap_of_literature_le`). -/
theorem literatureConstant_le_of_gap (C : NNReal)
    (hgap : ∀ u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
        (C : ℝ) * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2) :
    Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal) := by
  rw [← hν.closedWeightedOperator_id_constant_eq_literature m hi,
    ← Poincare.L2Energy.holds_iff_constant_le,
    Poincare.L2Energy.holds_iff]
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  intro f
  have hfT : f.1 ∈ T.domain := by
    by_contra h
    have htop :
        Energy.PreEnergy.normSqEnergy T f.1 = ⊤ :=
      Energy.PreEnergy.normSqEnergy_of_notMem T h
    exact f.2 htop
  let u : T.domain := ⟨f.1, hfT⟩
  have hvalue :
      Energy.PreEnergy.normSqEnergy T f.1 =
        ((‖T u‖₊ ^ 2 : NNReal) : ENNReal) := by
    simpa [u] using
      (Energy.PreEnergy.normSqEnergy_of_mem T u)
  have hfinite :
      (Energy.PreEnergy.normSqEnergy T).finiteValue f =
        ‖T u‖₊ ^ 2 := by
    apply ENNReal.coe_injective
    calc
      ((Energy.PreEnergy.normSqEnergy T).finiteValue f : ENNReal) =
          (Energy.PreEnergy.normSqEnergy T).toFun f :=
        Energy.Functional.coe_finiteValue
          (Energy.PreEnergy.normSqEnergy T) f
      _ = Energy.PreEnergy.normSqEnergy T f.1 := rfl
      _ = ((‖T u‖₊ ^ 2 : NNReal) : ENNReal) := hvalue
  have hgap' :
      ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖₊ ^ 2 ≤
        C * ‖T u‖₊ ^ 2 := by
    exact_mod_cast hgap u
  change
    L2.variance ν (f : Lp ℝ 2 (ν : Measure V)) ≤
      C * (Energy.PreEnergy.normSqEnergy T).finiteValue f
  rw [L2.variance, hfinite]
  simpa [u, T] using hgap'

include hνU hU in
/-- Bakry–Gentil–Ledoux (2014), Corollary 4.8.2, **under an ergodicity hypothesis**: if
`∇∇U ≥ ρ > 0` and `Var(P_t u) → 0` as `t → ∞` for every `u ∈ D(Tbar)`, then the literature Poincaré
constant satisfies `C_P(ν) ≤ 1/ρ`. -/
theorem literatureConstant_le_inv_of_tendsto {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (herg : ∀ u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      Tendsto (fun t : ℝ => ‖L2.center ν (Generated.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        (hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi)
        (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) t u)‖)
        atTop (𝓝 0)) :
    Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ ENNReal.ofReal ρ⁻¹ := by
  let C : NNReal := ⟨ρ⁻¹, (inv_pos.mpr hρ).le⟩
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hgap :
      ∀ u : T.domain,
        ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
          (C : ℝ) * ‖T u‖ ^ 2 := by
    intro u
    let a : ℝ := ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2
    let b : ℕ → ℝ := fun n =>
      ‖L2.center ν (Generated.apply T hT hd (n : ℝ) u)‖ ^ 2
    let d : ℝ := ‖T u‖ ^ 2
    have hpointwise : ∀ n : ℕ, a ≤ b n + ρ⁻¹ * d := by
      intro n
      have hn : 0 ≤ (n : ℝ) := by positivity
      have hmain :=
        norm_center_sq_sub_le m hν hi hνU hU hρ hH u hn
      change
        ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
            ‖L2.center ν (Generated.apply T hT hd (n : ℝ) u)‖ ^ 2 ≤
          (1 - Real.exp (-2 * ρ * (n : ℝ))) / ρ * ‖T u‖ ^ 2 at hmain
      have hnum :
          1 - Real.exp (-2 * ρ * (n : ℝ)) ≤ (1 : ℝ) := by
        linarith [Real.exp_nonneg (-2 * ρ * (n : ℝ))]
      have hcoef :
          (1 - Real.exp (-2 * ρ * (n : ℝ))) / ρ ≤ ρ⁻¹ := by
        calc
          (1 - Real.exp (-2 * ρ * (n : ℝ))) / ρ ≤ 1 / ρ :=
            div_le_div_of_nonneg_right hnum hρ.le
          _ = ρ⁻¹ := by rw [one_div]
      have hmul :
          (1 - Real.exp (-2 * ρ * (n : ℝ))) / ρ * ‖T u‖ ^ 2 ≤
            ρ⁻¹ * ‖T u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      dsimp [a, b, d]
      linarith
    have hb :
        Tendsto (fun n : ℕ => b n) atTop (𝓝 0) := by
      have hnat :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      have h := (herg u).comp hnat
      have h' :
          Tendsto
            (fun n : ℕ =>
              ‖L2.center ν (Generated.apply T hT hd (n : ℝ) u)‖ ^ 2)
            atTop (𝓝 (0 : ℝ)) := by
        simpa [T, hT, hd] using h.pow 2
      simpa [b] using h'
    have hsum :
        Tendsto (fun n : ℕ => b n + ρ⁻¹ * d)
          atTop (𝓝 (ρ⁻¹ * d)) := by
      simpa using hb.add tendsto_const_nhds
    have ha : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) :=
      tendsto_const_nhds
    have hlim : a ≤ ρ⁻¹ * d :=
      le_of_tendsto_of_tendsto' ha hsum hpointwise
    have hC : (C : ℝ) = ρ⁻¹ := by
      rfl
    dsimp [a, d] at hlim ⊢
    rw [hC]
    exact hlim
  have hconst :
      Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal) :=
    literatureConstant_le_of_gap m hν hi C hgap
  calc
    Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal) := hconst
    _ = ENNReal.ofReal ρ⁻¹ := by
      rw [ENNReal.ofReal_eq_coe_nnreal]
      rfl

include hνU hU in
/-- **The kernel of the closed unit gradient is the constants**: `Tbar h = 0` exactly when `h` is the
`L²(ν)` constant equal to its mean. -/
theorem closedWeightedOperator_eq_zero_iff
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h = 0 ↔
      (h : Lp ℝ 2 (ν : Measure V)) = L2.const ν (L2.mean ν (h : Lp ℝ 2 (ν : Measure V))) := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  constructor
  · intro h0
    exact eq_const_mean_of_closedWeightedOperator_eq_zero m hν hi hνU
      hU.continuous h h0
  · intro hh
    let c := L2.mean ν (h : Lp ℝ 2 (ν : Measure V))
    let o : T.domain :=
      ⟨L2.const ν 1,
        one_mem_domain_closedWeightedOperator m
          (ContinuousLinearMap.id ℝ V) hν hi⟩
    have hh' : h = c • o := by
      apply Subtype.ext
      change (h : Lp ℝ 2 (ν : Measure V)) = c • (L2.const ν 1)
      calc
        (h : Lp ℝ 2 (ν : Measure V)) =
            L2.const ν c := hh
        _ = L2.const ν (c * 1) := by rw [mul_one]
        _ = c • L2.const ν 1 := L2.const_smul ν c 1
    have ho : T o = 0 := by
      change
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨L2.const ν 1,
              one_mem_domain_closedWeightedOperator m
                (ContinuousLinearMap.id ℝ V) hν hi⟩ = 0
      exact hν.closedWeightedOperator_one_eq_zero m
        (ContinuousLinearMap.id ℝ V) hi
    have hres : T h = 0 := by
      have h' := congrArg (fun x : T.domain => T x) hh'
      calc
        T h = T (c • o) := h'
        _ = c • T o := T.toFun.map_smul c o
        _ = 0 := by rw [ho, smul_zero]
    simpa only [T] using hres

include hνU hU in
/-- Centered data are orthogonal to the kernel of the closed unit gradient. -/
theorem inner_center_eq_zero_of_closedWeightedOperator_eq_zero (u : Lp ℝ 2 (ν : Measure V))
    (k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (hk : hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0) :
    ⟪L2.center ν u, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 := by
  have hk' :
      (k : Lp ℝ 2 (ν : Measure V)) =
        L2.const ν (L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) :=
    (closedWeightedOperator_eq_zero_iff m hν hi hνU hU k).1 hk
  have hinner :
      ⟪L2.center ν u, (k : Lp ℝ 2 (ν : Measure V))⟫ =
        ⟪L2.center ν u,
          L2.const ν (L2.mean ν (k : Lp ℝ 2 (ν : Measure V)))⟫ :=
    congrArg (fun f : Lp ℝ 2 (ν : Measure V) =>
      ⟪L2.center ν u, f⟫) hk'
  calc
    ⟪L2.center ν u, (k : Lp ℝ 2 (ν : Measure V))⟫ =
        ⟪L2.center ν u,
          L2.const ν (L2.mean ν (k : Lp ℝ 2 (ν : Measure V)))⟫ := hinner
    _ = ⟪L2.center ν u,
          (L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) • L2.const ν 1⟫ := by
      rw [← L2.const_smul, mul_one]
    _ = L2.mean ν (k : Lp ℝ 2 (ν : Measure V)) *
          ⟪L2.center ν u, L2.const ν 1⟫ := by
      rw [inner_smul_right]
    _ = L2.mean ν (k : Lp ℝ 2 (ν : Measure V)) *
          L2.mean ν (L2.center ν u) := by
      rfl
    _ = 0 := by
      rw [L2.mean_center, mul_zero]

include hνU hU in
/-- **Ergodicity of the heat semigroup**: for every `u ∈ L²(ν)`, `Var(P_t u) → 0` as `t → ∞`. -/
theorem tendsto_norm_center_apply (u : Lp ℝ 2 (ν : Measure V)) :
    Tendsto (fun t : ℝ => ‖L2.center ν (Generated.apply
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
      (hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi)
      (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) t u)‖)
      atTop (𝓝 0) := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hg :
      ∀ x : T.domain, T x = 0 →
        ⟪L2.center ν u, (x : Lp ℝ 2 (ν : Measure V))⟫ = 0 := by
    intro x hx
    exact inner_center_eq_zero_of_closedWeightedOperator_eq_zero
      m hν hi hνU hU u x (by simpa [T] using hx)
  have hconv :
      Tendsto
        (fun t : ℝ => Generated.apply T hT hd t (L2.center ν u))
        atTop (𝓝 0) :=
    Generated.tendsto_apply_of_inner_eq_zero T hT hd
      (L2.center ν u) hg
  have hnorm :
      Tendsto
        (fun t : ℝ => ‖Generated.apply T hT hd t (L2.center ν u)‖)
        atTop (𝓝 0) := by
    simpa only [norm_zero] using hconv.norm
  have heq :
      ∀ᶠ t : ℝ in atTop,
        ‖Generated.apply T hT hd t (L2.center ν u)‖ =
          ‖L2.center ν (Generated.apply T hT hd t u)‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hc :=
      HeatSemigroup.center_operator m (ContinuousLinearMap.id ℝ V)
        hν hi ht u
    change
      L2.center ν (Generated.apply T hT hd t u) =
        Generated.apply T hT hd t (L2.center ν u) at hc
    exact (congrArg norm hc).symm
  change
    Tendsto
      (fun t : ℝ => ‖L2.center ν (Generated.apply T hT hd t u)‖)
      atTop (𝓝 0)
  exact hnorm.congr' heq

include hνU hU in
/-- **Bakry–Gentil–Ledoux (2014), Corollary 4.8.2, on the Dirichlet domain**: if `∇∇U ≥ ρ > 0`, then
`Var(u) ≤ ρ⁻¹ ‖Tbar u‖²` for every `u` in the domain of the closed unit gradient, the closure of
`C_c^∞` in the energy norm. -/
theorem norm_center_sq_le_inv_mul {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
      ρ⁻¹ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2 := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let a : ℝ :=
    ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2
  let b : ℝ → ℝ := fun t =>
    ‖L2.center ν (Generated.apply T hT hd t u)‖ ^ 2
  let d : ℝ := ‖T u‖ ^ 2
  have hpointwise : ∀ t : ℝ, 0 ≤ t → a ≤ ρ⁻¹ * d + b t := by
    intro t ht
    have hmain := norm_center_sq_sub_le m hν hi hνU hU hρ hH u ht
    change
      ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
          ‖L2.center ν (Generated.apply T hT hd t u)‖ ^ 2 ≤
        (1 - Real.exp (-2 * ρ * t)) / ρ * ‖T u‖ ^ 2 at hmain
    have hnum : 1 - Real.exp (-2 * ρ * t) ≤ (1 : ℝ) := by
      linarith [Real.exp_nonneg (-2 * ρ * t)]
    have hcoef :
        (1 - Real.exp (-2 * ρ * t)) / ρ ≤ ρ⁻¹ := by
      calc
        (1 - Real.exp (-2 * ρ * t)) / ρ ≤ 1 / ρ :=
          div_le_div_of_nonneg_right hnum hρ.le
        _ = ρ⁻¹ := by rw [one_div]
    have hmul :
        (1 - Real.exp (-2 * ρ * t)) / ρ * ‖T u‖ ^ 2 ≤
          ρ⁻¹ * ‖T u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    dsimp [a, b, d]
    linarith
  have hb :
      Tendsto (fun t : ℝ => b t) atTop (𝓝 0) := by
    have hnorm :=
      tendsto_norm_center_apply m hν hi hνU hU
        (u : Lp ℝ 2 (ν : Measure V))
    have hnorm' :
        Tendsto
          (fun t : ℝ =>
            ‖L2.center ν (Generated.apply T hT hd t u)‖ ^ 2)
          atTop (𝓝 0) := by
      simpa [T, hT, hd] using hnorm.pow 2
    simpa [b] using hnorm'
  have hsum :
      Tendsto (fun t : ℝ => ρ⁻¹ * d + b t)
        atTop (𝓝 (ρ⁻¹ * d)) := by
    simpa using tendsto_const_nhds.add hb
  have hsum_nat :
      Tendsto (fun n : ℕ => ρ⁻¹ * d + b (n : ℝ))
        atTop (𝓝 (ρ⁻¹ * d)) := by
    exact hsum.comp tendsto_natCast_atTop_atTop
  have hev :
      ∀ᶠ n : ℕ in atTop, a ≤ ρ⁻¹ * d + b (n : ℝ) := by
    filter_upwards [] with n
    exact hpointwise (n : ℝ) (by positivity)
  have hlim : a ≤ ρ⁻¹ * d :=
    ge_of_tendsto hsum_nat hev
  change a ≤ ρ⁻¹ * d
  exact hlim

include hν hi hνU hU in
/-- **Bakry–Gentil–Ledoux (2014), Corollary 4.8.2, in the heat-semigroup model**: if
`ν = m.tilted (-U)` is log-concave with full-dimensional support, `U` is `C²` and `∇∇U ≥ ρ > 0`,
then the literature Poincaré constant satisfies `C_P(ν) ≤ 1/ρ`. -/
theorem literatureConstant_le_inv {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) :
    Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ ENNReal.ofReal ρ⁻¹ := by
  exact literatureConstant_le_inv_of_tendsto m hν hi hνU hU hρ hH
    (fun u =>
      tendsto_norm_center_apply m hν hi hνU hU
        (u : Lp ℝ 2 (ν : Measure V)))

/-- **Bakry–Gentil–Ledoux (2014), Corollary 4.8.2**: let `ν = volume.tilted (-W)` be the
probability law with density proportional to `e^{-W}` on a finite-dimensional real inner product
space (for `ℝⁿ` with Lebesgue measure), with `W` of class `C²` and `∇∇W ≥ ρ Id`, `ρ > 0`. Then the
literature Poincaré constant satisfies `C_P(ν) ≤ 1/ρ`. -/
theorem literatureConstant_le_inv_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : ContDiff ℝ 2 W) {ρ : ℝ}
    (hρ : 0 < ρ) (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ W x v v) :
    Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ ENNReal.ofReal ρ⁻¹ := by
  let hconv :=
    Analysis.BakryEmery.convexOn_of_hessian_ge hW hρ.le hH
  have hν' : LogConcave ν :=
    logConcave_of_eq_tilted hνW hW.continuous hconv
  have hi' : (interior (ν : Measure V).support).Nonempty :=
    interior_support_nonempty_of_eq_tilted (volume : Measure V) hνW
  exact literatureConstant_le_inv (volume : Measure V) hν' hi' hνW hW hρ hH

/-- **Bakry–Gentil–Ledoux (2014), Corollary 4.8.2, as the Poincaré inequality `P(1/ρ)`**: under
the same hypotheses, `Var_ν(f) ≤ ρ⁻¹ ∫ ‖∇f‖² dν` for every smooth `f ∈ L²(ν)` with
`‖∇f‖ ∈ L²(ν)`. -/
theorem smoothTest_holds_inv_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : ContDiff ℝ 2 W) {ρ : ℝ}
    (hρ : 0 < ρ) (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ W x v v) :
    Poincare.SmoothTest.Holds (ν : Measure V) ρ⁻¹ := by
  let C : NNReal := ⟨ρ⁻¹, (inv_pos.mpr hρ).le⟩
  have hconv :
      ConvexOn ℝ Set.univ W :=
    Analysis.BakryEmery.convexOn_of_hessian_ge hW hρ.le hH
  have hν' : LogConcave ν :=
    logConcave_of_eq_tilted hνW hW.continuous hconv
  have hconstant :
      Poincare.SmoothGradient.Ambient.optimalConstant ν ≤ (C : ENNReal) := by
    calc
      Poincare.SmoothGradient.Ambient.optimalConstant ν =
          Poincare.SmoothTest.optimalConstant (ν : Measure V) := by
        symm
        exact Poincare.SmoothTest.constant_eq_ambient ν
      _ = Poincare.LocalSlope.Intrinsic.optimalConstant ν :=
        smoothTest_constant_eq_localSlope hν'
      _ ≤ ENNReal.ofReal ρ⁻¹ :=
        literatureConstant_le_inv_of_eq_tilted (ν := ν) hνW hW hρ hH
      _ = (C : ENNReal) := by
        rw [ENNReal.ofReal_eq_coe_nnreal]
        rfl
  have hambient :
      Poincare.SmoothGradient.Ambient.Holds ν C :=
    (Poincare.SmoothGradient.Ambient.holds_iff_constant_le ν C).2 hconstant
  have hsmooth :
      Poincare.SmoothTest.Holds (ν : Measure V) (C : ℝ) :=
    (Poincare.SmoothTest.holds_iff_ambient ν C).2 hambient
  exact hsmooth

end FunctionalInequalities.KLS.LogConcave
