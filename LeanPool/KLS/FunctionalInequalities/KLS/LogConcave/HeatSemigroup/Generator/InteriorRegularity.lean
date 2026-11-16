/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.Core
public import LeanPool.KLS.FunctionalInequalities.Analysis.Mollification.Basic

/-!
# Interior regularity of deficiency elements, and the operator core

`HeatSemigroup/Generator/Core.lean` reduces the operator-core property of `C_c^∞(V)` for
`A = Tbar†Tbar` — the hypothesis `hcore` of the heat-flow weak `Γ₂` theorem — to one local statement:
every `u ∈ L²(ν)` orthogonal to `(A + 1) C_c^∞(V)` has all of its localizations `[χ u]`,
`χ ∈ C_c^∞(V)`, in the form domain `D(Tbar)`. This module proves that statement and draws the
consequence.

## What is proved

Write `ν = m.tilted (-U)` with a `C¹` potential `U`, `ρ = e^{-U} / Z` for its density with
respect to the Haar measure `m`, `Tbar` for the closed unit-weight gradient and `A = Tbar†Tbar`.

* `toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`: **interior regularity.** If
  `⟪A [f], u⟫ + ⟪[f], u⟫ = 0` for every `f ∈ C_c^∞(V)`, then `[χ u] ∈ D(Tbar)` for every
  `χ ∈ C_c^∞(V)`. This is exactly the hypothesis `hreg` of the two criterion theorems.
* `exists_seq_smooth_tendsto_adjointComp`: consequently `C_c^∞(V)` **is** an operator core of
  `A`: every `F ∈ D(A)` is a graph-norm limit of smooth compactly supported classes. This is the
  hypothesis `hcore` of `HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core`, now a
  theorem for every `C¹` potential.

## The argument

Against the Haar measure the equation `ℒ u = u` for the class `W = ρ u` reads, in the weak sense,
`Δ W = -div (W ∇U) + W`: `∫ Δf W dm = ∫ ⟪∇f, W ∇U⟫ dm + ∫ f W dm` for all `f ∈ C_c^∞(V)`
(`integral_laplacian_mul_tiltedDensity_mul`). The principal part is the constant-coefficient
Laplacian, so mollification commutes with it: with a cutoff `η` equal to one near `tsupport χ`
and the normalised bumps `ρₙ` of `Analysis/Mollification/Basic.lean`, the smooth functions
`vₙ = ρₙ ⋆ (η W)` satisfy the same equation with the continuous fields `Hₙ = ρₙ ⋆ (η W ∇U)`
against every test supported in `tsupport χ` (`integral_laplacian_mul_convolution_eq`). The
Caccioppoli-type estimate `‖χ ∇v‖ ≤ 3 ‖v ∇χ‖ + 2 ‖χ H‖`, obtained from the test `g = χ² v`
(`norm_toLp_smul_gradient_le`), applied to the *differences* `vₙ - vₖ`, `Hₙ - Hₖ`, shows that
`χ ∇vₙ` is Cauchy in `L²(m)`, because `vₙ → η W` and `Hₙ → η W ∇U` in `L²(m)`. Hence the `C¹`
compactly supported tests `gₙ = χ vₙ / ρ` converge to `[χ u]` in `L²(ν)` with `[∇gₙ]` Cauchy in
`L²(ν; V)`, and closedness of `Tbar` gives `[χ u] ∈ D(Tbar)`. No weak compactness, no Friedrichs
commutator and no Fourier transform is used, and no classical derivative of `u` is ever taken.

## Scope and downstream results

This module proves the operator-core result for a `C¹` potential. Semigroup estimates and
convexity-based applications are proved in separate modules. The numerical π Cheeger--Buser
comparison and the BKL proof of KLS are formalized downstream; `KLS/Target.lean` contains the
proved target. None of those conclusions is asserted by the operator-core theorem alone.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Metric InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Mollification
open scoped ContDiff RealInnerProductSpace Convolution ENNReal

namespace FunctionalInequalities.KLS.LogConcave

open Energy Energy.WeightedGradient

section Generic

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- A pointwise bound `‖f x‖ ≤ C ‖g x‖` gives `eLpNorm f ≤ C eLpNorm g`. -/
private theorem eLpNorm_le_of_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : α → E} {g : α → F} {C : ℝ} (hC : 0 ≤ C) (hf : AEStronglyMeasurable f μ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖g x‖) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal C * eLpNorm g 2 μ := by
  refine (eLpNorm_mono_real hf h).trans ?_
  have : (fun x => C * ‖g x‖) = C • fun x => ‖g x‖ := rfl
  rw [this, eLpNorm_const_smul, Real.enorm_of_nonneg hC]
  gcongr
  by_cases hg : AEStronglyMeasurable g μ
  · rw [eLpNorm_norm g hg]
  · rw [eLpNorm_of_not_aestronglyMeasurable hg]
    exact le_top

end Generic

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The pairing of a compactly supported field with any field has compact support. -/
private theorem hasCompactSupport_inner_left {f g : V → V} (hf : HasCompactSupport f) :
    HasCompactSupport fun x => ⟪f x, g x⟫ := by
  refine HasCompactSupport.of_support_subset_isCompact hf fun x hx => subset_tsupport _ ?_
  rw [Function.mem_support] at hx ⊢
  intro hz
  exact hx (by rw [hz, inner_zero_left])

variable [FiniteDimensional ℝ V]

/-- The Laplacian vanishes outside the closed support. -/
private theorem laplacian_eq_zero_of_notMem_tsupport {f : V → ℝ} {y : V} (hy : y ∉ tsupport f) :
    Laplacian.laplacian f y = 0 := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = 0 := by
    by_contra h
    exact hy (tsupport_fderiv_subset (𝕜 := ℝ) (support_fderiv_subset (𝕜 := ℝ) h))
  rw [laplacian_eq_sum_fderiv_fderiv, h2]
  simp

end Pointwise

section Haar

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (m : Measure V) [m.IsAddHaarMeasure]

omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [m.IsAddHaarMeasure] in
/-- The standard mollifier sequence: bumps of radii `1/(2(n+1)) < 1/(n+1)`. -/
private def mollifier (n : ℕ) : ContDiffBump (0 : V) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have ha : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [show (1 : ℝ) / (2 * ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / 2 by field_simp]
    exact half_lt_self ha

omit [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [m.IsAddHaarMeasure] in
private theorem tendsto_mollifier_rOut :
    Tendsto (fun n => (mollifier (V := V) n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

omit [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [m.IsAddHaarMeasure] in
private theorem mollifier_rOut_le_one (n : ℕ) : (mollifier (V := V) n).rOut ≤ 1 := by
  change (1 : ℝ) / ((n : ℝ) + 1) ≤ 1
  exact div_le_one_of_le₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) (by positivity)

/-- **A Caccioppoli-type estimate for the mollified equation.** If a smooth `v` and a continuous
field `H` satisfy the weak equation `∫ Δg v = ∫ ⟪∇g, H⟫ + ∫ g v` for every smooth test `g`
supported in `tsupport χ`, then `‖χ ∇v‖ ≤ 3 ‖v ∇χ‖ + 2 ‖χ H‖` in `L²(m)`. Only the test
`g = χ² v` is used. -/
private theorem norm_toLp_smul_gradient_le {χ v : V → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hv : ContDiff ℝ ∞ v) {H : V → V}
    (heq :
      ∀ g : V → ℝ,
        ContDiff ℝ ∞ g →
          HasCompactSupport g →
            tsupport g ⊆ tsupport χ →
              ∫ x, Laplacian.laplacian g x * v x ∂m =
                ∫ x, ⟪gradient g x, H x⟫ ∂m + ∫ x, g x * v x ∂m)
    (hA : MemLp (fun x => χ x • gradient v x) 2 m)
    (hB : MemLp (fun x => v x • gradient χ x) 2 m) (hC : MemLp (fun x => χ x • H x) 2 m) :
    ‖hA.toLp _‖ ≤ 3 * ‖hB.toLp _‖ + 2 * ‖hC.toLp _‖ := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (WithTop.coe_le_coe.mpr le_top)
  have hχd : Differentiable ℝ χ := hχ1.differentiable one_ne_zero
  have hvd : Differentiable ℝ v :=
    hv1.differentiable
      one_ne_zero
  -- the test function `g = χ² v`
  set g : V → ℝ := fun x => χ x * χ x * v x with hg_def
  have hg : ContDiff ℝ ∞ g := (hχ.mul hχ).mul hv
  have hgc : HasCompactSupport g := (hχc.mul_right).mul_right
  have hgs : tsupport g ⊆ tsupport χ := by
    refine closure_mono fun x hx => ?_
    simp only [Function.mem_support, hg_def] at hx ⊢
    intro h0
    exact hx (by rw [h0]; ring)
  have hgrad :
    ∀ x, gradient g x = (χ x * χ x) • gradient v x + (2 * (χ x * v x)) • gradient χ x := by
    intro x
    have h1 : gradient (fun y => χ y * χ y) x = χ x • gradient χ x + χ x • gradient χ x :=
      gradient_mul (hχd x) (hχd x)
    have h2 :=
      gradient_mul (f := fun y => χ y * χ y) (g := v) (x := x) ((hχd x).mul (hχd x)) (hvd x)
    rw [hg_def]
    refine h2.trans ?_
    rw [h1]
    module
  -- integration by parts with the constant weight
  have hibp :=
    integral_mul_inner_gradient_eq_neg m (w := fun _ => (1 : ℝ)) contDiff_const
      (hg.of_le (WithTop.coe_le_coe.mpr le_top)) hgc hv1
  simp only [one_mul, gradient_fun_const, inner_zero_left, add_zero] at hibp
  have heqg :=
    heq g hg hgc
      hgs
  -- the three `L²` classes and their pairings
  have hAae := hA.coeFn_toLp
  have hBae := hB.coeFn_toLp
  have hCae := hC.coeFn_toLp
  have hint :
    ∀ (F G : Lp V 2 m) (f g : V → V),
      (F : V → V) =ᵐ[m] f → (G : V → V) =ᵐ[m] g → Integrable (fun x => ⟪f x, g x⟫) m :=
    fun F G f g hF hG =>
    (L2.integrable_inner F G).congr (by filter_upwards [hF, hG] with x e1 e2; rw [e1, e2])
  have hAA : ⟪hA.toLp _, hA.toLp _⟫ = ∫ x, ⟪χ x • gradient v x, χ x • gradient v x⟫ ∂m := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [hAae] with x e; rw [e])
  have hBA : ⟪hB.toLp _, hA.toLp _⟫ = ∫ x, ⟪v x • gradient χ x, χ x • gradient v x⟫ ∂m := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [hAae, hBae] with x e1 e2; rw [e1, e2])
  have hAC : ⟪hA.toLp _, hC.toLp _⟫ = ∫ x, ⟪χ x • gradient v x, χ x • H x⟫ ∂m := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [hAae, hCae] with x e1 e2; rw [e1, e2])
  have hBC : ⟪hB.toLp _, hC.toLp _⟫ = ∫ x, ⟪v x • gradient χ x, χ x • H x⟫ ∂m := by
    rw [L2.inner_def]
    exact
      integral_congr_ae
        (by filter_upwards [hBae, hCae] with x e1 e2; rw [e1, e2])
  -- `∫ ⟪∇g, ∇v⟫ = ‖A‖² + 2 ⟪B, A⟫`
  have e1 :
    ∫ x, ⟪gradient g x, gradient v x⟫ ∂m = ‖hA.toLp _‖ ^ 2 + 2 * ⟪hB.toLp _, hA.toLp _⟫ := by
    rw [← real_inner_self_eq_norm_sq, hAA, hBA, ← integral_const_mul, ←
      integral_add (hint _ _ _ _ hAae hAae) ((hint _ _ _ _ hBae hAae).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hgrad, inner_add_left, real_inner_smul_left, real_inner_smul_right]
    ring
  -- `∫ ⟪∇g, H⟫ = ⟪A, C⟫ + 2 ⟪B, C⟫`
  have e2 : ∫ x, ⟪gradient g x, H x⟫ ∂m = ⟪hA.toLp _, hC.toLp _⟫ + 2 * ⟪hB.toLp _, hC.toLp _⟫ := by
    rw [hAC, hBC, ← integral_const_mul, ←
      integral_add (hint _ _ _ _ hAae hCae) ((hint _ _ _ _ hBae hCae).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hgrad, inner_add_left, real_inner_smul_left, real_inner_smul_right]
    ring
  -- `∫ g v ≥ 0`
  have e3 : 0 ≤ ∫ x, g x * v x ∂m := by
    refine integral_nonneg fun x => ?_
    simp only [hg_def, Pi.zero_apply]
    nlinarith [sq_nonneg (χ x * v x)]
  -- the quadratic inequality
  have hkey :
    ‖hA.toLp _‖ ^ 2 + 2 * ⟪hB.toLp _, hA.toLp _⟫ +
        (⟪hA.toLp _, hC.toLp _⟫ + 2 * ⟪hB.toLp _, hC.toLp _⟫) ≤
      0 := by
    rw [← e1, ← e2, hibp]
    linarith [heqg, e3]
  have cs1 := abs_real_inner_le_norm (hB.toLp _) (hA.toLp _)
  have cs2 := abs_real_inner_le_norm (hA.toLp _) (hC.toLp _)
  have cs3 := abs_real_inner_le_norm (hB.toLp _) (hC.toLp _)
  have hA0 := norm_nonneg (hA.toLp _)
  have hB0 := norm_nonneg (hB.toLp _)
  have hC0 := norm_nonneg (hC.toLp _)
  have hsq :
    ‖hA.toLp _‖ ^ 2 ≤
      2 * ‖hB.toLp _‖ * ‖hA.toLp _‖ + ‖hA.toLp _‖ * ‖hC.toLp _‖ +
        2 * ‖hB.toLp _‖ * ‖hC.toLp _‖ := by
    have := neg_abs_le (⟪hB.toLp _, hA.toLp _⟫ : ℝ)
    have := neg_abs_le (⟪hA.toLp _, hC.toLp _⟫ : ℝ)
    have := neg_abs_le (⟪hB.toLp _, hC.toLp _⟫ : ℝ)
    nlinarith
  nlinarith [hsq, hA0, hB0, hC0, mul_nonneg hB0 hC0]

/-- **The mollified weak equation.** If `W` satisfies the weak equation
`∫ Δf W = ∫ ⟪∇f, W F⟫ + ∫ f W` against every smooth compactly supported `f`, `η` is a bump equal
to one on `closedBall 0 (R + 1)`, and `ρ` is a normalised bump of radius at most one, then the
mollifications `v = ρ ⋆ (η W)` and `H = ρ ⋆ (η W F)` satisfy the same equation against every
smooth test supported in `closedBall 0 R`. The mollifier is moved onto the test function by the
symmetry identity, commuted with `Δ` and `∇`, and the cutoff `η` is invisible where the mollified
test lives. -/
private theorem integral_laplacian_mul_convolution_eq {W : V → ℝ} {F : V → V}
    (hW : ∀ f : V → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ x, Laplacian.laplacian f x * W x ∂m =
        ∫ x, ⟪gradient f x, W x • F x⟫ ∂m + ∫ x, f x * W x ∂m)
    {R : ℝ} (η : ContDiffBump (0 : V)) (hη : R + 1 ≤ η.rIn)
    (hw : Integrable (fun x => η x * W x) m) (hG : Integrable (fun x => (η x * W x) • F x) m)
    (φ : ContDiffBump (0 : V)) (hφ : φ.rOut ≤ 1) {g : V → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hgR : tsupport g ⊆ closedBall 0 R) :
    ∫ x, Laplacian.laplacian g x *
        (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m =
      ∫ x, ⟪gradient g x,
          (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x⟫ ∂m +
        ∫ x, g x * (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiff ℝ 2 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hρloc : LocallyIntegrable (φ.normed m) m := φ.integrable_normed.locallyIntegrable
  -- the mollified test function
  set f : V → ℝ := φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g with hf_def
  have hf : ContDiff ℝ ∞ f :=
    HasCompactSupport.contDiff_convolution_left _ (φ.hasCompactSupport_normed (μ := m))
      φ.contDiff_normed hg1.continuous.locallyIntegrable
  have hfc : HasCompactSupport f :=
    HasCompactSupport.convolution _ (φ.hasCompactSupport_normed (μ := m)) hgc
  have hfsupp : tsupport f ⊆ closedBall 0 (R + 1) := by
    refine closure_minimal ?_ isClosed_closedBall
    refine (support_convolution_subset _).trans ?_
    rintro x ⟨a, ha, b, hb, rfl⟩
    rw [φ.support_normed_eq, mem_ball, dist_zero_right] at ha
    have hb' : ‖b‖ ≤ R := by
      have := hgR (subset_tsupport _ hb)
      rwa [mem_closedBall, dist_zero_right] at this
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_add_le a b]
  have hη1 : ∀ x ∈ tsupport f, η x = 1 := fun x hx =>
    η.one_of_mem_closedBall (closedBall_subset_closedBall hη (hfsupp hx))
  -- the derivatives of the mollified test
  have hlap : ∀ x, Laplacian.laplacian f x =
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] Laplacian.laplacian g) x :=
    laplacian_convolution φ hg hgc
  have hgrad : ∀ x, gradient f x = (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] gradient g) x :=
    gradient_convolution φ hg hgc
  -- the weak equation for `f`
  have hWf := hW f hf hfc
  -- (i) the Laplacian term
  have e1 : ∫ x, Laplacian.laplacian g x *
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m =
      ∫ x, Laplacian.laplacian f x * W x ∂m := by
    have h := integral_inner_convolution_eq (E := ℝ) φ hw (continuous_laplacian hg2)
      (hasCompactSupport_laplacian hgc)
    simp only [Real.inner_apply] at h
    rw [show (∫ x, Laplacian.laplacian g x *
        (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m) =
        ∫ x, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x *
          Laplacian.laplacian g x ∂m from
        integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _), h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [← hlap]
    by_cases hx : x ∈ tsupport f
    · rw [hη1 x hx]; ring
    · rw [laplacian_eq_zero_of_notMem_tsupport hx]; ring
  -- (ii) the gradient term
  have e2 : ∫ x, ⟪gradient f x, W x • F x⟫ ∂m = ∫ x, ⟪gradient g x,
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x⟫ ∂m := by
    have h := integral_inner_convolution_eq (E := V) φ hG (continuous_gradient hg1)
      (hasCompactSupport_gradient hgc)
    rw [show (∫ x, ⟪gradient g x,
        (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x⟫ ∂m) =
        ∫ x, ⟪(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x,
          gradient g x⟫ ∂m from
        integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_comm _ _), h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    by_cases hx : x ∈ tsupport f
    · rw [hgrad, hη1 x hx, one_mul, real_inner_comm]
    · rw [Analysis.BakryEmery.gradient_eq_zero_of_notMem_tsupport hx, inner_zero_left, ← hgrad,
        Analysis.BakryEmery.gradient_eq_zero_of_notMem_tsupport hx, inner_zero_right]
  -- (iii) the zeroth-order term
  have e3 : ∫ x, f x * W x ∂m =
      ∫ x, g x * (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m := by
    have h := integral_inner_convolution_eq (E := ℝ) φ hw hg1.continuous hgc
    simp only [Real.inner_apply] at h
    rw [show (∫ x, g x * (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m)
        = ∫ x, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x * g x ∂m from
        integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _), h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change f x * W x = η x * W x * f x
    by_cases hx : x ∈ tsupport f
    · rw [hη1 x hx]; ring
    · rw [image_eq_zero_of_notMem_tsupport hx]; ring
  rw [e1, hWf, e2, e3]

end Haar

section Density

variable {V : Type*} [MeasurableSpace V] {ν : ProbabilityMeasure V} (m : Measure V) {U : V → ℝ}

/-- The normalised density `exp (-U) / ∫ exp (-U) dm` of `m.tilted (-U)`. -/
private def tiltedDensity (m : Measure V) (U : V → ℝ) (x : V) : ℝ :=
  Real.exp ((-U) x) / ∫ y, Real.exp ((-U) y) ∂m

/-- `exp (-U)` is `m`-integrable when `m.tilted (-U)` is a probability measure. -/
private theorem integrable_exp_neg (hνU : (ν : Measure V) = m.tilted (-U)) :
    Integrable (fun x => Real.exp ((-U) x)) m := by
  by_contra h
  have h0 : (ν : Measure V) = 0 := by rw [hνU]; exact tilted_of_not_integrable h
  have h1 := measure_univ (μ := (ν : Measure V))
  rw [h0] at h1
  simp at h1

private theorem integral_exp_neg_pos [NeZero m] (hνU : (ν : Measure V) = m.tilted (-U)) :
    0 < ∫ y, Real.exp ((-U) y) ∂m :=
  integral_exp_pos (integrable_exp_neg m hνU)

private theorem tiltedDensity_pos [NeZero m] (hνU : (ν : Measure V) = m.tilted (-U)) (x : V) :
    0 < tiltedDensity m U x :=
  div_pos (Real.exp_pos _) (integral_exp_neg_pos m hνU)

/-- `1 / tiltedDensity = Z exp U`. -/
private theorem tiltedDensity_mul_exp [NeZero m] (hνU : (ν : Measure V) = m.tilted (-U))
    (x : V) :
    tiltedDensity m U x * ((∫ y, Real.exp ((-U) y) ∂m) * Real.exp (U x)) = 1 := by
  have hZ : (∫ y, Real.exp ((-U) y) ∂m) ≠ 0 := (integral_exp_neg_pos m hνU).ne'
  have hE : Real.exp (U x) ≠ 0 := (Real.exp_pos _).ne'
  unfold tiltedDensity
  rw [Pi.neg_apply, Real.exp_neg]
  field_simp

private theorem integral_eq_tiltedDensity (hνU : (ν : Measure V) = m.tilted (-U)) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : V → E) :
    ∫ x, g x ∂(ν : Measure V) = ∫ x, tiltedDensity m U x • g x ∂m := by
  rw [hνU]
  exact integral_tilted _ _

private theorem lintegral_eq_tiltedDensity (hνU : (ν : Measure V) = m.tilted (-U))
    (g : V → ℝ≥0∞) :
    ∫⁻ x, g x ∂(ν : Measure V) = ∫⁻ x, ENNReal.ofReal (tiltedDensity m U x) * g x ∂m := by
  rw [hνU]
  exact lintegral_tilted _ _

/-- **From `L²(m)` to `L²(ν)`** for a function supported where the density is at most `C`. -/
private theorem eLpNorm_tilted_le (hνU : (ν : Measure V) = m.tilted (-U)) {E : Type*}
    [NormedAddCommGroup E] {f : V → E} {C : ℝ}
    (h : ∀ x, f x ≠ 0 → tiltedDensity m U x ≤ C) :
    eLpNorm f 2 (ν : Measure V) ≤ ENNReal.ofReal C ^ (1 / 2 : ℝ) * eLpNorm f 2 m := by
  by_cases hfm : AEStronglyMeasurable f m
  · have hfν : AEStronglyMeasurable f (ν : Measure V) :=
      hfm.mono_ac (hνU ▸ tilted_absolutelyContinuous m (-U))
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hfν,
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hfm]
    simp only [ENNReal.toReal_ofNat]
    rw [lintegral_eq_tiltedDensity m hνU, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by norm_num)
    by_cases hx : f x = 0
    · simp [hx]
    · gcongr
      exact h x hx
  -- a function that is not `m`-measurable has infinite `L²(m)` seminorm; it is not identically
  -- zero, so `C` dominates a positive density value
  have hm : NeZero m := ⟨fun h0 => by
    have h1 := measure_univ (μ := (ν : Measure V))
    rw [hνU, h0, tilted_zero_measure] at h1
    simp at h1⟩
  have hC : 0 < C := by
    by_contra hC
    refine hfm ?_
    have hf0 : f = 0 := funext fun x => by
      by_contra hx
      exact hC ((tiltedDensity_pos m hνU x).trans_le (h x hx))
    rw [hf0]
    exact aestronglyMeasurable_const
  rw [eLpNorm_of_not_aestronglyMeasurable hfm,
    ENNReal.mul_top (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hC) ENNReal.ofReal_ne_top).ne']
  exact le_top

/-- **From `L²(ν)` to `L²(m)`**: a function dominated by `√(C ρ) |u|` with `u ∈ L²(ν)` is in
`L²(m)`, with the norm bound `√C ‖u‖_{L²(ν)}`. -/
private theorem eLpNorm_le_tilted_of_sq_le [NeZero m] (hνU : (ν : Measure V) = m.tilted (-U))
    {E : Type*} [NormedAddCommGroup E] {F : V → E} {C : ℝ} (hC : 0 ≤ C)
    (u : Lp ℝ 2 (ν : Measure V)) (hF : AEStronglyMeasurable F m)
    (h : ∀ x, ‖F x‖ ^ 2 ≤ C * tiltedDensity m U x * ‖u x‖ ^ 2) :
    eLpNorm F 2 m ≤ ENNReal.ofReal C ^ (1 / 2 : ℝ) * eLpNorm u 2 (ν : Measure V) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hF,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (Lp.aestronglyMeasurable u)]
  simp only [ENNReal.toReal_ofNat]
  rw [lintegral_eq_tiltedDensity m hνU, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by norm_num)
  have hρ := (tiltedDensity_pos m hνU x).le
  have e1 : ‖F x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖F x‖ ^ 2) := by
    rw [← ofReal_norm, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have e2 : ‖u x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖u x‖ ^ 2) := by
    rw [← ofReal_norm, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e1, e2, ← ENNReal.ofReal_mul hρ, ← ENNReal.ofReal_mul hC, ← mul_assoc]
  exact ENNReal.ofReal_le_ofReal (h x)

end Density

section DensityIntegrable

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  {ν : ProbabilityMeasure V} (m : Measure V) {U : V → ℝ}

/-- A bounded continuous compactly supported multiple of `ρ u` is `m`-integrable. -/
private theorem integrable_mul_tiltedDensity_mul (hνU : (ν : Measure V) = m.tilted (-U))
    (u : Lp ℝ 2 (ν : Measure V)) {h : V → ℝ} (hh : Continuous h) (hhc : HasCompactSupport h) :
    Integrable (fun x => h x * (tiltedDensity m U x * u x)) m := by
  obtain ⟨C, hC⟩ := hh.bounded_above_of_compact_support hhc
  have hu : Integrable (fun x => h x * u x) (ν : Measure V) :=
    ((Lp.memLp u).integrable one_le_two).bdd_mul hh.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have key : ∀ μ : Measure V, μ = m.tilted (-U) → Integrable (fun x => h x * u x) μ →
      Integrable (fun x => Real.exp ((-U) x) • (h x * u x)) m := by
    rintro μ rfl hμ
    exact (integrable_tilted_iff (integrable_exp_neg m hνU) _).mp hμ
  have h1 := (key _ hνU hu).const_mul (∫ y, Real.exp ((-U) y) ∂m)⁻¹
  refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [tiltedDensity, smul_eq_mul, div_eq_mul_inv]
  ring

end DensityIntegrable

section Tilted

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}

omit [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  [m.IsAddHaarMeasure] in
private theorem contDiff_tiltedDensity (hU : ContDiff ℝ 1 U) :
    ContDiff ℝ 1 (tiltedDensity m U) :=
  (hU.neg.exp).div_const _

variable (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- **The weak equation for the density-weighted class `W = ρ u`.** If `u ∈ L²(ν)` is orthogonal
to `(A + 1) C_c^∞(V)`, then for every smooth compactly supported `f`,
`∫ Δf W dm = ∫ ⟪∇f, W ∇U⟫ dm + ∫ f W dm`: the equation `ℒ u = u` in `L²(ν)` is, against the
Haar measure, the divergence-form equation `Δ W = -div (W ∇U) + W` in the weak sense. -/
private theorem integral_laplacian_mul_tiltedDensity_mul
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : Lp ℝ 2 (ν : Measure V))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : Lp ℝ 2 (ν : Measure V)), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : Lp ℝ 2 (ν : Measure V)), u⟫ = 0)
    {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∫ x, Laplacian.laplacian f x * (tiltedDensity m U x * u x) ∂m =
      ∫ x, ⟪gradient f x, (tiltedDensity m U x * u x) • gradient U x⟫ ∂m +
        ∫ x, f x * (tiltedDensity m U x * u x) ∂m := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have h0 := horth f hf hfc
  rw [hν.adjointComp_toLp_eq m hi hνU hU hf hfc, L2.inner_def, L2.inner_def] at h0
  have h1 : ∫ x, ⟪((memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).toLp
      (fun y => -weightedLaplacian U f y) : Lp ℝ 2 (ν : Measure V)) x, u x⟫ ∂(ν : Measure V) =
      ∫ x, -weightedLaplacian U f x * u x ∂(ν : Measure V) := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).coeFn_toLp] with x e
    rw [e, Real.inner_apply]
  have h2 : ∫ x, ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
      Lp ℝ 2 (ν : Measure V)) x, u x⟫ ∂(ν : Measure V) =
      ∫ x, f x * u x ∂(ν : Measure V) := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hf hfc).coeFn_toLp] with x e
    rw [e, Real.inner_apply]
  rw [h1, h2, integral_eq_tiltedDensity m hνU (fun x => -weightedLaplacian U f x * u x),
    integral_eq_tiltedDensity m hνU (fun x => f x * u x)] at h0
  have hI1 := integrable_mul_tiltedDensity_mul m hνU u (continuous_laplacian hf2)
    (hasCompactSupport_laplacian hfc)
  have hcont : Continuous fun x => ⟪gradient U x, gradient f x⟫ :=
    (continuous_gradient hU).inner (continuous_gradient hf1)
  have hcs : HasCompactSupport fun x => ⟪gradient U x, gradient f x⟫ := by
    refine HasCompactSupport.of_support_subset_isCompact (hasCompactSupport_gradient hfc)
      fun x hx => subset_tsupport _ ?_
    rw [Function.mem_support] at hx ⊢
    intro hz
    exact hx (by rw [hz, inner_zero_right])
  have hI2 := integrable_mul_tiltedDensity_mul m hνU u hcont hcs
  have hI1' : Integrable (fun x => -(Laplacian.laplacian f x * (tiltedDensity m U x * u x))) m :=
    hI1.neg
  have hsplit : ∫ x, tiltedDensity m U x • (-weightedLaplacian U f x * u x) ∂m =
      -∫ x, Laplacian.laplacian f x * (tiltedDensity m U x * u x) ∂m +
        ∫ x, ⟪gradient U x, gradient f x⟫ * (tiltedDensity m U x * u x) ∂m := by
    rw [← integral_neg, ← integral_add hI1' hI2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [weightedLaplacian_apply, smul_eq_mul]
    ring
  have hlast : ∫ x, tiltedDensity m U x • (f x * u x) ∂m =
      ∫ x, f x * (tiltedDensity m U x * u x) ∂m :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [smul_eq_mul]; ring)
  rw [hsplit, hlast] at h0
  have hg : ∫ x, ⟪gradient f x, (tiltedDensity m U x * u x) • gradient U x⟫ ∂m =
      ∫ x, ⟪gradient U x, gradient f x⟫ * (tiltedDensity m U x * u x) ∂m :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      beta_reduce
      rw [real_inner_smul_right, real_inner_comm]; ring)
  rw [hg]
  linarith

/-- A compactly supported `C¹` function is a weighted-gradient test for the unit weight. -/
private theorem isTest_of_contDiff_one {g : V → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) : IsTest ν (ContinuousLinearMap.id ℝ V) g := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨M, hM0, hM⟩ := Energy.Euclidean.exists_bound_fderiv_of_hasCompactSupport hg hgc
    refine ⟨⟨M, hM0⟩, lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable one_ne_zero)
      fun x => ?_⟩
    change ‖fderiv ℝ g x‖ ≤ M
    exact hM x
  · exact hg.continuous.memLp_of_hasCompactSupport hgc
  · rw [apply_id]
    exact (continuous_gradient hg).memLp_of_hasCompactSupport (hasCompactSupport_gradient hgc)

omit [SecondCountableTopology V] in
/-- The mollified weak equation gives a Caccioppoli estimate for differences. -/
private theorem mollified_difference_caccioppoli {χ : V → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (v : ℕ → V → ℝ) (H : ℕ → V → V)
    (hvs : ∀ n, ContDiff ℝ ∞ (v n)) (hHc : ∀ n, Continuous (H n))
    (hmoll : ∀ n (g : V → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ tsupport χ →
      ∫ x, Laplacian.laplacian g x * v n x ∂m =
        ∫ x, ⟪gradient g x, H n x⟫ ∂m + ∫ x, g x * v n x ∂m) :
 ∀ n k, eLpNorm (fun x => χ x • gradient (v n - v k) x) 2 m ≤
      3 * eLpNorm (fun x => (v n - v k) x • gradient χ x) 2 m +
        2 * eLpNorm (fun x => χ x • (H n - H k) x) 2 m := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdiff : ∀ n k (g : V → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ tsupport χ →
      ∫ x, Laplacian.laplacian g x * (v n - v k) x ∂m =
        ∫ x, ⟪gradient g x, (H n - H k) x⟫ ∂m + ∫ x, g x * (v n - v k) x ∂m := by
    intro n k g hg hgc hgs
    have hg1 : ContDiff ℝ 1 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
    have hg2 : ContDiff ℝ 2 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
    have i1 : ∀ j, Integrable (fun x => Laplacian.laplacian g x * v j x) m := fun j =>
      ((continuous_laplacian hg2).mul (hvs j).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_laplacian hgc).mul_right
    have i2 : ∀ j, Integrable (fun x => ⟪gradient g x, H j x⟫) m := fun j =>
      ((continuous_gradient hg1).inner (hHc j)).integrable_of_hasCompactSupport
        (hasCompactSupport_inner_left (hasCompactSupport_gradient hgc))
    have i3 : ∀ j, Integrable (fun x => g x * v j x) m := fun j =>
      (hg1.continuous.mul (hvs j).continuous).integrable_of_hasCompactSupport hgc.mul_right
    have h1 := hmoll n g hg hgc hgs
    have h2 := hmoll k g hg hgc hgs
    simp only [Pi.sub_apply, mul_sub, inner_sub_right]
    rw [integral_sub (i1 n) (i1 k), integral_sub (i2 n) (i2 k), integral_sub (i3 n) (i3 k)]
    linarith
  -- the Caccioppoli estimate for differences, in `eLpNorm` form
  have hcacc : ∀ n k, eLpNorm (fun x => χ x • gradient (v n - v k) x) 2 m ≤
      3 * eLpNorm (fun x => (v n - v k) x • gradient χ x) 2 m +
        2 * eLpNorm (fun x => χ x • (H n - H k) x) 2 m := by
    intro n k
    have hv' : ContDiff ℝ ∞ (v n - v k) := (hvs n).sub (hvs k)
    have hA : MemLp (fun x => χ x • gradient (v n - v k) x) 2 m :=
      (hχ.continuous.smul (continuous_gradient
        (hv'.of_le (WithTop.coe_le_coe.mpr le_top)))).memLp_of_hasCompactSupport hχc.smul_right
    have hB : MemLp (fun x => (v n - v k) x • gradient χ x) 2 m :=
      (hv'.continuous.smul (continuous_gradient hχ1)).memLp_of_hasCompactSupport
        (hasCompactSupport_gradient hχc).smul_left
    have hC : MemLp (fun x => χ x • (H n - H k) x) 2 m :=
      (hχ.continuous.smul ((hHc n).sub (hHc k))).memLp_of_hasCompactSupport hχc.smul_right
    have h := norm_toLp_smul_gradient_le m hχ hχc hv' (hdiff n k) hA hB hC
    rw [Lp.norm_toLp, Lp.norm_toLp, Lp.norm_toLp] at h
    have hA' := hA.eLpNorm_lt_top.ne
    have hB' := hB.eLpNorm_lt_top.ne
    have hC' := hC.eLpNorm_lt_top.ne
    rw [← ENNReal.ofReal_toReal hA', ← ENNReal.ofReal_toReal hB', ← ENNReal.ofReal_toReal hC']
    calc ENNReal.ofReal (eLpNorm (fun x => χ x • gradient (v n - v k) x) 2 m).toReal
        ≤ ENNReal.ofReal (3 * (eLpNorm (fun x => (v n - v k) x • gradient χ x) 2 m).toReal +
            2 * (eLpNorm (fun x => χ x • (H n - H k) x) 2 m).toReal) :=
          ENNReal.ofReal_le_ofReal h
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  exact hcacc

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    [m.IsAddHaarMeasure] in
/--
A bounded compactly supported error multiplier transfers Haar L2 convergence to the tilted law. -/
private theorem localized_toLp_tendsto (hνU : (ν : Measure V) = m.tilted (-U)) {χ : V → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (u : Lp ℝ 2 (ν : Measure V))
    {g v : ℕ → V → ℝ} {w A : V → ℝ} (hgL : ∀ n, MemLp (g n) 2 (ν : Measure V))
    (hgu : ∀ n x, g n x - χ x * u x = A x * (v n - w) x) (hA_zero : ∀ x ∉ tsupport χ, A x = 0)
    {M Cρ : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, ‖A x‖ ≤ M)
    (hρle : ∀ x ∈ tsupport χ, tiltedDensity m U x ≤ Cρ)
    (hvconv : Tendsto (fun n => eLpNorm (v n - w) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => (hgL n).toLp (g n)) atTop
      (𝓝 ((memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have heq :
    ∀ n,
      eLpNorm
          (((hgL n).toLp (g n) : Lp ℝ 2 (ν : Measure V)) -
              ((memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ :
                Lp ℝ 2 (ν : Measure V)) :
            V → ℝ)
          2 (ν : Measure V) =
        eLpNorm (fun x => g n x - χ x * u x) 2 (ν : Measure V) := by
    intro n
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hgL n).coeFn_toLp,
      (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).coeFn_toLp] with x e1 e2
    rw [Pi.sub_apply, e1, e2]
  simp only [heq]
  have hle :
    ∀ n,
      eLpNorm (fun x => g n x - χ x * u x) 2 (ν : Measure V) ≤
        (ENNReal.ofReal Cρ ^ (1 / 2 : ℝ)) * (ENNReal.ofReal M * eLpNorm (v n - w) 2 m) := by
    intro n
    have hzero : ∀ x ∉ tsupport χ, g n x - χ x * u x = 0 := fun x hx => by
      rw [hgu, hA_zero x hx, zero_mul]
    refine (eLpNorm_tilted_le m hνU fun x hx => hρle x ?_).trans ?_
    · by_contra hx'
      exact hx (hzero x hx')
    · gcongr
      have hmν : m ≪ (ν : Measure V) := by
        rw [hνU]; exact absolutelyContinuous_tilted (integrable_exp_neg m hνU)
      refine eLpNorm_le_of_norm_le m hM0 (((hgL n).aestronglyMeasurable.sub
        (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).aestronglyMeasurable).mono_ac
          hmν) fun x => ?_
      rw [hgu, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le) hle
  have h :=
    ENNReal.Tendsto.const_mul (a := (ENNReal.ofReal Cρ ^ (1 / 2 : ℝ)))
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal M) hvconv (Or.inr ENNReal.ofReal_ne_top))
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
  rwa [mul_zero, mul_zero] at h

/-- **Interior regularity of deficiency elements.** For `ν = m.tilted (-U)` with a `C¹` potential
and unit weight, let `u ∈ L²(ν)` be orthogonal to `(A + 1) C_c^∞(V)`, that is,
`⟪A [f], u⟫ + ⟪[f], u⟫ = 0` for every smooth compactly supported `f`. Then every localization
`[χ u]`, `χ ∈ C_c^∞(V)`, lies in the form domain `D(Tbar)` of the closed unit-weight gradient.

This is exactly the hypothesis `hreg` of
`exists_seq_smooth_tendsto_adjointComp_of_localRegularity` and
`HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_localRegularity`.

The proof is the mollification argument for the divergence-form equation
`Δ W = -div (W ∇U) + W` satisfied weakly by `W = ρ u` against the Haar measure: the mollifications
`vₙ = ρₙ ⋆ (η W)` satisfy the same equation with `ρₙ ⋆ (η W ∇U)` in place of `W ∇U`, the
Caccioppoli estimate applied to `vₙ - vₖ` shows that `χ ∇vₙ` is Cauchy in `L²(m)`, and the
`C¹` compactly supported functions `χ vₙ / ρ` are then a graph-Cauchy sequence of tests converging
to `[χ u]` in `L²(ν)`; closedness of `Tbar` concludes. No classical derivative of `u` is used.

The proof follows this order: localize the density-weighted class and its drift;
mollify their weak equation; apply Caccioppoli to differences; obtain a Cauchy
sequence of gradients; pass to the closed operator graph. The weighted L² limit
is supplied by `localized_toLp_tendsto`. -/
theorem toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : Lp ℝ 2 (ν : Measure V))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : Lp ℝ 2 (ν : Measure V)), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : Lp ℝ 2 (ν : Measure V)), u⟫ = 0)
    {χ : V → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by
  classical
  -- the density, its inverse and their regularity

  -- Localize the weighted equation and its inverse density.
  have hρpos : ∀ x, 0 < tiltedDensity m U x := tiltedDensity_pos m hνU
  have hρc : ContDiff ℝ 1 (tiltedDensity m U) := contDiff_tiltedDensity m hU
  set ρinv : V → ℝ := fun x => (∫ y, Real.exp ((-U) y) ∂m) * Real.exp (U x) with hρinv_def
  have hρρinv : ∀ x, tiltedDensity m U x * ρinv x = 1 := tiltedDensity_mul_exp m hνU
  have hρinvc : ContDiff ℝ 1 ρinv := contDiff_const.mul hU.exp
  have hρinvd : Differentiable ℝ ρinv := hρinvc.differentiable one_ne_zero
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hχd : Differentiable ℝ χ := hχ1.differentiable one_ne_zero
  have hUc : Continuous (gradient U) := continuous_gradient hU
  have hmν : m ≪ (ν : Measure V) := by
    rw [hνU]; exact absolutelyContinuous_tilted (integrable_exp_neg m hνU)
  have hum : AEStronglyMeasurable (u : V → ℝ) m := (Lp.aestronglyMeasurable u).mono_ac hmν
  -- the radius and the cutoff `η`, equal to one on `closedBall 0 (R + 1)`
  obtain ⟨R, hR0, hR⟩ := hχc.isBounded.subset_closedBall_lt 0 0
  set η : ContDiffBump (0 : V) := ⟨R + 1, R + 2, by linarith, by linarith⟩ with hη_def
  have hηχ : ∀ x ∈ tsupport χ, η x = 1 := fun x hx =>
    η.one_of_mem_closedBall (closedBall_subset_closedBall (by linarith) (hR hx))
  have hηzero : ∀ x ∉ closedBall (0 : V) (R + 2), η x = 0 := fun x hx => by
    refine η.zero_of_le_dist ?_
    rw [mem_closedBall, not_le] at hx
    exact hx.le
  -- the density-weighted class and its localizations
  set W : V → ℝ := fun x => tiltedDensity m U x * u x with hW_def
  set w : V → ℝ := fun x => η x * W x with hw_def
  set G : V → V := fun x => (η x * W x) • gradient U x with hG_def
  have hWm : AEStronglyMeasurable W m := hρc.continuous.aestronglyMeasurable.mul hum
  have hwm : AEStronglyMeasurable w m := η.continuous.aestronglyMeasurable.mul hWm
  have hGm : AEStronglyMeasurable G m :=
    (η.continuous.aestronglyMeasurable.mul hWm).smul hUc.aestronglyMeasurable
  have hufin : eLpNorm (u : V → ℝ) 2 (ν : Measure V) < ⊤ := (Lp.memLp u).eLpNorm_lt_top
  have hnorm_u : ∀ x, ‖(u : V → ℝ) x‖ ^ 2 = (u x) ^ 2 := fun x => by
    rw [Real.norm_eq_abs, sq_abs]
  obtain ⟨C₁, hC₁⟩ := (η.continuous.mul (η.continuous.mul
    hρc.continuous)).bounded_above_of_compact_support η.hasCompactSupport.mul_right
  have hwL : MemLp w 2 m := by
    refine lt_of_le_of_lt (eLpNorm_le_tilted_of_sq_le m hνU (C := max C₁ 0)
      (le_max_right _ _) u hwm fun x => ?_) ?_
    · have h1 : η x * (η x * tiltedDensity m U x) ≤ max C₁ 0 :=
        (le_abs_self _).trans ((hC₁ x).trans (le_max_left _ _))
      have h2 : 0 ≤ tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2 :=
        mul_nonneg (hρpos x).le (sq_nonneg _)
      calc ‖w x‖ ^ 2 = (η x * (η x * tiltedDensity m U x)) *
            (tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2) := by
            simp only [hw_def, hW_def, Real.norm_eq_abs, sq_abs]; ring
        _ ≤ max C₁ 0 * (tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = max C₁ 0 * tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2 := by ring
    · exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        ENNReal.ofReal_ne_top) hufin
  obtain ⟨C₂, hC₂⟩ := ((η.continuous.mul (η.continuous.mul hρc.continuous)).mul
    (hUc.norm.pow 2)).bounded_above_of_compact_support (η.hasCompactSupport.mul_right.mul_right)
  have hGL : MemLp G 2 m := by
    refine lt_of_le_of_lt (eLpNorm_le_tilted_of_sq_le m hνU (C := max C₂ 0)
      (le_max_right _ _) u hGm fun x => ?_) ?_
    · have h1 : η x * (η x * tiltedDensity m U x) * ‖gradient U x‖ ^ 2 ≤ max C₂ 0 :=
        (le_abs_self _).trans ((hC₂ x).trans (le_max_left _ _))
      have h2 : 0 ≤ tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2 :=
        mul_nonneg (hρpos x).le (sq_nonneg _)
      calc ‖G x‖ ^ 2 = (η x * (η x * tiltedDensity m U x) * ‖gradient U x‖ ^ 2) *
            (tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2) := by
            simp only [hG_def, hW_def, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
        _ ≤ max C₂ 0 * (tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = max C₂ 0 * tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2 := by ring
    · exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        ENNReal.ofReal_ne_top) hufin
  have hwsupp : ∀ x ∉ closedBall (0 : V) (R + 2), w x = 0 := fun x hx => by
    simp only [hw_def, hηzero x hx, zero_mul]
  have hGsupp : ∀ x ∉ closedBall (0 : V) (R + 2), G x = 0 := fun x hx => by
    simp only [hG_def, hηzero x hx, zero_mul, zero_smul]
  have hwI : Integrable w m := memLp_one_iff_integrable.mp
    (hwL.mono_exponent_of_measure_support_ne_top hwsupp measure_closedBall_lt_top.ne one_le_two)
  have hGI : Integrable G m := memLp_one_iff_integrable.mp
    (hGL.mono_exponent_of_measure_support_ne_top hGsupp measure_closedBall_lt_top.ne one_le_two)
  -- the weak equation for `W`
  have hW : ∀ f : V → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ x, Laplacian.laplacian f x * W x ∂m =
        ∫ x, ⟪gradient f x, W x • gradient U x⟫ ∂m + ∫ x, f x * W x ∂m :=
    fun f hf hfc => hν.integral_laplacian_mul_tiltedDensity_mul m hi hνU hU u horth hf hfc
  -- the mollified sequence

  -- Mollify the localized weak equation.
  set v : ℕ → V → ℝ := fun n =>
    (mollifier (V := V) n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] w with hv_def
  set H : ℕ → V → V := fun n =>
    (mollifier (V := V) n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] G with hH_def
  have hvs : ∀ n, ContDiff ℝ ∞ (v n) := fun n =>
    HasCompactSupport.contDiff_convolution_left _
      ((mollifier (V := V) n).hasCompactSupport_normed (μ := m))
      (mollifier (V := V) n).contDiff_normed hwI.locallyIntegrable
  have hv1 : ∀ n, ContDiff ℝ 1 (v n) := fun n => (hvs n).of_le (WithTop.coe_le_coe.mpr le_top)
  have hvd : ∀ n, Differentiable ℝ (v n) := fun n => (hv1 n).differentiable one_ne_zero
  have hHc : ∀ n, Continuous (H n) := fun n => continuous_convolution _ hGI.locallyIntegrable
  have hvL : ∀ n, MemLp (v n) 2 m := fun n => memLp_convolution _ hwL
  have hHL : ∀ n, MemLp (H n) 2 m := fun n => memLp_convolution _ hGL
  have hvconv : Tendsto (fun n => eLpNorm (v n - w) 2 m) atTop (𝓝 0) :=
    tendsto_eLpNorm_convolution_sub tendsto_mollifier_rOut hwL
  have hHconv : Tendsto (fun n => eLpNorm (H n - G) 2 m) atTop (𝓝 0) :=
    tendsto_eLpNorm_convolution_sub tendsto_mollifier_rOut hGL
  -- the mollified weak equation, and its version for differences
  have hmoll : ∀ n (g : V → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ tsupport χ →
      ∫ x, Laplacian.laplacian g x * v n x ∂m =
        ∫ x, ⟪gradient g x, H n x⟫ ∂m + ∫ x, g x * v n x ∂m := fun n g hg hgc hgs =>
    integral_laplacian_mul_convolution_eq m hW η le_rfl hwI hGI (mollifier (V := V) n)
      (mollifier_rOut_le_one n) hg hgc (hgs.trans hR)
  have hcacc := mollified_difference_caccioppoli m hχ hχc v H hvs hHc hmoll
  -- the bounds on the cutoff and the density on the support of `χ`
  obtain ⟨M₁, hM₁⟩ := (continuous_gradient hχ1).bounded_above_of_compact_support
    (hasCompactSupport_gradient hχc)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  obtain ⟨M₂, hM₂⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  obtain ⟨C₃, hC₃⟩ := (isCompact_closedBall (0 : V) R).exists_bound_of_continuousOn
    hρc.continuous.continuousOn
  obtain ⟨C₄, hC₄⟩ := (isCompact_closedBall (0 : V) R).exists_bound_of_continuousOn
    hρinvc.continuous.continuousOn
  have hC₄0 : 0 ≤ C₄ := (norm_nonneg _).trans (hC₄ 0 (mem_closedBall_self hR0.le))
  obtain ⟨M₅, hM₅⟩ := (hχ.continuous.mul hρinvc.continuous).bounded_above_of_compact_support
    hχc.mul_right
  have hM₅0 : 0 ≤ M₅ := (norm_nonneg _).trans (hM₅ 0)
  obtain ⟨M₆, hM₆⟩ := (hχ.continuous.smul (continuous_gradient
    hρinvc)).bounded_above_of_compact_support hχc.smul_right
  have hM₆0 : 0 ≤ M₆ := (norm_nonneg _).trans (hM₆ 0)
  have hρle : ∀ x ∈ tsupport χ, tiltedDensity m U x ≤ C₃ := fun x hx =>
    (le_abs_self _).trans (hC₃ x (hR hx))
  have hρinvle : ∀ x ∈ tsupport χ, ‖ρinv x‖ ≤ C₄ := fun x hx => hC₄ x (hR hx)
  have hgradχ : ∀ x ∉ tsupport χ, gradient χ x = 0 := fun x hx =>
    Analysis.BakryEmery.gradient_eq_zero_of_notMem_tsupport hx
  -- the tests `gₙ = χ vₙ / ρ`

  -- Construct compactly supported tests in the operator domain.
  set gfun : ℕ → V → ℝ := fun n x => χ x * v n x * ρinv x with hgfun_def
  have hgc1 : ∀ n, ContDiff ℝ 1 (gfun n) := fun n => (hχ1.mul (hv1 n)).mul hρinvc
  have hgcs : ∀ n, HasCompactSupport (gfun n) := fun n => hχc.mul_right.mul_right
  have htest : ∀ n, IsTest ν (ContinuousLinearMap.id ℝ V) (gfun n) := fun n =>
    isTest_of_contDiff_one (hgc1 n) (hgcs n)
  have hmem : ∀ n, (htest n).memLp.toLp (gfun n) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := fun n =>
    hν.toLp_mem_closedWeightedOperator_domain_of_isTest m _ hi (htest n)
  have hgradg : ∀ n x, gradient (gfun n) x = (χ x * v n x) • gradient ρinv x +
      ρinv x • (χ x • gradient (v n) x + v n x • gradient χ x) := by
    intro n x
    have h1 := gradient_mul (f := fun y => χ y * v n y) (g := ρinv) (x := x)
      ((hχd x).mul (hvd n x)) (hρinvd x)
    have h2 := gradient_mul (f := χ) (g := v n) (x := x) (hχd x) (hvd n x)
    refine h1.trans ?_
    rw [h2]
  have hgradsub : ∀ n k x, gradient (gfun n) x - gradient (gfun k) x =
      (χ x * (v n - v k) x) • gradient ρinv x + ρinv x • (χ x • gradient (v n - v k) x) +
        ρinv x • ((v n - v k) x • gradient χ x) := by
    intro n k x
    have hs : gradient (v n - v k) x = gradient (v n) x - gradient (v k) x :=
      gradient_sub (hvd n x) (hvd k x)
    rw [hgradg, hgradg, hs, Pi.sub_apply]
    module
  -- the sequence `Tbar [gₙ] = [∇gₙ]` and its Cauchy property
  have hY : ∀ n, hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem n⟩ =
      (htest n).memLp_apply.toLp (apply (ContinuousLinearMap.id ℝ V) (gfun n)) := fun n =>
    hν.closedWeightedOperator_apply_toLp m _ hi (htest n)
  have hdist : ∀ n k, dist (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
      ⟨_, hmem n⟩) (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem k⟩) =
      (eLpNorm (fun x => gradient (gfun n) x - gradient (gfun k) x) 2 (ν : Measure V)).toReal := by
    intro n k
    rw [hY, hY, Lp.dist_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [(htest n).memLp_apply.coeFn_toLp, (htest k).memLp_apply.coeFn_toLp]
      with x e1 e2
    rw [Pi.sub_apply, e1, e2, apply_id, apply_id]
  -- the three pieces of `∇gₙ - ∇gₖ`
  set K₀ : ℝ≥0∞ := ENNReal.ofReal C₃ ^ (1 / 2 : ℝ) with hK₀_def
  set K₁ : ℝ≥0∞ := ENNReal.ofReal M₆ + ENNReal.ofReal C₄ * (3 * ENNReal.ofReal M₁) +
    ENNReal.ofReal (C₄ * M₁) with hK₁_def
  set K₂ : ℝ≥0∞ := ENNReal.ofReal C₄ * (2 * ENNReal.ofReal M₂) with hK₂_def
  have hK₀ : K₀ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hK₁ : K₁ ≠ ⊤ := by
    simp only [hK₁_def]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        ENNReal.ofReal_ne_top)⟩, ENNReal.ofReal_ne_top⟩
  have hK₂ : K₂ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)

  -- Bound the gradient differences and prove the operator images are Cauchy.
  have hbound : ∀ n k, eLpNorm (fun x => gradient (gfun n) x - gradient (gfun k) x) 2
      (ν : Measure V) ≤ K₀ * (K₁ * eLpNorm (v n - v k) 2 m + K₂ * eLpNorm (H n - H k) 2 m) := by
    intro n k
    set d : V → ℝ := v n - v k with hd_def
    set Hd : V → V := H n - H k with hHd_def
    have hdc : Continuous d := ((hvs n).sub (hvs k)).continuous
    have hdgc : Continuous (gradient d) :=
      continuous_gradient (((hvs n).sub (hvs k)).of_le (WithTop.coe_le_coe.mpr le_top))
    have hHdc : Continuous Hd := (hHc n).sub (hHc k)
    set P₁ : V → V := fun x => (χ x * d x) • gradient ρinv x with hP₁_def
    set P₂ : V → V := fun x => ρinv x • (χ x • gradient d x) with hP₂_def
    set P₃ : V → V := fun x => ρinv x • (d x • gradient χ x) with hP₃_def
    have hP₁m : AEStronglyMeasurable P₁ m :=
      ((hχ.continuous.mul hdc).smul (continuous_gradient hρinvc)).aestronglyMeasurable
    have hP₂m : AEStronglyMeasurable P₂ m :=
      (hρinvc.continuous.smul (hχ.continuous.smul hdgc)).aestronglyMeasurable
    have hP₃m : AEStronglyMeasurable P₃ m :=
      (hρinvc.continuous.smul (hdc.smul (continuous_gradient hχ1))).aestronglyMeasurable
    have hsum : (fun x => gradient (gfun n) x - gradient (gfun k) x) = P₁ + P₂ + P₃ := by
      funext x
      simp only [Pi.add_apply, hP₁_def, hP₂_def, hP₃_def, hd_def]
      exact hgradsub n k x
    -- outside the support of `χ` all three pieces vanish
    have hzero : ∀ x ∉ tsupport χ, gradient (gfun n) x - gradient (gfun k) x = 0 := by
      intro x hx
      rw [hgradsub, image_eq_zero_of_notMem_tsupport hx, hgradχ x hx]
      simp
    -- the transfer to `ν`
    have hν_le : eLpNorm (fun x => gradient (gfun n) x - gradient (gfun k) x) 2 (ν : Measure V) ≤
        K₀ * eLpNorm (fun x => gradient (gfun n) x - gradient (gfun k) x) 2 m := by
      refine eLpNorm_tilted_le m hνU fun x hx => hρle x ?_
      by_contra hx'
      exact hx (hzero x hx')
    -- the three pieces in `L²(m)`
    have h₁ : eLpNorm P₁ 2 m ≤ ENNReal.ofReal M₆ * eLpNorm d 2 m := by
      refine eLpNorm_le_of_norm_le m hM₆0 hP₁m fun x => ?_
      change ‖(χ x * d x) • gradient ρinv x‖ ≤ M₆ * ‖d x‖
      rw [mul_comm (χ x), mul_smul, norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM₆ x) (norm_nonneg _)
    have h₂ : eLpNorm P₂ 2 m ≤ ENNReal.ofReal C₄ * eLpNorm (fun x => χ x • gradient d x) 2 m := by
      refine eLpNorm_le_of_norm_le m hC₄0 hP₂m fun x => ?_
      simp only [hP₂_def]
      rw [norm_smul]
      by_cases hx : x ∈ tsupport χ
      · exact mul_le_mul_of_nonneg_right (hρinvle x hx) (norm_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul, norm_zero, mul_zero, mul_zero]
    have h₃ : eLpNorm P₃ 2 m ≤ ENNReal.ofReal (C₄ * M₁) * eLpNorm d 2 m := by
      refine eLpNorm_le_of_norm_le m (mul_nonneg hC₄0 hM₁0) hP₃m fun x => ?_
      simp only [hP₃_def]
      rw [norm_smul, norm_smul]
      by_cases hx : x ∈ tsupport χ
      · calc ‖ρinv x‖ * (‖d x‖ * ‖gradient χ x‖) ≤ C₄ * (‖d x‖ * M₁) := by
              gcongr
              · exact hρinvle x hx
              · exact hM₁ x
          _ = C₄ * M₁ * ‖d x‖ := by ring
      · rw [hgradχ x hx, norm_zero, mul_zero, mul_zero]
        positivity
    have hBd : eLpNorm (fun x => d x • gradient χ x) 2 m ≤ ENNReal.ofReal M₁ * eLpNorm d 2 m := by
      refine eLpNorm_le_of_norm_le m hM₁0
        (hdc.smul (continuous_gradient hχ1)).aestronglyMeasurable fun x => ?_
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM₁ x) (norm_nonneg _)
    have hCd : eLpNorm (fun x => χ x • Hd x) 2 m ≤ ENNReal.ofReal M₂ * eLpNorm Hd 2 m := by
      refine eLpNorm_le_of_norm_le m hM₂0 (hχ.continuous.smul hHdc).aestronglyMeasurable
        fun x => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hM₂ x) (norm_nonneg _)
    have hcac := hcacc n k
    calc eLpNorm (fun x => gradient (gfun n) x - gradient (gfun k) x) 2 (ν : Measure V)
        ≤ K₀ * eLpNorm (fun x => gradient (gfun n) x - gradient (gfun k) x) 2 m := hν_le
      _ ≤ K₀ * (eLpNorm P₁ 2 m + eLpNorm P₂ 2 m + eLpNorm P₃ 2 m) := by
          gcongr
          rw [hsum]
          exact (eLpNorm_add_le one_le_two).trans
            (add_le_add_left (eLpNorm_add_le one_le_two) _)
      _ ≤ K₀ * (ENNReal.ofReal M₆ * eLpNorm d 2 m +
            ENNReal.ofReal C₄ * (3 * (ENNReal.ofReal M₁ * eLpNorm d 2 m) +
              2 * (ENNReal.ofReal M₂ * eLpNorm Hd 2 m)) +
            ENNReal.ofReal (C₄ * M₁) * eLpNorm d 2 m) := by
          gcongr
          refine h₂.trans ?_
          gcongr
          exact hcac.trans (by gcongr)
      _ = K₀ * (K₁ * eLpNorm d 2 m + K₂ * eLpNorm Hd 2 m) := by
          simp only [hK₁_def, hK₂_def]
          ring
  -- the bound tends to zero along `atTop` on pairs
  have hfst : Tendsto (fun p : ℕ × ℕ => p.1) atTop atTop := by
    rw [← Filter.prod_atTop_atTop_eq]; exact tendsto_fst
  have hsnd : Tendsto (fun p : ℕ × ℕ => p.2) atTop atTop := by
    rw [← Filter.prod_atTop_atTop_eq]; exact tendsto_snd
  have hvw : ∀ n, eLpNorm (v n - w) 2 m ≠ ⊤ := fun n => ((hvL n).sub hwL).eLpNorm_lt_top.ne
  have hHG : ∀ n, eLpNorm (H n - G) 2 m ≠ ⊤ := fun n => ((hHL n).sub hGL).eLpNorm_lt_top.ne
  set B : ℕ × ℕ → ℝ≥0∞ := fun p => K₀ * (K₁ * (eLpNorm (v p.1 - w) 2 m + eLpNorm (v p.2 - w) 2 m)
    + K₂ * (eLpNorm (H p.1 - G) 2 m + eLpNorm (H p.2 - G) 2 m)) with hB_def
  have hBfin : ∀ p, B p ≠ ⊤ := fun p =>
    ENNReal.mul_ne_top hK₀ (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top hK₁ (ENNReal.add_ne_top.mpr ⟨hvw _, hvw _⟩),
        ENNReal.mul_ne_top hK₂ (ENNReal.add_ne_top.mpr ⟨hHG _, hHG _⟩)⟩)
  have hBlim : Tendsto B atTop (𝓝 0) := by
    have h1 : Tendsto (fun p : ℕ × ℕ => eLpNorm (v p.1 - w) 2 m + eLpNorm (v p.2 - w) 2 m) atTop
        (𝓝 (0 + 0)) := (hvconv.comp hfst).add (hvconv.comp hsnd)
    have h2 : Tendsto (fun p : ℕ × ℕ => eLpNorm (H p.1 - G) 2 m + eLpNorm (H p.2 - G) 2 m) atTop
        (𝓝 (0 + 0)) := (hHconv.comp hfst).add (hHconv.comp hsnd)
    rw [add_zero] at h1 h2
    have h3 := (ENNReal.Tendsto.const_mul h1 (Or.inr hK₁)).add
      (ENNReal.Tendsto.const_mul h2 (Or.inr hK₂))
    rw [mul_zero, mul_zero, add_zero] at h3
    have h4 := ENNReal.Tendsto.const_mul h3 (Or.inr hK₀)
    rw [mul_zero] at h4
    exact h4
  have hdist_le : ∀ p : ℕ × ℕ, dist (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
      ⟨_, hmem p.1⟩) (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem p.2⟩)
      ≤ (B p).toReal := by
    intro p
    rw [hdist]
    refine ENNReal.toReal_mono (hBfin p) ((hbound p.1 p.2).trans ?_)
    simp only [hB_def]
    gcongr
    · have : v p.1 - v p.2 = (v p.1 - w) - (v p.2 - w) := by abel
      rw [this]
      exact eLpNorm_sub_le one_le_two
    · have : H p.1 - H p.2 = (H p.1 - G) - (H p.2 - G) := by abel
      rw [this]
      exact eLpNorm_sub_le one_le_two
  have hcauchy : CauchySeq fun n =>
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem n⟩ := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    refine squeeze_zero (fun _ => dist_nonneg) hdist_le ?_
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hBlim
    rw [ENNReal.toReal_zero] at this
    exact this

  -- Use closedness to recover the original localized function in the domain.
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- convergence `[gₙ] → [χ u]` in `L²(ν)`
  have hgu : ∀ n x, gfun n x - χ x * u x = (χ x * ρinv x) * (v n - w) x := by
    intro n x
    by_cases hx : x ∈ tsupport χ
    · simp only [hgfun_def, hw_def, hW_def, Pi.sub_apply, hηχ x hx, one_mul]
      linear_combination (χ x * u x) * hρρinv x
    · simp [hgfun_def, image_eq_zero_of_notMem_tsupport hx]
  have hxa : Tendsto (fun n => (htest n).memLp.toLp (gfun n)) atTop
      (𝓝 ((memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _)) := by
    exact localized_toLp_tendsto m hνU hχ hχc u (fun n => (htest n).memLp) hgu
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])
      hM₅0 hM₅ hρle hvconv
  obtain ⟨hmem', -⟩ := exists_mem_domain_apply_eq_of_tendsto
    (hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi) hmem hxa hb
  exact hmem'

/-- **`C_c^∞(V)` is an operator core of the generator `A = Tbar†Tbar`.** For `ν = m.tilted (-U)` with
a `C¹` potential and unit weight, every `F ∈ D(A)` is the limit of smooth compactly supported
classes in the graph norm of `A`: there are `fₙ ∈ C_c^∞(V)` with `[fₙ] → F` and `A [fₙ] → A F` in
`L²(ν)`. Equivalently, `ℒ = Δ - ⟪∇U, ∇·⟫` is essentially self-adjoint on `C_c^∞(V)` in `L²(ν)`.

This is the operator-core criterion `exists_seq_smooth_tendsto_adjointComp_of_localRegularity`
with its hypothesis discharged by `toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`; it
is exactly the hypothesis `hcore` of `HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core`.
No convexity of `U`, no semigroup and no `Γ₂` input is used. -/
theorem exists_seq_smooth_tendsto_adjointComp
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (F : ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - (F : (Lp ℝ 2 (ν : Measure V)))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖((adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n)
          (hfnc n)⟩ : (Lp ℝ 2 (ν : Measure V))) - ((adjointComp
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
              (ν : Measure V)))‖) atTop (𝓝 0) :=
  hν.exists_seq_smooth_tendsto_adjointComp_of_localRegularity m hi hνU hU
    (fun u horth _χ hχ hχc =>
      hν.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal m hi hνU hU u horth hχ hχc) F

end Tilted

end FunctionalInequalities.KLS.LogConcave
