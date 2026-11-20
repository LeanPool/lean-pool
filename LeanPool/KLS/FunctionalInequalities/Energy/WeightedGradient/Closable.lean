/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Domination.Local
public import LeanPool.KLS.FunctionalInequalities.Energy.WeightedGradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.WeakDerivative
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Closability of the weighted gradient operator

Source: Blueprint `lem:covariance-core-closure`, closability part. Read
`Probability.LocallyDominates`, the local comparison lemmas, and
`KLS.LogConcave.weightedOperator_isClosable`.

The hypothesis on the law `ν` is stated without densities: `ν` is absolutely continuous with
respect to a Haar measure `m`, the frontier of its support is `ν`-null, and on every compact subset
of the interior `Ω` of the support the Haar measure is dominated by a constant multiple of `ν`
(`Probability.LocallyDominates ν m`). For a log-concave law these follow from the Borell density
representative, which is bounded below by a positive constant on such compact sets; that
instantiation is in `KLS/LogConcave/WeightedGradient/Basic.lean`.

Proof. If `[g_j] → 0` in `L²(ν)` and `[B ∇g_j] → y` in `L²(ν; V)`, fix `φ ∈ C_c^∞` with support
in `Ω`. Local domination turns `L²(ν)` convergence into `L¹(m)` convergence on the support of
`φ`, so `∫ φ • y dm = lim ∫ φ • B ∇g_j dm = B (lim ∫ φ • ∇g_j dm)`. The weak-derivative identity
of `Energy/Euclidean/WeakDerivative.lean` gives
`‖∫ φ • ∇g_j dm‖ ≤ ∫ ‖g_j‖ ‖Dφ‖ dm → 0`. Hence `∫ φ • y dm = 0`
for every such `φ`, so `y = 0` almost everywhere on `Ω` for `m`, hence for `ν`; the complement of
`Ω` is `ν`-null. Thus the closure of the graph is a graph.

This module does not prove density of the domain, the core identification, or any Poincaré
statement; those are separate modules.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.Energy.WeightedGradient

universe u v

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]



open Energy.Euclidean

open Probability

section LocalComparison

variable {ν : ProbabilityMeasure V} {m : Measure V}

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V]
    [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- On a probability space, the `L¹` norm over any set is bounded by the `L²` norm. -/
theorem lintegral_enorm_restrict_le_eLpNorm {W : Type*} [NormedAddCommGroup W] {u : V → W}
    (hu : AEStronglyMeasurable u (ν : Measure V)) (K : Set V) :
    ∫⁻ x in K, ‖u x‖ₑ ∂(ν : Measure V) ≤ eLpNorm u 2 (ν : Measure V) := by
  calc
    ∫⁻ x in K, ‖u x‖ₑ ∂(ν : Measure V) ≤ ∫⁻ x, ‖u x‖ₑ ∂(ν : Measure V) :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = eLpNorm u 1 (ν : Measure V) := (eLpNorm_one_eq_lintegral_eNorm hu).symm
    _ ≤
        eLpNorm u 2 (ν : Measure V) *
          (ν : Measure V) Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hu
    _ = eLpNorm u 2 (ν : Measure V) := by simp

section LocalIntegrability

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V]
/-- Local domination bounds the `L¹(m)` norm over a compact subset of the interior by the
`L²(ν)` norm. -/
theorem exists_lintegral_enorm_restrict_le (W : Type v) [NormedAddCommGroup W]
    {Ω : Set V} (h : LocallyDominatesOn ν m Ω) {K : Set V}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (u : V → W),
      AEStronglyMeasurable u (ν : Measure V) →
      ∫⁻ x in K, ‖u x‖ₑ ∂m ≤ (C : ℝ≥0∞) * eLpNorm u 2 (ν : Measure V) := by
  obtain ⟨C, hC⟩ := h.exists_lintegral_le hK hKΩ
  refine ⟨C, fun u hu ↦ ?_⟩
  exact (hC fun x ↦ ‖u x‖ₑ).trans
    (mul_le_mul' le_rfl (lintegral_enorm_restrict_le_eLpNorm hu K))

/-- A square-integrable function for `ν` is integrable for `m` on compact subsets of the
interior of the support. -/
theorem integrableOn_of_locallyDominates {Ω : Set V} (h : LocallyDominatesOn ν m Ω) {K : Set V}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {W : Type v} [NormedAddCommGroup W] {u : V → W} (hu : StronglyMeasurable u)
    (hu2 : eLpNorm u 2 (ν : Measure V) ≠ ⊤) : IntegrableOn u K m := by
  obtain ⟨C, hC⟩ := exists_lintegral_enorm_restrict_le W h hK hKΩ
  refine ⟨hu.aestronglyMeasurable, ?_⟩
  change ∫⁻ x in K, ‖u x‖ₑ ∂m < ⊤
  exact (hC u hu.aestronglyMeasurable).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hu2.lt_top)

end LocalIntegrability

section NormedSpace

variable (W : Type v)
  [NormedAddCommGroup W] [NormedSpace ℝ W]

section LocalIntegralBounds

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- The lower integral of a bounded test times a square-integrable function, when the test
vanishes outside a compact subset of the interior. -/
theorem lintegral_enorm_smul_le
    {Ω : Set V} (h : LocallyDominatesOn ν m Ω) {K : Set V} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (ψ : V → ℝ) (M : ℝ≥0), (∀ x, ‖ψ x‖₊ ≤ M) → (∀ x, x ∉ K → ψ x = 0) →
      ∀ (u : V → W), AEStronglyMeasurable u (ν : Measure V) →
      ∫⁻ x, ‖ψ x • u x‖ₑ ∂m ≤ (M : ℝ≥0∞) * ((C : ℝ≥0∞) * eLpNorm u 2 (ν : Measure V)) := by
  obtain ⟨C, hC⟩ := exists_lintegral_enorm_restrict_le W h hK hKΩ
  refine ⟨C, fun ψ M hM hψ u hu ↦ ?_⟩
  have hpt : ∀ x, ‖ψ x • u x‖ₑ ≤ K.indicator (fun x ↦ (M : ℝ≥0∞) * ‖u x‖ₑ) x := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, eNorm_smul]
      gcongr
      rw [eNorm_eq_nnNorm]
      exact_mod_cast hM x
    · rw [Set.indicator_of_notMem hx, hψ x hx, zero_smul, eNorm_zero]
  calc ∫⁻ x, ‖ψ x • u x‖ₑ ∂m ≤ ∫⁻ x, K.indicator (fun x ↦ (M : ℝ≥0∞) * ‖u x‖ₑ) x ∂m :=
        lintegral_mono hpt
    _ = ∫⁻ x in K, (M : ℝ≥0∞) * ‖u x‖ₑ ∂m := lintegral_indicator hK.measurableSet _
    _ = (M : ℝ≥0∞) * ∫⁻ x in K, ‖u x‖ₑ ∂m := lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ (M : ℝ≥0∞) * ((C : ℝ≥0∞) * eLpNorm u 2 (ν : Measure V)) := by
        gcongr
        exact hC u hu

/-- Integrability of a bounded test times a square-integrable function, and the resulting bound
on the integral, in real form. -/
theorem exists_norm_integral_smul_le
    {Ω : Set V} (h : LocallyDominatesOn ν m Ω) {K : Set V} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (ψ : V → ℝ) (M : ℝ≥0), Measurable ψ → (∀ x, ‖ψ x‖₊ ≤ M) → (∀ x, x ∉ K → ψ x = 0) →
      ∀ (u : V → W), StronglyMeasurable u → eLpNorm u 2 (ν : Measure V) ≠ ⊤ →
      Integrable (fun x ↦ ψ x • u x) m ∧
        ‖∫ x, ψ x • u x ∂m‖ ≤ (M : ℝ) * ((C : ℝ) * (eLpNorm u 2 (ν : Measure V)).toReal) := by
  obtain ⟨C, hC⟩ := lintegral_enorm_smul_le W h hK hKΩ
  refine ⟨C, fun ψ M hψm hM hψ u hu hu2 ↦ ?_⟩
  have hbound := hC ψ M hM hψ u hu.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun x ↦ ψ x • u x) m :=
    (hψm.aestronglyMeasurable).smul hu.aestronglyMeasurable
  have hfin : (M : ℝ≥0∞) * ((C : ℝ≥0∞) * eLpNorm u 2 (ν : Measure V)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hu2)
  refine ⟨⟨hmeas, hbound.trans_lt hfin.lt_top⟩, ?_⟩
  calc ‖∫ x, ψ x • u x ∂m‖ ≤ (∫⁻ x, ENNReal.ofReal ‖ψ x • u x‖ ∂m).toReal :=
        norm_integral_le_lintegral_norm _
    _ = (∫⁻ x, ‖ψ x • u x‖ₑ ∂m).toReal := by simp_rw [ofReal_norm]
    _ ≤ ((M : ℝ≥0∞) * ((C : ℝ≥0∞) * eLpNorm u 2 (ν : Measure V))).toReal :=
        ENNReal.toReal_mono hfin hbound
    _ = (M : ℝ) * ((C : ℝ) * (eLpNorm u 2 (ν : Measure V)).toReal) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]

end LocalIntegralBounds

end NormedSpace

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] in
/-- Functions equal `ν`-almost everywhere give `m`-almost everywhere equal products with a test
vanishing outside a compact subset of the interior. -/
theorem smul_ae_eq_of_ae_eq {Ω : Set V} (h : LocallyDominatesOn ν m Ω) {K : Set V}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {ψ : V → ℝ} (hψ : ∀ x, x ∉ K → ψ x = 0) {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] {u₁ u₂ : V → W} (hu : u₁ =ᵐ[(ν : Measure V)] u₂) :
    (fun x ↦ ψ x • u₁ x) =ᵐ[m] fun x ↦ ψ x • u₂ x := by
  have hs : (ν : Measure V) {x | u₁ x ≠ u₂ x} = 0 := hu
  have hm := h.measure_inter_eq_zero hK hKΩ hs
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null ?_ hm
  intro x hx
  by_cases hxK : x ∈ K
  · exact ⟨fun heq ↦ hx (by simp [heq]), hxK⟩
  · exact absurd (by simp [hψ x hxK]) hx

end LocalComparison

section WeakLimit

variable (m : Measure V) [m.IsAddHaarMeasure]

/-- The `φ`-weighted integral of the gradient of a Lipschitz function is controlled by the
function itself against the derivative of `φ`: the quantitative form of the weak-derivative
identity. -/
theorem norm_integral_smul_gradient_le {g : V → ℝ} {K₀ : ℝ≥0} (hg : LipschitzWith K₀ g)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) :
    ‖∫ x, φ x • gradient g x ∂m‖ ≤ ∫ x, ‖g x‖ * ‖fderiv ℝ φ x‖ ∂m := by
  set wv := ∫ x, φ x • gradient g x ∂m with hwv
  have hint : Integrable (fun x ↦ φ x • gradient g x) m := by
    refine
      Integrable.mono'
        ((hφ.continuous.norm.mul continuous_const).integrable_of_hasCompactSupport
          (hφs.norm.mul_right (f' := fun _ ↦ (K₀ : ℝ))))
        ?_ (Eventually.of_forall fun x ↦ ?_)
    · exact
        (hφ.continuous.measurable.smul
            (LipschitzApproximation.measurable_gradient g)) |>.aestronglyMeasurable
    · change ‖φ x • gradient g x‖ ≤ ‖φ x‖ * (K₀ : ℝ)
      rw [norm_smul]
      gcongr
      exact LipschitzApproximation.norm_gradient_le_of_lipschitz hg x
  have hDφ : Integrable (fun x ↦ ‖g x‖ * ‖fderiv ℝ φ x‖) m :=
    (hg.continuous.norm.mul
          (hφ.continuous_fderiv (by simp)).norm).integrable_of_hasCompactSupport
      ((hφs.fderiv ℝ).norm.mul_left)
  have hsq : ‖wv‖ ^ 2 ≤ ‖wv‖ * ∫ x, ‖g x‖ * ‖fderiv ℝ φ x‖ ∂m := by
    have h1 : ‖wv‖ ^ 2 = ∫ x, φ x * inner ℝ (gradient g x) wv ∂m := by
      calc
        ‖wv‖ ^ 2 = inner ℝ wv wv := (real_inner_self_eq_norm_sq wv).symm
        _ = inner ℝ wv (∫ x, φ x • gradient g x ∂m) := by rw [← hwv]
        _ = ∫ x, inner ℝ wv (φ x • gradient g x) ∂m := (integral_inner hint wv).symm
        _ = ∫ x, φ x * inner ℝ (gradient g x) wv ∂m := by
          refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
          change inner ℝ wv (φ x • gradient g x) = φ x * inner ℝ (gradient g x) wv
          rw [inner_smul_right, real_inner_comm]
    have h2 := integral_mul_inner_gradient m hg hφ hφs wv
    rw [h1, h2]
    calc
      -∫ x, g x * fderiv ℝ φ x wv ∂m ≤ ‖∫ x, g x * fderiv ℝ φ x wv ∂m‖ := by
        rw [Real.norm_eq_abs]
        exact neg_le_abs _
      _ ≤ ∫ x, ‖g x * fderiv ℝ φ x wv‖ ∂m := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖wv‖ * (‖g x‖ * ‖fderiv ℝ φ x‖) ∂m := by
        refine
          integral_mono_of_nonneg (Eventually.of_forall fun x ↦ norm_nonneg _) (hDφ.const_mul _)
            (Eventually.of_forall fun x ↦ ?_)
        change ‖g x * fderiv ℝ φ x wv‖ ≤ ‖wv‖ * (‖g x‖ * ‖fderiv ℝ φ x‖)
        rw [norm_mul]
        calc
          ‖g x‖ * ‖fderiv ℝ φ x wv‖ ≤ ‖g x‖ * (‖fderiv ℝ φ x‖ * ‖wv‖) := by
            gcongr
            exact (fderiv ℝ φ x).le_opNorm wv
          _ = ‖wv‖ * (‖g x‖ * ‖fderiv ℝ φ x‖) := by ring
      _ = ‖wv‖ * ∫ x, ‖g x‖ * ‖fderiv ℝ φ x‖ ∂m := integral_const_mul _ _
  by_cases hw : ‖wv‖ = 0
  · rw [hw]
    exact integral_nonneg fun x ↦ by positivity
  · have hpos : 0 < ‖wv‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
    have := hsq
    rw [sq] at this
    exact le_of_mul_le_mul_left this hpos

end WeakLimit

section Closable

variable (ν : ProbabilityMeasure V) (B : V →L[ℝ] V) {m : Measure V} [m.IsAddHaarMeasure]

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
/-- Almost every point for `ν` lies in the interior of the support when the frontier is null. -/
theorem ae_mem_interior_support (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) :
    ∀ᵐ x ∂(ν : Measure V), x ∈ interior (ν : Measure V).support := by
  filter_upwards [Measure.support_mem_ae (μ := (ν : Measure V)), compl_mem_ae_iff.mpr hfr]
    with x hx hxf
  rw [Measure.isClosed_support.frontier_eq] at hxf
  exact by_contra fun hnot ↦ hxf ⟨hx, hnot⟩

/-- The weighted gradient operator is closable: if `[g_j] → 0` in `L²(ν)` and `[B ∇g_j] → y`
in `L²(ν; V)`, then `y = 0`. The open set `Ω` carries `ν` and `m` is locally dominated by `ν` on
its compact subsets; the frontier of the support is `ν`-null. -/
theorem operator_isClosable_of_isOpen (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {Ω : Set V} (hΩ : IsOpen Ω)
    (hΩν : (ν : Measure V) Ωᶜ = 0) (hloc : LocallyDominatesOn ν m Ω) :
    (operator ν B hac).IsClosable := by
  apply Energy.isClosable_of_graph_closure_snd_eq_zero
  rintro ⟨p₁, y⟩ hp h0
  simp only at h0
  subst h0
  obtain ⟨f, hf⟩ := (Energy.mem_graph_topologicalClosure_iff _ _).mp hp
  have hf1 : Tendsto (fun n ↦ ((f n : Lp ℝ 2 (ν : Measure V)))) atTop (𝓝 0) :=
    (continuous_fst.tendsto _).comp hf
  have hf2 : Tendsto (fun n ↦ operator ν B hac (f n)) atTop (𝓝 y) :=
    (continuous_snd.tendsto _).comp
      hf
  -- concrete representatives
  have hrep :
    ∀ n, ∃ (g : V → ℝ) (h : IsTest ν B g), ((f n : Lp ℝ 2 (ν : Measure V))) = h.memLp.toLp g :=
    fun n ↦ (mem_domain_operator_iff ν B hac _).mp (f n).2
  choose g hg hfg using hrep
  have hTf : ∀ n, operator ν B hac (f n) = (hg n).memLp_apply.toLp (apply B (g n)) := fun n ↦
    operator_apply ν B hac hfr (hg n) (f n).2 (hfg n)
  have hΩo : IsOpen Ω :=
    hΩ
  -- y is locally integrable on Ω
  have hyloc : LocallyIntegrableOn (fun x ↦ (y : V → V) x) Ω m := by
    rw [locallyIntegrableOn_iff ⟨Ω, Set.univ, hΩo, isClosed_univ, (Set.inter_univ _).symm⟩]
    intro k hkΩ hk
    exact
      integrableOn_of_locallyDominates hloc hk hkΩ (Lp.stronglyMeasurable y)
        (Lp.eLpNorm_ne_top y)
  -- the key vanishing of all test integrals
  have hvan :
    ∀ φ : V → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω → ∫ x, φ x • (y : V → V) x ∂m = 0 := by
    intro φ hφ hφs hφΩ
    set K := tsupport φ with hK
    have hKc : IsCompact K := hφs
    have hψ0 : ∀ x, x ∉ K → φ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
    obtain ⟨Mφ, hMφ⟩ := hKc.exists_bound_of_continuousOn hφ.continuous.continuousOn
    obtain ⟨M', hM'0, hM'⟩ :=
      exists_bound_fderiv_of_hasCompactSupport (hφ.of_le (mod_cast le_top)) hφs
    have hMφ' : ∀ x, ‖φ x‖₊ ≤ ⟨max Mφ 0, le_max_right _ _⟩ := by
      intro x
      change ‖φ x‖ ≤ max Mφ 0
      by_cases hx : x ∈ K
      · exact (hMφ x hx).trans (le_max_left _ _)
      · rw [hψ0 x hx, norm_zero]; exact le_max_right _ _
    have hDφ0 : ∀ x, x ∉ K → ‖fderiv ℝ φ x‖ = 0 := by
      intro x hx
      have : fderiv ℝ φ x = 0 := by
        by_contra hne
        exact hx (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
      rw [this, norm_zero]
    have hDφM : ∀ x, ‖(‖fderiv ℝ φ x‖)‖₊ ≤ ⟨M', hM'0⟩ := by
      intro x
      change ‖(‖fderiv ℝ φ x‖)‖ ≤ M'
      rw [norm_norm]
      exact hM' x
    obtain ⟨C, hC⟩ := exists_norm_integral_smul_le V hloc hKc hφΩ
    obtain ⟨C₂, hC₂⟩ :=
      exists_norm_integral_smul_le ℝ hloc hKc
        hφΩ
    -- the integrals against the operator values converge to the integral against y
    have hlim1 :
      Tendsto (fun n ↦ ∫ x, φ x • (operator ν B hac (f n) : V → V) x ∂m) atTop
        (𝓝 (∫ x, φ x • (y : V → V) x ∂m)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hbound :
        ∀ n,
          ‖(∫ x, φ x • (operator ν B hac (f n) : V → V) x ∂m) - ∫ x, φ x • (y : V → V) x ∂m‖ ≤
            ((⟨max Mφ 0, le_max_right _ _⟩ : ℝ≥0) : ℝ) *
              ((C : ℝ) * ‖operator ν B hac (f n) - y‖) := by
        intro n
        obtain ⟨hint_n, -⟩ :=
          hC φ _ hφ.continuous.measurable hMφ' hψ0 (operator ν B hac (f n) : V → V)
            (Lp.stronglyMeasurable _) (Lp.eLpNorm_ne_top _)
        obtain ⟨hint_y, -⟩ :=
          hC φ _ hφ.continuous.measurable hMφ' hψ0 (y : V → V) (Lp.stronglyMeasurable _)
            (Lp.eLpNorm_ne_top _)
        obtain ⟨-, hle⟩ :=
          hC φ _ hφ.continuous.measurable hMφ' hψ0
            ((operator ν B hac (f n) - y : Lp V 2 (ν : Measure V)) : V → V)
            (Lp.stronglyMeasurable _) (Lp.eLpNorm_ne_top _)
        rw [← integral_sub hint_n hint_y]
        have hcongr :
          (fun x ↦ φ x • (operator ν B hac (f n) : V → V) x - φ x • (y : V → V) x) =ᵐ[m] fun x ↦
            φ x • ((operator ν B hac (f n) - y : Lp V 2 (ν : Measure V)) : V → V) x := by
          have h1 :=
            smul_ae_eq_of_ae_eq hloc hKc hφΩ hψ0 (ψ := φ)
              (Lp.coeFn_sub (operator ν B hac (f n)) y)
          filter_upwards [h1] with x hx
          rw [hx, Pi.sub_apply, smul_sub]
        rw [integral_congr_ae hcongr, Lp.norm_def]
        exact hle
      refine squeeze_zero (fun n ↦ norm_nonneg _) hbound ?_
      have : Tendsto (fun n ↦ ‖operator ν B hac (f n) - y‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.mp hf2
      simpa using
        (tendsto_const_nhds.mul (tendsto_const_nhds.mul this))
    -- the integrals against the operator values tend to zero
    have hlim2 :
      Tendsto (fun n ↦ ∫ x, φ x • (operator ν B hac (f n) : V → V) x ∂m) atTop (𝓝 0) := by
      have hval :
        ∀ n,
          ∫ x, φ x • (operator ν B hac (f n) : V → V) x ∂m =
            B (∫ x, φ x • gradient (g n) x ∂m) := by
        intro n
        have h1 :
          (fun x ↦ φ x • (operator ν B hac (f n) : V → V) x) =ᵐ[m] fun x ↦
            φ x • apply B (g n) x := by
          have h0 :
            ((operator ν B hac (f n) : Lp V 2 (ν : Measure V)) : V → V) =ᵐ[(ν : Measure V)]
              apply B (g n) := by
            rw [hTf n]
            exact (hg n).memLp_apply.coeFn_toLp
          exact smul_ae_eq_of_ae_eq hloc hKc hφΩ hψ0 (ψ := φ) h0
        rw [integral_congr_ae h1]
        have hint : Integrable (fun x ↦ φ x • gradient (g n) x) m := by
          obtain ⟨K₀, hK₀⟩ := (hg n).1
          refine
            Integrable.mono'
              ((hφ.continuous.norm.mul continuous_const).integrable_of_hasCompactSupport
                (hφs.norm.mul_right (f' := fun _ ↦ (K₀ : ℝ))))
              ?_ (Eventually.of_forall fun x ↦ ?_)
          · exact
              (hφ.continuous.measurable.smul
                  (LipschitzApproximation.measurable_gradient (g n))) |>.aestronglyMeasurable
          · change ‖φ x • gradient (g n) x‖ ≤ ‖φ x‖ * (K₀ : ℝ)
            rw [norm_smul]
            gcongr
            exact LipschitzApproximation.norm_gradient_le_of_lipschitz hK₀ x
        rw [← B.integral_comp_comm hint]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp [apply]
      have hfun :
        (fun n ↦ ∫ x, φ x • (operator ν B hac (f n) : V → V) x ∂m) = fun n ↦
          B (∫ x, φ x • gradient (g n) x ∂m) :=
        funext hval
      rw [hfun, show (0 : V) = B 0 by simp]
      refine (B.continuous.tendsto 0).comp ?_
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      have hbound :
        ∀ n,
          ‖∫ x, φ x • gradient (g n) x ∂m‖ ≤
            ((⟨M', hM'0⟩ : ℝ≥0) : ℝ) * ((C₂ : ℝ) * ‖(f n : Lp ℝ 2 (ν : Measure V))‖) := by
        intro n
        obtain ⟨K₀, hK₀⟩ := (hg n).1
        refine (norm_integral_smul_gradient_le m hK₀ hφ hφs).trans ?_
        have hg2 : eLpNorm (fun x ↦ ‖g n x‖) 2 (ν : Measure V) ≠ ⊤ := by
          rw [eLpNorm_norm (g n) (hg n).memLp.aestronglyMeasurable]
          exact (hg n).memLp.eLpNorm_ne_top
        obtain ⟨-, hle⟩ :=
          hC₂ (fun x ↦ ‖fderiv ℝ φ x‖) _ (hφ.continuous_fderiv (by simp)).norm.measurable hDφM
            hDφ0 (fun x ↦ ‖g n x‖) (hK₀.continuous.norm.stronglyMeasurable) hg2
        have heq : ∫ x, ‖g n x‖ * ‖fderiv ℝ φ x‖ ∂m = ‖∫ x, ‖fderiv ℝ φ x‖ • ‖g n x‖ ∂m‖ := by
          rw [Real.norm_of_nonneg (integral_nonneg fun x ↦ by positivity)]
          refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
          simp [mul_comm]
        rw [heq]
        refine hle.trans (le_of_eq ?_)
        rw [eLpNorm_norm (g n) (hg n).memLp.aestronglyMeasurable,
          hfg n, Lp.norm_def, eLpNorm_congr_ae (hg n).memLp.coeFn_toLp]
        rfl
      refine squeeze_zero (fun n ↦ norm_nonneg _) hbound ?_
      have : Tendsto (fun n ↦ ‖(f n : Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) := by
        simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hf1)
      simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.mul this))
    exact
      tendsto_nhds_unique hlim1
        hlim2
  -- fundamental lemma on Ω, then transfer to ν
  have hae_m : ∀ᵐ x ∂m, x ∈ Ω → (y : V → V) x = 0 :=
    hΩo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hyloc hvan
  have hae_ν : ∀ᵐ x ∂(ν : Measure V), x ∈ Ω → (y : V → V) x = 0 := hac.ae_le hae_m
  have hΩae : ∀ᵐ x ∂(ν : Measure V), x ∈ Ω := by
    rw [ae_iff]
    exact hΩν
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hae_ν, hΩae] with x hx hxΩ
  exact hx hxΩ

/-- The weighted gradient operator is closable under local domination on the interior of the
support. -/
theorem operator_isClosable (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (hloc : LocallyDominates ν m) : (operator ν B hac).IsClosable := by
  refine operator_isClosable_of_isOpen ν B hac hfr isOpen_interior ?_ hloc
  exact ae_iff.mp (ae_mem_interior_support ν hfr)

end Closable

end FunctionalInequalities.Energy.WeightedGradient
