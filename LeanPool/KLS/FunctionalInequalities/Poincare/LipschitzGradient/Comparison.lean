/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.WeightedGradient.Core
public import LeanPool.KLS.FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison
public import LeanPool.KLS.FunctionalInequalities.Poincare.Relaxation
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Factorization

/-!
# The identity-weighted Lipschitz gradient relaxation and the literature constant

Source: Blueprint `thm:affine-isotropic-reduction`, the passages "pullback of the isotropic
inequality
gives the covariance-form inequality, first on the raw tests and then on their relaxation" and
"item (3) implies item (2) from `⟪Cov v, v⟫ ≤ ‖Cov‖ ‖v‖²`, together with cutoff and truncation from
locally to globally Lipschitz tests". Read `Energy.LipschitzGradient.relaxation`,
`Poincare.LipschitzGradient.holds_iff_localSlope`,
`FunctionalInequalities.Poincare.SmoothTest.constant_eq_lipschitz`,
`Energy.CovarianceGradient.relaxation_eq_lipschitz`
and `Energy.CovarianceGradient.relaxation_le_mul_lipschitz`.

For a probability law `ν` on a finite-dimensional Euclidean space `V` that is absolutely continuous
with respect to Haar measure and has a null support frontier, the sequential relaxation of the
squared-norm energy `f ↦ ‖∇f‖²` of the gradient operator on globally Lipschitz tests (the weighted
gradient operator of `lem:covariance-core-closure` with `B = 1`) has the same finite Poincaré
constants as the locally Lipschitz literature class and the same optimal constant as the legacy
smooth-test constant `Poincare.SmoothTest.constant ν`: one direction relaxes the raw inequality on
Lipschitz
tests, the other approximates a locally Lipschitz literature test by smooth compactly supported
functions in the weighted graph norm (the certified approximation lemma with `B = 1`). When the
covariance operator is the identity the covariance relaxation of `def:affine-poincare-constant` is
this relaxation; in general the covariance relaxation is at most `‖Σ‖` times it.

Nothing here asserts a Poincaré inequality, finiteness of any constant, or log-concavity; the
log-concave discharge of the two hypotheses is in `KLS/LogConcave/WeightedGradient/Basic.lean`. The
zero-dimensional space is included.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace FunctionalInequalities

open Energy.Euclidean

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure]

namespace Energy.LipschitzGradient

/--
The sequential relaxation of `f ↦ ‖∇f‖²` on the classes of globally Lipschitz `L²(ν)` functions
with square-integrable gradient: the weighted gradient operator with `B = 1`. -/
def relaxation (hac : (ν : Measure V) ≪ m) : Functional (Lp ℝ 2 (ν : Measure V)) :=
  (PreEnergy.ofLinearPMap
      (Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V)
        hac)).sequentialRelaxation

end Energy.LipschitzGradient

section Bridge

namespace Energy.LipschitzGradient

/-- A literature constant is valid on the raw globally Lipschitz gradient tests. -/
theorem holds_ofPreEnergy_of_localSlope (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {C : NNReal}
    (h : Poincare.LocalSlope.Holds ν C) :
    (Poincare.TestFamily.ofPreEnergy ν
          (PreEnergy.ofLinearPMap
            (Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac))).Holds
      C := by
  rintro ⟨x, hx⟩
  obtain ⟨g, hg, rfl⟩ := (Energy.WeightedGradient.mem_domain_operator_iff ν _ hac x).mp hx
  have hT :=
    Energy.WeightedGradient.operator_apply ν (ContinuousLinearMap.id ℝ V) hac hfr hg hx rfl
  have hgrad : MemLp (gradient g) 2 (ν : Measure V) := by
    simpa only [FunctionalInequalities.Energy.WeightedGradient.apply_id] using hg.memLp_apply
  obtain ⟨K, hK⟩ := hg.1
  have hlit :=
    h g
      ((Energy.LocalSlope.admissible_iff_memLp_gradient ν m hac g).mpr
        ⟨hK.locallyLipschitz, hg.memLp, hgrad⟩)
  rw [← ProbabilityTheory.ofReal_variance hg.memLp,
    Energy.LocalSlope.energy_eq_integral_gradient ν m hac g hK.locallyLipschitz hgrad, ←
    ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg] at hlit
  have hreal :
    ProbabilityTheory.variance g (ν : Measure V) ≤
      (C : ℝ) * ∫ x, ‖gradient g x‖ ^ 2 ∂(ν : Measure V) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg C.2 (integral_nonneg fun x ↦ sq_nonneg _))).mp
      hlit
  change
    L2.variance ν (hg.memLp.toLp g) ≤
      C * ‖Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac ⟨_, hx⟩‖₊ ^ 2
  rw [hT, L2.variance_toLp, ← NNReal.coe_le_coe]
  push_cast
  rw [Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg _ _), L2.norm_toLp_sq,
    FunctionalInequalities.Energy.WeightedGradient.apply_id]
  exact hreal

/--
A valid constant of the Lipschitz gradient relaxation is a literature constant: approximate a
locally Lipschitz literature test by smooth compactly supported functions in the graph norm. -/
theorem localSlope_holds_of_relaxation (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {C : NNReal}
    (h : Poincare.L2Energy.Holds ν (relaxation ν m hac) C) : Poincare.LocalSlope.Holds ν C := by
  intro f hf
  obtain ⟨hlip, hL2, hgL2⟩ := (Energy.LocalSlope.admissible_iff_memLp_gradient ν m hac f).mp hf
  obtain ⟨fs, hfs, hconv, hgconv⟩ :=
    LipschitzApproximation.exists_smooth_weighted_L2 ν m hac (ContinuousLinearMap.id ℝ V) f hlip
      hL2 (by simpa using hgL2)
  have hsL2 (j : ℕ) : MemLp (fs j) 2 (ν : Measure V) := (hfs j).2.2.1
  have hgsL2 (j : ℕ) : MemLp (gradient (fs j)) 2 (ν : Measure V) := by simpa using (hfs j).2.2.2
  have hval := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs hsL2 f hL2).mpr hconv
  have hgrad :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun j ↦ gradient (fs j)) hgsL2 (gradient f) hgL2).mpr
      (by convert! hgconv using 1)
  have hvar :
    Tendsto (fun j ↦ (L2.variance ν ((hsL2 j).toLp (fs j)) : ℝ)) atTop
      (𝓝 (L2.variance ν (hL2.toLp f) : ℝ)) :=
    ((NNReal.continuous_coe.comp (L2.continuous_variance ν)).tendsto _).comp hval
  have henergy :
    Tendsto (fun j ↦ ‖(hgsL2 j).toLp (gradient (fs j))‖ ^ 2) atTop
      (𝓝 (‖hgL2.toLp (gradient f)‖ ^ 2)) :=
    hgrad.norm.pow 2
  have hbound :
    ∀ j,
      (L2.variance ν ((hsL2 j).toLp (fs j)) : ℝ) ≤
        (C : ℝ) * ‖(hgsL2 j).toLp (gradient (fs j))‖ ^ 2 := by
    intro j
    have htest : Energy.WeightedGradient.IsTest ν (ContinuousLinearMap.id ℝ V) (fs j) :=
      Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν _ (hfs j).1 (hfs j).2.1
    have hmem :
      (hsL2 j).toLp (fs j) ∈
        (Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac).domain :=
      Energy.WeightedGradient.toLp_mem_domain_operator ν _ hac htest
    have hfin : (relaxation ν m hac).FiniteAt ((hsL2 j).toLp (fs j)) :=
      PreEnergy.sequentialRelaxation_finiteAt_toAmbient
        (PreEnergy.ofLinearPMap
            (Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac) :
          PreEnergy (Lp ℝ 2 (ν : Measure V)))
        ⟨_, hmem⟩
    have h1 := h ⟨_, hfin⟩
    have h2 :
      (relaxation ν m hac).finiteValue ⟨_, hfin⟩ ≤ ‖(hgsL2 j).toLp (gradient (fs j))‖₊ ^ 2 := by
      apply ENNReal.coe_le_coe.mp
      rw [Energy.Functional.coe_finiteValue]
      have h3 :=
        PreEnergy.sequentialRelaxation_toAmbient_le
          (PreEnergy.ofLinearPMap
              (Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac) :
            PreEnergy (Lp ℝ 2 (ν : Measure V)))
          ⟨_, hmem⟩
      change
        (relaxation ν m hac) ((hsL2 j).toLp (fs j)) ≤
          ((‖Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac ⟨_, hmem⟩‖₊ ^
                2 :
              NNReal) :
            ENNReal) at h3
      rw [Energy.WeightedGradient.operator_apply ν _ hac hfr htest hmem rfl] at h3
      exact h3
    have h4 :
      L2.variance ν ((hsL2 j).toLp (fs j)) ≤ C * ‖(hgsL2 j).toLp (gradient (fs j))‖₊ ^ 2 :=
      h1.trans (mul_le_mul_of_nonneg_left h2 zero_le)
    have h5 := NNReal.coe_le_coe.mpr h4
    push_cast at h5
    exact h5
  have hreal : (L2.variance ν (hL2.toLp f) : ℝ) ≤ (C : ℝ) * ‖hgL2.toLp (gradient f)‖ ^ 2 :=
    le_of_tendsto_of_tendsto' hvar (tendsto_const_nhds.mul henergy) hbound
  rw [L2.variance_toLp, Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg _ _),
    L2.norm_toLp_sq] at hreal
  rw [← ProbabilityTheory.ofReal_variance hL2,
    Energy.LocalSlope.energy_eq_integral_gradient ν m hac f hlip hgL2, ←
    ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal hreal

end Energy.LipschitzGradient

namespace Poincare.LipschitzGradient

/--
A finite constant is valid for the Lipschitz gradient relaxation exactly when it is a literature
constant. -/
theorem holds_iff_localSlope (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) (C : NNReal) :
    Poincare.L2Energy.Holds ν (Energy.LipschitzGradient.relaxation ν m hac) C ↔
      Poincare.LocalSlope.Holds ν C :=
  ⟨Energy.LipschitzGradient.localSlope_holds_of_relaxation ν m hac hfr, fun h ↦
    (Poincare.TestFamily.holds_ofPreEnergy_iff ν _ C).mp
      (Energy.LipschitzGradient.holds_ofPreEnergy_of_localSlope ν m hac hfr h)⟩

end Poincare.LipschitzGradient

namespace Poincare.SmoothTest

/-- The smooth-test constant equals the optimal constant of the Lipschitz gradient
relaxation. -/
theorem constant_eq_lipschitz (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) :
    optimalConstant (ν : Measure V) =
      Poincare.L2Energy.optimalConstant ν (Energy.LipschitzGradient.relaxation ν m hac) := by
  apply le_antisymm
  · by_cases htop :
      Poincare.L2Energy.optimalConstant ν (Energy.LipschitzGradient.relaxation ν m hac) = ⊤
    · rw [htop]
      exact le_top
    · set C :=
        (Poincare.L2Energy.optimalConstant ν (Energy.LipschitzGradient.relaxation ν m hac)).toNNReal
      have hC : Poincare.L2Energy.Holds ν (Energy.LipschitzGradient.relaxation ν m hac) C :=
        (Poincare.L2Energy.holds_iff_constant_le _ _ _).mpr (by rw [ENNReal.coe_toNNReal htop])
      have hlit :=
        (FunctionalInequalities.Poincare.LipschitzGradient.holds_iff_localSlope ν m hac hfr
              C).mp
          hC
      have hlegacy := (holds_iff_localSlope ν m hac C).mpr hlit
      rw [← ENNReal.coe_toNNReal htop]
      exact constant_le hlegacy
  · apply le_constant
    intro C hC
    have hlit := (holds_iff_localSlope ν m hac C).mp hC
    exact
      (Poincare.L2Energy.holds_iff_constant_le _ _ _).mp
        ((FunctionalInequalities.Poincare.LipschitzGradient.holds_iff_localSlope ν m hac hfr
              C).mpr
          hlit)

end Poincare.SmoothTest

namespace Energy.CovarianceGradient

/-- With identity covariance, the covariance relaxation of `def:affine-poincare-constant` is the
Lipschitz gradient relaxation. -/
theorem relaxation_eq_lipschitz (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (hcov : Covariance.operator (ν : Measure V) = ContinuousLinearMap.id ℝ V) :
    relaxation ν = Energy.LipschitzGradient.relaxation ν m hac :=
  relaxation_eq_ofLinearPMap ν (ContinuousLinearMap.id ℝ V) hac hfr
    (fun v ↦ by rw [hcov, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq])

/-- The covariance relaxation is at most the operator norm of the covariance times the Lipschitz
gradient relaxation, at every point of finite Lipschitz relaxation. -/
theorem relaxation_le_mul_lipschitz (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) (f : Lp ℝ 2 (ν : Measure V))
    (hf : Energy.LipschitzGradient.relaxation ν m hac f ≠ ⊤) :
    relaxation ν f ≤
      (‖Covariance.operator (ν : Measure V)‖₊ : ENNReal) *
        Energy.LipschitzGradient.relaxation ν m hac f := by
  obtain ⟨B, hB⟩ := Covariance.exists_inner_eq_norm_sq (ν : Measure V)
  rw [relaxation_eq_ofLinearPMap ν B hac hfr hB]
  refine
    PreEnergy.sequentialRelaxation_comp_le_mul
      (PreEnergy.ofLinearPMap
          (Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac) :
        PreEnergy (Lp ℝ 2 (ν : Measure V)))
      (PreEnergy.ofLinearPMap (Energy.WeightedGradient.operator ν B hac) :
        PreEnergy (Lp ℝ 2 (ν : Measure V)))
      id continuous_id ‖Covariance.operator (ν : Measure V)‖₊ ?_ f hf
  rintro ⟨x, hx⟩
  obtain ⟨g, hg, rfl⟩ := (Energy.WeightedGradient.mem_domain_operator_iff ν _ hac x).mp hx
  have hgrad : MemLp (gradient g) 2 (ν : Measure V) := by
    simpa only [FunctionalInequalities.Energy.WeightedGradient.apply_id] using hg.memLp_apply
  have hgB : Energy.WeightedGradient.IsTest ν B g := ⟨hg.1, hg.memLp, B.comp_memLp' hgrad⟩
  refine ⟨⟨_, Energy.WeightedGradient.toLp_mem_domain_operator ν B hac hgB⟩, rfl, ?_⟩
  rw [PreEnergy.ofLinearPMap_energy, PreEnergy.ofLinearPMap_energy,
    Energy.WeightedGradient.operator_apply ν B hac hfr hgB _ rfl,
    Energy.WeightedGradient.operator_apply ν (ContinuousLinearMap.id ℝ V) hac hfr hg hx rfl, ←
    ENNReal.coe_mul]
  apply ENNReal.coe_le_coe.mpr
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [L2.norm_toLp_sq, L2.norm_toLp_sq, FunctionalInequalities.Energy.WeightedGradient.apply_id,
    ← integral_const_mul]
  refine
    integral_mono_of_nonneg (ae_of_all _ fun x ↦ sq_nonneg _)
      (((memLp_two_iff_integrable_sq_norm hgrad.aestronglyMeasurable).mp hgrad).const_mul _)
      (ae_of_all _ fun x ↦ ?_)
  change ‖B (gradient g x)‖ ^ 2 ≤ ‖Covariance.operator (ν : Measure V)‖ * ‖gradient g x‖ ^ 2
  rw [← hB]
  calc
    inner ℝ (Covariance.operator (ν : Measure V) (gradient g x)) (gradient g x) ≤
        ‖Covariance.operator (ν : Measure V) (gradient g x)‖ * ‖gradient g x‖ :=
      real_inner_le_norm _ _
    _ ≤ ‖Covariance.operator (ν : Measure V)‖ * ‖gradient g x‖ * ‖gradient g x‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖Covariance.operator (ν : Measure V)‖ * ‖gradient g x‖ ^ 2 := by ring

end Energy.CovarianceGradient

end Bridge

end FunctionalInequalities
