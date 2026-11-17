/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothTest.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Basic
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Probability.Moments.CovarianceBilin

/-!
# The linear-test lower bound: source and formalization scope

Source: [Remark 3.8 of the historical manuscript](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/02-results-toolkit.tex#L108-L117)
states the Rayleigh lower bound and its linear-test consequence
`C_P ≥ λ_max(Cov_P)`. The [linear-test dossier](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/solutions/glm-linear-baselines.tex#L39-L68)
explicitly assumes a Euclidean probability measure with finite covariance, allows an extended
optimal constant, and gives the linear-test variance and energy calculation.

This module uses the globally `C∞`, L², finite-gradient-energy domain from
`Poincare.SmoothTest.Basic`.
The Hilbert formulation, explicit `MemLp id 2` hypotheses, and `ENNReal` zero-denominator
conventions are local precisifications. Centered covariance is represented through a bounded
Riesz operator; its Rayleigh supremum is an eigenvalue in nontrivial finite dimension and is
defined as zero in dimension zero. No infinite-dimensional eigenvalue attainment is claimed.
The source's mode-indicator discussion, Gaussian equality, and spectral-gap identification
are outside this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace FunctionalInequalities

namespace Poincare.SmoothTest

section LinearTestGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Source: the linear test in Remark 3.8 and its dossier, linked above,
encoded on a real inner product space. -/
def linear (v : E) : E → ℝ := fun x ↦ inner ℝ v x

/-- Source: the local definition `linear`, evaluated at a point. -/
@[simp]
theorem linear_apply (v x : E) : linear v x = inner ℝ v x :=
  rfl

/-- Source: the local definition `linear`, exposed as a function equality. -/
theorem linear_eq_inner (v : E) : linear v = fun x ↦ inner ℝ v x :=
  rfl

end LinearTestGeometry

section LinearTestAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E]

omit [MeasurableSpace E] in
/-- Source: local calculus helper using Mathlib's `innerSL`, its `hasFDerivAt` property,
and `InnerProductSpace.toDual`; the linear test has constant gradient `v`. -/
theorem hasGradientAt_linear (v x : E) : HasGradientAt (linear v) v x := by
  change HasFDerivAt (linear v) (InnerProductSpace.toDual ℝ E v) x
  convert (innerSL ℝ v).hasFDerivAt using 1 <;> ext <;> rfl

omit [MeasurableSpace E] in
/-- Source: local consequence of `hasGradientAt_linear` and `HasGradientAt.gradient`. -/
@[simp]
theorem gradient_linear (v x : E) : gradient (linear v) x = v :=
  (hasGradientAt_linear v x).gradient

/-- Source: the energy calculation in the linear-test dossier, linked above.
The Hilbert version follows from `gradient_linear` and probability normalization. -/
theorem energy_linear (μ : Measure E) [IsProbabilityMeasure μ] (v : E) :
    energy μ (linear v) = ‖v‖ ^ 2 := by
  simp [energy]

/-- Source: local test-domain helper using the `contDiff` property of `innerSL`,
`MemLp.continuousLinearMap_comp`, and `gradient_linear`.
An explicit finite second moment makes each linear test `Admissible`. -/
theorem linear_admissible {μ : Measure E} (hprob : IsProbabilityMeasure μ)
    (hμ : MemLp (id : E → E) 2 μ) (v : E) :
    Admissible μ (linear v) := by
  let _ := hprob
  refine ⟨?_, ?_, ?_⟩
  · change ContDiff ℝ ∞ (fun x ↦ inner ℝ v x)
    exact (innerSL ℝ v).contDiff
  · change MemLp (fun x ↦ inner ℝ v x) 2 μ
    simpa only [id_eq, innerSL_apply_apply] using
      hμ.continuousLinearMap_comp (innerSL ℝ v)
  · simp

/-- Source: the linear-test dossier's variance/energy argument, linked above,
specialized to a finite `Holds` constant using `linear_admissible` and `energy_linear`.
The Hilbert scope and explicit moment hypothesis are local precisifications. -/
theorem variance_linear_le {μ : Measure E} {C : ℝ}
    (hP : Holds μ C) (hμ : MemLp (id : E → E) 2 μ) (v : E) :
    variance (linear v) μ ≤ C * ‖v‖ ^ 2 := by
  let _ := hP.probability
  simpa [energy_linear] using
    hP.variance_le (linear_admissible hP.probability hμ v)

/-- Source: local `ENNReal` encoding of the quotient in Remark 3.8.
It explicitly sets positive variance over zero energy to `⊤` and `0 / 0` to zero;
the source remark does not spell out these conventions. -/
def rayleigh (μ : Measure E) (f : E → ℝ) : ENNReal :=
  ENNReal.ofReal (variance f μ) / ENNReal.ofReal (energy μ f)

/--
Source: the Rayleigh bound in [Remark 3.8](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/02-results-toolkit.tex#L108-L117).
This local `Admissible`/`ENNReal` version follows from `Holds.le` and `le_constant`,
including the stated zero-energy conventions and the absence of finite valid constants. -/
theorem rayleigh_le_constant {μ : Measure E} {f : E → ℝ} (hf : Admissible μ f) :
    rayleigh μ f ≤ optimalConstant μ := by
  apply le_constant
  intro C hC
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.zero_le_coe)]
  exact ENNReal.ofReal_le_ofReal (hC.variance_le hf)

/-- Source: local conversion helper using `rayleigh` and `ENNReal.ofReal_div_of_pos`.
Positive energy gives the ordinary real-quotient expression. -/
theorem rayleigh_eq_of_energy_pos {μ : Measure E} {f : E → ℝ}
    (henergy : 0 < energy μ f) :
    rayleigh μ f = ENNReal.ofReal (variance f μ / energy μ f) := by
  rw [rayleigh, ENNReal.ofReal_div_of_pos henergy]

/-- Source: local boundary consequence of `rayleigh` and `ENNReal.div_zero`.
Positive variance with zero energy gives an infinite quotient. -/
theorem rayleigh_eq_top_of_energy_zero {μ : Measure E} {f : E → ℝ}
    (hvariance : 0 < variance f μ) (henergy : energy μ f = 0) :
    rayleigh μ f = ⊤ := by
  rw [rayleigh, henergy, ENNReal.ofReal_zero]
  exact ENNReal.div_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hvariance))

/-- Source: local specialization of `rayleigh_le_constant` through
`rayleigh_eq_of_energy_pos`, expressing the source quotient at positive energy. -/
theorem realRayleigh_le_constant {μ : Measure E} {f : E → ℝ}
    (hf : Admissible μ f) (henergy : 0 < energy μ f) :
    ENNReal.ofReal (variance f μ / energy μ f) ≤ optimalConstant μ := by
  rw [← rayleigh_eq_of_energy_pos henergy]
  exact rayleigh_le_constant hf

end LinearTestAnalysis

end Poincare.SmoothTest

namespace Covariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Source: local consequence of `operator_inner`, Mathlib's `covarianceBilin_comm`,
and `real_inner_comm`. -/
theorem operator_isSymmetric (μ : Measure E) :
    (operator μ).toLinearMap.IsSymmetric := by
  intro x y
  calc
    inner ℝ (operator μ x) y = covarianceBilin μ x y := operator_inner μ x y
    _ = covarianceBilin μ y x := covarianceBilin_comm x y
    _ = inner ℝ (operator μ y) x := (operator_inner μ y x).symm
    _ = inner ℝ x (operator μ y) := real_inner_comm _ _

/-- Source: local consequence of `operator_inner` and Mathlib's `covarianceBilin_self_nonneg`. -/
theorem operator_self_nonneg (μ : Measure E) (x : E) :
    0 ≤ inner ℝ (operator μ x) x := by
  rw [operator_inner]
  exact covarianceBilin_self_nonneg x

/-- Source: the quadratic-form identity in the linear-test dossier, linked above,
realized using `operator_inner` and Mathlib's `covarianceBilin_self` under explicit L² data. -/
theorem operator_self_eq_variance {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) (x : E) :
    inner ℝ (operator μ x) x = variance (Poincare.SmoothTest.linear x) μ := by
  rw [operator_inner, covarianceBilin_self hμ, Poincare.SmoothTest.linear_eq_inner]

/-- Source: local encoding using Mathlib's `ContinuousLinearMap.rayleighQuotient`.
The real supremum runs over nonzero vectors, with the real empty supremum equal to zero. -/
def rayleighMax (μ : Measure E) : ℝ :=
  ⨆ x : {x : E // x ≠ 0}, (operator μ).rayleighQuotient x

/-- Source: local bridge to the unit-vector supremum used in the linear-test dossier,
via Mathlib's `iSup_rayleigh_eq_iSup_rayleigh_sphere` and `operator_inner`. -/
theorem rayleighMax_eq_iSup_sphere (μ : Measure E) :
    rayleighMax μ = ⨆ v : Metric.sphere (0 : E) 1, covarianceBilin μ v v := by
  rw [rayleighMax, (operator μ).iSup_rayleigh_eq_iSup_rayleigh_sphere zero_lt_one]
  congr 1
  funext v
  have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  simp [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, operator_inner, hvnorm]

/-- Source: local consequence of `operator_self_nonneg`, the operator-norm Rayleigh bound,
and `Real.iSup_of_isEmpty`; it includes the zero-dimensional case. -/
theorem rayleighMax_nonneg (μ : Measure E) :
    0 ≤ rayleighMax μ := by
  by_cases hE : Nontrivial E
  · let _ := hE
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hbdd : BddAbove
        (Set.range fun x : {x : E // x ≠ 0} ↦ (operator μ).rayleighQuotient x) := by
      refine ⟨‖operator μ‖, ?_⟩
      rintro y ⟨v, rfl⟩
      exact (le_abs_self _).trans ((operator μ).rayleighQuotient_le_norm v)
    apply le_ciSup_of_le hbdd ⟨x, hx⟩
    change 0 ≤ inner ℝ (operator μ x) x / ‖x‖ ^ 2
    exact div_nonneg (operator_self_nonneg μ x) (sq_nonneg _)
  · have _ : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    let _ : IsEmpty {x : E // x ≠ 0} :=
      ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
    rw [rayleighMax, Real.iSup_of_isEmpty]

/-- Source: Mathlib's `hasEigenvalue_iSup_of_finiteDimensional` applied to
`operator_isSymmetric`; it justifies eigenvalue terminology in nontrivial finite dimension. -/
theorem operator_hasEigenvalue_rayleighMax
    [FiniteDimensional ℝ E] [Nontrivial E] (μ : Measure E) :
    Module.End.HasEigenvalue (operator μ).toLinearMap (rayleighMax μ) := by
  exact (operator_isSymmetric μ).hasEigenvalue_iSup_of_finiteDimensional

/-- Source: local `ENNReal` encoding of the covariance Rayleigh maximum in Remark 3.8.
`operator_hasEigenvalue_rayleighMax` supplies the finite-dimensional eigenvalue interpretation;
in dimension zero the local empty-supremum convention gives zero. -/
def lambdaMax (μ : Measure E) : ENNReal :=
  ENNReal.ofReal (rayleighMax μ)

/-- Source: local conversion consequence of `lambdaMax` and `rayleighMax_nonneg`. -/
@[simp]
theorem lambdaMax_toReal (μ : Measure E) :
    (lambdaMax μ).toReal = rayleighMax μ := by
  simp [lambdaMax, rayleighMax_nonneg μ]

/-- Source: local zero-dimensional convention from `rayleighMax` and `Real.iSup_of_isEmpty`. -/
theorem lambdaMax_eq_zero_of_subsingleton [Subsingleton E] (μ : Measure E) :
    lambdaMax μ = 0 := by
  let _ : IsEmpty {x : E // x ≠ 0} :=
    ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
  rw [lambdaMax, rayleighMax, Real.iSup_of_isEmpty]
  exact ENNReal.ofReal_zero

/-- Source: local bound from Mathlib's `rayleighQuotient_le_norm` for the bounded
operator encoding, together with `Real.iSup_of_isEmpty` in dimension zero. -/
theorem lambdaMax_le_norm (μ : Measure E) :
    lambdaMax μ ≤ ENNReal.ofReal ‖operator μ‖ := by
  apply ENNReal.ofReal_le_ofReal
  by_cases hE : Nontrivial E
  · let _ := hE
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    let _ : Nonempty {x : E // x ≠ 0} := ⟨⟨x, hx⟩⟩
    refine ciSup_le fun x ↦ ?_
    exact (le_abs_self _).trans ((operator μ).rayleighQuotient_le_norm x)
  · have _ : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    let _ : IsEmpty {x : E // x ≠ 0} :=
      ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
    rw [rayleighMax, Real.iSup_of_isEmpty]
    exact norm_nonneg _

/-- Source: local consequence of `lambdaMax_le_norm` and `ENNReal.ofReal_ne_top`. -/
theorem lambdaMax_ne_top (μ : Measure E) :
    lambdaMax μ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lambdaMax_le_norm μ)

/-- Source: local fixed-constant version of the linear-test dossier's covariance argument,
using `Poincare.SmoothTest.variance_linear_le` and `operator_self_eq_variance`.
The Hilbert formulation and dimension-zero case are handled explicitly. -/
theorem lambdaMax_le {μ : Measure E} {C : ℝ}
    (hP : Poincare.SmoothTest.Holds μ C) (hμ : MemLp (id : E → E) 2 μ) :
    lambdaMax μ ≤ ENNReal.ofReal C := by
  let _ := hP.probability
  apply ENNReal.ofReal_le_ofReal
  by_cases hE : Nontrivial E
  · let _ := hE
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    let _ : Nonempty {x : E // x ≠ 0} := ⟨⟨x, hx⟩⟩
    refine ciSup_le fun v ↦ ?_
    have hv := Poincare.SmoothTest.variance_linear_le hP hμ (v : E)
    have hvnorm : 0 < ‖(v : E)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr v.property)
    apply (div_le_iff₀ hvnorm).2
    change inner ℝ (operator μ (v : E)) v ≤ C * ‖(v : E)‖ ^ 2
    rw [operator_self_eq_variance hμ]
    simpa only [mul_comm] using hv
  · have _ : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    let _ : IsEmpty {x : E // x ≠ 0} :=
      ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
    rw [rayleighMax, Real.iSup_of_isEmpty]
    exact hP.constant_nonneg

/--
Source: the covariance lower bound in [Remark 3.8](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/02-results-toolkit.tex#L108-L117)
and its [finite-covariance dossier](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/solutions/glm-linear-baselines.tex#L39-L68).
This Hilbert/`ENNReal` version follows from `lambdaMax_le` and `Poincare.SmoothTest.le_constant`,
with an explicit second moment and the local dimension-zero convention. -/
theorem lambdaMax_le_constant {μ : Measure E} (hμ : MemLp (id : E → E) 2 μ) :
    lambdaMax μ ≤ Poincare.SmoothTest.optimalConstant μ := by
  apply Poincare.SmoothTest.le_constant
  intro C hC
  simpa only [ENNReal.ofReal_coe_nnreal] using lambdaMax_le hC hμ

end Covariance

end FunctionalInequalities
