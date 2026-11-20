/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneH1Translation
public import LeanPool.FastDynamo.Analysis.WholePlaneLocalCompactness
public import LeanPool.FastDynamo.Analysis.WholePlaneIntegralWeakDerivative
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Band-limited approximations for whole-plane local Rellich

The spectral-isolation step of the paper (§2.3) uses compactness of the restriction of
`H¹(ℝ²)` to a bounded disc `D(0,R_w)` containing the support of the velocity, quoted there as
Rellich's theorem.  This module reduces that local Rellich statement to the compactness of one
concrete operator and supplies everything around it.

Two abstract criteria come first: a continuous linear map into a complete normed space is compact
as soon as the image of one positive-radius closed ball is totally bounded, and an operator-norm
limit of compact maps is compact.  Restriction to a measurable finite-measure set is then
realized as multiplication by an `L∞` indicator, a contraction on `L²`, so compact norm-convergent
approximations of the ambient `H¹ → L²` embedding stay compact after restriction; the
closed unit disk, which carries the support of the jump velocity, is the final specialization.

The approximations themselves are band limited.  The low-frequency inverse Bessel symbol is the
complement of the high-frequency symbol of `WholePlaneH1Translation`, and its physical synthesis
has an exact Fourier formula, a bounded frequency support, and a quantitative operator-norm error.
After the spatial cutoff this low-frequency map factors through a coefficient-level
time--frequency concentration operator; compactness of that single concrete operator is the
analytic input left to `WholePlaneBandLimitedRellichUnconditional`, which proves it, and no
compactness hypothesis is hidden in any definition below.

## Contents

* Abstract compactness criteria for local `L²` maps: total-boundedness criteria and compact
  approximation in operator norm.
* The local Rellich bridge on the whole plane: restriction as an `L²` contraction and the
  compact approximation bridge.
* Band-limited approximations for whole-plane local Rellich: the complementary low-frequency
  multiplier, the explicit band-limited physical map, and the time--frequency
  concentration core.
-/

@[expose] public section

/-!
## Abstract compactness criteria for local `L²` maps

This part records two small bridges used by local Rellich arguments.

* A continuous linear map into a complete normed space is compact exactly
  when the image of one positive-radius closed ball is totally bounded.
* An operator-norm limit of compact continuous linear maps is compact.

The first form is convenient for a direct finite-net proof.  The second form
is convenient when a local restriction is approximated by compact
band-limited restrictions.
-/

namespace FastDynamo

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-! ## Compact approximation in operator norm -/

/-- An operator-norm limit of a sequence of compact continuous linear maps is
compact.  The epsilon formulation is tailored to estimates obtained by
discarding the high-frequency tail of an `H¹` input. -/
theorem isCompactOperator_of_compact_approximation
    (T : E →L[𝕜] F) (A : ℕ → E →L[𝕜] F)
    (hA : ∀ n, IsCompactOperator (A n))
    (hAT : ∀ ε > 0, ∃ N, ∀ n ≥ N, ‖A n - T‖ < ε) :
    IsCompactOperator T := by
  apply isCompactOperator_of_tendsto
    (l := Filter.atTop) (F := A) (f := T)
  · rw [Metric.tendsto_atTop]
    intro ε hε
    rcases hAT ε hε with ⟨N, hN⟩
    exact ⟨N, fun n hn => by
      simpa only [dist_eq_norm] using hN n hn⟩
  · exact Filter.Eventually.of_forall hA

end FastDynamo

/-!
## The local Rellich bridge on the whole plane

This part separates the elementary operator-norm half of the whole-plane
Rellich argument from its analytic compact-kernel input.

For a measurable finite-measure set `s`, restriction is multiplication by its
`L∞` indicator.  We package that multiplication as an `L² → L²` contraction
and prove that compact, norm-convergent approximations to the ambient `H¹ → L²`
embedding remain compact after restriction.  The final specialization fixes
the closed unit disk, which carries the support of the jump velocity.

The remaining input is therefore precise:
compactness of the spatially restricted, frequency-truncated maps, proved in
`WholePlaneBandLimitedRellichUnconditional`.  No Rellich statement is assumed
under another name here.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Restriction as an `L²` contraction -/

/-- Multiplication by the indicator of `s`, acting directly on scalar `L²`. -/
def wholePlaneScalarCutoffL2
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) :
    WholePlaneScalarL2 →L[ℂ] WholePlaneScalarL2 :=
  scalarVectorMulL2 volume (wholePlaneLocalizationIndicator s hs hsm)

/-- Restriction to a measurable finite-measure set acts on scalar `L²` as multiplication by the
`L∞` indicator of that set. -/
@[simp] theorem wholePlaneScalarCutoffL2_apply
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) (f : WholePlaneScalarL2) :
    wholePlaneScalarCutoffL2 s hs hsm f =
      scalarVectorMulL2 volume
        (wholePlaneLocalizationIndicator s hs hsm) f :=
  rfl

/-- The `L∞` norm of a set indicator is at most one, including the null-set
case. -/
theorem norm_wholePlaneLocalizationIndicator_le_one
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) :
    ‖wholePlaneLocalizationIndicator s hs hsm‖ ≤ 1 := by
  unfold wholePlaneLocalizationIndicator
  simpa using
    (norm_indicatorConstLp_le
      (p := (∞ : ENNReal)) (μ := (volume : Measure WholePlane))
      (hs := hs) (hμs := hsm) (c := (1 : ℂ)))

/-- Cutting an `L²` function down to a measurable set is a contraction. -/
theorem norm_wholePlaneScalarCutoffL2_le_one
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) :
    ‖wholePlaneScalarCutoffL2 s hs hsm‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  calc
    ‖wholePlaneScalarCutoffL2 s hs hsm f‖ ≤
        ‖wholePlaneLocalizationIndicator s hs hsm‖ * ‖f‖ :=
      norm_scalarVectorMulL2_apply_le volume _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
      (norm_wholePlaneLocalizationIndicator_le_one s hs hsm) (norm_nonneg f)

/-- The concrete `H¹` restriction is the ambient value embedding followed by
the `L²` cutoff. -/
theorem wholePlaneScalarRestrictionH1_eq_cutoff_comp
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) :
    wholePlaneScalarRestrictionH1 s hs hsm =
      (wholePlaneScalarCutoffL2 s hs hsm).comp
        (wholePlaneH1Embedding ℂ) :=
  rfl

/-! ## Compact approximation bridge -/

/-- If maps approximating the ambient `H¹ → L²` value embedding converge in
operator norm and become compact after spatial cutoff, then the exact spatial
restriction is compact.

For the Fourier proof of Rellich, `A n` is the low-frequency part of the value
embedding.  The first hypothesis is exactly compactness of a simultaneously
space- and frequency-truncated map; the second is the high-frequency tail
estimate. -/
theorem
    isCompactOperator_wholePlaneScalarRestrictionH1_of_compact_approximation
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞)
    (A : ℕ → WholePlaneScalarH1 →L[ℂ] WholePlaneScalarL2)
    (hA : ∀ n, IsCompactOperator
      ((wholePlaneScalarCutoffL2 s hs hsm).comp (A n)))
    (hAT : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      ‖A n - wholePlaneH1Embedding ℂ‖ < ε) :
    IsCompactOperator (wholePlaneScalarRestrictionH1 s hs hsm) := by
  rw [wholePlaneScalarRestrictionH1_eq_cutoff_comp]
  apply isCompactOperator_of_compact_approximation
    ((wholePlaneScalarCutoffL2 s hs hsm).comp
      (wholePlaneH1Embedding ℂ))
    (fun n => (wholePlaneScalarCutoffL2 s hs hsm).comp (A n)) hA
  intro ε hε
  obtain ⟨N, hN⟩ := hAT ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hdiff :
      (wholePlaneScalarCutoffL2 s hs hsm).comp (A n) -
          (wholePlaneScalarCutoffL2 s hs hsm).comp
            (wholePlaneH1Embedding ℂ) =
      (wholePlaneScalarCutoffL2 s hs hsm).comp
          (A n - wholePlaneH1Embedding ℂ) := by
    ext u
    simp
  rw [hdiff]
  calc
    ‖(wholePlaneScalarCutoffL2 s hs hsm).comp
        (A n - wholePlaneH1Embedding ℂ)‖ ≤
        ‖wholePlaneScalarCutoffL2 s hs hsm‖ *
          ‖A n - wholePlaneH1Embedding ℂ‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖A n - wholePlaneH1Embedding ℂ‖ :=
      mul_le_mul_of_nonneg_right
        (norm_wholePlaneScalarCutoffL2_le_one s hs hsm)
        (norm_nonneg (A n - wholePlaneH1Embedding ℂ))
    _ < ε := by simpa using hN n hn

end

end FastDynamo

/-!
## Band-limited approximations for whole-plane local Rellich

This part identifies the exact operator whose compactness is the analytic
core of the Fourier proof of local Rellich compactness.

The low-frequency inverse Bessel symbol is the complement of the high-frequency
symbol from `WholePlaneH1Translation`.  Its physical synthesis is therefore an
explicit band-limited approximation to the weak `H¹ -> L²` value embedding.
We prove its exact Fourier formula, its frequency support, the decomposition
into low and high frequencies, and the quantitative operator-norm error bound.

After spatial cutoff, the low-frequency map factors through a coefficient-level
time--frequency concentration operator.  Proving that concrete operator compact
is the Hilbert--Schmidt/Arzelà--Ascoli input needed for the final
Rellich theorem (supplied in `WholePlaneBandLimitedRellichUnconditional`); no compactness
hypothesis is hidden in any definition below.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

/-! ## The complementary low-frequency multiplier -/

/-- The inverse Bessel multiplier restricted to frequencies `‖xi‖ < R`.

The strict inequality is chosen so that this symbol is exactly complementary
to `h1HighFrequencyRecoverMass R`, whose support condition is `R ≤ ‖xi‖`. -/
def h1LowFrequencyRecoverMass (R : ℝ) (xi : WholePlane) : ℂ :=
  if R ≤ ‖xi‖ then 0 else h1RecoverMass xi

/-- The low-frequency inverse Bessel symbol is strongly measurable, being the piecewise
combination of `0` and the continuous symbol `h1RecoverMass` across the sphere `‖ξ‖ = R`. -/
theorem h1LowFrequencyRecoverMass_stronglyMeasurable (R : ℝ) :
    StronglyMeasurable (h1LowFrequencyRecoverMass R) := by
  unfold h1LowFrequencyRecoverMass
  exact StronglyMeasurable.piecewise
    (measurableSet_le measurable_const continuous_norm.measurable)
    stronglyMeasurable_const
    (h1RecoverMass_hasTemperateGrowth.1.continuous.stronglyMeasurable)

/-- The low-frequency inverse Bessel symbol is bounded by one, so multiplication by it is
contractive on `L²`. -/
theorem norm_h1LowFrequencyRecoverMass_le_one
    (R : ℝ) (xi : WholePlane) :
    ‖h1LowFrequencyRecoverMass R xi‖ ≤ 1 := by
  by_cases hxi : R ≤ ‖xi‖
  · simp [h1LowFrequencyRecoverMass, hxi]
  · simpa [h1LowFrequencyRecoverMass, hxi] using
      norm_h1RecoverMass_le xi

/-- Quotient-level `L∞` representative of the low-frequency inverse Bessel
symbol. -/
def h1LowFrequencyRecoverMassLInf (R : ℝ) :
    Lp ℂ ∞ (volume : Measure WholePlane) :=
  (memLp_top_of_bound (μ := (volume : Measure WholePlane))
    (h1LowFrequencyRecoverMass_stronglyMeasurable R).aestronglyMeasurable
    1 (ae_of_all _ (norm_h1LowFrequencyRecoverMass_le_one R))).toLp _

/-- The `L∞` class of the low-frequency symbol has the symbol itself as an almost
everywhere representative. -/
theorem h1LowFrequencyRecoverMassLInf_coe_ae (R : ℝ) :
    (h1LowFrequencyRecoverMassLInf R : WholePlane → ℂ) =ᵐ[volume]
      h1LowFrequencyRecoverMass R := by
  exact MemLp.coeFn_toLp _

/-- The low- and high-frequency inverse Bessel symbols are exactly complementary: their sum
is `h1RecoverMass` at every frequency.  This is the frequency-space form of the splitting
of the weak `H¹ → L²` embedding into a band-limited part and a small remainder. -/
theorem h1LowFrequencyRecoverMass_add_highFrequencyRecoverMass
    (R : ℝ) (xi : WholePlane) :
    h1LowFrequencyRecoverMass R xi +
        h1HighFrequencyRecoverMass R xi = h1RecoverMass xi := by
  by_cases hxi : R ≤ ‖xi‖
  · simp [h1LowFrequencyRecoverMass, h1HighFrequencyRecoverMass, hxi]
  · simp [h1LowFrequencyRecoverMass, h1HighFrequencyRecoverMass, hxi]

/-! ## The explicit band-limited physical map -/

/-- Low-frequency physical value synthesized from an order-one Bessel
coefficient. -/
def wholePlaneH1LowFrequencyFromCoeff
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (R : ℝ) :
    WholePlaneL2 F →L[ℂ] WholePlaneL2 F :=
  (wholePlaneFourierSynthesis F).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (scalarVectorMulL2 (E := F) volume
      (h1LowFrequencyRecoverMassLInf R))

/-- The explicit low-frequency approximation of the weak `H¹ -> L²` value
embedding. -/
def wholePlaneH1LowFrequency
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (R : ℝ) :
    WholePlaneH1 F →L[ℂ] WholePlaneL2 F :=
  (wholePlaneH1LowFrequencyFromCoeff F R).comp
    (wholePlaneH1CoeffRecovery F)

/-- Frequency-side description of the band-limited approximation: its Fourier transform is
the low-frequency symbol times the order-one Bessel coefficient of `u`. -/
theorem wholePlaneH1LowFrequency_fourier
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (R : ℝ) (u : WholePlaneH1 F) :
    wholePlaneFourierAnalysis F (wholePlaneH1LowFrequency F R u) =
      scalarVectorMulL2 (E := F) volume
        (h1LowFrequencyRecoverMassLInf R)
        (wholePlaneH1CoeffRecovery F u) := by
  exact wholePlaneFourierAnalysis_synthesis F _

/-- Low and high frequency synthesis exactly reconstruct the physical value
embedding. -/
theorem wholePlaneH1LowFrequency_add_highFrequencyTail
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (R : ℝ) (u : WholePlaneH1 F) :
    wholePlaneH1LowFrequency F R u +
        wholePlaneH1HighFrequencyTail F R u =
      wholePlaneH1Embedding F u := by
  apply (wholePlaneFourierAnalysis F).injective
  rw [map_add, wholePlaneH1LowFrequency_fourier,
    wholePlaneH1HighFrequencyTail_fourier]
  have hvalue := congrArg (fun v ↦ wholePlaneFourierAnalysis F v)
    (h1CoeffToValueL2_wholePlaneH1CoeffRecovery F u)
  rw [h1CoeffToValueL2_fourier] at hvalue
  rw [← hvalue]
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_add
      (scalarVectorMulL2 (E := F) volume
        (h1LowFrequencyRecoverMassLInf R)
        (wholePlaneH1CoeffRecovery F u))
      (scalarVectorMulL2 (E := F) volume
        (h1HighFrequencyRecoverMassLInf R)
        (wholePlaneH1CoeffRecovery F u)),
    scalarVectorMulL2_coe_ae (E := F) volume
      (h1LowFrequencyRecoverMassLInf R)
      (wholePlaneH1CoeffRecovery F u),
    scalarVectorMulL2_coe_ae (E := F) volume
      (h1HighFrequencyRecoverMassLInf R)
      (wholePlaneH1CoeffRecovery F u),
    scalarVectorMulL2_coe_ae (E := F) volume h1RecoverMassLInf
      (wholePlaneH1CoeffRecovery F u),
    h1LowFrequencyRecoverMassLInf_coe_ae R,
    h1HighFrequencyRecoverMassLInf_coe_ae R,
    h1RecoverMassLInf_coe_ae]
    with xi hadd hlow hhigh hfull hlowSymbol hhighSymbol hfullSymbol
  simp only [hadd, Pi.add_apply, hlow, hhigh, hfull, hlowSymbol,
    hhighSymbol, hfullSymbol, ← add_smul,
    h1LowFrequencyRecoverMass_add_highFrequencyRecoverMass]

/-- Operator identity expressing the approximation error as the negative
high-frequency tail. -/
theorem wholePlaneH1LowFrequency_sub_embedding
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (R : ℝ) :
    wholePlaneH1LowFrequency F R - wholePlaneH1Embedding F =
      -wholePlaneH1HighFrequencyTail F R := by
  apply ContinuousLinearMap.ext
  intro u
  have h := wholePlaneH1LowFrequency_add_highFrequencyTail F R u
  simp only [sub_apply, neg_apply]
  rw [← h]
  abel

/-- Quantitative operator-norm error for the explicit band-limited
approximation. -/
theorem norm_wholePlaneH1LowFrequency_sub_embedding_le
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {R : ℝ} (hR : 0 ≤ R) :
    ‖wholePlaneH1LowFrequency F R - wholePlaneH1Embedding F‖ ≤
      h1HighFrequencyDecay R * ‖wholePlaneH1CoeffRecovery F‖ := by
  rw [wholePlaneH1LowFrequency_sub_embedding,
    ContinuousLinearMap.opNorm_neg]
  exact norm_wholePlaneH1HighFrequencyTail_operator_le F hR

/-! ## The time--frequency concentration core -/

/-- Spatial cutoff after low-frequency inverse Bessel synthesis, on the raw
coefficient space.  This is the concrete time--frequency concentration
operator whose kernel has finite `L²` norm when both cutoff sets have finite
measure. -/
def wholePlaneBandLimitedRestrictionFromCoeff
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) (R : ℝ) :
    WholePlaneScalarL2 →L[ℂ] WholePlaneScalarL2 :=
  (wholePlaneScalarCutoffL2 s hs hsm).comp
    (wholePlaneH1LowFrequencyFromCoeff ℂ R)

/-- Exact factorization of the spatially restricted band-limited `H¹` map
through coefficient recovery. -/
theorem wholePlaneScalarCutoff_comp_h1LowFrequency
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) (R : ℝ) :
    (wholePlaneScalarCutoffL2 s hs hsm).comp
        (wholePlaneH1LowFrequency ℂ R) =
      (wholePlaneBandLimitedRestrictionFromCoeff s hs hsm R).comp
        (wholePlaneH1CoeffRecovery ℂ) := by
  ext u
  rfl

/-- Compactness of the coefficient-level time--frequency core implies
compactness of the corresponding spatially restricted low-frequency `H¹`
map.  The premise is stated for the concrete coefficient-level operator. -/
theorem isCompactOperator_wholePlaneScalarCutoff_comp_h1LowFrequency_of_core
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) (R : ℝ)
    (hcore : IsCompactOperator
      (wholePlaneBandLimitedRestrictionFromCoeff s hs hsm R)) :
    IsCompactOperator
      ((wholePlaneScalarCutoffL2 s hs hsm).comp
        (wholePlaneH1LowFrequency ℂ R)) := by
  rw [wholePlaneScalarCutoff_comp_h1LowFrequency]
  exact hcore.comp_clm (wholePlaneH1CoeffRecovery ℂ)

end

end FastDynamo
