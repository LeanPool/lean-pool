/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Regular.Isometry
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Regular.Poincare
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.WeakLimit
public import LeanPool.KLS.FunctionalInequalities.KLS.IsotropicSupport
public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothTest.Comparison

/-!
# Reduction of the isotropic log-concave Poincaré bound to regular laws

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): the regular approximation reduces
Theorem 1.1 to isotropic regular laws. Formalized conditionally: if every isotropic regular law on
`ℝⁿ` (`n > 0`) has literature Poincaré constant at most `K`, then so does every isotropic
log-concave
law on every finite-dimensional inner product space (`KLS.IsotropicBound K`). The proof derives the
Borell density of the law, approximates it by the laws of regular potentials with converging
covariances, transfers the bound through centering/whitening with the envelope coefficient, and
passes to the weak limit. The universal bound for regular laws is a hypothesis (it is what Theorems
3.1, 4.1 and Proposition 7.1 would supply); nothing unconditional is asserted.
-/

@[expose] public section

open MeasureTheory Filter Topology

section

namespace FunctionalInequalities.KLS.LogConcave

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An isotropic law has full affine support (proved in `KLS/IsotropicSupport.lean`). -/
theorem affineSupport_eq_top_of_isotropic {μ : ProbabilityMeasure E} (hiso : KLS.Isotropic μ) :
    Probability.affineSupport μ = ⊤ :=
  hiso.affineSupport_eq_top

/-- An isotropic log-concave law has a Borell density with respect to Lebesgue measure. -/
theorem exists_isBorellDensity_of_isotropic {μ : ProbabilityMeasure E} (hLC : KLS.LogConcave μ)
    (hiso : KLS.Isotropic μ) : ∃ ρ : E → ℝ, KLS.IsBorellDensity (μ : Measure E) volume ρ := by
  have hi :=
    hLC.interior_support_nonempty_of_affineSupport_eq_top
      (affineSupport_eq_top_of_isotropic hiso)
  exact
    hLC.exists_isBorellDensity_of_interior_support_nonempty volume hi
      (hLC.absolutelyContinuous_of_interior_support_nonempty volume hi)

/-- A literature Poincaré bound for a regular law is a smooth-test bound. -/
theorem RegularPotential.smoothTest_holds_of_localSlope_le {V : E → ℝ} {a b : ℝ}
    (hV : KLS.RegularPotential V a b) (C : NNReal)
    (hC : Poincare.LocalSlope.Intrinsic.optimalConstant hV.law ≤ (C : ENNReal)) :
    Poincare.SmoothTest.Holds (hV.law : Measure E) (C : ℝ) := by
  apply (Poincare.SmoothTest.holds_iff_ambient hV.law C).mpr
  apply (Poincare.SmoothGradient.Ambient.holds_iff_constant_le hV.law C).mpr
  rw [← Poincare.SmoothTest.constant_eq_ambient,
    hV.logConcave_law.smoothTest_constant_eq_localSlope]
  exact hC

/--
**Reduction of the Poincaré bound to isotropic regular laws** (BKL Section 2, p. 5): if every
isotropic regular law on `E` (positive upper curvature) has literature constant `≤ K`, so does every
isotropic log-concave law on `E`: approximate by regular laws
(`GaussianSmoothing.exists_regularSeq_limits`),
transfer the bound with the envelope coefficient `K(1+‖Cov−Id‖) → K`, and pass to the weak limit. -/
theorem localSlope_le_of_regular_isotropic_bound {K : NNReal}
    (hBound :
      ∀ {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b),
        0 < b →
          KLS.Isotropic hV.law → Poincare.LocalSlope.Intrinsic.optimalConstant hV.law ≤ (K : ENNReal))
    (μ : ProbabilityMeasure E) (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ) :
    Poincare.LocalSlope.Intrinsic.optimalConstant μ ≤ (K : ENNReal) := by
  by_cases hdim : Module.finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff.mp hdim
    rw [Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton]
    exact bot_le
  obtain ⟨ρ, hρ⟩ := exists_isBorellDensity_of_isotropic hLC hiso
  obtain ⟨k, _hkl, _hpos, _hδ, _hregular, _hb, hweak, _hmean, _hsecond, hcov⟩ :=
    GaussianSmoothing.exists_regularSeq_limits hρ hiso.memLp_two
  let ν : ℕ → ProbabilityMeasure E := fun n => GaussianSmoothing.regularSeq hρ n (k n)
  let Cseq : ℕ → NNReal := fun n =>
    K * (1 + ‖Covariance.operator (ν n : Measure E) - ContinuousLinearMap.id ℝ E‖₊)
  have hcov' :
    Tendsto (fun n => Covariance.operator (ν n : Measure E)) atTop
      (𝓝 (ContinuousLinearMap.id ℝ E)) := by
    simpa only [ν, hiso.covariance_identity] using hcov
  have hC : Tendsto Cseq atTop (𝓝 K) := by
    apply NNReal.tendsto_coe.mp
    simpa only [Cseq, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, coe_nnnorm] using
      RegularPotential.envelope_coefficient_tendsto K hcov'
  apply KLS.LogConcave.localSlope_constant_le_of_tendsto ν μ hLC Cseq K hweak hC
  intro n
  have hV :=
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.regularPotential_quadraticPotential
      hρ (by positivity : (0 : ℝ) < (n : ℝ) + 1) (GaussianSmoothing.tiltRate_pos (k n))
  have hlit := RegularPotential.localSlope_le_covariance_envelope hBound hV
  have hCeq :
    (Cseq n : ENNReal) =
      ENNReal.ofReal
        ((K : ℝ) *
          (1 + ‖Covariance.operator (hV.law : Measure E) - ContinuousLinearMap.id ℝ E‖)) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    rfl
  apply RegularPotential.smoothTest_holds_of_localSlope_le hV (Cseq n)
  rw [hCeq]
  exact hlit

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- In positive dimension a regular potential has `b > 0`. -/
private theorem regular_upper_pos {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
    (hdim : 0 < Module.finrank ℝ E) : 0 < b := by
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdim
  have hq : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hab : a * ‖v‖ ^ 2 ≤ b * ‖v‖ ^ 2 := (hV.lower 0 v).trans (hV.upper 0 v)
  have hleft := mul_pos hV.pos hq
  by_contra hb
  have hright : b * ‖v‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hb) (sq_nonneg _)
  linarith

/--
The same reduction from a bound for isotropic regular laws on `ℝⁿ`, `n > 0` (standard coordinates).
-/
theorem localSlope_le_of_euclidean_regular_isotropic_bound {K : NNReal}
    (hEuclidean :
      ∀ (n : ℕ),
        0 < n →
          ∀ (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ) (hV : KLS.RegularPotential V a b),
            0 < b →
              KLS.Isotropic hV.law →
                Poincare.LocalSlope.Intrinsic.optimalConstant hV.law ≤ (K : ENNReal))
    (μ : ProbabilityMeasure E) (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ) :
    Poincare.LocalSlope.Intrinsic.optimalConstant μ ≤ (K : ENNReal) := by
  apply localSlope_le_of_regular_isotropic_bound ?_ μ hLC hiso
  intro V a b hV _hb hViso
  apply RegularPotential.localSlope_le_of_euclidean_bound ?_ hV hViso
  intro n hn U α β hU hUiso
  exact hEuclidean n hn U α β hU (regular_upper_pos hU (by simpa using hn)) hUiso

/-- `KLS.IsotropicBound K` (every isotropic log-concave law in every finite-dimensional space, any
universe) follows from the bound for isotropic regular laws on `ℝⁿ`, `n > 0`. -/
theorem isotropicBound_of_euclidean_regular_isotropic_bound {K : NNReal}
    (hEuclidean : ∀ (n : ℕ), 0 < n →
      ∀ (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ) (hV : KLS.RegularPotential V a b),
        0 < b → KLS.Isotropic hV.law →
          Poincare.LocalSlope.Intrinsic.optimalConstant hV.law ≤ (K : ENNReal)) :
    KLS.IsotropicBound.{u} K := by
  intro F _ _ _ _ _ _ _ μ hLC hiso
  exact localSlope_le_of_euclidean_regular_isotropic_bound hEuclidean μ hLC hiso

end FunctionalInequalities.KLS.LogConcave

end
