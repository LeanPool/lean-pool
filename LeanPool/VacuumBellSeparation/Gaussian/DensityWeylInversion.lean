/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WeylCoherentInversion
public import LeanPool.VacuumBellSeparation.Gaussian.DensityExpectationIndependence
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Actual density characteristic determines the coherent diagonal

The square-root basis series is absolutely summable. Unitary vector-norm
bounds justify exchange with the scalar Gaussian-weighted Weyl integral.
Weak inversion therefore gives the actual coherent diagonal of every
positive trace-class operator. The characteristic is its previously
constructed complex density expectation, not a positive-trace totalization.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory ContinuousLinearMap Filter Topology InnerProductSpace
open scoped ComplexConjugate

theorem densityExpectation_rankOne {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : 0 ≤ A) (w : E) :
    densityExpectation b A (rankOne ℂ w w) = inner ℂ w (A w) := by
  let S := CFC.sqrt A
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have ht (i : ι) : inner ℂ (S (b i)) (rankOne ℂ w w (S (b i))) =
      inner ℂ (S w) (b i) * inner ℂ (b i) (S w) := by
    rw [rankOne_apply, inner_smul_right,
      ← S.adjoint_inner_left (b i) w, ← S.adjoint_inner_right (b i) w, hS.adjoint_eq]
  change (∑' i, inner ℂ (S (b i)) (rankOne ℂ w w (S (b i)))) = _
  simp_rw [ht]
  rw [(b.hasSum_inner_mul_inner (S w) (S w)).tsum_eq,
    ← S.adjoint_inner_right, hS.adjoint_eq, ← mul_apply_eq_comp]
  change inner ℂ w ((CFC.sqrt A * CFC.sqrt A) w) = _
  rw [← pow_two, CFC.sq_sqrt A hA]

theorem norm_familyWeyl_term_le {ι : Type*} {m : ℕ}
    (v : ι → MultiModeOscillatorSpace m) (z : MultiModePhaseSpace m) (i : ι) :
    ‖inner ℂ (v i) (multiOscillatorWeyl z (v i))‖ ≤ ‖v i‖ ^ 2 := by
  calc
    _ ≤ ‖v i‖ * ‖multiOscillatorWeyl z (v i)‖ := norm_inner_le_norm _ _
    _ = _ := by rw [norm_multiOscillatorWeyl_apply, pow_two]

theorem continuous_familyExpectation_weyl {ι : Type*} {m : ℕ}
    (v : ι → MultiModeOscillatorSpace m) (hv : Summable fun i => ‖v i‖ ^ 2) :
    Continuous (fun z : MultiModePhaseSpace m => familyExpectation v (multiOscillatorWeyl z)) := by
  rw [continuous_iff_continuousAt]
  intro z
  apply tendsto_tsum_of_dominated_convergence hv
  · intro i
    exact tendsto_const_nhds.inner (continuous_multiOscillatorWeyl_apply (v i)).continuousAt
  · exact Filter.Eventually.of_forall fun z i => norm_familyWeyl_term_le v z i

theorem norm_familyExpectation_weyl_le {ι : Type*} {m : ℕ}
    (v : ι → MultiModeOscillatorSpace m) (hv : Summable fun i => ‖v i‖ ^ 2)
    (z : MultiModePhaseSpace m) :
    ‖familyExpectation v (multiOscillatorWeyl z)‖ ≤ ∑' i, ‖v i‖ ^ 2 :=
  tsum_of_norm_bounded hv.hasSum (norm_familyWeyl_term_le v z)

theorem integrable_familyWeyl_convolution {ι : Type*} {m : ℕ}
    (v : ι → MultiModeOscillatorSpace m) (hv : Summable fun i => ‖v i‖ ^ 2)
    (w : MultiModePhaseSpace m) :
    Integrable (fun z : Fin m → ℂ => weylVacuumWeight m z *
      coherentFourierPhase w (WithLp.toLp 2 z) *
        familyExpectation v (multiOscillatorWeyl (WithLp.toLp 2 z))) := by
  have hc : Continuous (fun z : Fin m → ℂ => weylVacuumWeight m z *
      coherentFourierPhase w (WithLp.toLp 2 z) *
        familyExpectation v (multiOscillatorWeyl (WithLp.toLp 2 z))) := by
    have hf := (continuous_familyExpectation_weyl v hv).comp (PiLp.continuous_toLp 2 _)
    unfold weylVacuumWeight coherentFourierPhase
    fun_prop
  apply ((integrable_weylVacuumWeight m).norm.mul_const (∑' i, ‖v i‖ ^ 2)).mono'
    hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [norm_mul, norm_mul, norm_coherentFourierPhase, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_familyExpectation_weyl_le v hv _) (norm_nonneg _)

theorem integral_familyWeyl_convolution {ι : Type*} [Countable ι] {m : ℕ}
    (v : ι → MultiModeOscillatorSpace m) (hv : Summable fun i => ‖v i‖ ^ 2)
    (w : MultiModePhaseSpace m) :
    (∫ z : Fin m → ℂ, weylVacuumWeight m z *
      coherentFourierPhase w (WithLp.toLp 2 z) *
        familyExpectation v (multiOscillatorWeyl (WithLp.toLp 2 z))) =
      (Real.pi : ℂ) ^ m * familyExpectation v
        (rankOne ℂ (multiCoherentVector w) (multiCoherentVector w)) := by
  let F (i : ι) (z : Fin m → ℂ) := weylVacuumWeight m z *
    coherentFourierPhase w (WithLp.toLp 2 z) *
      inner ℂ (v i) (multiOscillatorWeyl (WithLp.toLp 2 z) (v i))
  have hs := hasSum_integral_of_dominated_convergence
    (fun i z => ‖weylVacuumWeight m z‖ * ‖v i‖ ^ 2)
    (fun i => (integrable_coherentWeyl_kernel w (v i) (v i)).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall fun z => by
      change ‖F i z‖ ≤ _
      simp only [F, norm_mul, norm_coherentFourierPhase, mul_one]
      exact mul_le_mul_of_nonneg_left (norm_familyWeyl_term_le v _ i) (norm_nonneg _))
    (Filter.Eventually.of_forall fun z => hv.mul_left ‖weylVacuumWeight m z‖)
    (by
      simp only [tsum_mul_left]
      exact (integrable_weylVacuumWeight m).norm.mul_const _)
    (Filter.Eventually.of_forall fun z =>
      (summable_familyExpectation_terms v hv (multiOscillatorWeyl
        (WithLp.toLp 2 z))).hasSum.mul_left
        (weylVacuumWeight m z * coherentFourierPhase w (WithLp.toLp 2 z)))
  change (∫ z : Fin m → ℂ, weylVacuumWeight m z *
    coherentFourierPhase w (WithLp.toLp 2 z) *
      ∑' i, inner ℂ (v i) (multiOscillatorWeyl (WithLp.toLp 2 z) (v i))) = _
  rw [← hs.tsum_eq]
  simp only [integral_coherentWeyl_kernel]
  have he (i : ι) : (Real.pi : ℂ) ^ m * inner ℂ (v i) (multiCoherentVector w) *
      inner ℂ (multiCoherentVector w) (v i) =
      (Real.pi : ℂ) ^ m * inner ℂ (v i)
        (rankOne ℂ (multiCoherentVector w) (multiCoherentVector w) (v i)) := by
    rw [rankOne_apply, inner_smul_right]
    ring
  simp_rw [he]
  rw [tsum_mul_left]
  rfl

/-- Actual Gaussian convolution of the complex characteristic equals
the actual coherent diagonal. This holds for every positive trace-class
input before any Gaussian characteristic assumption is imposed. -/
theorem integral_densityWeyl_convolution {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (w : MultiModePhaseSpace m) :
    (∫ z : Fin m → ℂ, weylVacuumWeight m z *
      coherentFourierPhase w (WithLp.toLp 2 z) *
        densityExpectation (multiModeNumberBasis m) A
          (multiOscillatorWeyl (WithLp.toLp 2 z))) =
      (Real.pi : ℂ) ^ m * inner ℂ (multiCoherentVector w) (A (multiCoherentVector w)) := by
  rw [show (fun z : Fin m → ℂ => weylVacuumWeight m z *
      coherentFourierPhase w (WithLp.toLp 2 z) *
        densityExpectation (multiModeNumberBasis m) A (multiOscillatorWeyl (WithLp.toLp 2 z))) =
      fun z => weylVacuumWeight m z * coherentFourierPhase w (WithLp.toLp 2 z) *
        familyExpectation (fun i => CFC.sqrt A (multiModeNumberBasis m i))
          (multiOscillatorWeyl (WithLp.toLp 2 z)) from rfl,
    integral_familyWeyl_convolution (fun i => CFC.sqrt A (multiModeNumberBasis m i))
      (summable_sqrt_basis_norm_sq (multiModeNumberBasis m) hA) w]
  change (Real.pi : ℂ) ^ m * densityExpectation (multiModeNumberBasis m) A
    (rankOne ℂ (multiCoherentVector w) (multiCoherentVector w)) = _
  rw [densityExpectation_rankOne _ hA.1]

theorem integrable_densityWeyl_convolution {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (w : MultiModePhaseSpace m) :
    Integrable (fun z : Fin m → ℂ => weylVacuumWeight m z *
      coherentFourierPhase w (WithLp.toLp 2 z) *
        densityExpectation (multiModeNumberBasis m) A
          (multiOscillatorWeyl (WithLp.toLp 2 z))) :=
  integrable_familyWeyl_convolution _ (summable_sqrt_basis_norm_sq (multiModeNumberBasis m) hA) w

end VacuumBellSeparation.Gaussian
