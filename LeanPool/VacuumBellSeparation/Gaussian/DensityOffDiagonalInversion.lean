/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DensityWeylInversion

/-!
# Actual off-diagonal coherent matrix elements from Weyl expectations

Left and right displacement of the proved weak vacuum inversion gives
mixed coherent projectors. Absolute square-root-basis dominated convergence
then gives the actual off-diagonal density kernel. The left and right
labels are independent, and the complex density expectation is used on
the nonpositive Weyl product.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory ContinuousLinearMap Filter Topology InnerProductSpace
open scoped ComplexConjugate

theorem densityExpectation_rankOne_mixed {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : 0 ≤ A) (u v : E) :
    densityExpectation b A (rankOne ℂ u v) = inner ℂ v (A u) := by
  let S := CFC.sqrt A
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have ht (i : ι) : inner ℂ (S (b i)) (rankOne ℂ u v (S (b i))) =
      inner ℂ (S v) (b i) * inner ℂ (b i) (S u) := by
    rw [rankOne_apply, inner_smul_right,
      ← S.adjoint_inner_left (b i) v, ← S.adjoint_inner_right (b i) u, hS.adjoint_eq]
  change (∑' i, inner ℂ (S (b i)) (rankOne ℂ u v (S (b i)))) = _
  simp_rw [ht]
  rw [(b.hasSum_inner_mul_inner (S v) (S u)).tsum_eq,
    ← S.adjoint_inner_right, hS.adjoint_eq, ← mul_apply_eq_comp]
  change inner ℂ v ((CFC.sqrt A * CFC.sqrt A) u) = _
  rw [← pow_two, CFC.sq_sqrt A hA]

/-- Mixed displacement given by `multiOscillatorWeyl b * multiOscillatorWeyl z *
(multiOscillatorWeyl a).adjoint`. -/
def mixedDisplacement {m : ℕ} (b a z : MultiModePhaseSpace m) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  multiOscillatorWeyl b * multiOscillatorWeyl z * (multiOscillatorWeyl a).adjoint

theorem inner_mixedDisplacement {m : ℕ} (b a z : MultiModePhaseSpace m)
    (x y : MultiModeOscillatorSpace m) :
    inner ℂ x (mixedDisplacement b a z y) =
      inner ℂ ((multiOscillatorWeyl b).adjoint x)
        (multiOscillatorWeyl z ((multiOscillatorWeyl a).adjoint y)) := by
  rw [(multiOscillatorWeyl b).adjoint_inner_left]
  rfl

theorem norm_mixedDisplacement_apply {m : ℕ} (b a z : MultiModePhaseSpace m)
    (x : MultiModeOscillatorSpace m) : ‖mixedDisplacement b a z x‖ = ‖x‖ := by
  simp only [mixedDisplacement, mul_apply_eq_comp, multiOscillatorWeyl_adjoint,
    norm_multiOscillatorWeyl_apply]

theorem integrable_mixedWeyl_kernel {m : ℕ} (b a : MultiModePhaseSpace m)
    (x y : MultiModeOscillatorSpace m) :
    Integrable (fun z : Fin m → ℂ => weylVacuumWeight m z *
      inner ℂ x (mixedDisplacement b a (WithLp.toLp 2 z) y)) := by
  have h := (integrable_weylVacuumOrbit ((multiOscillatorWeyl a).adjoint y)).const_inner (𝕜 := ℂ)
    ((multiOscillatorWeyl b).adjoint x)
  simpa only [inner_smul_right, ← inner_mixedDisplacement] using h

theorem integral_mixedWeyl_kernel {m : ℕ} (b a : MultiModePhaseSpace m)
    (x y : MultiModeOscillatorSpace m) :
    (∫ z : Fin m → ℂ, weylVacuumWeight m z *
      inner ℂ x (mixedDisplacement b a (WithLp.toLp 2 z) y)) =
        (Real.pi : ℂ) ^ m * inner ℂ x (multiCoherentVector b) *
          inner ℂ (multiCoherentVector a) y := by
  simp_rw [inner_mixedDisplacement]
  rw [integral_gaussianWeyl_kernel,
    (multiOscillatorWeyl b).adjoint_inner_left,
    (multiOscillatorWeyl a).adjoint_inner_right,
    multiOscillatorWeyl_exponential_zero, multiOscillatorWeyl_exponential_zero]

theorem norm_familyMixedWeyl_term_le {ι : Type*} {m : ℕ}
    (v : ι → MultiModeOscillatorSpace m) (b a z : MultiModePhaseSpace m) (i : ι) :
    ‖inner ℂ (v i) (mixedDisplacement b a z (v i))‖ ≤ ‖v i‖ ^ 2 := by
  calc
    _ ≤ ‖v i‖ * ‖mixedDisplacement b a z (v i)‖ := norm_inner_le_norm _ _
    _ = _ := by rw [norm_mixedDisplacement_apply, pow_two]

theorem continuous_familyExpectation_mixedDisplacement {ι : Type*} {m : ℕ}
    (v : ι → MultiModeOscillatorSpace m) (hv : Summable fun i => ‖v i‖ ^ 2)
    (b a : MultiModePhaseSpace m) :
    Continuous (fun z : MultiModePhaseSpace m => familyExpectation v
      (mixedDisplacement b a z)) := by
  rw [continuous_iff_continuousAt]
  intro z
  apply tendsto_tsum_of_dominated_convergence hv
  · intro i
    have hc := (multiOscillatorWeyl b).continuous.comp
      (continuous_multiOscillatorWeyl_apply ((multiOscillatorWeyl a).adjoint (v i)))
    exact tendsto_const_nhds.inner hc.continuousAt
  · exact Filter.Eventually.of_forall fun z i => norm_familyMixedWeyl_term_le v b a z i

theorem integrable_familyMixedWeyl {ι : Type*} {m : ℕ}
    (v : ι → MultiModeOscillatorSpace m) (hv : Summable fun i => ‖v i‖ ^ 2)
    (b a : MultiModePhaseSpace m) :
    Integrable (fun z : Fin m → ℂ => weylVacuumWeight m z *
      familyExpectation v (mixedDisplacement b a (WithLp.toLp 2 z))) := by
  have hc : Continuous (fun z : Fin m → ℂ => weylVacuumWeight m z *
      familyExpectation v (mixedDisplacement b a (WithLp.toLp 2 z))) := by
    have hf := (continuous_familyExpectation_mixedDisplacement v hv b a).comp
      (PiLp.continuous_toLp 2 _)
    have hw : Continuous (weylVacuumWeight m) := by unfold weylVacuumWeight; fun_prop
    exact hw.mul hf
  apply ((integrable_weylVacuumWeight m).norm.mul_const (∑' i, ‖v i‖ ^ 2)).mono'
    hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (tsum_of_norm_bounded hv.hasSum (norm_familyMixedWeyl_term_le v b a _)) (norm_nonneg _)

theorem integral_familyMixedWeyl {ι : Type*} [Countable ι] {m : ℕ}
    (v : ι → MultiModeOscillatorSpace m) (hv : Summable fun i => ‖v i‖ ^ 2)
    (b a : MultiModePhaseSpace m) :
    (∫ z : Fin m → ℂ, weylVacuumWeight m z *
      familyExpectation v (mixedDisplacement b a (WithLp.toLp 2 z))) =
        (Real.pi : ℂ) ^ m * familyExpectation v
          (rankOne ℂ (multiCoherentVector b) (multiCoherentVector a)) := by
  let F (i : ι) (z : Fin m → ℂ) := weylVacuumWeight m z *
    inner ℂ (v i) (mixedDisplacement b a (WithLp.toLp 2 z) (v i))
  have hs := hasSum_integral_of_dominated_convergence
    (fun i z => ‖weylVacuumWeight m z‖ * ‖v i‖ ^ 2)
    (fun i => (integrable_mixedWeyl_kernel b a (v i) (v i)).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall fun z => by
      change ‖F i z‖ ≤ _
      dsimp only [F]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_familyMixedWeyl_term_le v b a _ i) (norm_nonneg _))
    (Filter.Eventually.of_forall fun z => hv.mul_left ‖weylVacuumWeight m z‖)
    (by
      simp only [tsum_mul_left]
      exact (integrable_weylVacuumWeight m).norm.mul_const _)
    (Filter.Eventually.of_forall fun z =>
      (summable_familyExpectation_terms v hv (mixedDisplacement b a
        (WithLp.toLp 2 z))).hasSum.mul_left
        (weylVacuumWeight m z))
  have hsum : (∫ z : Fin m → ℂ, weylVacuumWeight m z *
      familyExpectation v (mixedDisplacement b a (WithLp.toLp 2 z))) =
      ∑' i, ∫ z : Fin m → ℂ, weylVacuumWeight m z *
        inner ℂ (v i) (mixedDisplacement b a (WithLp.toLp 2 z) (v i)) :=
    hs.tsum_eq.symm
  rw [hsum]
  simp only [integral_mixedWeyl_kernel]
  have he (i : ι) : (Real.pi : ℂ) ^ m * inner ℂ (v i) (multiCoherentVector b) *
      inner ℂ (multiCoherentVector a) (v i) =
      (Real.pi : ℂ) ^ m * inner ℂ (v i)
        (rankOne ℂ (multiCoherentVector b) (multiCoherentVector a) (v i)) := by
    rw [rankOne_apply, inner_smul_right]
    ring
  simp_rw [he]
  exact tsum_mul_left

/-- Actual off-diagonal coherent density kernel, with independent labels. -/
theorem integral_densityMixedWeyl {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (b a : MultiModePhaseSpace m) :
    (∫ z : Fin m → ℂ, weylVacuumWeight m z *
      densityExpectation (multiModeNumberBasis m) A
        (mixedDisplacement b a (WithLp.toLp 2 z))) =
        (Real.pi : ℂ) ^ m * inner ℂ (multiCoherentVector a) (A (multiCoherentVector b)) := by
  change (∫ z : Fin m → ℂ, weylVacuumWeight m z *
    familyExpectation (fun i => CFC.sqrt A (multiModeNumberBasis m i))
      (mixedDisplacement b a (WithLp.toLp 2 z))) = _
  calc
    _ = (Real.pi : ℂ) ^ m * familyExpectation
        (fun i => CFC.sqrt A (multiModeNumberBasis m i))
        (rankOne ℂ (multiCoherentVector b) (multiCoherentVector a)) :=
      integral_familyMixedWeyl _
        (summable_sqrt_basis_norm_sq (multiModeNumberBasis m) hA) b a
    _ = _ := by
      change (Real.pi : ℂ) ^ m * densityExpectation (multiModeNumberBasis m) A
        (rankOne ℂ (multiCoherentVector b) (multiCoherentVector a)) = _
      rw [densityExpectation_rankOne_mixed _ hA.1]

theorem integrable_densityMixedWeyl {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (b a : MultiModePhaseSpace m) :
    Integrable (fun z : Fin m → ℂ => weylVacuumWeight m z *
      densityExpectation (multiModeNumberBasis m) A
        (mixedDisplacement b a (WithLp.toLp 2 z))) :=
  integrable_familyMixedWeyl _ (summable_sqrt_basis_norm_sq (multiModeNumberBasis m) hA) b a

end VacuumBellSeparation.Gaussian
