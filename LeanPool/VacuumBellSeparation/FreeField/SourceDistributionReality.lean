/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceDistributionReconstruction

/-!
# Reality of the completed position distributions

Real literal sources obey conjugation of test pairings. Continuity extends
this identity to the actual real source completion. Consequently a complex
combination of two such real distributions vanishes only when both vanish.
This fact concerns position distributions, not injectivity of the physical
complex source map, which additionally needs the compact Fourier argument.
-/

@[expose] public section

open MeasureTheory
open scoped SchwartzMap ComplexConjugate

namespace VacuumBellSeparation

/-- Pointwise complex conjugation as an actual real-linear Schwartz map. -/
noncomputable def spatialSchwartzConjugate :
    SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ →L[ℝ]
      SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap

@[simp] theorem spatialSchwartzConjugate_apply
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (x : EuclideanSpace ℝ (Fin 3)) :
    spatialSchwartzConjugate φ x = conj (φ x) := rfl

/-- A complex-linear distribution is real if conjugating its test conjugates its value. -/
def IsRealSpatialDistribution (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) : Prop :=
  ∀ φ, T (spatialSchwartzConjugate φ) = conj (T φ)

theorem isRealSpatialDistribution_spatialSchwartz (f : SpatialTestFunction) :
    IsRealSpatialDistribution (spatialSchwartz f :
      TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) := by
  intro φ
  rw [SchwartzMap.coe_apply, SchwartzMap.coe_apply, ← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [spatialSchwartzConjugate_apply, spatialSchwartz_apply, smul_eq_mul,
      map_mul, Complex.conj_ofReal]

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

theorem isReal_sourceFirstDistribution (u : SourceHilbert hm U) :
    IsRealSpatialDistribution (sourceFirstDistribution hm U u) := by
  intro φ
  have hleft : Continuous (fun v : SourceHilbert hm U =>
      sourceFirstDistribution hm U v (spatialSchwartzConjugate φ)) :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ
      (spatialSchwartzConjugate φ)).continuous.comp (sourceFirstDistribution hm U).continuous
  have hright : Continuous (fun v : SourceHilbert hm U =>
      conj (sourceFirstDistribution hm U v φ)) :=
    Complex.continuous_conj.comp
      ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).continuous.comp
        (sourceFirstDistribution hm U).continuous)
  refine UniformSpace.Completion.induction_on u (isClosed_eq hleft hright) ?_
  intro v
  rw [sourceFirstDistribution_coe]
  exact isRealSpatialDistribution_spatialSchwartz v.1.1 φ

theorem isReal_sourceSecondDistribution (u : SourceHilbert hm U) :
    IsRealSpatialDistribution (sourceSecondDistribution hm U u) := by
  intro φ
  have hleft : Continuous (fun v : SourceHilbert hm U =>
      sourceSecondDistribution hm U v (spatialSchwartzConjugate φ)) :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ
      (spatialSchwartzConjugate φ)).continuous.comp (sourceSecondDistribution hm U).continuous
  have hright : Continuous (fun v : SourceHilbert hm U =>
      conj (sourceSecondDistribution hm U v φ)) :=
    Complex.continuous_conj.comp
      ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).continuous.comp
        (sourceSecondDistribution hm U).continuous)
  refine UniformSpace.Completion.induction_on u (isClosed_eq hleft hright) ?_
  intro v
  rw [sourceSecondDistribution_coe]
  exact isRealSpatialDistribution_spatialSchwartz v.1.2 φ

/-- The real and imaginary distribution components cannot cancel each other. -/
theorem real_distributions_add_I_smul_eq_zero
    {T S : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ}
    (hT : IsRealSpatialDistribution T) (hS : IsRealSpatialDistribution S)
    (h : T + Complex.I • S = 0) : T = 0 ∧ S = 0 := by
  have hpoint (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) : T φ = 0 ∧ S φ = 0 := by
    have hp : T φ + Complex.I * S φ = 0 := DFunLike.congr_fun h φ
    have hn := congrArg conj (DFunLike.congr_fun h (spatialSchwartzConjugate φ))
    change conj (T (spatialSchwartzConjugate φ) + Complex.I *
      S (spatialSchwartzConjugate φ)) = conj 0 at hn
    rw [hT φ, hS φ, map_add, map_mul, Complex.conj_conj,
      Complex.conj_I, Complex.conj_conj, map_zero] at hn
    have ht : T φ = 0 := by linear_combination (1 / 2 : ℂ) * hp + (1 / 2 : ℂ) * hn
    have hs : Complex.I * S φ = 0 := by rw [ht, zero_add] at hp; exact hp
    exact ⟨ht, (mul_eq_zero.mp hs).resolve_left Complex.I_ne_zero⟩
  constructor
  · ext φ
    exact (hpoint φ).1
  · ext φ
    exact (hpoint φ).2

/-- Joint position-distribution injectivity also separates real and imaginary
completed sources. No physical complex-source injectivity is assumed here. -/
theorem source_complex_distributions_eq_zero (u v : SourceHilbert hm U)
    (hf : sourceFirstDistribution hm U u + Complex.I • sourceFirstDistribution hm U v = 0)
    (hg : sourceSecondDistribution hm U u + Complex.I • sourceSecondDistribution hm U v = 0) :
    u = 0 ∧ v = 0 := by
  have hf' := real_distributions_add_I_smul_eq_zero
    (isReal_sourceFirstDistribution hm U u) (isReal_sourceFirstDistribution hm U v) hf
  have hg' := real_distributions_add_I_smul_eq_zero
    (isReal_sourceSecondDistribution hm U u) (isReal_sourceSecondDistribution hm U v) hg
  exact ⟨source_eq_zero_of_distributions_eq_zero hm U u hf'.1 hg'.1,
    source_eq_zero_of_distributions_eq_zero hm U v hf'.2 hg'.2⟩

end VacuumBellSeparation
