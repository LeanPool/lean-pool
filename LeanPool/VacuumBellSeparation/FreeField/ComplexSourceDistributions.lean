/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSource
public import LeanPool.VacuumBellSeparation.FreeField.SourceDistributionReality

/-!
# Actual complexified position and momentum distributions

Continuous real source distribution maps are complexified on the already
constructed Hilbert complexification. The resulting position pair is
injective, has the actual compact-support bound, and obeys the normalized
Fourier identities. The physical complex source kernel gives the genuine
distributional relation `F + iω G = 0`. Showing that this relation forces
both compact position distributions to vanish remains the analytic step.
-/

@[expose] public section

open MeasureTheory
open VacuumBellSeparation.Gaussian.HilbertComplexification
open scoped SchwartzMap

namespace VacuumBellSeparation

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- Complexification into the actual locally convex distribution space; no norm is assigned to
it. -/
noncomputable def complexifySourceDistribution
    (D : SourceHilbert hm U →L[ℝ] TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) :
    ComplexSourceHilbert hm U →L[ℂ] TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ where
  toFun z := D z.re + Complex.I • D z.im
  map_add' z w := by simp [smul_add]; abel
  map_smul' c z := by
    have hreal (r : ℝ) (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) :
        r • T = (r : ℂ) • T := by
      ext φ
      simp only [smul_apply, Complex.real_smul, smul_eq_mul]
    have hre : (c.re : ℂ) + Complex.I * (c.im : ℂ) = c := by
      apply Complex.ext <;> simp
    have him : -(c.im : ℂ) + Complex.I * (c.re : ℂ) = c * Complex.I := by
      apply Complex.ext <;> simp
    simp only [re_smul, im_smul, map_sub, map_add, map_smul,
      hreal, smul_add, smul_smul]
    calc
      ((c.re : ℂ) • D z.re - (c.im : ℂ) • D z.im) +
          ((Complex.I * (c.im : ℂ)) • D z.re +
            (Complex.I * (c.re : ℂ)) • D z.im) =
          ((c.re : ℂ) + Complex.I * (c.im : ℂ)) • D z.re +
            (-(c.im : ℂ) + Complex.I * (c.re : ℂ)) • D z.im := by module
      _ = c • D z.re + (c * Complex.I) • D z.im := by rw [hre, him]
  cont := by
    have hre : Continuous (fun z : ComplexSourceHilbert hm U => z.re) := WithLp.continuous_fst 2 _ _
    have him : Continuous (fun z : ComplexSourceHilbert hm U => z.im) := WithLp.continuous_snd 2 _ _
    exact (D.continuous.comp hre).add ((D.continuous.comp him).const_smul Complex.I)

@[simp] theorem complexifySourceDistribution_apply
    (D : SourceHilbert hm U →L[ℝ] TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (z : ComplexSourceHilbert hm U) :
    complexifySourceDistribution hm U D z = D z.re + Complex.I • D z.im := rfl

/-- Continuous linear map for the complex source first distribution, of type `ComplexSourceHilbert
hm U →L[ℂ] TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ`. -/
noncomputable def complexSourceFirstDistribution : ComplexSourceHilbert hm U →L[ℂ]
    TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ :=
  complexifySourceDistribution hm U (sourceFirstDistribution hm U)

/-- Continuous linear map for the complex source second distribution, of type `ComplexSourceHilbert
hm U →L[ℂ] TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ`. -/
noncomputable def complexSourceSecondDistribution : ComplexSourceHilbert hm U →L[ℂ]
    TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ :=
  complexifySourceDistribution hm U (sourceSecondDistribution hm U)

/-- Continuous linear map for the complex source first momentum, of type `ComplexSourceHilbert hm U
→L[ℂ] TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ`. -/
noncomputable def complexSourceFirstMomentum : ComplexSourceHilbert hm U →L[ℂ]
    TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ :=
  complexifySourceDistribution hm U (sourceFirstMomentum hm U)

/-- Continuous linear map for the complex source second momentum, of type `ComplexSourceHilbert hm
U →L[ℂ] TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ`. -/
noncomputable def complexSourceSecondMomentum : ComplexSourceHilbert hm U →L[ℂ]
    TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ :=
  complexifySourceDistribution hm U (sourceSecondMomentum hm U)

theorem complexSourceFirstDistribution_fourier (z : ComplexSourceHilbert hm U) :
    complexSourceFirstDistribution hm U z =
      sourceInverseFourier (complexSourceFirstMomentum hm U z) := by
  change sourceInverseFourier (sourceFirstMomentum hm U z.re) +
      Complex.I • sourceInverseFourier (sourceFirstMomentum hm U z.im) =
    sourceInverseFourier (sourceFirstMomentum hm U z.re + Complex.I • sourceFirstMomentum hm U z.im)
  rw [map_add, map_smul]

theorem complexSourceSecondDistribution_fourier (z : ComplexSourceHilbert hm U) :
    complexSourceSecondDistribution hm U z =
      sourceInverseFourier (complexSourceSecondMomentum hm U z) := by
  change sourceInverseFourier (sourceSecondMomentum hm U z.re) +
      Complex.I • sourceInverseFourier (sourceSecondMomentum hm U z.im) =
    sourceInverseFourier (sourceSecondMomentum hm U z.re + Complex.I • sourceSecondMomentum hm U
      z.im)
  rw [map_add, map_smul]

/-- The actual pair of complex position distributions is faithful to the source complexification. -/
theorem complexSource_eq_zero_of_distributions_eq_zero (z : ComplexSourceHilbert hm U)
    (hf : complexSourceFirstDistribution hm U z = 0)
    (hg : complexSourceSecondDistribution hm U z = 0) : z = 0 := by
  have h := source_complex_distributions_eq_zero hm U z.re z.im hf hg
  apply Gaussian.HilbertComplexification.ext
  · simpa using h.1
  · simpa using h.2

theorem complexSourceDistributions_injective :
    Function.Injective (fun z : ComplexSourceHilbert hm U =>
      (complexSourceFirstDistribution hm U z, complexSourceSecondDistribution hm U z)) := by
  intro z w h
  apply sub_eq_zero.mp
  apply complexSource_eq_zero_of_distributions_eq_zero hm U (z - w)
  · rw [map_sub, (Prod.mk.inj h).1, sub_self]
  · rw [map_sub, (Prod.mk.inj h).2, sub_self]

theorem complexSourceFirstDistribution_isVanishingOn (z : ComplexSourceHilbert hm U) :
    Distribution.IsVanishingOn (complexSourceFirstDistribution hm U z) (closure U)ᶜ := by
  intro φ hφ
  change sourceFirstDistribution hm U z.re φ + Complex.I * sourceFirstDistribution hm U z.im φ = 0
  rw [sourceFirstDistribution_isVanishingOn hm U z.re φ hφ,
    sourceFirstDistribution_isVanishingOn hm U z.im φ hφ, mul_zero, add_zero]

theorem complexSourceSecondDistribution_isVanishingOn (z : ComplexSourceHilbert hm U) :
    Distribution.IsVanishingOn (complexSourceSecondDistribution hm U z) (closure U)ᶜ := by
  intro φ hφ
  change sourceSecondDistribution hm U z.re φ + Complex.I * sourceSecondDistribution hm U z.im φ = 0
  rw [sourceSecondDistribution_isVanishingOn hm U z.re φ hφ,
    sourceSecondDistribution_isVanishingOn hm U z.im φ hφ, mul_zero, add_zero]

/-- Complexification preserves the actual momentum reconstruction formula. -/
theorem complexSourceMomentum_reconstruction (z : ComplexSourceHilbert hm U) :
    unweightedMomentumDistribution hm (complexSourceMap hm U z) =
      complexSourceFirstMomentum hm U z +
        TemperedDistribution.smulLeftCLM ℂ (sourceSecondInverseMultiplier m)
          (complexSourceSecondMomentum hm U z) := by
  change unweightedMomentumDistribution hm
      (sourceEmbedding hm U z.re + Complex.I • sourceEmbedding hm U z.im) =
    (sourceFirstMomentum hm U z.re + Complex.I • sourceFirstMomentum hm U z.im) +
      TemperedDistribution.smulLeftCLM ℂ (sourceSecondInverseMultiplier m)
        (sourceSecondMomentum hm U z.re + Complex.I • sourceSecondMomentum hm U z.im)
  rw [map_add, map_smul, sourceMomentum_reconstruction hm U z.re,
    sourceMomentum_reconstruction hm U z.im, map_add, map_smul]
  module

/-- The physical complex kernel produces the genuine compact-source distribution equation. -/
theorem complexSource_distribution_relation_of_kernel (z : ComplexSourceHilbert hm U)
    (hz : complexSourceMap hm U z = 0) :
    complexSourceFirstMomentum hm U z +
      TemperedDistribution.smulLeftCLM ℂ (sourceSecondInverseMultiplier m)
        (complexSourceSecondMomentum hm U z) = 0 := by
  rw [← complexSourceMomentum_reconstruction hm U z, hz, map_zero]

end VacuumBellSeparation
