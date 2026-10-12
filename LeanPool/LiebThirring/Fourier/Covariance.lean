/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Fourier.Functoriality

/-!
# Orthogonal covariance of the L² Fourier transform

Orthogonal changes of spatial coordinates commute with the L² Fourier transform, by the integral
formula and Schwartz density.
-/

public section

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace LiebThirring.Fourier

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Schwartz Fourier covariance under an orthogonal change of variables. -/
theorem fourier_comp_isometry (A : V ≃ₗᵢ[ℝ] V) (f : 𝓢(V, H)) :
    𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv (𝓕 f) := by
  ext x
  exact Real.fourier_comp_linearIsometry A (fun y => f y) x

omit [CompleteSpace H] in
/-- The measure-preserving L² pullback agrees with composition on Schwartz maps. -/
theorem compMeasurePreserving_toLp (A : V ≃ₗᵢ[ℝ] V) (f : 𝓢(V, H)) :
    Lp.compMeasurePreserving A A.measurePreserving (f.toLp 2 (volume : Measure V)) =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (f.toLp 2 (volume : Measure V))
    A.measurePreserving,
    A.measurePreserving.quasiMeasurePreserving.ae (f.coeFn_toLp 2 (volume : Measure V)),
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f).coeFn_toLp 2 volume]
    with x hx hf hg
  rw [hx, hg]
  exact hf

/-- Fourier on L² commutes with orthogonal spatial pullback. -/
theorem fourier_compMeasurePreserving (A : V ≃ₗᵢ[ℝ] V)
    (f : Lp H 2 (volume : Measure V)) :
    𝓕 (Lp.compMeasurePreserving A A.measurePreserving f) =
      Lp.compMeasurePreserving A A.measurePreserving (𝓕 f) := by
  apply DenseRange.induction_on (p := fun f : Lp H 2 (volume : Measure V) =>
    𝓕 (Lp.compMeasurePreserving A A.measurePreserving f) =
      Lp.compMeasurePreserving A A.measurePreserving (𝓕 f))
    (SchwartzMap.denseRange_toLpCLM (E := V) (F := H) (p := 2)
      (μ := (volume : Measure V)) ENNReal.ofNat_ne_top) f
  · have hc : Continuous (Lp.compMeasurePreserving A A.measurePreserving :
        Lp H 2 (volume : Measure V) → Lp H 2 volume) :=
      (Lp.compMeasurePreservingₗᵢ ℂ A A.measurePreserving).continuous
    exact isClosed_eq ((Lp.fourierTransformₗᵢ V H).continuous.comp hc)
      (hc.comp (Lp.fourierTransformₗᵢ V H).continuous)
  · intro g
    change 𝓕 (Lp.compMeasurePreserving A A.measurePreserving (g.toLp 2 volume)) =
      Lp.compMeasurePreserving A A.measurePreserving (𝓕 (g.toLp 2 volume))
    rw [compMeasurePreserving_toLp, SchwartzMap.toLp_fourier_eq, fourier_comp_isometry,
      SchwartzMap.toLp_fourier_eq, compMeasurePreserving_toLp]

end LiebThirring.Fourier
end
