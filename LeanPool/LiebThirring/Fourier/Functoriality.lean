/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Fourier transform and bounded target maps

Bounded target maps commute with Fourier transform. Schwartz identities extend by unweighted L²
density.
-/

public section

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace LiebThirring.Fourier

variable {V H K : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A bounded complex target map commutes with the Schwartz Fourier transform. -/
theorem fourier_postcomp (L : H →L[ℂ] K) (f : 𝓢(V, H)) :
    𝓕 (f.postcompCLM L) = (𝓕 f).postcompCLM L := by
  ext x
  change (𝓕 (fun y => L (f y))) x = L ((𝓕 (fun y => f y)) x)
  rw [Real.fourier_eq, Real.fourier_eq]
  have hi := (Real.fourierIntegral_convergent_iff x).mpr (f.integrable (μ := (volume : Measure V)))
  rw [← L.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards with y
  simp only [Circle.smul_def, map_smul]

omit [CompleteSpace H] [CompleteSpace K] in
/-- The bounded L² target map agrees with postcomposition on Schwartz maps. -/
theorem compLp_toLp (L : H →L[ℂ] K) (f : 𝓢(V, H)) :
    L.compLp (f.toLp 2 (volume : Measure V)) =
      (f.postcompCLM L).toLp 2 (volume : Measure V) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (f.toLp 2 (volume : Measure V)),
    f.coeFn_toLp 2 (volume : Measure V),
    (f.postcompCLM L).coeFn_toLp 2 (volume : Measure V)] with x hx hf hg
  rw [hx, hf, hg, SchwartzMap.postcompCLM_apply]

/-- Fourier on L² commutes with every bounded complex map on the target. -/
theorem fourier_compLp (L : H →L[ℂ] K) (f : Lp H 2 (volume : Measure V)) :
    𝓕 (L.compLp f) = L.compLp (𝓕 f) := by
  apply DenseRange.induction_on (p := fun f : Lp H 2 (volume : Measure V) =>
    𝓕 (L.compLp f) = L.compLp (𝓕 f))
    (SchwartzMap.denseRange_toLpCLM (E := V) (F := H) (p := 2) (μ := (volume : Measure V))
      ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ V K).continuous.comp (L.compLpL 2 volume).continuous)
      ((L.compLpL 2 volume).continuous.comp (Lp.fourierTransformₗᵢ V H).continuous)
  · intro g
    change 𝓕 (L.compLp (g.toLp 2 volume)) = L.compLp (𝓕 (g.toLp 2 volume))
    rw [compLp_toLp, SchwartzMap.toLp_fourier_eq, fourier_postcomp,
      SchwartzMap.toLp_fourier_eq, compLp_toLp]

end LiebThirring.Fourier
end
