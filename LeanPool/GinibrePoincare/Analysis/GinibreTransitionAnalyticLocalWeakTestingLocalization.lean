/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalWeakTestingLocalization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingLeibniz
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevMultiplierL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Ginibre transition analytic local weak testing localization

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalWeak_cutoff_pair_memLp`, `ginibreLocalWeak_cutoff_inner_memLp`,
`ginibreLocalWeak_cutoff_gradient_memLp`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalWeak_compact_gradient_memLp {n : ℕ} (hn : 0 < n)
    (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (K : Set (Configuration n)) (hK : IsCompact K)
    (hg : MemLp g 2 (volume.restrict K)) :
    MemLp (K.indicator g) 2 (ginibreMeasure n) :=
  memLp_ginibre_of_volume n hn _ ((memLp_indicator_iff_restrict
      hK.measurableSet.nullMeasurableSet).mpr hg)

theorem ginibreLocalWeak_cutoff_pair_memLp {n : ℕ} (hn : 0 < n)
    (u : Configuration n → ℝ) (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : MemLp u 2 (ginibreMeasure n))
    (η : Configuration n → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hg : MemLp g 2 (volume.restrict (tsupport η))) :
    MemLp (fun z => η z*u z) 2 (ginibreMeasure n) ∧
    MemLp (fun z => η z • g z + u z • ginibreEuclideanGradient η z) 2 (ginibreMeasure n) := by
  have hG := ginibreLocalWeak_compact_gradient_memLp hn g (tsupport η) hc hg
  obtain ⟨hv, hh⟩ := configuration_weak_multiplier_memLp n (ginibreMeasure n)
    u ((tsupport η).indicator g) hu hG η hη hc
  refine ⟨hv, hh.ae_eq (ae_of_all _ ?_)⟩
  intro z
  by_cases hz : z ∈ tsupport η
  · simp [hz]
  · have he : η z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp [hz, he]

theorem ginibreLocalWeak_compact_smul_memLp {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure (Configuration n)) (η : Configuration n → ℝ)
    (hη : Continuous η) (hc : HasCompactSupport η)
    (v : Configuration n → V) (hv : MemLp v 2 μ) :
    MemLp (fun z => η z • v z) 2 μ := by
  obtain ⟨A, hA⟩ := hη.bounded_above_of_compact_support hc
  apply hv.of_le_mul (c := A) (hη.aestronglyMeasurable.smul hv.aestronglyMeasurable)
  exact ae_of_all μ (fun z => by
    change ‖η z • v z‖ ≤ A * ‖v z‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hA z) (norm_nonneg _))

theorem ginibreLocalWeak_cutoff_inner_memLp {n : ℕ} (hn : 0 < n)
    (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (η : Configuration n → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hg : MemLp g 2 (volume.restrict (tsupport η))) :
    MemLp (fun z => inner ℝ (g z) (ginibreEuclideanGradient η z)) 2 (ginibreMeasure n) := by
  let G := (tsupport η).indicator g
  have hG := ginibreLocalWeak_compact_gradient_memLp hn g (tsupport η) hc hg
  obtain ⟨A, hA⟩ := (continuous_ginibreEuclideanGradient η hη).bounded_above_of_compact_support
    (compactSupport_ginibreEuclideanGradient η hc)
  have hh : MemLp (fun z => inner ℝ (G z) (ginibreEuclideanGradient η z)) 2 (ginibreMeasure n) := by
    apply hG.of_le_mul (c := A)
      (hG.aestronglyMeasurable.inner (continuous_ginibreEuclideanGradient η
          hη).aestronglyMeasurable)
    apply ae_of_all
    intro z
    exact (norm_inner_le_norm _ _).trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hA z) (norm_nonneg (G z)))
  apply hh.ae_eq
  apply ae_of_all
  intro z
  by_cases hz : z ∈ tsupport η
  · simp [G, hz]
  · have hd : fderiv ℝ η z = 0 := fderiv_of_notMem_tsupport ℝ hz
    have he : ginibreEuclideanGradient η z = 0 := by
      ext k
      simp only [ginibreEuclideanGradient_coordinate, hd, zero_apply, PiLp.zero_apply]
    simp [he]

theorem ginibreLocalWeak_cutoff_gradient_memLp {n : ℕ} (hn : 0 < n)
    (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (η : Configuration n → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hg : MemLp g 2 (volume.restrict (tsupport η))) :
    MemLp (fun z => η z • g z) 2 (ginibreMeasure n) := by
  have hG := ginibreLocalWeak_compact_gradient_memLp hn g (tsupport η) hc hg
  have hh := ginibreLocalWeak_compact_smul_memLp (ginibreMeasure n) η hη.continuous hc
    ((tsupport η).indicator g) hG
  apply hh.ae_eq
  apply ae_of_all
  intro z
  by_cases hz : z ∈ tsupport η
  · simp [hz]
  · simp [hz, image_eq_zero_of_notMem_tsupport hz]

end
end GinibrePoincare
