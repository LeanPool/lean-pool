/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Analysis.LpTranslationContinuity


/-!
# Shifting before mollifying

Mollifying a function near the boundary of its domain asks for values the function does not
have. The global approximation theorem answers by shifting first: the function is translated
into the domain far enough that the mollifier of the shift only ever sees points where the
function is defined, and then the shift and the mollifier radius are sent to zero together.

This file proves that the two limits compose, so that a shifted mollification converges to the
function it started from. The identity that makes it work is that convolution commutes with
translation, so the mollification error of the shift is the shift of the mollification error,
which has the same norm.

## Main declarations

* `EllipticPdes.Extension.convolution_comp_translate`: convolution commutes with translation.
* `EllipticPdes.Extension.tendsto_eLpNorm_translate_convolution_sub`: a shifted mollification
  converges in `Lᵖ` to the function, as the shift and the radius go to zero together.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.3.3, Theorem 3.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Topology Convolution

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Analysis EllipticPdes.Embedding

variable {d : ℕ}

/-- **Convolution commutes with translation.** Convolving a translate is translating the
convolution, by the change of variables `t ↦ t + h` in the defining integral. -/
theorem convolution_comp_translate (f ρ : EuclideanSpace ℝ (Fin d) → ℝ)
    (h x : EuclideanSpace ℝ (Fin d)) :
    ((fun y => f (y + h)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x
      = (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) (x + h) := by
  simp only [convolution]
  rw [← integral_add_right_eq_self
    (fun t => (ContinuousLinearMap.lsmul ℝ ℝ) (f t) (ρ (x + h - t))) h]
  have harg : ∀ t : EuclideanSpace ℝ (Fin d), x + h - (t + h) = x - t := fun t => by abel
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only [harg]

/-- **Convergence of a shifted mollification.** For `f` in `Lᵖ`, translating by `hᵢ` and
mollifying at radius `(φ i).rOut` gives a family converging to `f` in `Lᵖ`, as soon as both the
shift and the radius tend to zero.

The error splits into the mollification error of the shift and the shift error. The first is the
shift of the mollification error, by `convolution_comp_translate`, and translation is an `Lᵖ`
isometry, so it has the norm of the mollification error of `f` itself. -/
theorem tendsto_eLpNorm_translate_convolution_sub {p : ℝ} (hp : 1 ≤ p)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin d))} {K : ℝ}
    {hv : ι → EuclideanSpace ℝ (Fin d)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hK : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn)
    (hh : Tendsto hv l (𝓝 0)) :
    Tendsto (fun i => eLpNorm
        ((fun y => f (y + hv i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            ((φ i).normed volume) - f)
        (ENNReal.ofReal p) volume) l (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  -- The two limits the error splits into.
  have hconv := tendsto_eLpNorm_convolution_sub (h := f) hp hf hφ hK
  have htrans := (tendsto_eLpNorm_translate_sub hp1 hptop hf).comp hh
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : ε / 2 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε.ne', by norm_num⟩
  have hA := (ENNReal.tendsto_nhds_zero.mp hconv) (ε / 2) (pos_iff_ne_zero.mpr hε2)
  have hB := (ENNReal.tendsto_nhds_zero.mp htrans) (ε / 2) (pos_iff_ne_zero.mpr hε2)
  filter_upwards [hA, hB] with i h1 h2
  set ρ := (φ i).normed volume with hρ
  set g := f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ with hg
  -- The convolution is continuous, so both pieces are measurable.
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable hp1
  have hgc : Continuous g := by
    rw [hg]
    exact ((φ i).hasCompactSupport_normed).continuous_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hloc (φ i).continuous_normed
  have hgf : AEStronglyMeasurable (fun y => g y - f y) volume :=
    hgc.aestronglyMeasurable.sub hf.aestronglyMeasurable
  have hft : AEStronglyMeasurable (fun y => f (y + hv i) - f y) volume :=
    (hf.aestronglyMeasurable.comp_measurePreserving (measurePreserving_translate (hv i))).sub
        hf.aestronglyMeasurable
  -- The shifted mollification error is the shift of the mollification error.
  have hshift : ((fun y => f (y + hv i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ)
      = fun y => g (y + hv i) := by
    funext y
    exact convolution_comp_translate f ρ (hv i) y
  have hfirst : eLpNorm
      (fun y => ((fun y => f (y + hv i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y
        - f (y + hv i)) (ENNReal.ofReal p) volume
      = eLpNorm (fun y => g y - f y) (ENNReal.ofReal p) volume := by
    rw [show (fun y => ((fun y => f (y + hv i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y
          - f (y + hv i)) = fun y => (fun z => g z - f z) (y + hv i) from by
        funext y; rw [hshift]]
    exact eLpNorm_comp_translate hgf (hv i) _
  -- The triangle inequality on the split.
  have hsplit : ((fun y => f (y + hv i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ - f)
      = (fun y => ((fun y => f (y + hv i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y
          - f (y + hv i))
        + (fun y => f (y + hv i) - f y) := by
    funext y
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hmeas1 : AEStronglyMeasurable
      (fun y => ((fun y => f (y + hv i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y
        - f (y + hv i)) volume := by
    rw [show (fun y => ((fun y => f (y + hv i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y
          - f (y + hv i)) = fun y => (fun z => g z - f z) (y + hv i) from by
        funext y; rw [hshift]]
    exact hgf.comp_measurePreserving (measurePreserving_translate (hv i))
  calc eLpNorm ((fun y => f (y + hv i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ - f)
        (ENNReal.ofReal p) volume
      ≤ eLpNorm (fun y => ((fun y => f (y + hv i))
            ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y - f (y + hv i))
          (ENNReal.ofReal p) volume
        + eLpNorm (fun y => f (y + hv i) - f y) (ENNReal.ofReal p) volume := by
        rw [hsplit]
        exact eLpNorm_add_le hp1
    _ = eLpNorm (fun y => g y - f y) (ENNReal.ofReal p) volume
        + eLpNorm (fun y => f (y + hv i) - f y) (ENNReal.ofReal p) volume := by rw [hfirst]
    _ ≤ ε / 2 + ε / 2 := by
        refine add_le_add ?_ h2
        refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) h1
        exact Filter.EventuallyEq.of_eq (funext fun y => rfl)
    _ = ε := ENNReal.add_halves ε

end EllipticPdes.Extension
