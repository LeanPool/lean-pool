/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevLocalIntegrability.lean.
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

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Local unweighted integrability from the actual positive Gaussian density -/

@[expose] public section
open MeasureTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Weighted integrability under a continuous strictly positive density gives
actual ordinary local integrability everywhere. -/
theorem positive_density_integrable_locallyIntegrable
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace E] [T2Space E]
    (μ : Measure E) (w f : E → ℝ) (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    (hf : Integrable f (μ.withDensity (fun x => ENNReal.ofReal (w x)))) :
    LocallyIntegrable f μ := by
  have hi := (integrable_withDensity_iff_integrable_smul'
    hw.measurable.ennreal_ofReal (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hf
  have hmul : Integrable (fun x => w x * f x) μ := by
    simpa only [ENNReal.toReal_ofReal (le_of_lt (hpos _)), smul_eq_mul] using hi
  have hlocal := hmul.locallyIntegrable.mul_continuous (hw.inv₀ fun x => ne_of_gt (hpos x))
  apply hlocal.congr
  filter_upwards with x
  change w x * f x * (w x)⁻¹ = f x
  field_simp [ne_of_gt (hpos x)]

/-- Ordinary Gaussian integrability implies genuine local Lebesgue integrability. -/
theorem gaussianReal_integrable_locallyIntegrable (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → ℝ) (hf : Integrable f (ProbabilityTheory.gaussianReal m v)) :
    LocallyIntegrable f volume := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero m hv] at hf
  apply positive_density_integrable_locallyIntegrable volume
    (ProbabilityTheory.gaussianPDFReal m v) f _
    (fun x => ProbabilityTheory.gaussianPDFReal_pos m v x hv) hf
  unfold ProbabilityTheory.gaussianPDFReal
  fun_prop

/-- Global integrability under an actual product Gaussian law supplies the
local ordinary integrability of almost every real coordinate derivative slice. -/
theorem gaussian_product_integrable_slices_locallyIntegrable
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (f : ℝ × Y → ℝ)
    (hf : Integrable f ((ProbabilityTheory.gaussianReal m v).prod ν)) :
    ∀ᵐ y ∂ν, LocallyIntegrable (fun t => f (t, y)) volume := by
  filter_upwards [hf.prod_left_ae] with y hy
  exact gaussianReal_integrable_locallyIntegrable m v hv _ hy

/-- Positive-density weighted L² functions with actual compact support are
ordinary global L² functions; no regularity of the representative is assumed. -/
theorem positive_density_memLp_volume_of_compactSupport
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace E] [T2Space E]
    {V : Type*} [NormedAddCommGroup V]
    (μ : Measure E) (w : E → ℝ) (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    (f : E → V) (hf : MemLp f 2 (μ.withDensity (fun x => ENNReal.ofReal (w x))))
    (hc : HasCompactSupport f) : MemLp f 2 μ := by
  have hac : μ ≪ μ.withDensity (fun x => ENNReal.ofReal (w x)) :=
    withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
      (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  have hm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable.mono_ac hac
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hl := positive_density_integrable_locallyIntegrable μ w (fun x => ‖f x‖ ^ 2)
    hw hpos ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
  apply (hl.integrableOn_isCompact hc).integrable_of_forall_notMem_eq_zero
  intro x hx
  simp [image_eq_zero_of_notMem_tsupport hx]

end
end GinibrePoincare
