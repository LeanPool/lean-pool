/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryPositiveWeightLocal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianEntireRepresentatives
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Correspondence auxiliary positive weight local

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `locallyIntegrable_of_positive_compact_weight`,
`positiveWeightLocalRestriction_coe`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- A strictly positive local lower bound on an arbitrary weight controls
ordinary local L² directly by the actual weighted L² norm. -/
theorem memLp_restrict_of_weight_lower_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} {w : X → ℝ} {s : Set X}
    (hs : MeasurableSet s) {c : ℝ} (hc : 0 < c) (hw : ∀ x ∈ s, c ≤ w x)
    (hf : MemLp f 2 (μ.withDensity (fun x => ENNReal.ofReal (w x)))) :
    MemLp f 2 (μ.restrict s) := by
  have hle : ENNReal.ofReal c • μ.restrict s ≤
      (μ.withDensity (fun x => ENNReal.ofReal (w x))).restrict s := by
    rw [restrict_withDensity hs,← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hs] with x hx
    exact ENNReal.ofReal_le_ofReal (hw x hx)
  have hm := (hf.restrict s).mono_measure hle
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hct : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hinv : (ENNReal.ofReal c)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc0
  have hb := hm.smul_measure hinv
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul] using hb

/-- Weighted square-integrability for a weight bounded below on compact sets
implies genuine ordinary local integrability in every configuration dimension. -/
theorem locallyIntegrable_of_positive_compact_weight (n : ℕ)
    (w : Configuration n → ℝ) (f : Configuration n → ℂ)
    (hw : ∀ K : Set (Configuration n), IsCompact K →
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ w z)
    (hf : MemLp f 2 (volume.withDensity (fun z => ENNReal.ofReal (w z)))) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨c, hc, hcw⟩ := hw K hK
  have hm := memLp_restrict_of_weight_lower_bound hK.measurableSet hc hcw hf
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  exact hm.integrable (by norm_num)

theorem measure_restrict_le_weight_multiple {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w : X → ℝ) {s : Set X} (hs : MeasurableSet s)
    {c : ℝ} (hc : 0 < c) (hw : ∀ x ∈ s, c ≤ w x) :
    μ.restrict s ≤ (ENNReal.ofReal c)⁻¹ •
      μ.withDensity (fun x => ENNReal.ofReal (w x)) := by
  have hle : ENNReal.ofReal c • μ.restrict s ≤
      (μ.withDensity (fun x => ENNReal.ofReal (w x))).restrict s := by
    rw [restrict_withDensity hs,← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hs] with x hx
    exact ENNReal.ofReal_le_ofReal (hw x hx)
  have hbase := hle.trans (Measure.restrict_le_self)
  have hb : (ENNReal.ofReal c)⁻¹ • (ENNReal.ofReal c • μ.restrict s) ≤
      (ENNReal.ofReal c)⁻¹ • μ.withDensity (fun x => ENNReal.ofReal (w x)) := by
    gcongr
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul] using hb

/-- Canonical continuous ordinary-local L² restriction from the actual
arbitrarily weighted L² space; no supplied restriction operator. -/
def positiveWeightLocalRestriction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w : X → ℝ) {s : Set X} (hs : MeasurableSet s)
    {c : ℝ} (hc : 0 < c) (hw : ∀ x ∈ s, c ≤ w x) :
    Lp ℂ 2 (μ.withDensity (fun x => ENNReal.ofReal (w x))) →L[ℝ]
      Lp ℂ 2 (μ.restrict s) :=
  Lp.LpToLpOfMeasureLeSMul (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne')
    (measure_restrict_le_weight_multiple μ w hs hc hw)

theorem positiveWeightLocalRestriction_coe {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w : X → ℝ) {s : Set X} (hs : MeasurableSet s)
    {c : ℝ} (hc : 0 < c) (hw : ∀ x ∈ s, c ≤ w x)
    (u : Lp ℂ 2 (μ.withDensity (fun x => ENNReal.ofReal (w x)))) :
    positiveWeightLocalRestriction μ w hs hc hw u =ᵐ[μ.restrict s] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

end
end GinibrePoincare
