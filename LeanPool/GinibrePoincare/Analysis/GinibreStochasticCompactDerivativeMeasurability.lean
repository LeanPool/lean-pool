/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCompactDerivativeMeasurability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactTaylorMeasurability

/-! Measurability of actual local test derivatives evaluated on measurable increments. -/

@[expose] public section
open Set MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem ginibreCompact_fderiv_apply_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (X H : Ω → Configuration n) (hmX : Measurable X) (hmH : Measurable H)
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hKU : K ⊆ U)
    (hRange : ∀ ω, X ω ∈ K) : Measurable (fun ω => fderiv ℝ f (X ω) (H ω)) := by
  have hdf : Measurable (fun ω => fderiv ℝ f (X ω)) :=
    ((hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono
        hKU).domRestrict.measurable.comp
      (hmX.subtype_mk : Measurable (fun ω => (⟨X ω, hRange ω⟩ : K)))
  exact (continuous_fst.clm_apply continuous_snd).measurable.comp (hdf.prodMk hmH)

theorem ginibreCompact_hessian_apply_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (X H : Ω → Configuration n) (hmX : Measurable X) (hmH : Measurable H)
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hKU : K ⊆ U)
    (hRange : ∀ ω, X ω ∈ K) : Measurable (fun ω => itoDirectionalHessian f (X ω) (H ω)) := by
  classical
  have hc (i : Fin n × Fin 2) :
      Measurable (fun ω => configurationEuclideanLinearEquiv n (H ω) i) :=
    ((configurationEuclideanLinearEquiv n).toContinuousLinearEquiv.continuous.measurable.comp
      hmH).eval
  have hh (i j : Fin n × Fin 2) : Measurable (fun ω => itoConfigurationHessianEntry f (X ω) i j) :=
    ((itoConfigurationHessianEntry_continuousOn f U hU hf i j).mono
        hKU).domRestrict.measurable.comp
      (hmX.subtype_mk : Measurable (fun ω => (⟨X ω, hRange ω⟩ : K)))
  simp_rw [itoConfigurationHessian_coordinate_sum]
  exact Finset.measurable_sum Finset.univ (fun i hi => Finset.measurable_sum Finset.univ
    (fun j hj => ((hc i).mul (hc j)).mul (hh i j)))
end
end GinibrePoincare
