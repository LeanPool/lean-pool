/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Integrability from uniformly bounded cutoff integrals

A nonnegative function whose cutoffs `c_n h` (with `0 ≤ c_n → 1` pointwise) have uniformly bounded
integrals is integrable, by Fatou's lemma. Generic tool, used to pass from compactly supported
integration by parts to global integrability (Letwin Lemma 2.3 supports).
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace FunctionalInequalities.Analysis

/--
**Integrability from bounded cutoff integrals** (Fatou): if `h ≥ 0`, the cutoffs `c_n h` are
integrable with
`c_n ≥ 0`, `c_n → 1` pointwise and `∫ c_n h ≤ C`, then `h` is integrable. -/
theorem integrable_of_cutoff_bounds {A : Type*} [MeasurableSpace A] (μ : Measure A) {h : A → ℝ}
    (hh : AEStronglyMeasurable h μ) (hpos : ∀ x, 0 ≤ h x) {c : ℕ → A → ℝ}
    (hcpos : ∀ n x, 0 ≤ c n x) (hlim : ∀ x, Tendsto (fun n => c n x) atTop (𝓝 1))
    (hi : ∀ n, Integrable (fun x => c n x * h x) μ) {C : ℝ}
    (hbound : ∀ n, (∫ x, c n x * h x ∂μ) ≤ C) : Integrable h μ := by
  let F : ℕ → A → ENNReal := fun n x => ENNReal.ofReal (c n x * h x)
  have hm : ∀ n, AEMeasurable (F n) μ := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable (hi n).aestronglyMeasurable.aemeasurable
  have hFlim (x : A) : Tendsto (fun n => F n x) atTop (𝓝 (ENNReal.ofReal (h x))) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    simpa only [one_mul] using (hlim x).mul_const (h x)
  have hfatou := lintegral_liminf_le' (u := (atTop : Filter ℕ)) hm
  have htarget : (∫⁻ x, ENNReal.ofReal (h x) ∂μ) ≤ liminf (fun n => ∫⁻ x, F n x ∂μ) atTop := by
    simpa only [(hFlim _).liminf_eq] using hfatou
  have hupper (n : ℕ) : (∫⁻ x, F n x ∂μ) ≤ ENNReal.ofReal C := by
    dsimp only [F]
    rw [←
      ofReal_integral_eq_lintegral_ofReal (hi n)
        (ae_of_all μ fun x => mul_nonneg (hcpos n x) (hpos x))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hfinite : (∫⁻ x, ENNReal.ofReal (h x) ∂μ) < ⊤ :=
    (htarget.trans
          (liminf_le_of_frequently_le'
            (Filter.Eventually.of_forall hupper).frequently)).trans_lt
      (ENNReal.ofReal_lt_top)
  exact (lintegral_ofReal_ne_top_iff_integrable hh (ae_of_all μ hpos)).mp hfinite.ne

end FunctionalInequalities.Analysis
