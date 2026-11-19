/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGirsanovContinuousTime.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltRationalLaw
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Brownian integral Girsanov continuous time

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianRationalApproxIndex_le`, `brownianRationalApproxTime_tendsto`,
`brownianCorrectedPath_continuousOn`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The index `⌊t / T * (n + 1)⌋` of the last point of the `(n + 1)`-step uniform grid on
`[0, T]` that does not exceed `t`. -/
def brownianRationalApproxIndex (T t : ℝ≥0) (n : ℕ) : ℕ :=
  Nat.floor ((t : ℝ)/(T : ℝ)*((n : ℝ)+1))

theorem brownianRationalApproxIndex_le (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) (n : ℕ) :
    brownianRationalApproxIndex T t n≤n+1 := by
  have hT' : 0<(T : ℝ) := hT
  have ht' : (t : ℝ)≤T := ht
  have h := Nat.floor_mono (mul_le_mul_of_nonneg_right
    ((div_le_one hT').mpr ht') (by positivity : 0≤(n : ℝ)+1))
  have he : ⌊(n : ℝ)+1⌋₊=n+1 := by
    rw [← Nat.cast_one,← Nat.cast_add, Nat.floor_natCast]
  simpa only [one_mul, he, brownianRationalApproxIndex] using h

theorem brownianRationalApproxTime_tendsto (T t : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => T*(brownianRationalApproxIndex T t n : ℝ≥0)/(n+1 : ℕ)) atTop (𝓝 t) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hf := (tendsto_nat_floor_mul_div_atTop (div_nonneg t.coe_nonneg T.coe_nonneg)).comp hnat
  have h := hf.const_mul (T : ℝ)
  have he : (T : ℝ)*((t : ℝ)/(T : ℝ))=(t : ℝ) := by
    field_simp
  rw [he] at h
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n => ((T*(brownianRationalApproxIndex T t n : ℝ≥0)/(n+1 : ℕ) : ℝ≥0) : ℝ))
      atTop (𝓝 (t : ℝ))
  simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one,
    brownianRationalApproxIndex, NNReal.coe_add, NNReal.coe_one]
  simpa only [mul_div_assoc, Function.comp_def] using h

/-- The literal adapted drift correction has continuous paths on the terminal
interval whenever the original Brownian paths and integrand paths do. -/
theorem brownianCorrectedPath_continuousOn {Ω ι : Type*} [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : ∀ i, IsBrownianReal (B i) P)
    (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Set.Icc 0 T)) (i : ι) :
    ∀ᵐ ω ∂P, ContinuousOn (fun t : ℝ≥0 => B i t ω-B i 0 ω-
      ∫ s in (0 : ℝ)..(t : ℝ), F i (Real.toNNReal s) ω) (Set.Icc 0 T) := by
  filter_upwards [(hB i).cont, hc i] with ω hω hf
  have hfc : ContinuousOn (fun s : ℝ => F i (Real.toNNReal s) ω) (Set.Icc 0 (T : ℝ)) :=
    hf.comp continuous_real_toNNReal.continuousOn (by
      intro s hs
      exact ⟨by positivity, by simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hs.2⟩)
  have hfc' : ContinuousOn (fun s : ℝ => F i (Real.toNNReal s) ω) (Set.uIcc 0 (T : ℝ)) := by
    simpa only [Set.uIcc_of_le T.coe_nonneg] using hfc
  have hp := intervalIntegral.continuousOn_primitive_interval
    (hfc'.integrableOn_compact (μ := volume) isCompact_uIcc)
  rw [Set.uIcc_of_le T.coe_nonneg] at hp
  apply (hω.sub continuous_const).continuousOn.sub
  exact hp.comp continuous_subtype_val.continuousOn (by intro t ht; exact ht)

end
end GinibrePoincare
