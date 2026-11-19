/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianGlobalPath.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicCompleted
public import Mathlib.Probability.ProductMeasure
/-!
# Alternative Bakry Emery Brownian global path

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryBrownianGlobalPath_zero`, `bakryBrownianGlobalPath_eval_measurable`,
`bakryBrownianGlobalProcess_continuous`, `bakryBrownianUnitClamp_sum_min`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous paths `C(Icc 0 1, ℝ)`, used locally in this file. -/
local instance instBorelAlternativeBakryEmeryBrownianGlobalPath54 :
    MeasurableSpace C(Icc (0 : ℝ) 1, ℝ) := borel _
local instance : BorelSpace C(Icc (0 : ℝ) 1, ℝ) := ⟨rfl⟩

/-- Sample space of the global Brownian motion: one completed dyadic sample for each unit time
block `[n, n + 1]`. -/
abbrev BakryBrownianGlobalSample := ℕ → BakryBrownianDyadicCompletedSample

/-- The infinite product of copies of `bakryBrownianDyadicCompletedMeasure`, one per time
block. -/
def bakryBrownianGlobalMeasure : Measure BakryBrownianGlobalSample :=
  Measure.infinitePi (fun _ : ℕ => bakryBrownianDyadicCompletedMeasure)

instance : IsProbabilityMeasure bakryBrownianGlobalMeasure := by
  unfold bakryBrownianGlobalMeasure
  infer_instance

/-- The clamp `min 1 (max 0 r)` of a real number into the unit interval. -/
def bakryBrownianUnitClamp (r : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨min 1 (max 0 r), by constructor <;> simp⟩

lemma bakryBrownianUnitClamp_continuous : Continuous bakryBrownianUnitClamp := by
  unfold bakryBrownianUnitClamp
  fun_prop

@[simp] lemma bakryBrownianUnitClamp_zero_of_nonpos (r : ℝ) (hr : r ≤ 0) :
    bakryBrownianUnitClamp r = ⟨0, by norm_num, by norm_num⟩ := by
  apply Subtype.ext
  simp [bakryBrownianUnitClamp, max_eq_left hr]

/-- Actual all-time stitched path, adding each independent unit block up to
its clipped elapsed time. Every bounded time interval uses finitely many blocks. -/
def bakryBrownianGlobalPath (ω : BakryBrownianGlobalSample) (t : ℝ) : ℝ :=
  ∑' n : ℕ, bakryBrownianDyadicCompletedPath (ω n) (bakryBrownianUnitClamp (t-n))

lemma bakryBrownianGlobalPath_eq_finite (ω : BakryBrownianGlobalSample)
    (N : ℕ) (t : ℝ) (ht : t ≤ N) :
    bakryBrownianGlobalPath ω t =
      ∑ n ∈ Finset.range N, bakryBrownianDyadicCompletedPath (ω n)
        (bakryBrownianUnitClamp (t-n)) := by
  apply tsum_eq_sum
  intro n hn
  have hNn : N ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hNn
  rw [bakryBrownianUnitClamp_zero_of_nonpos _ (by linarith)]
  exact (bakryBrownianDyadicPath_endpoints (ω n)).1

lemma bakryBrownianGlobalPath_continuous (ω : BakryBrownianGlobalSample) :
    Continuous (bakryBrownianGlobalPath ω) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have hc : Continuous (fun r : ℝ => ∑ n ∈ Finset.range N,
      bakryBrownianDyadicCompletedPath (ω n) (bakryBrownianUnitClamp (r-n))) := by
    apply continuous_finsetSum
    intro n hn
    exact (bakryBrownianDyadicCompletedPath (ω n)).continuous.comp
      (bakryBrownianUnitClamp_continuous.comp (continuous_id.sub continuous_const))
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hN] with r hr
  exact bakryBrownianGlobalPath_eq_finite ω N r hr.le

@[simp] lemma bakryBrownianGlobalPath_zero (ω : BakryBrownianGlobalSample) :
    bakryBrownianGlobalPath ω 0 = 0 := by
  rw [bakryBrownianGlobalPath_eq_finite ω 0 0 (by norm_num)]
  simp

lemma bakryBrownianGlobalPath_eval_measurable (t : ℝ) :
    Measurable (fun ω : BakryBrownianGlobalSample => bakryBrownianGlobalPath ω t) := by
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have he : (fun ω : BakryBrownianGlobalSample => bakryBrownianGlobalPath ω t) =
      (fun ω => ∑ n ∈ Finset.range N, bakryBrownianDyadicCompletedPath (ω n)
        (bakryBrownianUnitClamp (t-n))) := by
    funext ω
    exact bakryBrownianGlobalPath_eq_finite ω N t hN.le
  rw [he]
  apply Finset.measurable_sum
  intro n hn
  exact (continuous_eval_const (bakryBrownianUnitClamp (t-n))).measurable.comp
    (bakryBrownianDyadicCompletedPath_measurable.comp (measurable_pi_apply n))

/-- The global Brownian process indexed by `t : ℝ≥0`: the stitched path
`bakryBrownianGlobalPath ω` at time `t`. -/
def bakryBrownianGlobalProcess (t : ℝ≥0) (ω : BakryBrownianGlobalSample) : ℝ :=
  bakryBrownianGlobalPath ω t

lemma bakryBrownianGlobalProcess_continuous (ω : BakryBrownianGlobalSample) :
    Continuous (fun t => bakryBrownianGlobalProcess t ω) :=
  (bakryBrownianGlobalPath_continuous ω).comp NNReal.continuous_coe

lemma bakryBrownianUnitClamp_telescope (r : ℝ) :
    (bakryBrownianUnitClamp r : ℝ) = max 0 r-max 0 (r-1) := by
  by_cases h0 : r ≤ 0
  · simp [bakryBrownianUnitClamp, max_eq_left h0, max_eq_left (show r-1 ≤ 0 by linarith)]
  · by_cases h1 : 1 ≤ r
    · simp [bakryBrownianUnitClamp, max_eq_right (by linarith : 0 ≤ r),
        max_eq_right (by linarith : 0 ≤ r-1), min_eq_left h1]
    · simp [bakryBrownianUnitClamp, max_eq_right (by linarith : 0 ≤ r),
        max_eq_left (by linarith : r-1 ≤ 0), min_eq_right (by linarith : r ≤ 1)]

lemma bakryBrownianUnitClamp_sum (N : ℕ) (t : ℝ) :
    ∑ n ∈ Finset.range N, (bakryBrownianUnitClamp (t-n) : ℝ) =
      max 0 t-max 0 (t-N) := by
  induction N with
  | zero => simp
  | succ N hN =>
    rw [Finset.sum_range_succ, hN, bakryBrownianUnitClamp_telescope]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show t-((N : ℝ)+1)=t-N-1 by ring]
    ring

lemma bakryBrownianUnitClamp_sum_min (N : ℕ) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hsN : s ≤ N) (htN : t ≤ N) :
    ∑ n ∈ Finset.range N, min (bakryBrownianUnitClamp (s-n) : ℝ)
      (bakryBrownianUnitClamp (t-n) : ℝ) = min s t := by
  wlog hst : s ≤ t generalizing s t
  · rw [min_comm]
    simpa only [min_comm] using this t s ht hs htN hsN (le_of_not_ge hst)
  have hh (n : ℕ) : (bakryBrownianUnitClamp (s-n) : ℝ) ≤
      (bakryBrownianUnitClamp (t-n) : ℝ) :=
    min_le_min le_rfl (max_le_max le_rfl (sub_le_sub_right hst _))
  simp_rw [min_eq_left (hh _)]
  rw [bakryBrownianUnitClamp_sum, max_eq_right hs, max_eq_left (by linarith : s-N ≤ 0),
    sub_zero, min_eq_left hst]

end
end GinibrePoincare
