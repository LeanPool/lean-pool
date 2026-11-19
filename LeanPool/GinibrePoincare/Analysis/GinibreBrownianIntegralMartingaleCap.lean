/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralMartingaleCap.lean.
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

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-! Deterministic horizon caps preserve genuine continuous L² martingales. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The process `M` stopped at the deterministic horizon `T`, i.e. `t ↦ M (min t T)`. -/
def realMartingaleHorizonCap {Ω : Type*} (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    ℝ≥0 → Ω → ℝ := fun t => M (min t T)

theorem realMartingaleHorizonCap_martingale
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → ℝ)
    (hM : Martingale M F P) (hML : ∀ t, MemLp (M t) 2 P) (T : ℝ≥0) :
    Martingale (realMartingaleHorizonCap M T) F P := by
  constructor
  · intro t
    exact (hM.1 (min t T)).mono (F.mono (min_le_left _ _))
  · intro s t hst
    by_cases hs : s ≤ T
    · have hh := hM.2 s (min t T) (le_min hst hs)
      simpa only [realMartingaleHorizonCap, min_eq_left hs] using hh
    · have hTs : T ≤ s := (not_le.mp hs).le
      have hTt : T ≤ t := hTs.trans hst
      simp only [realMartingaleHorizonCap, min_eq_right hTs, min_eq_right hTt]
      rw [condExp_of_stronglyMeasurable (F.le s)
        ((hM.1 T).mono (F.mono hTs)) ((hML T).integrable (by norm_num))]

theorem realMartingaleHorizonCap_continuous
    {Ω : Type*} (M : ℝ≥0 → Ω → ℝ) (hMC : ∀ ω, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    ∀ ω, Continuous (fun t => realMartingaleHorizonCap M T t ω) := fun ω =>
  (hMC ω).comp (continuous_id.min continuous_const)

theorem realMartingaleHorizonCap_memLp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : ℝ≥0 → Ω → ℝ)
    (hML : ∀ t, MemLp (M t) 2 P) (T t : ℝ≥0) :
    MemLp (realMartingaleHorizonCap M T t) 2 P := hML (min t T)

@[simp] theorem realMartingaleHorizonCap_eq_before {Ω : Type*}
    (M : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t ≤ T) :
    realMartingaleHorizonCap M T t = M t := by simp [realMartingaleHorizonCap, ht]

@[simp] theorem realMartingaleHorizonCap_eq_after {Ω : Type*}
    (M : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : T ≤ t) :
    realMartingaleHorizonCap M T t = M T := by simp [realMartingaleHorizonCap, ht]

end
end GinibrePoincare
