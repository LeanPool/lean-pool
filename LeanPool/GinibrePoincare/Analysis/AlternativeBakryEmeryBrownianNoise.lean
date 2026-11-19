/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianNoise.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGrid
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousNoisePath
public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# Alternative Bakry Emery Brownian noise

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryBrownianNoisePath_measurable`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

/-- The actual unscaled independent coordinate Brownian driving path. -/
def bakryEmeryBrownianNoiseReal (B : ι → ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) :
    EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => B i t.toNNReal ω)

omit [Fintype ι] in
theorem bakryEmeryBrownianNoiseReal_actual [Finite ι] (B : ι → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, Continuous (bakryEmeryBrownianNoiseReal B ω) ∧
      bakryEmeryBrownianNoiseReal B ω 0=0 := by
  have hc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => B i t ω) := ae_all_iff.mpr (fun i => (hB i).cont)
  have hz : ∀ᵐ ω ∂P, ∀ i, B i 0 ω=0 := ae_all_iff.mpr (fun i => (hB i).eval_zero_ae_eq_zero)
  filter_upwards [hc, hz] with ω hc hz
  constructor
  · exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i =>
      (hc i).comp continuous_real_toNNReal))
  · apply PiLp.ext
    intro i
    simpa [bakryEmeryBrownianNoiseReal] using hz i

/-- The vector noise path `t ↦ (B i t ω)_i` on `[0, T]` as a continuous map (defaulting to `0`
when this function is not continuous). -/
def bakryEmeryBrownianNoisePath (T : ℝ) (B : ι → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    C(Icc 0 T, EuclideanSpace ℝ ι) :=
  ContinuousMap.mkD (fun t => bakryEmeryBrownianNoiseReal B ω t.val) 0

omit [Fintype ι] in
theorem bakryEmeryBrownianNoisePath_actual [Finite ι] (T : ℝ) (B : ι → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, ∀ t : Icc 0 T,
      bakryEmeryBrownianNoisePath T B ω t = bakryEmeryBrownianNoiseReal B ω t.val := by
  filter_upwards [bakryEmeryBrownianNoiseReal_actual B P hB] with ω hω
  intro t
  have hc : Continuous (fun t : Icc 0 T => bakryEmeryBrownianNoiseReal B ω t.val) :=
    hω.1.comp continuous_subtype_val
  simp [bakryEmeryBrownianNoisePath, ContinuousMap.mkD, hc]

omit [Fintype ι] in
theorem bakryEmeryBrownianNoisePath_measurable [Finite ι] (T : ℝ) (hT : 0 ≤ T)
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) :
    @Measurable Ω C(Icc 0 T, EuclideanSpace ℝ ι) _ (borel _)
      (bakryEmeryBrownianNoisePath T B) := by
  have := Fintype.ofFinite ι
  let : Nonempty (Icc 0 T) := ⟨⟨0, ⟨le_rfl, hT⟩⟩⟩
  let : MeasurableSpace C(Icc 0 T, EuclideanSpace ℝ ι) := borel _
  let : BorelSpace C(Icc 0 T, EuclideanSpace ℝ ι) := ⟨rfl⟩
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  apply (aemeasurable_iff_measurable (μ := P)).mp
  have hr : Measurable (fun ω => bakryEmeryBrownianNoiseReal B ω t.val) := by
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    apply Measurable.of_eval
    intro i
    exact aemeasurable_iff_measurable.mp ((hB i).aemeasurable t.val.toNNReal)
  apply hr.aemeasurable.congr
  filter_upwards [bakryEmeryBrownianNoisePath_actual T B P hB] with ω hω
  exact (hω t).symm

end
end GinibrePoincare
