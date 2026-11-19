/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianTransitionKernel.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianBrownianRestart
public import Mathlib.Probability.Kernel.Composition.Prod

/-! Genuine Borel transition kernels obtained from the constructed canonical Brownian solution. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The time-`t` transition kernel from collision-free configurations to configurations: the
image of `δ z ⊗ μ` under the maximal driven value at time `t`, for a noise law `μ`. -/
def ginibreCanonicalTransitionKernel {n : ℕ} (_ : 0 < n) (α : ℝ) (t : ℝ≥0)
    (μ : Measure (GinibreContinuousNoise n)) :
    Kernel {z : Configuration n // CollisionFree z} (Configuration n) :=
  ((Kernel.id : Kernel {z : Configuration n // CollisionFree z} _) |>.prod
    (Kernel.const {z : Configuration n // CollisionFree z} μ)).map
    (fun p => ginibreDrivenMaximalValue n α p.2.val p.1.val t)

instance ginibreCanonicalTransitionKernel_isMarkov {n : ℕ} (hn : 0 < n)
    (α : ℝ) (t : ℝ≥0) (μ : Measure (GinibreContinuousNoise n)) [IsProbabilityMeasure μ] :
    IsMarkovKernel (ginibreCanonicalTransitionKernel hn α t μ) := by
  unfold ginibreCanonicalTransitionKernel
  exact Kernel.IsMarkovKernel.map _ (ginibreDrivenMaximalValue_joint_measurable hn α t)

/-- The canonical transition kernel whose noise law is the image of `P` under the Brownian
driving noise of `B`. -/
def ginibreBrownianTransitionKernel {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (hn : 0 < n) (α : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) (t : ℝ≥0) :
    Kernel {z : Configuration n // CollisionFree z} (Configuration n) :=
  ginibreCanonicalTransitionKernel hn α t (P.map (ginibreBrownianFullContinuousNoise n B α))

theorem ginibreBrownianTransitionKernel_isMarkov {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (t : ℝ≥0) :
    IsMarkovKernel (ginibreBrownianTransitionKernel hn α B P t) := by
  have hm := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  let : IsProbabilityMeasure (P.map (ginibreBrownianFullContinuousNoise n B α)) :=
    (by infer_instance)
  exact ginibreCanonicalTransitionKernel_isMarkov hn α t _

theorem ginibreCanonicalTransitionKernel_apply {n : ℕ} (hn : 0 < n) (α : ℝ)
    (t : ℝ≥0) (μ : Measure (GinibreContinuousNoise n)) [IsProbabilityMeasure μ]
    (z : {z : Configuration n // CollisionFree z}) :
    ginibreCanonicalTransitionKernel hn α t μ z =
      μ.map (fun N => ginibreDrivenMaximalValue n α N.val z.val t) := by
  unfold ginibreCanonicalTransitionKernel
  rw [Kernel.map_apply _ (ginibreDrivenMaximalValue_joint_measurable hn α t),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (ginibreDrivenMaximalValue_joint_measurable hn α t) measurable_prodMk_left]
  rfl

theorem ginibreBrownianTransitionKernel_apply_eq_process_law
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (t : ℝ≥0) (z : {z : Configuration n // CollisionFree z}) :
    ginibreBrownianTransitionKernel hn α B P t z =
      P.map (ginibreBrownianMaximalProcess n α z.val B t) := by
  have hm := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  let : IsProbabilityMeasure (P.map (ginibreBrownianFullContinuousNoise n B α)) :=
    (by infer_instance)
  unfold ginibreBrownianTransitionKernel
  rw [ginibreCanonicalTransitionKernel_apply,
    Measure.map_map (ginibreDrivenMaximalValue_measurable hn α z.val t) hm]
  rfl

end
end GinibrePoincare
