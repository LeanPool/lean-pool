/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsLSICoupling.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsLSIClosure
/-!
# Alternative Bakry Emery Gibbs LSI coupling

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryBrownianEndpoint_randomInitial_measurable`,
`bakryEmeryBrownianEndpoint_stationary_square_lsi`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

omit [DecidableEq ι] in
/-- Actual Brownian-noise endpoint with a measurable random initial point. -/
theorem bakryEmeryBrownianEndpoint_randomInitial_measurable
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (Z : Ω → EuclideanSpace ℝ ι) (hZ : Measurable Z)
    (T : ℝ) (hT : 0 ≤ T) (B : ι → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (fun ω => bakryEmeryBrownianEndpoint W κ hκ hW hc (Z ω) T hT B ω) := by
  classical
  let : MeasurableSpace C(Icc 0 T, EuclideanSpace ℝ ι) := borel _
  let : BorelSpace C(Icc 0 T, EuclideanSpace ℝ ι) := ⟨rfl⟩
  have hN := bakryEmeryBrownianNoisePath_measurable T hT B P hB
  have hsc : Measurable (fun N : C(Icc 0 T, EuclideanSpace ℝ ι) => Real.sqrt 2 • N) :=
    (continuous_id.const_smul (Real.sqrt 2)).measurable
  exact (bakryEmeryLangevinEndpoint_continuous W κ hκ hW hc T hT).measurable.comp
    (hZ.prodMk (hsc.comp hN))

omit [DecidableEq ι] [MeasurableSpace Ω] in
omit [DecidableEq ι] in
/-- Common actual Brownian noise synchronously forgets every random initial
point pointwise, with no position integrability assumption. -/
theorem bakryEmeryBrownianEndpoint_randomInitial_distance_tendsto
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (Z : Ω → EuclideanSpace ℝ ι)
    (B : ι → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Tendsto (fun n : ℕ => dist
      (bakryEmeryBrownianEndpoint W κ hκ hW hc z (n+1 : ℝ) (by positivity) B ω)
      (bakryEmeryBrownianEndpoint W κ hκ hW hc (Z ω) (n+1 : ℝ) (by positivity) B ω))
      atTop (nhds 0) := by
  classical
  simpa only [dist_eq_norm, bakryEmeryBrownianEndpoint] using
    bakryEmeryLangevinEndpoint_initial_distance_tendsto W κ hκ hW hc z (Z ω)
      (fun n => Real.sqrt 2 • bakryEmeryBrownianNoisePath (n+1 : ℝ) B ω)

omit [DecidableEq ι] in
/-- Stochastic equilibrium bridge for the actual constructed Langevin
endpoint. This generic bridge is not yet the concrete Gibbs theorem: its
stationary law is discharged by the actual Gibbs reversal construction. -/
theorem bakryEmeryBrownianEndpoint_stationary_square_lsi
    [Nonempty ι]
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (Z : Ω → EuclideanSpace ℝ ι)
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (ν : Measure (EuclideanSpace ℝ ι))
    (hstat : ∀ n : ℕ, HasLaw
      (fun ω => bakryEmeryBrownianEndpoint W κ hκ hW hc (Z ω) (n+1 : ℝ) (by positivity) B ω) ν P)
    (f : EuclideanSpace ℝ ι → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    squareEntropy ν f ≤ (2/κ)*∫ x, ‖gradient f x‖^2 ∂ν := by
  classical
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hf (by simp)
  obtain ⟨C, hC⟩ := bakryEmery_compactObservable_bound f hf.continuous hs
  apply bakryEmery_stationaryCoupling_square_lsi_limit P ν f hf hs
    (fun n ω => bakryEmeryBrownianEndpoint W κ hκ hW hc z (n+1 : ℝ) (by positivity) B ω)
    (fun n ω => bakryEmeryBrownianEndpoint W κ hκ hW hc (Z ω) (n+1 : ℝ) (by positivity) B ω)
    (fun n => (bakryEmeryBrownianEndpoint_measurable W κ hκ hW hc z
      (n+1 : ℝ) (by positivity) B P hB).aemeasurable) hstat
    (ae_of_all _ (bakryEmeryBrownianEndpoint_randomInitial_distance_tendsto W κ hκ hW hc z Z B))
  intro n
  exact bakryEmeryBrownianEndpoint_square_lsi W κ hκ hW hc z (n+1 : ℝ) (by positivity)
    B P hB hind f hf hL C hC

end
end GinibrePoincare
