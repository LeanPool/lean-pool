/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticRadialBrownian.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRadialDirection
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticUnitFieldBrownian

/-! # Brownian motion obtained by radial projection

The unit field `u` is the recentered radial direction along the maximal
configuration process. The fixed unit vector `e` supplies its definition at
exceptional configurations. `GinibreStochasticRadialDirection` proves the
adaptation, unit norm and almost-sure continuity needed to integrate this field
against the independent coordinate Brownian motions.

The proof applies `ginibreUnitField_Brownian_exists`. Besides Brownian law,
the conclusion keeps martingale and square-integrability properties, the
uniform-sum limits on ordinary and shifted intervals, and independence of
fresh increments from every measurable variable in the augmented past.
The shifted limits are useful when proving independence of the two radial
drivers; the ordinary limits are used for CIR substitution. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_radial_Brownian_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    let e : EuclideanSpace ℝ (Fin n × Fin 2) := EuclideanSpace.single (⟨0, by omega⟩, 0) 1
    let u := fun t ω => ginibreRecenteredRadialDirection n e
      (ginibreBrownianMaximalProcess n α z B t ω)
    ∃ β : ℝ≥0 → Ω → ℝ,
      IsBrownianReal β P ∧
      Martingale β (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ t, MemLp (β t) 2 P) ∧ β 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t, TendstoInMeasure P (fun k ω => ∑ i,
        brownianUniformLeftSum (B i) (fun s ω => u s ω i) t (k+1) ω) atTop (β t)) ∧
      (∀ s t, TendstoInMeasure P (fun k => brownianUnitShiftedUniformSum B u s t (k+1))
        atTop (fun ω => β (s+t) ω-β s ω)) ∧
      (∀ s t (Y : Ω → ℝ),
        @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P (fun i => (hB
            i).toIsPreBrownianReal) s) _ Y →
        IndepFun Y (fun ω => β (s+t) ω-β s ω) P) := by
  classical
  let i₀ : Fin n × Fin 2 := (⟨0, by omega⟩, 0)
  let e : EuclideanSpace ℝ (Fin n × Fin 2) := EuclideanSpace.single i₀ 1
  have he : ‖e‖=1 := by simp [e, PiLp.norm_single]
  obtain ⟨hu, hunit, hc⟩ := ginibreBrownianMaximalProcess_radialDirection_properties
    hn α z hz B P hB hind e he
  exact ginibreUnitField_Brownian_exists B P hB hind _ hu hunit hc i₀
end
end GinibrePoincare
