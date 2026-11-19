/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterZeroDirection.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroRestartNonvanishing
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterDirection

/-! The actual center direction is adapted, unit length, and continuous at all
positive times, without requiring a nonzero initial center. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_centerDirection_punctured_properties
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (he : ‖e‖ = 1) :
    let u := fun t ω => ginibreCenterRadialDirection n e
      (ginibreBrownianMaximalProcess n α z B t ω)
    (∀ t, @Measurable Ω (EuclideanSpace ℝ (Fin n × Fin 2))
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (u t)) ∧
    (∀ t ω, ‖u t ω‖=1) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => u t ω) (Ioi (0 : ℝ≥0))) := by
  dsimp only
  obtain ⟨hAdapt, hPath⟩ := ginibreBrownianMaximalProcess_global_original_solution
    (by omega) α z hz B P hB hind
  refine ⟨fun t => (ginibreCenterRadialDirection_measurable n e).comp
    (hAdapt t).measurable, fun t ω => ginibreCenterRadialDirection_norm n e he _,?_⟩
  filter_upwards [hPath, ginibreBrownian_center_all_positive_times_nonzero hn α hα z hz B P hB hind]
    with ω hω hnonzero
  have hX : Continuous (fun t : ℝ≥0 => ginibreBrownianMaximalProcess n α z B t ω) := by
    simpa only [Function.comp_def, Real.toNNReal_coe] using hω.1.comp NNReal.continuous_coe
  intro t ht
  have hd : ContinuousAt (fun s : ℝ≥0 => ginibreCenterRadialDirection n e
      (ginibreBrownianMaximalProcess n α z B s ω)) t :=
    (ginibreCenterRadialDirection_continuousAt (by omega) e _ (hnonzero t ht)).comp (f := fun s :
        ℝ≥0 => ginibreBrownianMaximalProcess n α z B s ω) hX.continuousAt
  exact hd.continuousWithinAt

/-- The actual center squared radius is uniformly positive on every compact
interval bounded away from zero, including when its initial center is zero. -/
theorem ginibreBrownian_center_positive_interval_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0, 0 < a → a ≤ b →
      ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc a b,
        c ≤ ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B t ω) := by
  filter_upwards [ginibreBrownian_center_all_positive_times_nonzero hn α hα z hz B P hB hind,
    (ginibreBrownianMaximalProcess_global_original_solution (by omega) α z hz B P hB hind).2]
    with ω hnonzero hsolution
  intro a b ha hab
  let r := fun t : ℝ≥0 => ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B t ω)
  have hc : Continuous r := (contDiff_ginibreCenterSquared n).continuous.comp
    (by simpa only [Function.comp_def, Real.toNNReal_coe] using hsolution.1.comp
          NNReal.continuous_coe)
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc a b).Nonempty from ⟨a, le_rfl, hab⟩) hc.continuousOn
  refine ⟨r t,?_, hmin⟩
  exact lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (hnonzero t (ha.trans_le ht.1)))

end
end GinibrePoincare
