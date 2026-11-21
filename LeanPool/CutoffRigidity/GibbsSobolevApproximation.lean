/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsSobolev
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Approximation by compact tests in the closed Gibbs gradient graph -/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Approximate a closed Gibbs gradient pair by compact tests, with strong L² convergence of
both components and almost-everywhere convergence of the scalar component. -/
theorem gibbsSobolev_approximation_seq {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : gibbsSobolevGraph hV hprob) :
    ∃ p : ℕ → (E →₂[gibbsMeasure volume V] ℝ) × (E →₂[gibbsMeasure volume V] E),
      (∀ n, p n ∈ (compactGibbsGradient hV.continuous hprob).graph) ∧
      Tendsto (fun n => (p n).1) atTop (𝓝 (gibbsSobolevInclusion hV hprob u)) ∧
      Tendsto (fun n => (p n).2) atTop (𝓝 (gibbsSobolevDerivative hV hprob u)) ∧
      ∀ᵐ x ∂gibbsMeasure volume V,
        Tendsto (fun n => (p n).1 x) atTop (𝓝 (gibbsSobolevInclusion hV hprob u x)) := by
  let G := compactGibbsGradient hV.continuous hprob
  let U := gibbsSobolevInclusion hV hprob u
  let D := gibbsSobolevDerivative hV hprob u
  have hmem : (U, D) ∈ closure (G.graph : Set _) := by
    change (U, D) ∈ G.graph.topologicalClosure
    rw [(compactGibbsGradient_isClosable hV hprob).graph_closure_eq_closure_graph]
    exact u.property
  obtain ⟨p, hp, hplim⟩ := mem_closure_iff_seq_limit.mp hmem
  have hfirst : Tendsto (fun n => (p n).1) atTop (𝓝 U) := (continuous_fst.tendsto _).comp hplim
  have hsecond : Tendsto (fun n => (p n).2) atTop (𝓝 D) := (continuous_snd.tendsto _).comp hplim
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hfirst).exists_seq_tendsto_ae'
  exact ⟨fun n => p (ns n), fun n => hp (ns n), hfirst.comp hns, hsecond.comp hns, hae⟩

end CutoffRigidity
