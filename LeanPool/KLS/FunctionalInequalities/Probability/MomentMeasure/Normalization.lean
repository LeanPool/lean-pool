/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Affine
public import LeanPool.KLS.FunctionalInequalities.Probability.Support.Convex
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Affine
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Truncation
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Coercivity

/-!
# Effective-domain interior from a lower bound

`origin_mem_interior_domain_of_lower_bound`: the generic interior step used before supporting-plane
normalization.

Supporting infrastructure for Cordero-Erausquin–Klartag, Proposition 12.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

section
-- The origin is interior to the domain under a constant lower bound.

open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [BorelSpace E] in
/-- A constant lower bound `-M ≤ c` reduces a signed convex potential, after the constant shift
by `M`, to the nonnegative case `mem_interior_setOf_ne_top_of_lintegral_ne_top`. -/
theorem origin_mem_interior_domain_of_lower_bound (μ : Measure E) [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
    (hfirst : Integrable (fun x : E => x) μ)
    (c : E → EReal) (hc : ConvexPotential c) (hp : PotentialIntegrable c μ)
    (M : ℝ) (hlower : ∀ x, ((-M : ℝ) : EReal) ≤ c x) :
    (0 : E) ∈ interior {x | c x ≠ ⊤} := by
  let g := affineSubtract c 0 (-M)
  have hnn : ∀ x, 0 ≤ g x := by
    intro x
    change 0 ≤ c x - ((inner ℝ 0 x + -M : ℝ) : EReal)
    simp only [inner_zero_left, zero_add]
    exact (EReal.sub_nonneg (.inr (EReal.coe_ne_top _)) (.inr (EReal.coe_ne_bot _))).mpr (hlower x)
  have hg : PotentialIntegrable g μ := affineSubtract_potentialIntegrable c 0 (-M) hp hfirst
  obtain ⟨hm, hlin, _⟩ := lintegral_nonneg_potential g hg hnn
  have hfin : (∫⁻ x, (g x).toENNReal ∂μ) ≠ ⊤ := by rw [hlin]; exact ENNReal.ofReal_ne_top
  have hint := FunctionalInequalities.Probability.mem_interior_setOf_ne_top_of_lintegral_ne_top
    μ 0 h0 g hnn (convex_epigraph_affineSubtract c 0 (-M) hc.2) hm hfin
  have hD : {x | g x ≠ ⊤} = {x | c x ≠ ⊤} := by
    ext x
    change (g x ≠ ⊤) ↔ (c x ≠ ⊤)
    by_cases hx : c x = ⊤
    · simp only [g, affineSubtract, hx, EReal.top_sub_coe, ne_eq, not_true_eq_false]
    · have hgf : g x ≠ ⊤ := by
        change c x - ((inner ℝ 0 x + -M : ℝ) : EReal) ≠ ⊤
        rw [← EReal.coe_toReal hx (hc.1 x), ← EReal.coe_sub]
        exact EReal.coe_ne_top _
      exact iff_of_true hgf hx
  rwa [hD] at hint

end

end FunctionalInequalities.Probability.MomentMeasure
