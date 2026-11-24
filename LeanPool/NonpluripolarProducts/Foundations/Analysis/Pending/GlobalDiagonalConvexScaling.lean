/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalDiagonalScaling
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ThetaPshConvexCombination

/-!
# Diagonal scaling along a convex combination

For two genuine `θ`-PSH potentials `a`, `b` and a weight `t ∈ (0,1)` the
diagonal global mixed measure of the convex combination dominates `tⁿ` times
the diagonal measure of `a`:

  `tⁿ · θⁿ_a ≤ θⁿ_{t a + (1-t) b}`   as measures on every set.

This is the manifold form of the elementary current inequality
`θ_{t a + (1-t) b} = t θ_a + (1-t) θ_b ≥ t θ_a`.  It is proved exactly as
`Pending.GlobalDiagonalScaling.globalMixedMeasure_diagonal_scale`, by replacing
one slot at a time and dropping the `b`-summand, but with the constant `0` of
that lemma replaced by an arbitrary second potential `b`.  That generality is
what the Monge--Ampere capacity needs: in a big but non-semipositive class the
constant `0` need not be `θ`-PSH, so the comparison potential has to be
`V_θ` (or any other genuine potential) rather than a constant.

The pole hypotheses of one-slot linearity
(`Pending.GlobalSlotLinear.globalMixedMeasure_update_add_smul`) are free here:
the pole set of a genuine `θ`-PSH potential is locally pluripolar and hence
null for every global mixed measure
(`globalMixedMeasure_pole_null_of_nondegenerate`).  No boundedness and no
semipositivity of `θ` is assumed.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling

open FirstPass FirstPass.PositiveClasses
open GlobalNonPluripolar GlobalDiagonalScaling
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Diagonal domination along a convex combination.**  For genuine `θ`-PSH
potentials `a`, `b` and `0 < t < 1`,
`tⁿ · θⁿ_a (S) ≤ θⁿ_{t a + (1-t) b} (S)` for every `S`. -/
theorem globalMixedMeasure_diagonal_convexComb_le {θ : ClosedRealOneOneForm n M}
    {a b : M → EReal} (ha : IsThetaPshPotential θ.val a)
    (hb : IsThetaPshPotential θ.val b) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (S : Set M) :
    ENNReal.ofReal (t ^ n) *
        globalMixedMeasure (fun _ => θ) (fun _ => a) (fun _ => ha.1) S ≤
      globalMixedMeasure (fun _ => θ) (fun _ => convexComb t a b)
        (fun _ => (isThetaPshPotential_convexComb ha hb ht0 ht1).1) S :=
  globalMixedMeasure_diagonal_add_smul_le ha hb ht0 ht1
    (isThetaPshPotential_convexComb ha hb ht0 ht1).1 S

end

end SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
