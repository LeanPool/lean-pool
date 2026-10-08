/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.AnalyticBoundOnConstant
public import LeanPool.CIVAxisymmetric.Reduction.AxisymmetricDerivativeCongruence

/-!
# Transfer of the analyticity bound along agreement on the unit cylinder

`AnalyticBoundOn` and `ForceSpatiallyAnalytic` read only spatial derivatives at points of
`B(1) × (-1, 0)`, and each such derivative is determined by the field on a spatial
neighbourhood inside that cylinder. So the analyticity bound `eq:analytic:interior:force`,
and with it `eq:interior:force:analytic`, transfers between two fields that merely agree on
the unit cylinder.

The consequence used by `cor:interior:nonanalytic` is the last theorem below: a force that
vanishes identically on the unit cylinder agrees there with the zero field, which satisfies
`eq:interior:force:analytic` by `forceSpatiallyAnalytic_const`. Contrapositively, a force
that violates `eq:interior:force:analytic` is somewhere nonzero on the unit cylinder, which
is the corollary's step from its first conclusion to its second, `f ≢ 0`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV



/-- Two scalar fields agreeing on the unit cylinder have equal multi-index spatial partial
derivatives at every point of the unit cylinder: each of the three iterated directional
derivatives is taken at fixed time inside the open ball `B(1)`. -/
theorem multiPartial_congr_of_eqOn_unitCylinder {g h : ParabolicPoint → ℝ}
    (heq : Set.EqOn g h unitCylinder) (α : Fin 3 → ℕ)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    multiPartial g α z = multiPartial h α z := by
  have heq2 := spatialPartial_iterate_congr_of_eqOn heq 2 (α 2)
  have heq1 := spatialPartial_iterate_congr_of_eqOn heq2 1 (α 1)
  have heq0 := spatialPartial_iterate_congr_of_eqOn heq1 0 (α 0)
  exact heq0 hz

/-- The analyticity bound `eq:analytic:interior:force` transfers between two vector fields
that agree on the unit cylinder, on every cylinder `B(R') × J` the unit one contains. Only
agreement on the unit cylinder is assumed, not at every point of space-time. -/
theorem analyticBoundOn_congr_of_eqOn_unitCylinder {g h : ParabolicPoint → Vec3}
    {R' : ℝ} {J : Set ℝ} {M a : ℝ} (hR' : R' ≤ 1) (hJ : J ⊆ Ioo (-1 : ℝ) 0)
    (heq : Set.EqOn g h unitCylinder) (hb : AnalyticBoundOn h R' J M a) :
    AnalyticBoundOn g R' J M a := by
  intro α t ht x hx i
  have hz : ((x, t) : ParabolicPoint) ∈ unitCylinder := ⟨vec3Ball_mono hR' hx, hJ ht⟩
  have heqi : Set.EqOn (fun w => g w i) (fun w => h w i) unitCylinder :=
    fun w hw => congrFun (heq hw) i
  rw [multiPartial_congr_of_eqOn_unitCylinder heqi α hz]
  exact hb α t ht x hx i

/-- Spatial analyticity of the force, `eq:interior:force:analytic`, transfers between two
forces that agree on the unit cylinder: the predicate is read on subcylinders
`B(R) × [t₁, t₂]` with `R < 1` and `-1 < t₁`, `t₂ < 0`, all of which sit inside the unit
cylinder. -/
theorem forceSpatiallyAnalytic_congr_of_eqOn_unitCylinder {f g : ParabolicPoint → Vec3}
    (heq : Set.EqOn f g unitCylinder) (hg : ForceSpatiallyAnalytic g) :
    ForceSpatiallyAnalytic f := by
  rw [forceSpatiallyAnalytic_iff_locallyUniformlyAnalyticOn] at hg ⊢
  intro R' hR' s₁ s₂ hs₁ hs₂
  obtain ⟨M, a, ha, hb⟩ := hg R' hR' s₁ s₂ hs₁ hs₂
  refine ⟨M, a, ha, analyticBoundOn_congr_of_eqOn_unitCylinder hR'.le ?_ heq hb⟩
  intro t ht
  exact ⟨lt_of_lt_of_le hs₁ ht.1, lt_of_le_of_lt ht.2 hs₂⟩

/-- A force that vanishes identically on the unit cylinder satisfies
`eq:interior:force:analytic`: it agrees there with the zero field, for which every
derivative of positive order vanishes. -/
theorem forceSpatiallyAnalytic_of_eqOn_unitCylinder_zero {f : ParabolicPoint → Vec3}
    (heq : ∀ z ∈ unitCylinder, f z = 0) : ForceSpatiallyAnalytic f := by
  refine forceSpatiallyAnalytic_congr_of_eqOn_unitCylinder
    (g := fun _ : ParabolicPoint => (0 : Vec3)) (fun w hw => heq w hw) ?_
  exact forceSpatiallyAnalytic_const (M := 0) (fun i => by simp)

/-- The step of `cor:interior:nonanalytic` from its first conclusion to its second: a force
violating `eq:interior:force:analytic` cannot vanish identically on the unit cylinder, so
`f ≢ 0` there. -/
theorem exists_mem_unitCylinder_ne_zero_of_not_forceSpatiallyAnalytic
    {f : ParabolicPoint → Vec3} (hf : ¬ ForceSpatiallyAnalytic f) :
    ∃ z ∈ unitCylinder, f z ≠ 0 := by
  by_contra hcon
  refine hf (forceSpatiallyAnalytic_of_eqOn_unitCylinder_zero ?_)
  intro z hz
  by_contra hz0
  exact hcon ⟨z, hz, hz0⟩

end CIV
