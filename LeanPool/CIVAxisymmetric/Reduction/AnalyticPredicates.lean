/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.ForceSpatiallyAnalytic
public import LeanPool.CIVAxisymmetric.Statements.LocallyUniformlyAnalyticOn
public import LeanPool.CIVAxisymmetric.Statements.IsClassicalSolutionOn

/-!
# The two spatial-analyticity predicates

`eq:interior:force:analytic` and `eq:analytic:interior:force` state the same locally uniform
spatial analyticity bound, once for the force on the unit cylinder and once for a general
field on `B(R) × (t₁, t₂)`. This module records the identity of the two readings at the unit
cylinder, and the restriction step that turns a single analyticity bound on a closed time
interval into the locally uniform statement, by monotonicity in the ball and in the interval.

The companion restriction on the other side of `lem:analytic:slice` is
`IsClassicalSolutionOn.mono`: being a classical solution is inherited by every subset of the
space-time set on which it holds, so the hypothesis may be read on the smaller cylinder the
analyticity statement is applied to.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Spatial analyticity of the force on the unit cylinder, `eq:interior:force:analytic`, is
the locally uniform analyticity of `eq:analytic:interior:force` at `R = 1` on the time
interval `(-1, 0)`: the two definitions unfold to the same proposition. -/
theorem forceSpatiallyAnalytic_iff_locallyUniformlyAnalyticOn (f : ParabolicPoint → Vec3) :
    ForceSpatiallyAnalytic f ↔ LocallyUniformlyAnalyticOn f 1 (-1) 0 :=
  Iff.rfl

/-- One analyticity bound on `B(R') × [t₁, t₂]` already gives the locally uniform statement on
`B(R') × (t₁, t₂)`: every smaller ball and every compactly contained closed time interval
inherit the same constants `M`, `a`. This is the restriction step owed by `lem:analytic:slice`
away from `R = 1`. -/
theorem locallyUniformlyAnalyticOn_of_analyticBoundOn {g : ParabolicPoint → Vec3}
    {R' t₁ t₂ M a : ℝ} (h : AnalyticBoundOn g R' (Icc t₁ t₂) M a) (ha : 0 < a) :
    LocallyUniformlyAnalyticOn g R' t₁ t₂ := by
  intro R'' hR'' s₁ s₂ hs₁ hs₂
  refine ⟨M, a, ha, ?_⟩
  intro α t ht x hx i
  exact h α t ⟨le_trans hs₁.le ht.1, le_trans ht.2 hs₂.le⟩ x (vec3Ball_mono hR''.le hx) i

/-- Being a classical solution of `eq:nse:forced` is inherited by subsets: the smoothness of
the three fields restricts by `ContDiffOn.mono`, and the momentum and divergence equations
are pointwise conditions, so they hold at every point of the smaller set. -/
theorem IsClassicalSolutionOn.mono {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {S T : Set ParabolicPoint}
    (h : IsClassicalSolutionOn u p f S) (hTS : T ⊆ S) :
    IsClassicalSolutionOn u p f T :=
  ⟨h.1.mono hTS, h.2.1.mono hTS, h.2.2.1.mono hTS,
    fun z hz i => h.2.2.2.1 z (hTS hz) i, fun z hz => h.2.2.2.2 z (hTS hz)⟩

end CIV
