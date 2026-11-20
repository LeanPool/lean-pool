/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.TransverseSmoothBumpPeriodization
public import LeanPool.FastDynamo.Global.MatchingCellScalingParameters
public import LeanPool.FastDynamo.Global.TorusSupportedH2Output

/-!
# Almost-everywhere support of whole-plane `L²` classes in a set

`IsAEL2SupportedIn s f` says that the whole-plane `L²` class `f` vanishes almost everywhere
off the set `s`; `isAEL2SupportedIn_add` shows that this is preserved by addition.  The
predicate is the set-parametric companion of the chart predicate
`IsSupportedInWholePlaneFundamentalBox`.  `Global/TorusChartMultiplierDescent.lean`,
`Global/TorusChartActionBridge.lean` and `Global/TorusChartCutoffSupport.lean` state their
support hypotheses with it.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Metric Set
open scoped LineDeriv SchwartzMap

namespace WholePlaneAESupport

open TorusChartL2
open TransverseSmoothBumpH2Cutoff

/-- An `L²` class is almost-everywhere supported in a specified subset of
the whole plane.  This set-parametric version complements the fixed
fundamental-box predicate used by the chart transfer. -/
def IsAEL2SupportedIn (s : Set WholePlane)
    {F : Type*} [NormedAddCommGroup F] (f : WholePlaneL2 F) : Prop :=
  ∀ᵐ x ∂volume, x ∉ s → f x = 0

/-- Almost-everywhere support in a set is preserved by addition. -/
theorem isAEL2SupportedIn_add
    {s : Set WholePlane} {f g : WholePlaneC3L2}
    (hf : IsAEL2SupportedIn s f) (hg : IsAEL2SupportedIn s g) :
    IsAEL2SupportedIn s (f + g) := by
  filter_upwards [hf, hg, Lp.coeFn_add f g]
    with x hfx hgx hadd hs
  rw [hadd]
  change f x + g x = 0
  rw [hfx hs, hgx hs, add_zero]

end WholePlaneAESupport

end

end FastDynamo
