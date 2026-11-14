/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4207T1DiamondFormula
public import LeanPool.ApollonianSuperharmonic.PartialOdometer
public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: P4207T1FormulaRestriction]

/-!
# P4207T1FormulaRestriction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a prototile $T$, let $V_T$ be the finite union of the four corner sets
of its cells if its cell set is nonempty, and let $V_T=\{T.\mathrm{anchor}\}$
otherwise. Define the partial odometer
$R(T)=\operatorname{P4207\_T1\_FormulaRestriction}(T)$ to have domain $V_T$ and values
$$
 R(T)(x)=
 \begin{cases}\operatorname{P4207\_T1\_DiamondFormula}(x),&x\in V_T,\\
 0,&x\notin V_T.
 \end{cases}
$$
Thus empty line prototiles retain their singleton function domains.
-/
noncomputable def P4207T1FormulaRestriction (T : ProtoTile) : PartialOdometer :=
-- BODY
  let V : Finset GaussianInt := if T.cells.Nonempty then
    T.cells.biUnion (fun x => {x, x + 1, x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩})
    else {T.anchor}
  { domain := V
    value := fun x => if x ∈ V then P4207T1DiamondFormula x else 0
    value_outside := by
      intro x hx
      simp [hx] }

end ApollonianSuperharmonic

end
