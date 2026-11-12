/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3821T1AngularIncrement

-- [TABLET NODE: P3821T1LoopIndex]

/-!
# P3821T1LoopIndex

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Write $\mathbb S^1=\{z\in\mathbb C:|z|=1\}$ and
$q(t)=e^{2\pi\mathrm i t}$.  For a continuous map
$g:\mathbb S^1\to\mathbb C$ define the real-valued loop index by
$$
 I(g,p)=\operatorname{P3821\_T1\_LoopIndex}(g,p)
       =\frac{\operatorname{P3821\_T1\_AngularIncrement}(g\circ q,p)}{2\pi}.
$$
The definition applies even when $p$ is on the loop.  Its integrality and
the usual index laws are asserted only when the loop avoids $p$.
For a circle-valued map $\alpha$, its angular degree means
$I(\iota\circ\alpha,0)$, where $\iota:\mathbb S^1\hookrightarrow\mathbb C$.
-/
noncomputable def P3821T1LoopIndex (g : C(Circle, ℂ)) (p : ℂ) : ℝ :=
-- BODY
  P3821T1AngularIncrement
    (g.comp ⟨fun t : unitInterval => Circle.exp (2 * Real.pi * (t : ℝ)),
      by fun_prop⟩) p / (2 * Real.pi)

end ApollonianSuperharmonic

end
