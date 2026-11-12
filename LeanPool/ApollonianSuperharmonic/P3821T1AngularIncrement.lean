/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Path
public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: P3821T1AngularIncrement]

/-!
# P3821T1AngularIncrement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a continuous map $g:[0,1]\to\mathbb C$ and $p\in\mathbb C$, define
$\Delta_p(g)=\operatorname{P3821\_T1\_AngularIncrement}(g,p)$ as follows.
If there is a continuous real function $\theta$ with
$$
 e^{\mathrm i\theta(t)}=\frac{g(t)-p}{|g(t)-p|}\quad(0\le t\le1),
$$
choose one such function and set $\Delta_p(g)=\theta(1)-\theta(0)$.
If there is no such function, set $\Delta_p(g)=0$.
Here complex division by zero has its usual totalized value zero.
The choice is part of the definition; independence and the existence of
a lift for a puncture-avoiding path are separate assertions.
-/
noncomputable def P3821T1AngularIncrement
    (g : C(unitInterval, ℂ)) (p : ℂ) : ℝ := by
-- BODY
  classical
  exact if h : ∃ theta : C(unitInterval, ℝ), ∀ t,
      Complex.exp ((theta t : ℂ) * Complex.I) =
        (g t - p) / (‖g t - p‖ : ℂ) then
    (Classical.choose h) ⟨1, by norm_num⟩ -
      (Classical.choose h) ⟨0, by norm_num⟩
  else 0

end ApollonianSuperharmonic

end
