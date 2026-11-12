/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4828T1Disk
public import LeanPool.ApollonianSuperharmonic.P4909T1ParentPolygon

-- [TABLET NODE: P4828T1Gap]

/-!
# P4828T1Gap

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $L\in\mathbb R$ and
$q:\operatorname{Fin}4\to\texttt{CircleCoordinates}$ be arbitrary.
Use the closed parent hull $P_L(q)$, positive-parent index set $J_+$,
and centers $p_j=w_j/c_j$ from `P4909T1ParentPolygon`, with
all its raw-input and contextual supporting-line conventions.
The open gap, denoted by `P4828T1Gap`, is
$$
 G_L(q)=\operatorname{int}_{\mathbb C}P_L(q)\cap
 \bigcap_{j\in J_+}\{z\in\mathbb C:|z-p_j|>1/c_j\}.
$$
Here the interior is the ambient planar interior, and each strict
inequality specifies the exterior of the positive parent's closed disk.
Zero- and negative-curvature parents impose no disk exclusions, and
the entry $q_0$ is entirely unused. No properness, tangency, or
nondegeneracy assumption is imposed. In particular, the ambient
interior makes the gap empty whenever the parent hull has empty
planar interior.
-/
def P4828T1Gap (L : Real) (q : Fin 4 → CircleCoordinates) : Set Complex :=
-- BODY
  let center (j : Fin 3) : Complex := (q j.succ).2 / ((q j.succ).1 : Real)
  {p | p ∈ interior (P4909T1ParentPolygon L q) ∧
    ∀ j : Fin 3, 0 < (q j.succ).1 →
      (1 / ((q j.succ).1 : Real)) < dist p (center j)}

end ApollonianSuperharmonic

end
