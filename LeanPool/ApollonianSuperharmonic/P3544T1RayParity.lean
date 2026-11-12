/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3544T1BoundaryCarrier
public import Mathlib.Data.Set.Card

-- [TABLET NODE: P3544T1RayParity]

/-!
# P3544T1RayParity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $C_p$ be `P3544T1BoundaryCarrier`.  A vector $d$ is generic
at $x\notin C_p$ if $\det(d,p_i-x)\ne0$ and
$\det(d,p_{i+1}-p_i)\ne0$ for every index $i$.  Count those side indices
whose closed segment meets $x+td$ for some $t>0$; write this finite count
as $N_p(x,d)$.  The set $O_p$ consists of the points $x\notin C_p$ for
which some generic $d$ has $N_p(x,d)$ odd.  Here
$\det(u,v)=u_1v_2-u_2v_1$.  The existential convention does not assume
direction independence, connectedness, diskness, or separation.
-/
noncomputable def P3544T1RayParity {n : Nat} (p : P3381T1PolygonBoundary n) :
    Set (Real × Real) :=
-- BODY
  {x | x ∉ P3544T1BoundaryCarrier p ∧ ∃ d : Real × Real,
    (∀ i, d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ 0) ∧
    (∀ i, d.1 * (p.vertex (i + 1) - p.vertex i).2 -
      d.2 * (p.vertex (i + 1) - p.vertex i).1 ≠ 0) ∧
    Set.ncard {i : Fin (n + 3) | ∃ t : Real, 0 < t ∧
      x + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))} % 2 = 1}

end ApollonianSuperharmonic

end
