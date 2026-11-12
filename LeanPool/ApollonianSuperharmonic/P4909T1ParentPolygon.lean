/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.Complex.Module

-- [TABLET NODE: P4909T1ParentPolygon]

/-!
# P4909T1ParentPolygon

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $L\in\mathbb R$ and
$q:\operatorname{Fin}4\to\texttt{CircleCoordinates}$ be arbitrary, with
$q_j=(c_j,w_j)\in\mathbb Z\times\mathbb Z[i]$ as in
`CircleCoordinates`. The parent indices are $1,2,3$; no
properness, tangency, or unit-normal assumption is imposed. Put
$$
 J_+=\{j\in\{1,2,3\}:c_j>0\},\qquad
 J_0=\{k\in\{1,2,3\}:c_k=0\}.
$$
For $j\in J_+$ let $p_j=w_j/c_j\in\mathbb C$, using the natural
embeddings of the coordinates, and for $k\in J_0$ set
$$
 h_k=\begin{cases}
 L,&w_k=-1,\\
 L+2,&w_k\ne-1.
 \end{cases}
$$
The closed parent polygon, denoted by `P4909T1ParentPolygon`,
is the real convex hull
$$
 V_L(q)=\{p_j:j\in J_+\}\cup
 \{h_k+i\operatorname{Im}p_j:j\in J_+,\ k\in J_0\},\qquad
 P_L(q)=\operatorname{conv}_{\mathbb R}V_L(q).
$$
Negative-curvature parents contribute no vertices, and the entry $q_0$
is entirely unused. In particular, if there are no positive parents,
the vertex set and hull are empty.

For arbitrary raw zero-curvature coordinates, the otherwise branch
$h_k=L+2$ is only a convention making this definition total. It does not
assert that $w_k=1$ or that $(0,w_k)$ represents a band line.
In the paper's band between $X=L$ and $X=L+2$, the normalized coordinates
$(0,-1)$ and $(0,1)$ represent the left and right supporting lines,
respectively. For these coordinates, the added points are precisely the
orthogonal projections of the positive-parent centers onto the
corresponding supporting line. The offset $L$ is contextual data, not
part of a line's curvature coordinates; for the paper's band
$\mathcal B_m$ it is $L=2m$.

If all three parents have positive curvature and their centers are
noncollinear, $P_L(q)$ is their nondegenerate center triangle. If exactly
two parents have positive curvature and the remaining parent is
$(0,-1)$ or $(0,1)$, the vertex set consists of the two centers and their
feet on the corresponding supporting line. Provided that the centers
have distinct heights and lie strictly on its inward side ($X>L$ for
$(0,-1)$, or $X<L+2$ for $(0,1)$), these four points form a nondegenerate
quadrilateral. These geometric descriptions are conditional; the same
definition applies to degenerate hulls and all other raw inputs.
-/
def P4909T1ParentPolygon (L : ℝ) (q : Fin 4 → CircleCoordinates) : Set ℂ :=
-- BODY
  let p (i : Fin 3) : ℂ := (q i.succ).2 / ((q i.succ).1 : ℝ)
  convexHull ℝ {z | ∃ i : Fin 3, 0 < (q i.succ).1 ∧
    (z = p i ∨ ∃ k : Fin 3, (q k.succ).1 = 0 ∧
      z = ⟨if (q k.succ).2 = -1 then L else L + 2, (p i).im⟩)}

end ApollonianSuperharmonic

end
