/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandTangency
public import LeanPool.ApollonianSuperharmonic.PrimitiveVectorOrientation

-- [TABLET NODE: RecursiveVectorSystem]

/-!
# RecursiveVectorSystem

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A recursive vector system is a pair of functions
$v(C,C'),a(C,C')\in\mathbb Z[i]$ on ordered pairs of raw curvature
coordinates.  Both functions vanish away from band-tangent pairs.  On the
clockwise base quadruple
$((1,1+2z),(1,1+2z+2i),(0,1),(0,-1))$ their three clockwise values are
$$
(v_{32},v_{21},v_{13})=(0,-1,1),\qquad
(a_{32},a_{21},a_{13})=(1,-1-z-i,z+i).
$$
For every semi-proper quadruple the successor values are prescribed by
$$
\begin{aligned}
v_{20}&=v_{21}-iv_{32},&v_{03}&=v_{13}+iv_{32},\\
a_{20}&=a_{21}+ia_{32},&a_{03}&=a_{13}-ia_{32}.
\end{aligned}
$$
These successor relations are the unnumbered recursion display in Section 5.3
of the cited paper; parent rotations provide the other cases.  Finally, only when $C\to D$ is the
canonical orientation of \operatorname{PrimitiveVectorOrientation}, the opposite
ordered value is prescribed once by
$$
 v(D,C)=iv(C,D),\qquad a(D,C)=-ia(C,D).
$$
The uniqueness theorem for the primitive orientation ensures that this rule
is never imposed again in the reverse direction.
-/
def RecursiveVectorSystem
    (s : (CircleCoordinates → CircleCoordinates → GaussianInt) ×
      (CircleCoordinates → CircleCoordinates → GaussianInt)) : Prop :=
-- BODY
  let v := s.1
  let a := s.2
  let ii : GaussianInt := ⟨0, 1⟩
  (∀ C D, ¬ BandTangency C D → v C D = 0 ∧ a C D = 0) ∧
  (∀ z : GaussianInt,
    let q : Fin 4 → CircleCoordinates :=
      ![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ii), (0, 1), (0, -1)]
    v (q 3) (q 2) = 0 ∧ v (q 2) (q 1) = -1 ∧ v (q 1) (q 3) = 1 ∧
    a (q 3) (q 2) = 1 ∧ a (q 2) (q 1) = -1 - z - ii ∧
    a (q 1) (q 3) = z + ii) ∧
  (∀ q : Fin 4 → CircleCoordinates, SemiProperQuadruple q →
    v (q 2) (q 0) = v (q 2) (q 1) - ii * v (q 3) (q 2) ∧
    v (q 0) (q 3) = v (q 1) (q 3) + ii * v (q 3) (q 2) ∧
    a (q 2) (q 0) = a (q 2) (q 1) + ii * a (q 3) (q 2) ∧
    a (q 0) (q 3) = a (q 1) (q 3) - ii * a (q 3) (q 2)) ∧
  (∀ C D : CircleCoordinates, PrimitiveVectorOrientation C D →
    v D C = ii * v C D ∧ a D C = -ii * a C D)

end ApollonianSuperharmonic

end
