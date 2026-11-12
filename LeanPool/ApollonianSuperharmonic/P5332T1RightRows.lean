/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5332T1Stencil

-- [TABLET NODE: P5332T1RightRows]

/-!
# P5332T1RightRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a Ford--Farey parameter put $r=q_1$, $s=q_2$ and
$C_d(N)=-\lfloor-N/d\rfloor$.  The three equal-square contact stencils,
indexed by $j=0,1,2$ and an integer $t$, are the following records
$(d,a,z,w,V)$ of `P5332T1Stencil`; in each row $w=0$:
$$
\begin{array}{c|c|c|c}
j&d&a&z\\ \hline
0&(-r,q)&(p,-p_1)&(t,q)\\
1&(-s,-q)&(-p,-p_2)&(t,0)\\
2&(q,0)&(0,p)&(q,t)
\end{array}
$$
Their five value vectors, in the prescribed order, are
$$
\begin{array}{c|l}
0&(pt,p(t+1),p(t-1),pt+C_q(pt-1),pt-\lfloor pt/q\rfloor)\\
1&(0,0,0,C_q(pt),-\lfloor(pt+1)/q\rfloor)\\
2&(pt,pt+C_q(pt),pt-\lfloor pt/q\rfloor,p(t+1),p(t-1)).
\end{array}
$$
These are data definitions, not an assertion that any function takes these
values.  For positive $d$, $C_d$ is the usual ceiling for signed numerators.
-/
def P5332T1RightRows (P : FordFareyParameter) (j : Fin 3) (t : Int) :
    P5332T1Stencil :=
-- BODY
  let q : Int := P.q
  let r : Int := P.q₁
  let s : Int := P.q₂
  let p := P.p
  let C (N : Int) := -((-N) / q)
  ![
    ⟨⟨-r, q⟩, ⟨p, -P.p₁⟩, ⟨t, q⟩, 0,
      ![p*t, p*(t+1), p*(t-1), p*t+C (p*t-1), p*t-(p*t/q)]⟩,
    ⟨⟨-s, -q⟩, ⟨-p, -P.p₂⟩, ⟨t, 0⟩, 0,
      ![0, 0, 0, C (p*t), -((p*t+1)/q)]⟩,
    ⟨⟨q, 0⟩, ⟨0, p⟩, ⟨q, t⟩, 0,
      ![p*t, p*t+C (p*t), p*t-(p*t/q), p*(t+1), p*(t-1)]⟩
  ] j

end ApollonianSuperharmonic

end
