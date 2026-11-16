/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5332T1Stencil
public import LeanPool.ApollonianSuperharmonic.FordFareyParameter

-- [TABLET NODE: P5332T1ParentRows]

/-!
# P5332T1ParentRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For every reduced Ford--Farey parameter $P$ of
`FordFareyParameter`, put $r=q_1,s=q_2,a=p_1,b=p_2$.
Thus $p,a,b$ are integers, $q,r,s$ are nonnegative integers,
$q,s>0$, and $0\le r<q$.
For every integer $N$ and nonnegative integer $d$, define
$$
Q_d(N)=\begin{cases}
\lfloor N/d\rfloor,&d>0,\\
0,&d=0,
\end{cases}
\qquad C_d(N)=-Q_d(-N).
$$
In particular, $Q_0(N)=C_0(N)=0$.
For every integer $t$, $j\in\{0,1\}$, and $k\in\{0,1,2,3\}$,
define the child--parent contact stencils as records
$(d,\alpha,z,w,V)$ of `P5332T1Stencil`.
Here $j=0$ means parent $(a,r)$ and $j=1$ means parent $(b,s)$;
$k$ is the displayed rotation.
The domain includes $q=1$, when $(a,r)=(1,0)$ and
$(b,s)=(p-1,1)$; the first parent is the oriented line parent.
No contact or coverage hypothesis is imposed on $t$ in this definition.
$$
\begin{array}{cc|c|c|c|c}
j&k&d&\alpha&z&w\\ \hline
0&0&(s,q)&(p,b)&(s+t,q)&(-r,q)\\
0&1&(-r,s)&(b,-a)&(0,s+t)&(-r,q)\\
0&2&(0,-r)&(-a,0)&(r-t,0)&(r,-q)\\
0&3&(q,0)&(0,p)&(q,r-t)&(r,-q)\\
1&0&(-s,0)&(0,-b)&(0,s-t)&(-s,-q)\\
1&1&(r,-s)&(-b,a)&(r+t,0)&(-s,-q)\\
1&2&(q,r)&(a,p)&(q,r+t)&(s,q)\\
1&3&(0,q)&(p,0)&(s-t,q)&(s,q)
\end{array}
$$
The five values in the prescribed order are
$$
\begin{array}{cc|l}
0&0&(p(s+t),p(s+t+1),p(s+t-1),
 p(s+t)+b+C_r(at),p(s+t)-b-Q_q(pt+1))\\
0&1&(0,b+C_q(pt+1),-b-Q_r(at),0,0)\\
0&2&(0,0,0,C_q(p(r-t)),-Q_r(a(r-t)))\\
0&3&(p(r-t),p(r-t)+C_r(a(r-t)),p(r-t)-Q_q(p(r-t)),
 p(r-t+1),p(r-t-1))\\
1&0&(0,C_q(p(s-t)),-Q_s(b(s-t)),0,0)\\
1&1&(0,0,0,a+C_q(pt-1),-a-Q_s(bt))\\
1&2&(p(r+t),p(r+t)+a+C_s(bt),p(r+t)-a-Q_q(pt-1),
 p(r+t+1),p(r+t-1))\\
1&3&(p(s-t),p(s-t+1),p(s-t-1),
 p(s-t)+C_s(b(s-t)),p(s-t)-Q_q(p(s-t))).
\end{array}
$$
These formulas only specify data; the contact calculation must establish
that they are the actual values of a normalized function.
-/
def P5332T1ParentRows (P : FordFareyParameter) (j : Fin 2) (k : Fin 4)
    (t : Int) : P5332T1Stencil :=
-- BODY
  let q : Int := P.q
  let r : Int := P.q₁
  let s : Int := P.q₂
  let p := P.p
  let a := P.p₁
  let b := P.p₂
  let C (N d : Int) := -((-N) / d)
  ![
    ![
      ⟨⟨s,q⟩, ⟨p,b⟩, ⟨s+t,q⟩, ⟨-r,q⟩,
        ![p*(s+t),p*(s+t+1),p*(s+t-1),
          p*(s+t)+b+C (a*t) r,p*(s+t)-b-((p*t+1)/q)]⟩,
      ⟨⟨-r,s⟩, ⟨b,-a⟩, ⟨0,s+t⟩, ⟨-r,q⟩,
        ![0,b+C (p*t+1) q,-b-(a*t/r),0,0]⟩,
      ⟨⟨0,-r⟩, ⟨-a,0⟩, ⟨r-t,0⟩, ⟨r,-q⟩,
        ![0,0,0,C (p*(r-t)) q,-(a*(r-t)/r)]⟩,
      ⟨⟨q,0⟩, ⟨0,p⟩, ⟨q,r-t⟩, ⟨r,-q⟩,
        ![p*(r-t),p*(r-t)+C (a*(r-t)) r,
          p*(r-t)-(p*(r-t)/q),p*(r-t+1),p*(r-t-1)]⟩
    ],
    ![
      ⟨⟨-s,0⟩, ⟨0,-b⟩, ⟨0,s-t⟩, ⟨-s,-q⟩,
        ![0,C (p*(s-t)) q,-(b*(s-t)/s),0,0]⟩,
      ⟨⟨r,-s⟩, ⟨-b,a⟩, ⟨r+t,0⟩, ⟨-s,-q⟩,
        ![0,0,0,a+C (p*t-1) q,-a-(b*t/s)]⟩,
      ⟨⟨q,r⟩, ⟨a,p⟩, ⟨q,r+t⟩, ⟨s,q⟩,
        ![p*(r+t),p*(r+t)+a+C (b*t) s,
          p*(r+t)-a-((p*t-1)/q),p*(r+t+1),p*(r+t-1)]⟩,
      ⟨⟨0,q⟩, ⟨p,0⟩, ⟨s-t,q⟩, ⟨s,q⟩,
        ![p*(s-t),p*(s-t+1),p*(s-t-1),
          p*(s-t)+C (b*(s-t)) s,p*(s-t)-(p*(s-t)/q)]⟩
    ]
  ] j k

end ApollonianSuperharmonic

end
