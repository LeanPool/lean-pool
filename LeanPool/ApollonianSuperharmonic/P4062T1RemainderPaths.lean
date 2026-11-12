/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4062T1RecursiveInteriors

-- [TABLET NODE: P4062T1RemainderPaths]

/-!
# P4062T1RemainderPaths

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a Ford parameter write $r=q_1,s=q_2,q=r+s$. The following two
rooted lattice sets $(W_0,a_0),(W_1,a_1)$ are subsets of $D_q$.
If $r>s$, set
$$
\begin{array}{ll}
W_0=\{(r,y):1\leq y\leq s\}\cup\{(x,s):r\leq x<q\},&a_0=(r,s),\cr
W_1=\{(x,r):1\leq x\leq s\}\cup\{(s,y):r\leq y<q\},&a_1=(s,r).
\end{array}
$$
If $r\leq s$, set
$$
\begin{array}{ll}
W_0=\{(r,y):1\leq y\leq r\}\cup\{(x,r):1\leq x\leq r\},&a_0=(r,r),\cr
W_1=\{(s,y):s\leq y<q\}\cup\{(x,s):s\leq x<q\},&a_1=(s,s).
\end{array}
$$
In all four displayed sets the defining ranges are additionally intersected
with $D_q$, so the definition also makes sense in the unit-denominator case.
-/
def P4062T1RemainderPaths (P : FordFareyParameter) :
    Fin 2 → Finset GaussianInt × GaussianInt :=
-- BODY
  if P.q₂ < P.q₁ then
    ![((P4062T1InteriorSquare P.q).filter (fun x =>
        (x.re = (P.q₁ : Int) ∧ x.im ≤ (P.q₂ : Int)) ∨
        (x.im = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ x.re)),
        ⟨(P.q₁ : Int), (P.q₂ : Int)⟩),
      ((P4062T1InteriorSquare P.q).filter (fun x =>
        (x.im = (P.q₁ : Int) ∧ x.re ≤ (P.q₂ : Int)) ∨
        (x.re = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ x.im)),
        ⟨(P.q₂ : Int), (P.q₁ : Int)⟩)]
  else
    ![((P4062T1InteriorSquare P.q).filter (fun x =>
        (x.re = (P.q₁ : Int) ∧ x.im ≤ (P.q₁ : Int)) ∨
        (x.im = (P.q₁ : Int) ∧ x.re ≤ (P.q₁ : Int))),
        ⟨(P.q₁ : Int), (P.q₁ : Int)⟩),
      ((P4062T1InteriorSquare P.q).filter (fun x =>
        (x.re = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ x.im) ∨
        (x.im = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ x.re)),
        ⟨(P.q₂ : Int), (P.q₂ : Int)⟩)]

end ApollonianSuperharmonic

end
