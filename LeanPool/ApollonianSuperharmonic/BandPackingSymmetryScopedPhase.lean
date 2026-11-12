/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryQuadrupleAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn

-- [TABLET NODE: BandPackingSymmetryScopedPhase]

/-!
# BandPackingSymmetryScopedPhase

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $h$ be a band-packing symmetry word, let
$p=(C_0,C_1,C_2,C_3)$ be an ordered coordinate quadruple, and let
$\delta$ be a Boolean.  Put
$$
 P_i=C_{i+1},\qquad
 W_i=v(P_{i+2},P_{i+1}),\qquad
 \sigma_h(i)=\begin{cases}-i,&h\text{ reverses orientation},\\
 i,&h\text{ preserves orientation},\end{cases}
$$
where all parent indices lie in $\operatorname{Fin}3$.  Thus, with the
zero-based labels used by the occurrence definition,
$$
       (W_0,W_1,W_2)=(v_{32},v_{13},v_{21}).
$$
Write $p'=h_*p$ and $P'_j=p'_{j+1}$, let $L_h$ be the vector action, let
$Qv=iv$, and set
$\epsilon_\delta=-1$ when $\delta=\mathrm{true}$ and
$\epsilon_\delta=1$ otherwise.  The scoped phase predicate
$\operatorname{BandPackingSymmetryScopedPhase}(h,p,\delta)$ means that,
for every $i\in\operatorname{Fin}3$,
$$
\begin{aligned}
 v(p'_{\sigma_h(i)+1},p'_0)
   &=\epsilon_\delta L_h\bigl(v(P_i,C_0)\bigr),\\
 v(p'_0,p'_{\sigma_h(i)+1})
   &=\epsilon_\delta
     \begin{cases}-L_h\bigl(v(C_0,P_i)\bigr),&h\text{ reverses},\\
                    L_h\bigl(v(C_0,P_i)\bigr),&h\text{ preserves},
       \end{cases}\\
 v(P'_{\sigma_h(i)+2},P'_{\sigma_h(i)+1})
   &=\epsilon_\delta
     \begin{cases}Q L_h(W_i),&h\text{ reverses},\\
                    L_h(W_i),&h\text{ preserves}.
       \end{cases}
\end{aligned}
$$
All subscripts on $P'$ are computed in $\operatorname{Fin}3$.
Equivalently, the last left-hand side is the cyclic occurrence edge
$W'_{\sigma_h(i)}$.  In particular orientation reversal keeps the label
$\sigma_h(i)=-i$ and reverses the edge endpoints; the displayed $Q$ is the
resulting flip correction, not an additional cyclic shift.
-/
def BandPackingSymmetryScopedPhase (h : BandPackingSymmetry)
    (p : Fin 4 → CircleCoordinates) (negative : Bool) : Prop :=
-- BODY
  let sigma : Fin 3 → Fin 3 := fun i =>
    if BandPackingSymmetryReversesOrientation h then -i else i
  ∀ i : Fin 3,
    BandVectors.1
        (BandPackingSymmetryQuadrupleAction h p (sigma i).succ)
        (BandPackingSymmetryQuadrupleAction h p 0) =
      (if negative then (-1 : GaussianInt) else 1) *
        BandPackingSymmetryVectorAction h
          (BandVectors.1 (p i.succ) (p 0)) ∧
    BandVectors.1
        (BandPackingSymmetryQuadrupleAction h p 0)
        (BandPackingSymmetryQuadrupleAction h p (sigma i).succ) =
      (if negative then (-1 : GaussianInt) else 1) *
        (if BandPackingSymmetryReversesOrientation h then
          -BandPackingSymmetryVectorAction h
            (BandVectors.1 (p 0) (p i.succ))
        else
          BandPackingSymmetryVectorAction h
            (BandVectors.1 (p 0) (p i.succ))) ∧
    BandVectors.1
        (BandPackingSymmetryQuadrupleAction h p ((sigma i + 2).succ))
        (BandPackingSymmetryQuadrupleAction h p ((sigma i + 1).succ)) =
      (if negative then (-1 : GaussianInt) else 1) *
        (if BandPackingSymmetryReversesOrientation h then
          GaussianQuarterTurn
            (BandPackingSymmetryVectorAction h
              (BandVectors.1 (p ((i + 2).succ)) (p ((i + 1).succ))))
        else
          BandPackingSymmetryVectorAction h
            (BandVectors.1 (p ((i + 2).succ)) (p ((i + 1).succ))))

end ApollonianSuperharmonic

end
