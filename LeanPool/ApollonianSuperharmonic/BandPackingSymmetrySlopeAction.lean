/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetry
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction
public import LeanPool.ApollonianSuperharmonic.TileCentroid

-- [TABLET NODE: BandPackingSymmetrySlopeAction]

/-!
# BandPackingSymmetrySlopeAction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For every prototile $T$ and every pair $p=(p_1,p_2)\in\mathbb R^2$, the
lifted slope action of a band-packing symmetry word is defined recursively
on generators by
$$
\begin{aligned}
1\star_Tp&=p,\\
T_w\star_Tp&=p+M_w\operatorname{cent}(T)+(-A/2,A/2),
 \quad w=A+Bi,\quad
 M_w=\begin{pmatrix}A&B\\B&-A\end{pmatrix},\\
N\star_T(p_1,p_2)&=(-p_2,p_1),\\
K\star_T(p_1,p_2)&=(-p_1,p_2).
\end{aligned}
$$
Writing $h\cdot T$ for the literal grid action
`BandPackingSymmetryTileAction`, the composition rule is
$$
 \operatorname{comp}(g,h)\star_Tp
   =g\star_{h\cdot T}\bigl(h\star_Tp\bigr).
$$
Here $\operatorname{cent}(T)$ is the total centroid of
`TileCentroid`: if $T.\mathrm{cells}$ is empty, it is the
designated anchor of $T$, so the shift clause uses that anchor.  The
half-cell term in the shift clause is part of the definition.  It is
independent of $T$ and therefore cancels from a difference of two vectors
acted on by the same shift.  Later covariance results specialize this
total algebraic action to vectors that are actual slopes of partial
odometers on nonempty supports.
-/
noncomputable def BandPackingSymmetrySlopeAction :
    BandPackingSymmetry → ProtoTile → (ℝ × ℝ) → (ℝ × ℝ) :=
-- BODY
  fun g T p => match g with
    | .identity => p
    | .shift w =>
        (p.1 + (w.re : ℝ) * (TileCentroid T).1 +
            (w.im : ℝ) * (TileCentroid T).2 - (w.re : ℝ) / 2,
          p.2 + (w.im : ℝ) * (TileCentroid T).1 -
            (w.re : ℝ) * (TileCentroid T).2 + (w.re : ℝ) / 2)
    | .negate => (-p.2, p.1)
    | .conjugate => (-p.1, p.2)
    | .comp a b =>
        BandPackingSymmetrySlopeAction a
          (BandPackingSymmetryTileAction b T)
          (BandPackingSymmetrySlopeAction b T p)

end ApollonianSuperharmonic

end
