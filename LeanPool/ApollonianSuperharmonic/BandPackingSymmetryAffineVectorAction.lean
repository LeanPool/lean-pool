/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetry
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import LeanPool.ApollonianSuperharmonic.GaussianReflection

-- [TABLET NODE: BandPackingSymmetryAffineVectorAction]

/-!
# BandPackingSymmetryAffineVectorAction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The affine action of a band-packing symmetry on a recursive spatial and
slope-vector pair $(v,a)\in\mathbb Z[i]^2$ is
$$
\begin{array}{c|c}
g&g\diamond(v,a)\\ \hline
1&(v,a)\\
T_w&(v,a+w\bar v)\\
N&(iv,ia)\\
K&(-\bar v,-\bar a).
\end{array}
$$
Here $N$ is coordinate negation and $K$ is coordinate conjugation in the
band packing.  A composite acts by composition with the right-hand word
first.  This is an action on the lifted pair; comparison with the
canonical recursive vectors at a proper occurrence still requires the
single local projective phase.
-/
def BandPackingSymmetryAffineVectorAction :
    BandPackingSymmetry → (GaussianInt × GaussianInt) →
      (GaussianInt × GaussianInt) :=
-- BODY
  fun g x => match g with
    | .identity => x
    | .shift w => (x.1, x.2 + w * GaussianReflection x.1)
    | .negate => (GaussianQuarterTurn x.1, GaussianQuarterTurn x.2)
    | .conjugate => (-GaussianReflection x.1, -GaussianReflection x.2)
    | .comp a b =>
        BandPackingSymmetryAffineVectorAction a
          (BandPackingSymmetryAffineVectorAction b x)

end ApollonianSuperharmonic

end
