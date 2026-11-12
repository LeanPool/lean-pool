/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.Basic

public import LeanPool.ApollonianSuperharmonic.DiamondParameter
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: DiamondVertexDomains]

/-!
# DiamondVertexDomains

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $k>0$, let
$$
 T_k=\{x:\max(|x_1|,|x_2-k|,|x_1|+|x_2-k|-1)\le k\}
$$
and let its inner diamond be
$$
 T'_k=\{x:|x_1|+|x_2-k|\le k-1\}.
$$
We write `false` for $T_k$ and `true` for $T'_k$.  These are
closed vertex domains, not the staircase cell set `DiamondCellDomain`.
-/
def DiamondVertexDomains (K : DiamondParameter) : Bool -> Set GaussianInt :=
-- BODY
  fun interior x =>
    if interior then
      Int.natAbs x.re + Int.natAbs (x.im - (K.1 : Int)) <= K.1 - 1
    else
      max (Int.natAbs x.re)
        (max (Int.natAbs (x.im - (K.1 : Int)))
          (Int.natAbs x.re + Int.natAbs (x.im - (K.1 : Int)) - 1)) <= K.1

end ApollonianSuperharmonic

end
