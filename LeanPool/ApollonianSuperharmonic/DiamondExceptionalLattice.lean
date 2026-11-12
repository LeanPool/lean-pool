/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.DiamondParameter
public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction

-- [TABLET NODE: DiamondExceptionalLattice]

/-!
# DiamondExceptionalLattice

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $k>0$, the diamond exceptional period lattice is
$$
 L_k=\langle(0,-2k),(k+1,k)\rangle_{\mathbb Z}.
$$
Its third displayed displacement $(-k-1,k)$ is the negative sum of the
two generators.
-/
def DiamondExceptionalLattice (K : DiamondParameter) : AddSubgroup GaussianInt :=
-- BODY
  AddSubgroup.closure
    {v | v = (⟨0, -(2 * K.1 : Int)⟩ : GaussianInt) ∨
      v = (⟨(K.1 + 1 : Int), (K.1 : Int)⟩ : GaussianInt)}

end ApollonianSuperharmonic

end
