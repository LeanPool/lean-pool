/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordFareyParameter
public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction

-- [TABLET NODE: FordExceptionalLattice]

/-!
# FordExceptionalLattice

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a Ford--Farey parameter, the exceptional period lattice is
$$
 L_{p,q}=\langle(0,-q),(q,q_1)\rangle_{\mathbb Z}\subseteq\mathbb Z^2.
$$
The third displayed displacement $(-q,q_2)$ is the negative sum of these
two generators because $q=q_1+q_2$.
-/
def FordExceptionalLattice (P : FordFareyParameter) : AddSubgroup GaussianInt :=
-- BODY
  AddSubgroup.closure
    {v | v = (⟨0, -(P.q : Int)⟩ : GaussianInt) ∨
      v = (⟨(P.q : Int), (P.q₁ : Int)⟩ : GaussianInt)}

end ApollonianSuperharmonic

end
