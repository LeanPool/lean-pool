/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordRecursiveVertexDomains
public import LeanPool.ApollonianSuperharmonic.LatticeVertexBoundary

-- [TABLET NODE: FordBoundaryMultiplicity]

/-!
# FordBoundaryMultiplicity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a Ford--Farey parameter and a lattice vertex $x$, the recursive boundary
multiplicity $m_P(x)$ is the number of indices $i\in\{1,2,3,4\}$ for which
$x\in\partial E_i$.
-/
noncomputable def FordBoundaryMultiplicity (P : FordFareyParameter)
    (x : GaussianInt) : Nat :=
-- BODY
  by
    classical
    exact (Finset.univ.filter fun i : Fin 4 =>
      x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P i)).card

end ApollonianSuperharmonic

end
