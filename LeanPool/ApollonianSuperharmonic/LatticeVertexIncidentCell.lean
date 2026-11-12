/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic

public import LeanPool.ApollonianSuperharmonic.LatticeCell

-- [TABLET NODE: LatticeVertexIncidentCell]

/-!
# LatticeVertexIncidentCell

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a lattice vertex $x$, number its four incident unit cells cyclically by
their lower-left corners
$$
 \operatorname{inc}(x,0)=x,\quad
 \operatorname{inc}(x,1)=x-1,\quad
 \operatorname{inc}(x,2)=x-1-\mathrm{i},\quad
 \operatorname{inc}(x,3)=x-\mathrm{i}.
$$
Indices are read modulo four.  In particular, sectors $j$ and $j+2$ are
opposite at $x$.
-/
def LatticeVertexIncidentCell (x : GaussianInt) : Fin 4 -> LatticeCell :=
-- BODY
  ![x, x - 1, x - 1 - ⟨0, 1⟩, x - ⟨0, 1⟩]

end ApollonianSuperharmonic

end
