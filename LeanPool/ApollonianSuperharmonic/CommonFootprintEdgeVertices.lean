/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FootprintEdges

-- [TABLET NODE: CommonFootprintEdgeVertices]

/-!
# CommonFootprintEdgeVertices

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For prototiles $T$ and $U$, the common-footprint-edge vertex set is the set
of all endpoints of actual edges in
$E(T)\cap E(U)$, where $E$ is `FootprintEdges`.  Thus
$$
 V_E(T,U)=\{x:\text{ for some }e\in E(T)\cap E(U),\ x\in e\}.
$$
In particular, an isolated vertex in $\operatorname{foot}(T)\cap\operatorname{foot}(U)$ does not
belong
to this set unless it is also an endpoint of a common footprint edge.
-/
def CommonFootprintEdgeVertices (T U : ProtoTile) : Set GaussianInt :=
-- BODY
  {x | ∃ e ∈ FootprintEdges T ∩ FootprintEdges U, x ∈ e}

end ApollonianSuperharmonic

end
