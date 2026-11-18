/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.TouchingTriple
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices

-- [TABLET NODE: P4418T3SelectedInterfaceData]

/-!
# P4418T3SelectedInterfaceData

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For literal tiles $V,W,G_0,G_1$, these data consist of distinct vertices
$y_0,y_1$, a complete nontrivial simple grid path from $y_0$ to $y_1$
whose vertex set is $\operatorname{foot}(V)\cap\operatorname{foot}(W)$ and whose edge set is
$E(V)\cap E(W)$, lattice-disk certificates for all four tiles, and
cell disjointness of $V,W$ and of each $G_a$ from each of $V,W$.
They also retain touching triples $(V,W,G_a)$ and membership of $y_a$
in their three raw footprints, for $a=0,1$. No orientation is imposed on
any independently supplied interface record.
-/
structure P4418T3SelectedInterfaceData (V W G₀ G₁ : ProtoTile) where
-- BODY
  /-- The distinguished interface endpoint belonging to the first companion. -/
  first : GaussianInt
  /-- The opposite interface endpoint belonging to the second companion. -/
  last : GaussianInt
  distinct : first ≠ last
  path : SimpleGridPathBetween (FootprintVertices V ∩ FootprintVertices W)
    (FootprintEdges V ∩ FootprintEdges W) first last
  latticeV : LatticeTile V
  latticeW : LatticeTile W
  latticeG₀ : LatticeTile G₀
  latticeG₁ : LatticeTile G₁
  disjointVW : Disjoint V.cells W.cells
  disjointVG₀ : Disjoint V.cells G₀.cells
  disjointWG₀ : Disjoint W.cells G₀.cells
  disjointVG₁ : Disjoint V.cells G₁.cells
  disjointWG₁ : Disjoint W.cells G₁.cells
  touching₀ : TouchingTriple V W G₀
  touching₁ : TouchingTriple V W G₁
  common₀ : first ∈ FootprintVertices V ∩ FootprintVertices W ∩ FootprintVertices G₀
  common₁ : last ∈ FootprintVertices V ∩ FootprintVertices W ∩ FootprintVertices G₁

end ApollonianSuperharmonic

end
