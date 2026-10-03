/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BrooksSubcubic.Main

/-!
# Brooks' theorem for subcubic graphs

Source: doi:10.1017/S030500410002168X, url:https://github.com/jtraverso/lean-pool/blob/66caffc3dbae5a766a96a3980f5ddd7f4b2bef6f/LeanPool/BrooksSubcubic/Main.lean
Authors: Juan Pablo Traverso Gianini
Status: verified
Main declarations: `BrooksSubcubic.brooks_cubic`
Tags: graph-theory, vertex-colouring, brooks-theorem, subcubic-graphs
MSC: 05C15
-/

/-!
## Mathematical overview

The public theorem `BrooksSubcubic.brooks_cubic` states that a finite simple graph
with maximum degree at most three and no four-clique admits a three-colouring.
Connectedness is not assumed. This is the subcubic case, not the general Brooks theorem.

The proof works componentwise. A component with a vertex of degree less than three
is coloured greedily in a distance-based order. For a cubic component, a cut vertex
allows two colourings to be glued. Otherwise, a good triple supplies two nonadjacent
neighbours whose deletion leaves a connected graph: give these neighbours the same
colour and greedily colour the remaining vertices, finishing at their common neighbour.

All graph, walk, connected-component and colouring objects are Mathlib's native ones.
`Greedy` provides a rank-based colouring with control of colour zero; the separator
and attachment modules isolate the connectivity arguments used to find a good triple.
No paper-specific packing or asymptotic infrastructure is included.
-/
