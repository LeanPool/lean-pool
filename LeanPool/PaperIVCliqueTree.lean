/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

module

public import LeanPool.PaperIVCliqueTree.Basic
public import LeanPool.PaperIVCliqueTree.Characterization
public import LeanPool.PaperIVCliqueTree.Counting
public import LeanPool.PaperIVCliqueTree.GluingChordal
public import LeanPool.PaperIVCliqueTree.GluingCounting
public import LeanPool.PaperIVCliqueTree.Helly
public import LeanPool.PaperIVCliqueTree.Maximal
public import LeanPool.PaperIVCliqueTree.MaximalBridge
public import LeanPool.PaperIVCliqueTree.PEO
public import LeanPool.PaperIVCliqueTree.Separator
public import LeanPool.PaperIVCliqueTree.TreeDecomposition

/-!
# Clique trees and separators of chordal graphs

Source: url:https://github.com/jtraverso/erdos-81-chordal-clique-partitions
Authors: Juan Pablo Traverso Gianini
Status: verified
Main declarations: `SimpleGraph.isChordal_iff_nonempty_cliqueTree`
Tags: graph-theory, chordal-graphs, clique-trees, perfect-elimination-orders, separators
MSC: 05C75
-/
