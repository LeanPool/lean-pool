/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Bridge
public import LeanPool.GraphMinor.GM07.CuffSlide
public import LeanPool.GraphMinor.GM07.Section35
public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.GM07.Open
public import LeanPool.GraphMinor.GM07.Section7
public import LeanPool.GraphMinor.GM07.Section9
public import LeanPool.GraphMinor.GM09.Bridge
public import LeanPool.GraphMinor.GM11.Cited
public import LeanPool.GraphMinor.GM12.Bridge
public import LeanPool.GraphMinor.GM12.Cited
public import LeanPool.GraphMinor.GM12.Section5Final
public import LeanPool.GraphMinor.GM12.Section6
public import LeanPool.GraphMinor.GM12.Section710
public import LeanPool.GraphMinor.GM12.Section76
public import LeanPool.GraphMinor.GM12.Section77
public import LeanPool.GraphMinor.GM14.Adapted
public import LeanPool.GraphMinor.GM14.Bridge
public import LeanPool.GraphMinor.GM14.Cited
public import LeanPool.GraphMinor.GM14.Section8Core
public import LeanPool.GraphMinor.GM14.Section9a
public import LeanPool.GraphMinor.GM14.Section9b
public import LeanPool.GraphMinor.GM14.Whitney
public import LeanPool.GraphMinor.GM12.Section75Proof
public import LeanPool.GraphMinor.GM15.Cited
public import LeanPool.GraphMinor.GM15.Section3
public import LeanPool.GraphMinor.GM15.Section3Crosscap
public import LeanPool.GraphMinor.GM15.Section3Handle
public import LeanPool.GraphMinor.GM15.Section3Parallel
public import LeanPool.GraphMinor.GM15.Section4
public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM16.MainProof
public import LeanPool.GraphMinor.GM16.Section4
public import LeanPool.GraphMinor.GM16.Section4Proof
public import LeanPool.GraphMinor.GM16.Section5
public import LeanPool.GraphMinor.GM16.Section5Five
public import LeanPool.GraphMinor.GM16.Theorem35Bridge
public import LeanPool.GraphMinor.GM16.Tower
public import LeanPool.GraphMinor.GM17.Bridge
public import LeanPool.GraphMinor.GM17.PushNode
public import LeanPool.GraphMinor.GM17.RegionBoundary
public import LeanPool.GraphMinor.GM17.RegionDisc
public import LeanPool.GraphMinor.GM17.Section5
public import LeanPool.GraphMinor.GM17.Section8
public import LeanPool.GraphMinor.GM19.Cited
public import LeanPool.GraphMinor.GM19.Conditional
public import LeanPool.GraphMinor.GM19.Conditional2
public import LeanPool.GraphMinor.GM19.FeatureCount
public import LeanPool.GraphMinor.GM19.FragmentForm
public import LeanPool.GraphMinor.GM19.FragmentOrient
public import LeanPool.GraphMinor.GM19.FragmentSimpler
public import LeanPool.GraphMinor.GM19.Section10f
public import LeanPool.GraphMinor.GM19.Section10s
public import LeanPool.GraphMinor.GM19.Section10t
public import LeanPool.GraphMinor.GM19.Section11g
public import LeanPool.GraphMinor.GM19.Section14ah
public import LeanPool.GraphMinor.GM19.Section15b
public import LeanPool.GraphMinor.GM19.Section15q
public import LeanPool.GraphMinor.GM19.Section2
public import LeanPool.GraphMinor.GM19.Section5o
public import LeanPool.GraphMinor.GM19.Section5r
public import LeanPool.GraphMinor.GM19.Section6a
public import LeanPool.GraphMinor.GM19.Section6Five
public import LeanPool.GraphMinor.GM19.Section6Six
public import LeanPool.GraphMinor.GM19.Section6Two
public import LeanPool.GraphMinor.GM19.Thinning
public import LeanPool.GraphMinor.GM20.Cited
public import LeanPool.GraphMinor.GM20.Main
public import LeanPool.GraphMinor.Surface.Cuffs
public import LeanPool.GraphMinor.Surface.TopologyStatements

import LeanPool.GraphMinor.GM16.InductionsProved

import LeanPool.GraphMinor.GM17.Section8Proved

import LeanPool.GraphMinor.GM19.Section2Proved

import LeanPool.GraphMinor.GM19.Section5oProved

import LeanPool.GraphMinor.GM19.Section6aProved

/-!
# The graph minor theorem, assembled

`GM20.graph_minor_theorem_assembled` proves that in every infinite sequence of finite multigraphs,
an earlier graph is isomorphic to a minor of a later one. The proof discharges the statements used
from the preceding papers, including the dependence of Graph Minors XX on XVII and XIX.

The preceding results are assembled at universe level `0`. The final theorem holds for vertex and
edge types at arbitrary universe levels.
-/

@[expose] public section

namespace GraphMinor.GM20

open Graph

/-- **The graph minor theorem** (Graph Minors XX, (10.5)), for a sequence of finite multigraphs. -/
theorem graph_minor_theorem_assembled
    {α β : Type*} (G : ℕ → Graph α β) (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by
  exact graph_minor_theorem_of_cited G hV hE

end GraphMinor.GM20
