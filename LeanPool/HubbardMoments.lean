/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/

module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Defs
public import LeanPool.HubbardMoments.Spec
public import LeanPool.HubbardMoments.Combinatorics.Subsets
public import LeanPool.HubbardMoments.Torus
public import LeanPool.HubbardMoments.Sectors
public import LeanPool.HubbardMoments.SecondMoment
public import LeanPool.HubbardMoments.ProjectedHopping
public import LeanPool.HubbardMoments.Doublon
public import LeanPool.HubbardMoments.SchriefferWolff
public import LeanPool.HubbardMoments.FinitePopulation
public import LeanPool.HubbardMoments.TorusBand
public import LeanPool.HubbardMoments.ClosedWalks
public import LeanPool.HubbardMoments.Fermions
public import LeanPool.HubbardMoments.Hubbard
public import LeanPool.HubbardMoments.Weighted
public import LeanPool.HubbardMoments.Main

/-!
# Spectral moments of the projected Hubbard configuration graph

Source: arxiv:2611.19929, url:https://github.com/zhineos/hubbard-spectral-moments/tree/66d5104785daae03e2f91bbb681aa0fbcea1e6d4/lean
Authors: Daniel Souza
Status: verified
Main declarations: `HubbardMoments.secondMomentHubbardWeighted`,
  `HubbardMoments.canonicalAnticommutation`, `HubbardMoments.schriefferWolffHubbard`,
  `HubbardMoments.doubledPeierlsPhase`, `HubbardMoments.fourHopPermutations`
Tags: mathematical-physics, hubbard-model, spectral-moments, graph-theory
MSC: 81V70, 05C50, 82B20
-/
