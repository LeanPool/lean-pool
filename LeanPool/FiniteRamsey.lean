/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/

module

public import LeanPool.FiniteRamsey.ArrowNumber
public import LeanPool.FiniteRamsey.ArrowSemantics
public import LeanPool.FiniteRamsey.BinomialBound
public import LeanPool.FiniteRamsey.DigraphTournament
public import LeanPool.FiniteRamsey.DigraphTournamentRamsey
public import LeanPool.FiniteRamsey.GraphRamseyNumber
public import LeanPool.FiniteRamsey.HypergraphRamsey
public import LeanPool.FiniteRamsey.ColorInducedArrow
public import LeanPool.FiniteRamsey.InfiniteRamsey
public import LeanPool.FiniteRamsey.InfiniteRamseyKUniform
public import LeanPool.FiniteRamsey.MonochromaticClique
public import LeanPool.FiniteRamsey.MonochromaticKUniform
public import LeanPool.FiniteRamsey.MulticolorRamsey
public import LeanPool.FiniteRamsey.MulticolorRamseyUnconditional
public import LeanPool.FiniteRamsey.OrderedRamsey
public import LeanPool.FiniteRamsey.RamseyExistence
public import LeanPool.FiniteRamsey.RamseyLowerBound
public import LeanPool.FiniteRamsey.RamseyLowerBoundAsymptotic
public import LeanPool.FiniteRamsey.RamseyNumber
public import LeanPool.FiniteRamsey.RamseyProperty
public import LeanPool.FiniteRamsey.RamseyTheorem
public import LeanPool.FiniteRamsey.Schur
public import LeanPool.FiniteRamsey.SimpleGraphAddVertex
public import LeanPool.FiniteRamsey.SimpleGraphComplementIso
public import LeanPool.FiniteRamsey.SimpleGraphLemmas
public import LeanPool.FiniteRamsey.SimpleGraphSaturation
public import LeanPool.FiniteRamsey.SimpleGraphTwins

/-!
# Finite-colour Ramsey theory

Source: url:https://github.com/Egly443/lean-ramsey
Authors: Brian Sanders
Status: verified
Main declarations: `SimpleGraph.exists_arrow`, `SimpleGraph.lt_ramseyNumber_of_choose_lt`,
  `SimpleGraph.schur`
Tags: ramsey-theory, edge-colorings, combinatorics
MSC: 05C55, 05D10
-/
