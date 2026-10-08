/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini, Claude AI
-/
module

public import LeanPool.MicrowaveNetworks.PhaseShifters
public import LeanPool.MicrowaveNetworks.HybridCouplersPhaseShifters

/-!
# Microwave network synthesis and power-of-two DFT implementation

Source: arxiv:2610.04774, url:https://github.com/matteonerini/formalizing-analog-computing/tree/a89c1e9263658c20a29046f9ed1a8eeb867dd537
Authors: Matteo Nerini, Claude AI
Status: verified
Main declarations: `MiLAC.HybridCouplersPhaseShifters.implementable_dft`
Tags: applied-mathematics, signal-processing, matrix-theory, fourier-transform, network-synthesis
MSC: 94A12, 15A23, 42A38
-/

/-!
# Microwave network synthesis

Adapted from Matteo Nerini's formalizing-analog-computing at commit
`a89c1e9263658c20a29046f9ed1a8eeb867dd537` (Apache-2.0).
The complete proofs were published on 30 September 2026 at 23:58:57 UTC;
the accompanying paper is arXiv:2610.04774, submitted on 3 October 2026.
The upstream credits Matteo Nerini and Claude AI for the Lean development.

The network model is a complex transmission matrix of a reciprocal matched
microwave network; series and parallel composition are matrix multiplication
and block sum. This development proves the phase-only and hybrid-coupler
synthesis characterizations and implementability of the normalized DFT at every
power-of-two size. It preserves finite-type reindexing and block-diagonal
implementability infrastructure. It does not formalize general scattering
physics or the Hadamard and Haar extensions mentioned in the paper.
-/
