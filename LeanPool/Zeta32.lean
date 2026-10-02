/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Results


/-!
# Linear independence of 1, zeta(2), and zeta(3)

Source: url:https://github.com/dtq1997/zeta2-zeta3-linear-independence/tree/669c92bf7a3728e0de9ad80c373bc29fb5ca3d58
Authors: Qian Tang
Status: verified
Main declarations: `Zeta32.one_zeta_two_zeta_three_linearIndependent`
Tags: zeta-values, irrationality, linear-independence, p-adic-valuations, potential-theory
MSC: 11J72, 11M06
-/


/-!
# Linear independence of 1, zeta(2), and zeta(3)

Imported from https://github.com/dtq1997/zeta2-zeta3-linear-independence at
commit 669c92bf7a3728e0de9ad80c373bc29fb5ca3d58. The first public proof release was
2026-09-30 03:47:38 UTC (commit ec4fcb5617126b0a861f9e0c16f95425b32d4638).
The proof was produced with AI systems under Qian Tang's direction.
The mathematical argument adapts Fauzan's polynomial method; novelty as an
informal mathematical result has not been independently established.

The import reuses the existing prime number theorem in `LeanPool.MooreBound`.
The upstream notice below lists original upstream paths, including the replaced PNT copy.
All listed source licenses are Apache-2.0 and remain available in the pinned upstream tree.

## Preserved upstream attribution notice

This repository contains a Lean 4 proof that 1, ζ(2) and ζ(3) are linearly independent over ℚ.

The Lean code was written with substantial assistance from AI systems (Anthropic Claude, OpenAI
Codex).

It includes code adapted from the following Apache-2.0 projects. Each adapted file names its
source in a comment.

Irrationality of Li₂(1/2), by Qian Tang
  https://github.com/dtq1997/li2-half-irrationality, commit d5d8206427e58833d85ca6dc349fec0bd53d5108
  (which itself adapts code from the projects below; see its NOTICE)
  Zeta32/Analytic/Contour/Andreief.lean
  Zeta32/Analytic/Contour/AndreiefIntegrable.lean
  Zeta32/Analytic/Contour/Kernel.lean
  Zeta32/Analytic/Contour/PartialFractions.lean
  Zeta32/Analytic/Contour/RectangleResidue.lean
  Zeta32/Analytic/Contour/Shift.lean
  Zeta32/Analytic/Energy/Assembly.lean
  Zeta32/Analytic/Energy/CircleTools.lean
  Zeta32/Analytic/Energy/LogNorm.lean
  Zeta32/Analytic/Energy/Pointwise.lean
  Zeta32/Analytic/Energy/Stirling.lean
  Zeta32/Analytic/Energy/ZeroMass.lean
  Zeta32/Arith/Local/Val.lean
  Zeta32/Arith/Local/ValExtra.lean
  Zeta32/Arith/Node.lean
  Zeta32/Arith/Outer/Classes.lean
  Zeta32/Arith/Outer/Entries.lean
  Zeta32/Arith/Outer/Norm.lean
  Zeta32/Arith/Outer/RankOne.lean
  Zeta32/Arith/Outer/Raw.lean
  Zeta32/Arith/Relaxed.lean
  Zeta32/Arith/Small/Binom.lean
  Zeta32/Arith/Small/Entry.lean
  Zeta32/Arith/Small/Gram.lean
  Zeta32/Arith/Sum/PNT/DecayPNTConsequences.lean
  Zeta32/Arith/Sum/PNT/DecayPNTFourier.lean
  Zeta32/Arith/Sum/PNT/DecayPNTInterface.lean
  Zeta32/Arith/Sum/PNT/DecayPNTSmooth.lean
  Zeta32/Arith/Sum/PNT/DecayPNTSobolev.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener1.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener2a.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener2b.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener3.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener4a.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener4b.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener5a.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener5b.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener6a.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener6b.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener6c.lean
  Zeta32/Arith/Sum/PNT/PrimeThetaInterval.lean
  Zeta32/Arith/Sum/PNT/PrimeWeightedAbel.lean
  Zeta32/Arith/Sum/Windows.lean
  Zeta32/PrimeEdge/Auxiliary/ClassBasis.lean
  Zeta32/PrimeEdge/Gram.lean
  Zeta32/PrimeEdge/Valuation.lean

mo271/Zeta5 (irrationality of ζ(5)), by Moritz Firsching
  https://github.com/mo271/Zeta5, commit f19a1960609f7d38e7b63fd2acb05e6f60a7b741
  Licence: licenses/LICENSE-Zeta5.txt
  Zeta32/Analytic/Contour/Andreief.lean
  Zeta32/Analytic/Contour/PartialFractions.lean
  Zeta32/Analytic/Energy/CircleTools.lean
  Zeta32/Analytic/Energy/ZeroMass.lean
  Zeta32/Arith/Local/Binom.lean
  Zeta32/Arith/Local/Entry.lean
  Zeta32/Arith/Local/PoleFun.lean
  Zeta32/Arith/Local/Val.lean
  Zeta32/Arith/Small/Gram.lean
  Zeta32/Arith/Sum/Main.lean
  Zeta32/Arith/Sum/Windows.lean
  Zeta32/Criterion.lean
  Zeta32/PrimeEdge/Auxiliary/ClassBasis.lean
  Zeta32/PrimeObstruction.lean

Prime Number Theorem and More, organised by Alex Kontorovich and Terence Tao
  https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, commit
  d7f9e2bfdcc7e34dfb9328b7494a6d424ff50c96
  (via the Li₂(1/2) repository)
  Licence: licenses/LICENSE-PNT.txt
  Zeta32/Arith/Sum/PNT/DecayPNTConsequences.lean
  Zeta32/Arith/Sum/PNT/DecayPNTFourier.lean
  Zeta32/Arith/Sum/PNT/DecayPNTInterface.lean
  Zeta32/Arith/Sum/PNT/DecayPNTSmooth.lean
  Zeta32/Arith/Sum/PNT/DecayPNTSobolev.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener1.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener2a.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener2b.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener3.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener4a.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener4b.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener5a.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener5b.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener6a.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener6b.lean
  Zeta32/Arith/Sum/PNT/DecayPNTWiener6c.lean
  Zeta32/Arith/Sum/PNT/PrimeThetaInterval.lean
  Zeta32/Arith/Sum/PNT/PrimeWeightedAbel.lean

Mathlib (https://github.com/leanprover-community/mathlib4)
  Mathlib/Analysis/Real/Pi/Irrational.lean (Bhavik Mehta), adapted to prove the irrationality of π²;
  the rectangular-contour residue development of Mathlib draft pull request #39232 (Jeremy Tan),
  commit cad38f70f5a649a40dbb3b334055a8e9aff69af5, via the Li₂(1/2) repository.
  Licence: licenses/LICENSE-Mathlib.txt
  Zeta32/Analytic/Contour/RectangleResidue.lean
  Zeta32/PiSqIrrational.lean

-/
