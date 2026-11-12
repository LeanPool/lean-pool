/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.IntegerSuperharmonicCharacterization
public import LeanPool.ApollonianSuperharmonic.BandOdometerTheorem
public import LeanPool.ApollonianSuperharmonic.IntegralityTiling
public import LeanPool.ApollonianSuperharmonic.LambdaTiling
public import LeanPool.ApollonianSuperharmonic.BandLatticeEquality

/-!
# Apollonian classification of integer superharmonic matrices

Source: arxiv:1309.3267, url:https://github.com/wpegden/superharmonic
Authors: Wesley Pegden
Status: verified
Main declarations: `ApollonianSuperharmonic.IntegerSuperharmonicCharacterization`,
  `ApollonianSuperharmonic.BandOdometerTheorem`, `ApollonianSuperharmonic.IntegralityTiling`,
  `ApollonianSuperharmonic.LambdaTiling`, `ApollonianSuperharmonic.BandLatticeEquality`
Tags: apollonian-packings, superharmonic-functions, discrete-potential-theory, lattice-tilings
MSC: 31C20, 52C15, 60G50
-/

/-!
## Upstream formalization

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization at commit
`45094b210503f117502dec51caf737e96da221f8`. The mathematical source is Levine,
Pegden and Smart, *The Apollonian structure of integer superharmonic matrices*.
Trellis produced the Lean proofs using AI agents; the project records `AI` provenance.

The imported scope is the dependency closure of the five public root theorems.
The upstream paper, process tooling and development history are not imported.
The upstream reference notes explain two local repairs to the printed proof:
edge-supported interfaces with isolated corners, and occurrence-oriented unit strings.
-/
