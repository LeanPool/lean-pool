/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxence Faldor, Moritz Firsching
-/
module

public import LeanPool.CryptidsGoldbach.Semantics
public import LeanPool.CryptidsGoldbach.BrocardSemantics

/-!
# Finite-state Turing machines for Goldbach and Brocard

Source: url:https://github.com/google-deepmind/cryptids/tree/481f4e3e39907304dbcad33e508bf21d80c6d5a6
Authors: Maxence Faldor, Moritz Firsching, Daniel Veljjanoski
Status: verified
Main declarations: `ConjectureMachines.Goldbach21.Semantics.halts_candidate_iff_not_goldbach`,
  `ConjectureMachines.Brocard28.halts_brocard28_iff_exists_square`
Tags: computability, turing-machines, goldbach-conjecture, machine-simulation, brocard-problem
MSC: 03D10, 11P32
-/

/-!
# Goldbach and Brocard Turing machines

Adapted from google-deepmind/cryptids at f873434871b2301d5c8c91ba6fa224f92c93c1e1.
The 21-state machine uses the Goldbach proof and its finite-machine infrastructure.
The 28-state Brocard machine and its halting equivalence come from the same upstream repository
at 481f4e3e39907304dbcad33e508bf21d80c6d5a6.
-/
