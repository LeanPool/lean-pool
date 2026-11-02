/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxence Faldor, Moritz Firsching
-/
module

public import LeanPool.CryptidsGoldbach.Semantics

/-!
# A 21-state Turing machine for Goldbach's conjecture

Source: url:https://github.com/google-deepmind/cryptids/tree/f873434871b2301d5c8c91ba6fa224f92c93c1e1
Authors: Maxence Faldor, Moritz Firsching
Status: verified
Main declarations: `ConjectureMachines.Goldbach21.Semantics.halts_candidate_iff_not_goldbach`
Tags: computability, turing-machines, goldbach-conjecture, machine-simulation
MSC: 03D10, 11P32
-/

/-!
# A 21-state Goldbach Turing machine

Adapted from google-deepmind/cryptids at f873434871b2301d5c8c91ba6fa224f92c93c1e1.
The imported scope is the complete Goldbach proof and its finite-machine infrastructure.
The Riemann, ZF and Busy Beaver developments are outside this project.
-/
