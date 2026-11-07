/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/



module

public import LeanPool.KloostermanWeil.Weil
public import LeanPool.KloostermanWeil.Weil.Contracts

/-!
# Kloosterman–Weil bounds via Carlitz and Stepanov

Source: url:https://github.com/charliedorsey/weil-bounds-toolkit/tree/7adcd23667b063ae54cc0e8707c89ce259e8fd31
Authors: Charlie Dorsey
Status: verified
Main declarations: `KloostermanWeil.weil1948_bound`, `KloostermanWeil.kloostermanUnitSum_crt`,
  `KloostermanWeil.centeredReducedIntervalSum_bound`
Tags: analytic-number-theory, exponential-sums, finite-fields
MSC: 11L05, 11T23
-/

@[expose] public section

