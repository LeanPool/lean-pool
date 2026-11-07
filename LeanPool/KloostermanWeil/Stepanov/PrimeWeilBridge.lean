/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Stepanov.PrimeWeil
public import LeanPool.KloostermanWeil.Weil.PrimeFoundation


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Prime-bound normalization

Transfers the proved prime estimate to the coefficient convention of Harcos (2015),
equation (1), and Weil’s classical statement.
-/

@[expose] public section

namespace KloostermanWeil.Stepanov

open KloostermanWeil

/-- Prime nondegenerate Weil bound proved using the Stepanov–Carlitz route. -/
theorem primeNondegenerateWeil_proved :
    PrimeNondegenerateWeil :=
  (primeNondegenerateWeil_iff_oneParameter).2
    oneParameterPrimeWeil_proved

/-- The classical Weil statement follows from the normalization equivalence. -/
theorem weil1948PrimeKloostermanBound_proved :
    Weil1948PrimeKloostermanBound :=
  (primeNondegenerateWeil_iff_weil1948).1
    primeNondegenerateWeil_proved


end KloostermanWeil.Stepanov
