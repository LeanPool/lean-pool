/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Stepanov.PrimeWeilBridge


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# The public prime estimate

Exports Weil’s classical bound and the equivalent coefficient ordering used in Harcos
(2015), Theorem 1.
-/

@[expose] public section

namespace KloostermanWeil

/-- Prime nondegenerate Kloosterman–Weil bound via the Stepanov–Carlitz development. -/
theorem prime_bound : PrimeNondegenerateWeil :=
  KloostermanWeil.Stepanov.primeNondegenerateWeil_proved

/-- Conventional Weil (1948) coefficient order and normalization. -/
theorem weil1948_bound : Weil1948PrimeKloostermanBound :=
  primeNondegenerateWeil_iff_weil1948.mp prime_bound

end KloostermanWeil
