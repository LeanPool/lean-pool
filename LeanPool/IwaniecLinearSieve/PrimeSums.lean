/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.PrimeSums.Error
public import LeanPool.IwaniecLinearSieve.PrimeSums.Mertens
public import LeanPool.IwaniecLinearSieve.PrimeSums.Product
public import LeanPool.IwaniecLinearSieve.PrimeSums.SummationByParts
public import LeanPool.IwaniecLinearSieve.PrimeSums.Lemma13
public import LeanPool.IwaniecLinearSieve.PrimeSums.NthPrime

/-!
# Prime sums with de la Vallée Poussin error terms, from `StrongPNT`

* `IwaniecLinearSieve.PrimeSums.Error`: the error term `pntE x = exp (-pntκ √(log x))` and
  `theta_asymp : |θ x - x| ≤ C x pntE x` for `x ≥ 2`.
* `IwaniecLinearSieve.PrimeSums.Mertens`: `S x = ∑_{p ≤ x} 1/p` and `S_asymp`.
* `IwaniecLinearSieve.PrimeSums.Product`: `R_asymp`, `R_lower`, `R_upper`.
* `IwaniecLinearSieve.PrimeSums.SummationByParts`: an abstract summation by parts bound.
* `IwaniecLinearSieve.PrimeSums.Lemma13`: [I71, Lemma 13] (`lemma13_mono`, `lemma13_anti`) and
  [I71, Lemma 14] (`lemma14`).
* `IwaniecLinearSieve.PrimeSums.NthPrime`: `nth_prime_le`.
-/

@[expose] public section
