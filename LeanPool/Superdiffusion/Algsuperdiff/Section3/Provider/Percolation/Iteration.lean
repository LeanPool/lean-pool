/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.ClusterEvent
public import Mathlib.Order.Lattice.Nat

/-!
# Iteration

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Tuple bookkeeping for the scale-iteration inequality

ABK26's inequality `e.paths.ready.for.iteration` reads

`P[𝒞_{k+h}(z)] ≤ (W · sup_z P[𝒞_k(z)]) ^ M  +  W · h · sup {P[B_l(z)] : k < l ≤ k+h}`,

where `M = 3 ^ (h - 3)` is the number of well-separated sites extracted from a
long path (ABK26 uses `3 ^ (h - 4)`; the shell selection of
`SeparatedSelection.lean` gives the slightly better `3 ^ (h - 3)`) and
`W = 3 ^ (d (k + h + 1))` bounds the number of lattice sites the truncated path
can visit (ABK26 uses `3 ^ (d (k+h))` for the open cube; the truncated path can
also touch the sites just outside it, whence the extra factor `3 ^ d`).

The extraction step behind that inequality produces its well-separated sites as
a tuple indexed by `Fin M`, whereas the cluster and bad-event families are
indexed by `ℕ`.  This module supplies the piece of bookkeeping that reconciles
the two indexings.

## Main definitions

* `tupleFun`: the extension of a tuple of sites indexed by `Fin M` to a family
  indexed by `ℕ`, taking the value `0` beyond `M`.

## Main results

* `tupleFun_apply`: the extension agrees with the tuple at every index below
  `M`.

## References

* ABK26, proof of `l.percolation.bound.general`, Step 3.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open MeasureTheory ProbabilityTheory

variable {d : ℕ} {Ω : Type*}

/-- Extend a tuple of sites indexed by `Fin M` to a function on `ℕ`. -/
def tupleFun {M : ℕ} (y : Fin M → (Fin d → ℤ)) : ℕ → (Fin d → ℤ) :=
  fun m => if h : m < M then y ⟨m, h⟩ else 0

theorem tupleFun_apply {M : ℕ} (y : Fin M → (Fin d → ℤ)) {m : ℕ} (hm : m < M) :
    tupleFun y m = y ⟨m, hm⟩ := dite_eq_left hm


end Algsuperdiff.Section3.Provider.Percolation
