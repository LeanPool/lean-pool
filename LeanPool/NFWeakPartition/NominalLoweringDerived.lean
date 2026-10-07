/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalLoweringLemmas

/-! NF weak partition development: NominalLoweringDerived. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal

open NFChoice.SemanticCore

/-! Logical wrappers whose Metamath freshness condition follows directly from
the nominal free-variable computation.  Keeping them separate from the
generic lowering theorem makes the source emitter's primitive table small
and explicit.
-/


/-- Metamath `ax-6`: `x` is not free in `¬ ∀ x, p`. -/
@[expose]
def ax6 (x : Var) (p : Wff) :
    NPrf (.imp (Wff.neg (.all x p)) (.all x (Wff.neg (.all x p)))) :=
  ax17 (Wff.neg (.all x p)) x (by simp [Wff.neg, Wff.fv])


end NFChoice.DirectNominalPrf.Nominal
