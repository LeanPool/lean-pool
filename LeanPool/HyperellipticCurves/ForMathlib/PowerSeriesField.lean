/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PowerSeries.Inverse

import Mathlib.Algebra.CharP.Algebra

/-!
# `k⟦X⟧` as a complete discrete valuation ring

The instances that let power series over a field `k` be used through the
`IsAdicComplete (maximalIdeal O) O` interface of the `p`-adic kit: adic completeness at the
maximal ideal, `CharZero` for `k⟦X⟧` (its fraction field then has it by Mathlib's
`IsFractionRing.charZero`), algebraic closedness of the residue field, and `NeZero 2` there.
Mathlib has the discrete valuation ring structure but none of these.
-/

@[expose] public section

open IsLocalRing

namespace PowerSeries

variable {k : Type*} [Field k]

/-- `k⟦X⟧` is complete for its maximal ideal `(X)`. -/
instance instIsAdicCompleteMaximalIdeal : IsAdicComplete (maximalIdeal k⟦X⟧) k⟦X⟧ := by
  rw [PowerSeries.maximalIdeal_eq_span_X]
  infer_instance

/-- The residue field of `k⟦X⟧` is `k`, so it inherits algebraic closedness. -/
instance instIsAlgClosedResidueField [IsAlgClosed k] : IsAlgClosed (ResidueField k⟦X⟧) :=
  IsAlgClosed.of_ringEquiv k _ (residueFieldOfPowerSeries (k := k)).symm

/-- Characteristic zero passes to `k⟦X⟧` along the constant coefficient. -/
instance instCharZero [CharZero k] : CharZero k⟦X⟧ :=
  (constantCoeff : k⟦X⟧ →+* k).charZero

/-- `2 ≠ 0` in the residue field of `k⟦X⟧`, which the hyperelliptic charts need. -/
instance instNeZeroTwoResidueField [CharZero k] : NeZero (2 : ResidueField k⟦X⟧) :=
  ⟨fun h ↦ two_ne_zero (α := k) <| by
    have := congrArg (residueFieldOfPowerSeries (k := k)) h
    rwa [map_ofNat, map_zero] at this⟩

end PowerSeries

end
