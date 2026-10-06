/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Fin

/-! NF weak partition development: NFStandard.StratificationNormalize. -/


public section

namespace NFChoice.Foundation

namespace Formula

/-! The Hailperin construction first raises every variable to a common type.
For a nonempty finite context, `typeCeiling ty` is the largest assigned
integer type and `typeOffset ty i` is the number of singleton applications
needed to raise variable `i` to that ceiling.
-/


/-- The largest type in a nonempty intrinsic context. -/
@[expose]
def typeCeiling {n : Nat} (ty : Fin (n + 1) → Int) : Int :=
  Finset.univ.sup' (by simp) ty

/-- Every assigned type lies below the chosen ceiling. -/
theorem le_typeCeiling {n : Nat} (ty : Fin (n + 1) → Int) (i : Fin (n + 1)) :
    ty i ≤ typeCeiling ty := by exact Finset.le_sup' ty (Finset.mem_univ i)

/-- Number of singleton raises taking variable `i` to the common ceiling. -/
@[expose]
def typeOffset {n : Nat} (ty : Fin (n + 1) → Int) (i : Fin (n + 1)) : Nat :=
  Int.toNat (typeCeiling ty - ty i)

theorem typeOffset_cast {n : Nat} (ty : Fin (n + 1) → Int) (i : Fin (n + 1)) :
    (typeOffset ty i : Int) = typeCeiling ty - ty i :=
  by
  rw [typeOffset, Int.toNat_of_nonneg]
  exact Int.sub_nonneg_of_le (le_typeCeiling ty i)

/-- Equal-typed variables need the same number of singleton raises. -/
theorem typeOffset_eq_of_eq {n : Nat} {ty : Fin (n + 1) → Int} {i j : Fin (n + 1)}
    (h : ty i = ty j) : typeOffset ty i = typeOffset ty j := by simp [typeOffset, h]

/-- A membership source needs exactly one more raise than its target. -/
theorem typeOffset_mem {n : Nat} {ty : Fin (n + 1) → Int} {i j : Fin (n + 1)}
    (h : ty j = ty i + 1) : typeOffset ty i = typeOffset ty j + 1 :=
  by
  have hi := typeOffset_cast ty i
  have hj := typeOffset_cast ty j
  omega

end Formula

end NFChoice.Foundation
