/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.RingTheory.Artinian.Algebra

/-!
# Inverses of integral units in subalgebras over an Artinian ring

Over an Artinian ring `R`, an `R`-subalgebra `B` of `A` contains the inverse of every unit of `A`
which lies in `B` and is integral over `R`.

## Main statements

* `IsArtinianRing.inv_mem_of_isIntegral`.
-/

public section

namespace IsArtinianRing

variable {R A : Type*} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]

open nonZeroDivisors

private theorem isUnit_of_isIntegral_of_isUnit_subalgebra {B : Subalgebra R A} {a : B}
    (hi : IsIntegral R (a : A)) (ha : IsUnit (a : A)) : IsUnit a :=
  isUnit_of_isIntegral_of_nonZeroDivisor
    ((isIntegral_algHom_iff B.val Subtype.val_injective).mp hi)
    (comap_nonZeroDivisors_le_of_injective (f := B.val) Subtype.val_injective
      ha.mem_nonZeroDivisors)

/-- Over an Artinian ring `R`, an `R`-subalgebra `B` of `A` contains the inverse of every unit
of `A` which lies in `B` and is integral over `R`. For instance, when `R = K` is a field, a
`K`-subalgebra of `Module.End K V` with `V` finite-dimensional is closed under taking inverses. -/
theorem inv_mem_of_isIntegral {B : Subalgebra R A} {u : Aˣ} (hi : IsIntegral R (u : A))
    (hu : (u : A) ∈ B) : ((u⁻¹ : Aˣ) : A) ∈ B := by
  obtain ⟨v, hv⟩ := isUnit_of_isIntegral_of_isUnit_subalgebra (a := (⟨u, hu⟩ : B)) hi u.isUnit
  rw [← (Units.ext (congrArg Subtype.val hv) : Units.map (B.val : B →* A) v = u)]
  exact (↑v⁻¹ : B).2

end IsArtinianRing
