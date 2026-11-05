/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Splitness

/-!
# Reduced composition algebras (`GPR 22.6–22.7`)

`GPR 22.6` defines a composition algebra to be **reduced** when it contains an absolutely
primitive idempotent. `GPR 22.7` supplies the characterization used throughout the structure
theory: in rank greater than one, reducedness is equivalent to the existence of an elementary
idempotent, while every rank-one composition algebra is reduced.

This file uses that equivalent characterization together with the rank decomposition of
`GPR Exc. 9.31`. Thus a composition algebra is reduced when its rank `2`, `4`, and `8` components
have elementary idempotents; the rank-one component needs no condition.

## Main definitions

* `ConicAlgebra.IsReduced` : reducedness, expressed on the four rank components.

## Main results

* `ConicAlgebra.IsReduced.isComposition` : reducedness includes the composition property.
* `ConicAlgebra.IsSplit.isReduced` : **`GPR 22.16`, split implies reduced**, over every
  commutative ring.

## Implementation notes

⚠ **Equivalent characterization rather than absolute primitivity.** Absolute primitivity in
`GPR 22.1` quantifies over all field extensions and decompositions into orthogonal idempotents.
Nothing downstream uses that data: every application passes immediately through `GPR 22.7` to
elementary idempotents. Accordingly `IsReduced` records the rankwise elementary-idempotent
condition equivalent to `GPR 22.6`, rather than introducing an unused absolute-primitivity API.
The distinction at rank one is preserved explicitly: rank one is reduced but generally has no
elementary idempotent.

Zero rank factors cause no exception. Their base rings are zero rings, where `0` is elementary
because `0 = 1`; retaining all three factors therefore matches the convention in `GPR 21.19`.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Exc. 9.31,
  21.19, 22.1, 22.6, 22.7, 22.16.
-/

@[expose] public section

universe u v

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]

/-- **Reducedness (`GPR 22.6–22.7`) through the rank decomposition.** A conic algebra is reduced
when it is a composition algebra and each of its rank `2`, `4`, and `8` components has an
elementary idempotent. The rank-one component is automatically reduced and deliberately carries
no elementary-idempotent condition. -/
def IsReduced (C : ConicAlgebra k A) : Prop :=
  C.IsComposition.{u, v, u} ∧
    (C.splitRankComponent 2).HasElementaryIdempotent ∧
    (C.splitRankComponent 4).HasElementaryIdempotent ∧
    (C.splitRankComponent 8).HasElementaryIdempotent

namespace IsReduced

variable {C : ConicAlgebra k A}

/-- A reduced conic algebra is a composition algebra, by definition. -/
theorem isComposition (h : C.IsReduced) : C.IsComposition.{u, v, u} :=
  h.1

/-- The rank-two component of a reduced composition algebra has an elementary idempotent. -/
theorem hasElementaryIdempotent_splitRankComponent_two (h : C.IsReduced) :
    (C.splitRankComponent 2).HasElementaryIdempotent :=
  h.2.1

/-- The rank-four component of a reduced composition algebra has an elementary idempotent. -/
theorem hasElementaryIdempotent_splitRankComponent_four (h : C.IsReduced) :
    (C.splitRankComponent 4).HasElementaryIdempotent :=
  h.2.2.1

/-- The rank-eight component of a reduced composition algebra has an elementary idempotent. -/
theorem hasElementaryIdempotent_splitRankComponent_eight (h : C.IsReduced) :
    (C.splitRankComponent 8).HasElementaryIdempotent :=
  h.2.2.2

end IsReduced

/-- **`GPR 22.16`, split ⇒ reduced.** Every split composition algebra over an arbitrary
commutative ring is reduced.

On each rank greater than one, the defining isomorphism with the standard split model transports
its visible elementary idempotent back to the corresponding rank component. Rank one is reduced
without an elementary-idempotent condition. -/
theorem IsSplit.isReduced {C : ConicAlgebra k A} (h : C.IsSplit) : C.IsReduced := by
  rcases h with ⟨hcomp, -, htwo, hfour, height⟩
  exact ⟨hcomp,
    htwo.hasElementaryIdempotent_of_two_or_four_or_eight (Or.inl rfl),
    hfour.hasElementaryIdempotent_of_two_or_four_or_eight (Or.inr (Or.inl rfl)),
    height.hasElementaryIdempotent_of_two_or_four_or_eight (Or.inr (Or.inr rfl))⟩

end ConicAlgebra
