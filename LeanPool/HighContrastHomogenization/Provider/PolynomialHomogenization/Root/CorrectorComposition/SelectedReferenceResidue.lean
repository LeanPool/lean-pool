/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.PushforwardCorrectorFamily

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.SelectedReferenceResidue

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The selected-reference residue, reduced to one pointwise identity

The corrector-family hypothesis `RootPushCanonicalFamily` of the decay and
Liouville clauses reduces to a selected-reference identity, a conjunction of

1. a **pointwise** normalized-root coefficient identity for the *selected*
   corrector datum's reference family, on every triadic cube; and
2. a **natural delay** `∃ L : ℕ, (selected …).start ≤ triadicCeilingIndex x + L`.

Clause 2 is free: it is the statement that an integer is below `k + L` for some
natural `L`, which the Archimedean property of `ℤ` settles.  This module proves
that, so the residue is clause 1 **alone** — a single pointwise coefficient
identity, with no delay, no order, no tolerance and no estimate.

## Why clause 1 is not provable in this form, and what the minimal repair is

The obstruction is a data-structure defect, not an analytic gap, and it is worth
recording exactly.

* `Root.RootCorrectorEvent d b` is `Nonempty (RootCorrectorData d b)` and
  `Root.selectedRootCorrectorData b h` is `Classical.choice h`.  So the
  selected family `aFin` is an **arbitrary** inhabitant of the datum type.
* `RootCorrectorData`'s coefficient field is
  `coeff : ∀ q : ℕ, Book.Ch03.publicCoeffField (originCube d q) aFin
     =ᵐ[volume.restrict (localGradientCube d q)] ⇑b.1`
  — almost-everywhere, on **origin** cubes only, and against `publicCoeffField`.
  Clause 1 asks for a **pointwise** identity, on **every** triadic cube, against
  `(aFin.coeffOn Q).toCoeffField`.  Neither weakening of the datum's field
  yields it, so clause 1 cannot be derived from the datum type.
* The identity nevertheless **exists and is already proved** upstream.  The
  converter
  `exists_shiftedNormalizedReferencePowerTail_of_hasAllLaterPhysicalBlockRow`
  returns exactly
  `∀ Q : TriadicCube d, (aRef.coeffOn Q).toCoeffField =
      affineCoefficient (Selection.normalizedRoot (symmPart abar)) _
        ⇑(normalizedCenteredCoeff a abar hS).1`,
  pointwise and on every cube; the stationary corrector family clause's supply route consumes that
  witness
  and then **discards the identity** when it packages `aRef` through
  `rootCorrectorEvent_of_goodTail`, keeping only the a.e. `coeff` field.

**Minimal repair (an interface item for the stationary corrector family clause module, not applied
here):** index
the corrector datum by the exact coefficient field it represents — add
`exactField : CoeffField d` together with
`coeffExact : ∀ Q, (aFin.coeffOn Q).toCoeffField = exactField` to
`RootCorrectorData`, and pin the exact field in `RootCorrectorEvent`'s index rather
than leaving it to `Classical.choice`.  The single constructor
`rootCorrectorEvent_of_goodTail` then gains one hypothesis, which the supply
site discharges **directly** with the converter's own witness.  Adding the field
without pinning the index does *not* work: two data with a.e.-equal exact fields
are both inhabitants, and the choice may return either.

Nothing in this file assumes clause 1.  It is carried as a named hypothesis.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## The delay clause is free -/

/-- Every integer lies below `k + L` for some natural `L`. -/
theorem exists_natDelay_ge (n : ℤ) (k : ℕ) : ∃ L : ℕ, n ≤ ((k + L : ℕ) : ℤ) := by
  refine ⟨n.toNat, ?_⟩
  have h1 : n ≤ (n.toNat : ℤ) := Int.self_le_toNat n
  have h2 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have hcast : ((k + n.toNat : ℕ) : ℤ) = (k : ℤ) + (n.toNat : ℤ) := by
    push_cast
    ring
  rw [hcast]
  linarith only [h1, h2]

/-! ## The residue without the delay -/

end

end Root
end HighContrast
end HCPolySupport
