/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Invertibility of `2` in quotient rings and localizations

Mathlib provides `Invertible (2 : K)` for division rings of characteristic zero
(`invertibleTwo`, re-exported here so that this file supplies every standard source of the
instance), but nothing for quotients or localizations. The instances here transport an
`Invertible (2 : R)` along the quotient map `R → R ⧸ I`, along the residue map of a local ring
and along the localization map `R → Localization M` (so in particular to `FractionRing R`);
they make a hypothesis `[Invertible (2 : R)]` on a base ring available on its reductions.
The residue field of a local ring is a `def`, not reducibly a quotient, so it needs its own
instance. The general numeral `OfNat.ofNat n` version does not fire in instance search, hence
the numeral `2`, as for Mathlib's `invertibleTwo`.
-/

@[expose] public section

/-- Invertibility of `2` descends to quotient rings. -/
instance Ideal.Quotient.invertibleTwo {R : Type*} [CommRing R] (I : Ideal R) [Invertible (2 : R)] :
    Invertible (2 : R ⧸ I) :=
  (Invertible.map (Ideal.Quotient.mk I) 2).copy _ (map_ofNat _ 2).symm

/-- Invertibility of `2` descends to the residue field of a local ring. -/
noncomputable instance IsLocalRing.ResidueField.invertibleTwo {R : Type*} [CommRing R]
    [IsLocalRing R] [Invertible (2 : R)] : Invertible (2 : IsLocalRing.ResidueField R) :=
  (Invertible.map (IsLocalRing.residue R) 2).copy _ (map_ofNat _ 2).symm

/-- Invertibility of `2` ascends to localizations, in particular to the fraction ring. -/
instance Localization.invertibleTwo {R : Type*} [CommRing R] (M : Submonoid R)
    [Invertible (2 : R)] : Invertible (2 : Localization M) :=
  (Invertible.map (algebraMap R (Localization M)) 2).copy _ (map_ofNat _ 2).symm

end
