/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.HypRing
public import LeanPool.HyperellipticCurves.ForMathlib.Invertible
public import LeanPool.HyperellipticCurves.ForMathlib.Resultant
public import Mathlib.FieldTheory.Perfect

/-!
# Hyperelliptic curves `y² = f(x)`

`HyperellipticCurve R` is the type of hyperelliptic curves over a commutative ring `R` in which
`2` is invertible: a genus `g` and a polynomial `f : R[X]` of degree at most `2g + 2` whose
discriminant as a polynomial of degree `2g + 2` (`Polynomial.discrOfDegree`, the discriminant of
the binary form `Z^(2g+2) f(X/Z)`) is a unit. This is the condition for the model `y² = f(x)`,
including its points at infinity, to be smooth over `R`. Over a nontrivial ring the degree of `f`
is then `2g + 1` or `2g + 2`, and in the odd case the leading coefficient is a unit.

## Main definitions

* `HyperellipticCurve`: the structure, with the genus `HyperellipticCurve.genus`, the polynomial
  `HyperellipticCurve.f`, the degree bound `HyperellipticCurve.natDegree_le` and the unit
  discriminant `HyperellipticCurve.isUnit_discr`.
* `HyperellipticCurve.IsOdd`: the class of curves whose model is monic of odd degree `2g + 1`.
* `HyperellipticCurve.map`, `HyperellipticCurve.baseChange`: base change along any ring
  homomorphism, resp. to any algebra, without hypotheses.
* `HyperellipticCurve.ofSeparable`, `HyperellipticCurve.ofSquarefree`: the curve of a nonconstant
  separable polynomial with unit leading coefficient, and of a nonconstant squarefree polynomial
  over a perfect field.

## Implementation notes

The invertibility of `2` is an instance parameter of the type, `[Invertible (2 : R)]`: a
structure field cannot serve as an instance (its head would not mention the curve), whereas the
parameter is found by instance search wherever a curve is in scope, and `Invertible.toNeZero`
turns it into `NeZero (2 : R)` over a nontrivial ring. Invertibility descends to quotients and
residue fields by the instances of `LeanPool.HyperellipticCurves.ForMathlib.Invertible`.

The genus is part of the data. The discriminant condition at the fixed degree `2g + 2` is a
polynomial in the coefficients of `f` and commutes with every ring homomorphism, which is what
makes `HyperellipticCurve.map` hypothesis-free; the smallest even degree `≥ deg f` is recovered as
a theorem (`HyperellipticCurve.natDegree_eq_or_eq`), and so is the nonconstancy of `f`
(`HyperellipticCurve.natDegree_pos`).

Unlike Mathlib's `WeierstrassCurve`, where nonsingularity is the separate class
`WeierstrassCurve.IsElliptic`, the unit discriminant is a field of the structure, so every
`HyperellipticCurve` is nonsingular and no further hypothesis is needed for the coordinate-ring
instances. The instances `Fact (Odd C.f.natDegree)` (for `[C.IsOdd]`) and `Fact (Squarefree C.f)`
(over a field) connect the curve to the development indexed by the polynomial: every declaration
guarded by these `Fact`s, such as the domain and Dedekind-domain instances of
`ChabautyColeman.HypRing`, applies to `C.f`.
-/

@[expose] public section

open Polynomial

/-- A hyperelliptic curve `y² = f(x)` of genus `g` over a commutative ring `R` in which `2` is
invertible: a polynomial `f` of degree at most `2g + 2` whose discriminant as a polynomial of
degree `2g + 2` — the discriminant of the binary form `Z^(2g+2) f(X/Z)` — is a unit. -/
@[ext]
structure HyperellipticCurve (R : Type*) [CommRing R] [Invertible (2 : R)] where
  /-- The genus. -/
  genus : ℕ
  /-- The polynomial `f` of the model `y² = f(x)`. -/
  f : R[X]
  /-- The degree of `f` is at most `2g + 2`. -/
  natDegree_le : f.natDegree ≤ 2 * genus + 2
  /-- The discriminant of `f` as a polynomial of degree `2g + 2` is a unit. -/
  isUnit_discr : IsUnit (f.discrOfDegree (2 * genus + 2))

namespace HyperellipticCurve

variable {R : Type*} [CommRing R] [Invertible (2 : R)] (C : HyperellipticCurve R)

attribute [grind! .] natDegree_le isUnit_discr

/-- The curve `y² = x` of genus `0`. -/
noncomputable instance instInhabited : Inhabited (HyperellipticCurve R) :=
  ⟨⟨0, X, natDegree_X_le.trans one_le_two, by simp [discrOfDegree_add_two natDegree_X_le]⟩⟩

@[grind! .]
theorem two_mul_genus_add_one_le [Nontrivial R] : 2 * C.genus + 1 ≤ C.f.natDegree := by
  grind [→ le_natDegree_add_one_of_isUnit_discrOfDegree]

/-- Over a nontrivial ring, the model of a curve of genus `g` has degree `2g + 1` or `2g + 2`. -/
theorem natDegree_eq_or_eq [Nontrivial R] :
    C.f.natDegree = 2 * C.genus + 1 ∨ C.f.natDegree = 2 * C.genus + 2 := by
  grind

theorem natDegree_pos [Nontrivial R] : 0 < C.f.natDegree := by
  grind

theorem f_ne_zero [Nontrivial R] : C.f ≠ 0 := ne_zero_of_natDegree_gt C.natDegree_pos

theorem genus_eq [Nontrivial R] : C.genus = (C.f.natDegree - 1) / 2 := by
  grind

theorem isUnit_discr_f : IsUnit C.f.discr :=
  isUnit_discr_of_isUnit_discrOfDegree C.natDegree_le C.isUnit_discr

/-- The polynomial of a hyperelliptic curve is separable as soon as its leading coefficient is a
unit. -/
theorem separable (hlc : IsUnit C.f.leadingCoeff) : C.f.Separable :=
  (isUnit_discr_iff_separable hlc).mp C.isUnit_discr_f

theorem separable_of_monic (hf : C.f.Monic) : C.f.Separable :=
  hf.isUnit_discr_iff.mp C.isUnit_discr_f

/-- A model of odd degree `2g + 1` has unit leading coefficient. -/
theorem isUnit_leadingCoeff_of_natDegree_eq (h : C.f.natDegree = 2 * C.genus + 1) :
    IsUnit C.f.leadingCoeff :=
  isUnit_leadingCoeff_of_isUnit_discrOfDegree (by lia) (by rw [h]; exact C.isUnit_discr)

/-- The curve `y² = f(x)` of a nonconstant separable polynomial `f` with unit leading
coefficient; its genus is `⌊(deg f - 1) / 2⌋`. -/
@[simps]
def ofSeparable {f : R[X]} (hd : 0 < f.natDegree) (hlc : IsUnit f.leadingCoeff)
    (hsep : f.Separable) : HyperellipticCurve R where
  genus := (f.natDegree - 1) / 2
  f := f
  natDegree_le := by lia
  isUnit_discr := (isUnit_discrOfDegree_iff_isUnit_discr (by lia) (by lia) hlc).mpr
    ((isUnit_discr_iff_separable hlc).mpr hsep)

/-- The curve `y² = f(x)` of a monic separable polynomial `f` of odd degree `2g + 1`, of genus
`g = deg f / 2`; it is an odd-degree model (`HyperellipticCurve.instIsOddOfMonicOdd`). -/
def ofMonicOdd {f : R[X]} (hf : f.Monic) (hodd : Odd f.natDegree) (hsep : f.Separable) :
    HyperellipticCurve R where
  genus := f.natDegree / 2
  f := f
  natDegree_le := by lia
  isUnit_discr := by
    obtain ⟨g, hg⟩ := hodd
    exact (isUnit_discrOfDegree_iff_isUnit_discr (by lia) (by lia)
      (hf.leadingCoeff ▸ isUnit_one)).mpr (hf.isUnit_discr_iff.mpr hsep)

@[simp]
theorem ofMonicOdd_f {f : R[X]} (hf : f.Monic) (hodd : Odd f.natDegree) (hsep : f.Separable) :
    (ofMonicOdd hf hodd hsep).f = f := rfl

@[simp]
theorem ofMonicOdd_genus {f : R[X]} (hf : f.Monic) (hodd : Odd f.natDegree) (hsep : f.Separable) :
    (ofMonicOdd hf hodd hsep).genus = f.natDegree / 2 := rfl

/-! ### Odd-degree models -/

/-- The model `y² = f(x)` of the curve is monic of odd degree `2g + 1`; the curve then has exactly
one point at infinity. This is the setting of the Chabauty–Coleman development. In odd degree the
leading coefficient is automatically a unit (`isUnit_leadingCoeff_of_natDegree_eq`), so monicity
is a normalization. -/
class IsOdd : Prop where
  natDegree_f : C.f.natDegree = 2 * C.genus + 1
  monic_f : C.f.Monic

theorem natDegree_f [C.IsOdd] : C.f.natDegree = 2 * C.genus + 1 := IsOdd.natDegree_f

theorem monic_f [C.IsOdd] : C.f.Monic := IsOdd.monic_f

theorem odd_natDegree_f [C.IsOdd] : Odd C.f.natDegree := ⟨C.genus, C.natDegree_f⟩

/-- Every declaration assuming `Fact (Odd f.natDegree)` applies to the polynomial of a curve
of odd degree. -/
instance instFactOddNatDegreeF [C.IsOdd] : Fact (Odd C.f.natDegree) := ⟨C.odd_natDegree_f⟩

instance instIsOddOfMonicOdd {f : R[X]} (hf : f.Monic) (hodd : Odd f.natDegree)
    (hsep : f.Separable) : (ofMonicOdd hf hodd hsep).IsOdd where
  natDegree_f := by
    change f.natDegree = 2 * (f.natDegree / 2) + 1
    obtain ⟨g, hg⟩ := hodd
    lia
  monic_f := hf

/-! ### Base change -/

section map

variable {S : Type*} [CommRing S] [Invertible (2 : S)] (φ : R →+* S)

/-- The curve mapped along a ring homomorphism `φ`: the genus is preserved and the degree of `f`
can only drop, while the discriminant at degree `2g + 2` maps to that of the image
(`Polynomial.discrOfDegree_map`), so no hypothesis on `φ` is needed. -/
@[simps]
noncomputable def map : HyperellipticCurve S where
  genus := C.genus
  f := C.f.map φ
  natDegree_le := natDegree_map_le.trans C.natDegree_le
  isUnit_discr := by rw [discrOfDegree_map]; exact C.isUnit_discr.map φ

instance instIsOddMap [C.IsOdd] [Nontrivial S] : (C.map φ).IsOdd where
  natDegree_f := by rw [map_f, C.monic_f.natDegree_map, C.natDegree_f, map_genus]
  monic_f := C.monic_f.map φ

/-- The oddness `Fact` for the image of the polynomial of an odd-degree curve, in the spelling
`C.f.map φ` of the polynomial-indexed development (instance search does not see through
`(C.map φ).f`). -/
instance instFactOddNatDegreeMap [C.IsOdd] [Nontrivial S] : Fact (Odd (C.f.map φ).natDegree) :=
  (C.map φ).instFactOddNatDegreeF

@[simp]
theorem map_id : C.map (RingHom.id R) = C := by
  ext <;> simp

theorem map_map {T : Type*} [CommRing T] [Invertible (2 : T)] (ψ : S →+* T) :
    (C.map φ).map ψ = C.map (ψ.comp φ) := by
  ext <;> simp [Polynomial.map_map]

variable (A : Type*) [CommRing A] [Invertible (2 : A)] [Algebra R A]

/-- The curve base changed to an `R`-algebra `A`. -/
noncomputable abbrev baseChange : HyperellipticCurve A := C.map (algebraMap R A)

end map

/-! ### Curves over a field -/

section Field

variable {K : Type*} [Field K] [Invertible (2 : K)] (C : HyperellipticCurve K)

theorem separable_f : C.f.Separable :=
  C.separable (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr C.f_ne_zero))

theorem squarefree_f : Squarefree C.f := C.separable_f.squarefree

/-- Every declaration assuming `Fact (Squarefree f)` applies to the polynomial of a curve over a
field. -/
instance instFactSquarefreeF : Fact (Squarefree C.f) := ⟨C.squarefree_f⟩

/-- The curve `y² = f(x)` of a nonconstant squarefree polynomial over a perfect field. -/
def ofSquarefree [PerfectField K] {f : K[X]} (hf : Squarefree f) (hd : 0 < f.natDegree) :
    HyperellipticCurve K :=
  ofSeparable hd (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf.ne_zero))
    (PerfectField.separable_iff_squarefree.mpr hf)

@[simp]
theorem ofSquarefree_f [PerfectField K] {f : K[X]} (hf : Squarefree f) (hd : 0 < f.natDegree) :
    (ofSquarefree hf hd).f = f := rfl

@[simp]
theorem ofSquarefree_genus [PerfectField K] {f : K[X]} (hf : Squarefree f) (hd : 0 < f.natDegree) :
    (ofSquarefree hf hd).genus = (f.natDegree - 1) / 2 := rfl

end Field

/-- The squarefreeness `Fact` for the image of the polynomial of a curve in a field, in the
spelling `C.f.map φ` of the polynomial-indexed development. -/
instance instFactSquarefreeMap {K : Type*} [Field K] [Invertible (2 : K)] (φ : R →+* K) :
    Fact (Squarefree (C.f.map φ)) :=
  (C.map φ).instFactSquarefreeF

end HyperellipticCurve

end
