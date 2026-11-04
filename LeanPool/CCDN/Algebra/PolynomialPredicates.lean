/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Predicates on polynomials and ideals

Named forms of hypotheses that recur throughout the library: homogeneity of an ideal of a
polynomial ring, absolute irreducibility of a polynomial (irreducibility over `the algebraic closure
of ℚ`), and
absolute irreducibility of its top-degree homogeneous part (the hypothesis of CCDN Theorem 4).
All are abbreviations, so proofs may use them as their unfolded statements.
-/

@[expose] public section

namespace CCDN

open MvPolynomial

variable {σ K : Type*} [CommSemiring K]

/-- An ideal of a polynomial ring is homogeneous when it contains every homogeneous
component of each of its elements. -/
abbrev IsHomogeneousIdeal (I : Ideal (MvPolynomial σ K)) : Prop :=
  ∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I

/-- An integer polynomial is absolutely irreducible when it is irreducible over `the algebraic
closure of ℚ`. -/
abbrev AbsolutelyIrreducible (f : MvPolynomial σ ℤ) : Prop :=
  Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f)

/-- A rational polynomial is absolutely irreducible when it is irreducible over `the algebraic
closure of ℚ`. -/
abbrev AbsolutelyIrreducibleRat (f : MvPolynomial σ ℚ) : Prop :=
  Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) f)

/-- An integer polynomial is absolutely irreducible exactly when its image over `ℚ` is. -/
theorem absolutelyIrreducibleRat_map_iff (f : MvPolynomial σ ℤ) :
    AbsolutelyIrreducibleRat (map (Int.castRingHom ℚ) f) ↔ AbsolutelyIrreducible f := by
  rw [AbsolutelyIrreducibleRat, map_map, RingHom.ext_int ((algebraMap ℚ _).comp _)]

/-- The top-degree homogeneous part of an integer polynomial is irreducible over `the algebraic
closure of ℚ`. -/
abbrev HasAbsIrreducibleTopForm (f : MvPolynomial σ ℤ) : Prop :=
  AbsolutelyIrreducible (homogeneousComponent f.totalDegree f)

/-- The top-degree homogeneous part of a rational polynomial is irreducible over `the algebraic
closure of ℚ`. -/
abbrev HasAbsIrreducibleTopFormRat (f : MvPolynomial σ ℚ) : Prop :=
  AbsolutelyIrreducibleRat (homogeneousComponent f.totalDegree f)

end CCDN
