/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import LeanPool.AaronsonAmbainis.Statements

/-!
# Interface for the proof of the determinant inequality

This file defines the lowest monomials of a polynomial (`IsLowest`, Section 3.2 of the paper)
and the agreement matrix (`agMatrix`, Section 3.3), and splits the proof of `DetInequality`
(Corollary 3.2) into two independent parts:

* `LowestUnit`  — multiplying by a polynomial with constant coefficient `1` does not change
                   the monomials of least total degree (Lemma 3.3);
* `LowestBound` — the determinant of the agreement matrix on the ones of `g` is nonzero, and
                   each of its monomials of least total degree has exponent at most
                   `bdry g j` in every variable `j` (Lemma 3.4 and Lemma 3.6).

The directory `DetLow` proves `LowestUnit` and `LowestBound`.
The directory `DetBij` proves `LowestUnit → LowestBound → DetInequality`.
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset MvPolynomial

section
variable {ι : Type} [Fintype ι]

/-- `m` is a monomial of `q` of least total degree. -/
def IsLowest (q : MvPolynomial ι ℤ) (m : ι →₀ ℕ) : Prop :=
  m ∈ q.support ∧ ∀ m' ∈ q.support, ∑ i, m i ≤ ∑ i, m' i

/-- `agMon x z = ∏_{i : x_i = z_i} s_i`: the monomial of the agreement set of `x` and `z`. -/
noncomputable def agMon (x z : Cube ι) : MvPolynomial ι ℤ :=
  ∏ i, if x i = z i then X i else 1

end

section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The ones of `g`, as a type. -/
abbrev Ones (g : Cube ι → Bool) := {x : Cube ι // g x = true}

/-- The agreement matrix `M[x,z] = s^{ag(x,z)}` on the ones of `g`. -/
noncomputable def agMatrix (g : Cube ι → Bool) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x z => agMon x.1 z.1

end

/-- Multiplying by a polynomial with constant coefficient `1` does not change the
monomials of least total degree. -/
def LowestUnit : Prop :=
  ∀ (ι : Type) [Fintype ι] (u q : MvPolynomial ι ℤ), constantCoeff u = 1 →
    ∀ m : ι →₀ ℕ, IsLowest (u * q) m ↔ IsLowest q m

/-- The determinant of the agreement matrix is nonzero, and each of its monomials of least
total degree has exponent at most `bdry g j` in every variable `j`. -/
def LowestBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool),
    (agMatrix g).det ≠ 0 ∧
      ∀ m : ι →₀ ℕ, IsLowest (agMatrix g).det m → ∀ j, m j ≤ bdry g j

end AaronsonAmbainis
