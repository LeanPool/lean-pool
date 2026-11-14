/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

/-
Adapted from JD-Jones-ASES/persistent-sos, commit
d432ff9a67594cc0fa7a7af1913320b46d2a86db.
Original MIT notice (retained under the permission to sublicense):

MIT License

Copyright (c) 2026 JD Jones

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Fin.VecNotation

/-!
# Definitions

Part of the explicit persistent quartic SOS counterexample.
-/

@[expose] public section

namespace PersistentSOS

/-- Ordinary real multivariate polynomials in fourteen variables. -/
abbrev Poly := MvPolynomial (Fin 14) ℝ

/-- The squared Euclidean norm polynomial, the sum of all coordinate squares. -/
noncomputable def qPoly : Poly := ∑ i, MvPolynomial.X i ^ 2

/-- The fixed sparse rational cubic, in coordinate order `(t, x₁, …, x₄, y₁, …, y₉)`. -/
noncomputable def cubicPoly : Poly :=
  MvPolynomial.X 0 ^ 3
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 5 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 6 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 7 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 8 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 9 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 10 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 11 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 12 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 13 ^ 2
  + MvPolynomial.C (3 / 2) * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
  + MvPolynomial.C (3 / 2) * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2
  + MvPolynomial.C (3 / 2) * MvPolynomial.X 0 * MvPolynomial.X 3 ^ 2
  + MvPolynomial.C (3 / 2) * MvPolynomial.X 0 * MvPolynomial.X 4 ^ 2
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 5 * MvPolynomial.X 1 ^ 2
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 6 * MvPolynomial.X 2 ^ 2
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 7 * MvPolynomial.X 3 ^ 2
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 8 * MvPolynomial.X 1 * MvPolynomial.X 2
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 8 * MvPolynomial.X 3 * MvPolynomial.X 4
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 9 * MvPolynomial.X 1 * MvPolynomial.X 3
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 9 * MvPolynomial.X 2 * MvPolynomial.X 4
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 10 * MvPolynomial.X 2 * MvPolynomial.X 3
  + MvPolynomial.C (1813 / 500) * MvPolynomial.X 11 * MvPolynomial.X 1 * MvPolynomial.X 4
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 12 * MvPolynomial.X 2 * MvPolynomial.X 4
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 13 * MvPolynomial.X 3 * MvPolynomial.X 4

/-- Evaluation of the squared Euclidean norm polynomial at a real vector. -/
noncomputable def Q (z : Fin 14 → ℝ) : ℝ := MvPolynomial.eval z qPoly
/-- Evaluation of the fixed cubic polynomial at a real vector. -/
noncomputable def C (z : Fin 14 → ℝ) : ℝ := MvPolynomial.eval z cubicPoly
/-- Euclidean radius, written as the square root of the sum of coordinate squares. -/
noncomputable def radius (z : Fin 14 → ℝ) : ℝ := Real.sqrt (Q z)

/-- Ordinary SOS: a finite sum of squares of arbitrary real polynomials. -/
def IsSOS (p : Poly) : Prop :=
  ∃ (m : ℕ) (f : Fin m → Poly), p = ∑ i, (f i) ^ 2

/-- Euclidean quartic regularization with quadratic coefficient -a / 2 and cubic -bC. -/
noncomputable def quarticPoly (σ a b : ℝ) : Poly :=
  MvPolynomial.C (σ / 4) * qPoly ^ 2 - MvPolynomial.C (a / 2) * qPoly
    - MvPolynomial.C b * cubicPoly

/-- The real - valued function obtained by evaluating the quartic polynomial. -/
noncomputable def objective (σ a b : ℝ) (z : Fin 14 → ℝ) : ℝ :=
  MvPolynomial.eval z (quarticPoly σ a b)

/-- The point on the distinguished coordinate axis with first coordinate `r`. -/
def axis (r : ℝ) : Fin 14 → ℝ := fun i => if i = 0 then r else 0

/-- Positive minimizing radius for quartic regularization with negative quadratic
strength `a` and positive cubic strength `b`. -/
noncomputable def minimizingRadius (σ a b : ℝ) : ℝ :=
  (3 * b + Real.sqrt (9 * b ^ 2 + 4 * a * σ)) / (2 * σ)

/-- Exact minimum, once the cubic has sphere maximum one. -/
noncomputable def minimumValue (σ a b : ℝ) : ℝ :=
  -(b * minimizingRadius σ a b ^ 3 + a * minimizingRadius σ a b ^ 2) / 4

/-- A second literal rational cubic selecting the positive first coordinate axis. -/
noncomputable def uniqueCubicPoly : Poly :=
  MvPolynomial.C (1 / 1001) * (1000 * cubicPoly + MvPolynomial.X 0 * qPoly)

/-- Evaluation of the cubic with a unique sphere maximizer. -/
noncomputable def uniqueCubic (z : Fin 14 → ℝ) : ℝ := MvPolynomial.eval z uniqueCubicPoly

/-- Quartic regularization using the cubic with a unique sphere maximizer. -/
noncomputable def uniqueQuarticPoly (σ a b : ℝ) : Poly :=
  MvPolynomial.C (σ / 4) * qPoly ^ 2 - MvPolynomial.C (a / 2) * qPoly
    - MvPolynomial.C b * uniqueCubicPoly

/-- Evaluation of the quartic with a unique global minimizer. -/
noncomputable def uniqueObjective (σ a b : ℝ) (z : Fin 14 → ℝ) : ℝ :=
  MvPolynomial.eval z (uniqueQuarticPoly σ a b)

/-- The strict rational moment separation for the selected cubic. -/
noncomputable def uniqueSeparation : ℝ := 132860603 / 143000000000


@[simp] theorem Q_eq_sum (z : Fin 14 → ℝ) : Q z = ∑ i, z i ^ 2 := by
  simp [Q, qPoly, map_sum]

@[simp] theorem objective_eq (σ a b : ℝ) (z : Fin 14 → ℝ) :
    objective σ a b z = σ / 4 * Q z ^ 2 - a / 2 * Q z - b * C z := by
  simp [objective, quarticPoly, Q, C]

end PersistentSOS
