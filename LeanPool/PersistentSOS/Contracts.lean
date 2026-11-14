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

public import LeanPool.PersistentSOS.Main
public import LeanPool.PersistentSOS.UniqueMain

/-!
# Contracts

Part of the explicit persistent quartic SOS counterexample.
-/

@[expose] public section
namespace PersistentSOS

/-- The norm polynomial uses every Euclidean coordinate once. -/
theorem qPoly_definition : qPoly = ∑ i : Fin 14, MvPolynomial.X i ^ 2 := rfl

/-- Literal coefficients of the fixed cubic. -/
theorem cubicPoly_definition : cubicPoly =
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
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 13 * MvPolynomial.X 3 * MvPolynomial.X 4 := rfl

/-- Ordinary finite sums of squares, without a restriction on summand degree. -/
theorem sos_definition (p : Poly) : IsSOS p ↔
    ∃ (m : ℕ) (f : Fin m → Poly), p = ∑ i, (f i) ^ 2 := Iff.rfl

/-- The exact quartic polynomial, with ordinary polynomial scalar coefficients. -/
theorem quarticPoly_definition (σ a b : ℝ) : quarticPoly σ a b =
    MvPolynomial.C (σ / 4) * qPoly ^ 2 - MvPolynomial.C (a / 2) * qPoly -
      MvPolynomial.C b * cubicPoly := rfl

/-- Ordinary polynomial evaluation defines the objective function. -/
theorem objective_definition (σ a b : ℝ) (z : Fin 14 → ℝ) :
    objective σ a b z = MvPolynomial.eval z (quarticPoly σ a b) := rfl

/-- Explicit positive minimizing root. -/
theorem minimizingRadius_definition (σ a b : ℝ) : minimizingRadius σ a b =
    (3 * b + Real.sqrt (9 * b ^ 2 + 4 * a * σ)) / (2 * σ) := rfl

/-- Explicit attained minimum. -/
theorem minimumValue_definition (σ a b : ℝ) : minimumValue σ a b =
    -(b * minimizingRadius σ a b ^ 3 + a * minimizingRadius σ a b ^ 2) / 4 := rfl

/-- Exact rational separation constant. -/
theorem separation_definition : separation = 753357629 / 500000000000 := rfl

/-- Literal rational coefficients defining the companion cubic. -/
theorem uniqueCubicPoly_definition : uniqueCubicPoly =
    MvPolynomial.C (1 / 1001) * (1000 * cubicPoly + MvPolynomial.X 0 * qPoly) := rfl

/-- The companion cubic uses ordinary polynomial evaluation. -/
theorem uniqueCubic_definition (z : Fin 14 → ℝ) :
    uniqueCubic z = MvPolynomial.eval z uniqueCubicPoly := rfl

/-- Literal quartic regularization of the companion cubic. -/
theorem uniqueQuarticPoly_definition (σ a b : ℝ) : uniqueQuarticPoly σ a b =
    MvPolynomial.C (σ / 4) * qPoly ^ 2 - MvPolynomial.C (a / 2) * qPoly
      - MvPolynomial.C b * uniqueCubicPoly := rfl

/-- The companion objective uses ordinary polynomial evaluation. -/
theorem uniqueObjective_definition (σ a b : ℝ) (z : Fin 14 → ℝ) :
    uniqueObjective σ a b z = MvPolynomial.eval z (uniqueQuarticPoly σ a b) := rfl

/-- Exact rational separation for the companion cubic. -/
theorem uniqueSeparation_definition : uniqueSeparation = 132860603 / 143000000000 := rfl

end PersistentSOS
