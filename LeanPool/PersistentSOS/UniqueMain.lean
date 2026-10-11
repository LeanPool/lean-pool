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

public import LeanPool.PersistentSOS.UniqueGeometry
public import LeanPool.PersistentSOS.UniqueMoments
public import LeanPool.PersistentSOS.UniqueDerivatives

/-!
# Unique Main

Part of the explicit persistent quartic SOS counterexample.
-/

@[expose] public section
namespace PersistentSOS

/-- The selected quartic's exact minimum shift is globally nonnegative. -/
theorem unique_minimum_shift_nonnegative {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (hb : 0 < b) (z : Fin 14 → ℝ) :
    0 ≤ MvPolynomial.eval z
      (uniqueQuarticPoly σ a b - MvPolynomial.C (minimumValue σ a b)) := by
  simpa only [map_sub, MvPolynomial.eval_C, sub_nonneg, uniqueObjective]
    using unique_objective_global_lower_bound hσ ha hb z

/-- Persistent ordinary - SOS failure with a unique global minimizer and
positive - definite Hessian there, for every positive real parameter. -/
theorem unique_persistent_failure {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hb : 0 < b) :
    (∀ z : Fin 14 → ℝ, minimumValue σ a b ≤ uniqueObjective σ a b z) ∧
    (∀ z : Fin 14 → ℝ, uniqueObjective σ a b z = minimumValue σ a b ↔
      z = axis (minimizingRadius σ a b)) ∧
    Matrix.PosDef (fun i j : Fin 14 =>
      MvPolynomial.eval (axis (minimizingRadius σ a b))
        (MvPolynomial.pderiv j (MvPolynomial.pderiv i (uniqueQuarticPoly σ a b)))) ∧
    ¬ IsSOS (uniqueQuarticPoly σ a b - MvPolynomial.C (minimumValue σ a b)) :=
  ⟨unique_objective_global_lower_bound hσ ha hb,
    unique_objective_minimizer hσ ha hb, unique_hessian_posDef hσ ha hb,
    unique_minimum_shift_not_sos hσ ha hb⟩

end PersistentSOS
