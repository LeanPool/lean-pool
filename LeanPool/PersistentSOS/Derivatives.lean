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

public import LeanPool.PersistentSOS.Definitions
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Derivatives

Part of the explicit persistent quartic SOS counterexample.
-/

@[expose] public section
namespace PersistentSOS
open MvPolynomial

theorem cubic_first_at_zero (i : Fin 14) : eval (0 : Fin 14 → ℝ) (pderiv i cubicPoly) = 0 := by
  simp [cubicPoly]

theorem cubic_second_at_zero (i j : Fin 14) :
    eval (0 : Fin 14 → ℝ) (pderiv j (pderiv i cubicPoly)) = 0 := by
  simp [cubicPoly]

theorem q_first (i : Fin 14) : pderiv i qPoly = 2 * X i := by
  simp [qPoly, Pi.single_apply, mul_ite]

theorem stationary_origin (σ a b : ℝ) (i : Fin 14) :
    eval (0 : Fin 14 → ℝ) (pderiv i (quarticPoly σ a b)) = 0 := by
  have hc : constantCoeff (pderiv i cubicPoly) = 0 := by simpa using cubic_first_at_zero i
  have hq : constantCoeff qPoly = 0 := by simp [qPoly]
  simp [quarticPoly, q_first, hc, hq]

theorem hessian_origin (σ a b : ℝ) (i j : Fin 14) :
    eval (0 : Fin 14 → ℝ) (pderiv j (pderiv i (quarticPoly σ a b))) =
      if i = j then -a else 0 := by
  have hc : constantCoeff (pderiv j (pderiv i cubicPoly)) = 0 := by
    simpa using cubic_second_at_zero i j
  have hq : constantCoeff qPoly = 0 := by simp [qPoly]
  have htwo : constantCoeff (2 : Poly) = 2 := by
    rw [← map_ofNat MvPolynomial.C 2]
    simp
  simp [quarticPoly, q_first, hc, hq, Pi.single_apply, htwo]
  split_ifs <;> simp_all

end PersistentSOS
