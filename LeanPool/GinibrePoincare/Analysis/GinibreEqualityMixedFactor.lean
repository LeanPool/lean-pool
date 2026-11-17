/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityMixedFactor.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityMixedPolynomial
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Ginibre Equality Mixed Factor
-/


@[expose] public section

noncomputable section
namespace GinibrePoincare
open MvPolynomial
open scoped ComplexConjugate

def ginibreMixedHolomorphicLift {n : ℕ} (P : ConfigurationPolynomial n) : GinibreMixedPolynomial n
  :=
  MvPolynomial.rename (fun j => (j, 0)) P

def ginibreMixedAntiholomorphicLift {n : ℕ} (P : ConfigurationPolynomial n) :
  GinibreMixedPolynomial n :=
  MvPolynomial.rename (fun j => (j, 1)) (MvPolynomial.map (starRingEnd ℂ) P)

theorem ginibreMixedPolynomialSpecialize_holomorphic {n : ℕ}
    (P : ConfigurationPolynomial n) (z : Configuration n) :
    ginibreMixedPolynomialSpecialize z (ginibreMixedHolomorphicLift P) = C (MvPolynomial.eval z P)
      := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [ginibreMixedHolomorphicLift, ginibreMixedPolynomialSpecialize]
  | add P Q hp hq => simpa [ginibreMixedHolomorphicLift, map_add] using congrArg₂ (·+·) hp hq
  | mul_X P j hp =>
    simp only [ginibreMixedHolomorphicLift, map_mul, MvPolynomial.rename_X]
    simp only [ginibreMixedPolynomialSpecialize, MvPolynomial.aeval_X]
    simp only [ginibreMixedHolomorphicLift, ginibreMixedPolynomialSpecialize] at hp
    rw [hp]
    simp

theorem ginibreMixedPolynomialSpecialize_antiholomorphic {n : ℕ}
    (P : ConfigurationPolynomial n) (z : Configuration n) :
    ginibreMixedPolynomialSpecialize z (ginibreMixedAntiholomorphicLift P) =
      MvPolynomial.map (starRingEnd ℂ) P := by
  unfold ginibreMixedPolynomialSpecialize ginibreMixedAntiholomorphicLift
  rw [MvPolynomial.aeval_rename]
  simpa only [Function.comp_def, show (1 : Fin 2)≠0 by decide, ite_false] using
    MvPolynomial.aeval_X_left_apply (MvPolynomial.map (starRingEnd ℂ) P)

/-- A nonzero holomorphic factor preserves the specialized conjugate degree. -/
theorem ginibreEquality_mixed_factor_degree_bound_of_specialize {n : ℕ}
    (V Q : ConfigurationPolynomial n) (P : GinibreMixedPolynomial n)
    (z : Configuration n) (hV : MvPolynomial.eval z V ≠ 0) (K : ℕ)
    (hdegree : (ginibreMixedPolynomialSpecialize z P).totalDegree ≤ K)
    (hfactor : P = ginibreMixedHolomorphicLift V * ginibreMixedAntiholomorphicLift Q) :
    Q.totalDegree ≤ K := by
  by_cases hQ : Q=0
  · simp [hQ]
  have hm : MvPolynomial.map (starRingEnd ℂ) Q ≠ 0 := by
    intro hz
    apply hQ
    apply MvPolynomial.map_injective (starRingEnd ℂ)
      (show Function.Injective (starRingEnd ℂ) from star_injective)
    simpa using hz
  have he := hdegree
  rw [hfactor, map_mul, ginibreMixedPolynomialSpecialize_holomorphic,
    ginibreMixedPolynomialSpecialize_antiholomorphic,
    MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.C_ne_zero.mpr hV) hm,
    MvPolynomial.totalDegree_C, zero_add] at he
  have hd : (MvPolynomial.map (starRingEnd ℂ) Q).totalDegree = Q.totalDegree := by
    simp only [MvPolynomial.totalDegree, MvPolynomial.support_map_of_injective Q (show
      Function.Injective (starRingEnd ℂ) from star_injective)]
  rwa [hd] at he


/-- A true holomorphic factor cannot conceal higher antiholomorphic polynomial
 degree in an actual mixed-polynomial representative. -/
theorem ginibreEquality_mixed_factor_degree_bound {n : ℕ}
    (V Q : ConfigurationPolynomial n) (P : GinibreMixedPolynomial n)
    (z : Configuration n) (hV : MvPolynomial.eval z V ≠ 0) (K : ℕ)
    (hP : ∀ d ∈ P.support, ginibreMixedAntiDegree d ≤ K)
    (hfactor : P = ginibreMixedHolomorphicLift V * ginibreMixedAntiholomorphicLift Q) :
    Q.totalDegree ≤ K := by
  exact ginibreEquality_mixed_factor_degree_bound_of_specialize V Q P z hV K
    (ginibreMixedPolynomialSpecialize_degree_le P z K hP) hfactor

theorem ginibreMixedHolomorphicLift_eval {n : ℕ} (P : ConfigurationPolynomial n)
    (z : Configuration n) : ginibreMixedPolynomialEval (ginibreMixedHolomorphicLift P) z =
      MvPolynomial.eval z P := by
  unfold ginibreMixedPolynomialEval ginibreMixedHolomorphicLift
  rw [MvPolynomial.eval_rename]
  congr 1

theorem ginibreMixedAntiholomorphicLift_eval {n : ℕ} (P : ConfigurationPolynomial n)
    (z : Configuration n) : ginibreMixedPolynomialEval (ginibreMixedAntiholomorphicLift P) z =
      conj (MvPolynomial.eval z P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [ginibreMixedPolynomialEval, ginibreMixedAntiholomorphicLift]
  | add P Q hp hq =>
    simpa only [ginibreMixedPolynomialEval, ginibreMixedAntiholomorphicLift, map_add] using
      congrArg₂ (·+·) hp hq
  | mul_X P j hp =>
    simp only [ginibreMixedPolynomialEval, ginibreMixedAntiholomorphicLift, map_mul,
      MvPolynomial.map_X, MvPolynomial.rename_X, MvPolynomial.eval_X]
    simp only [ginibreMixedPolynomialEval, ginibreMixedAntiholomorphicLift] at hp
    rw [hp]
    simp

end GinibrePoincare
