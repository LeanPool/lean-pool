/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityMixedPolynomial.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityPolynomial
public import Mathlib.Algebra.MvPolynomial.Funext
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Ginibre Equality Mixed Polynomial
-/


@[expose] public section

noncomputable section
namespace GinibrePoincare
open scoped ComplexConjugate BigOperators
open MvPolynomial

abbrev GinibreMixedPolynomial (n : ℕ) := MvPolynomial (Fin n × Fin 2) ℂ

def ginibreMixedPolynomialEval {n : ℕ} (P : GinibreMixedPolynomial n) (z : Configuration n) : ℂ :=
  MvPolynomial.eval (fun k => if k.2=0 then z k.1 else conj (z k.1)) P

private def mixedToRealVariables (n : ℕ) : GinibreMixedPolynomial n →ₐ[ℂ] GinibreMixedPolynomial n
  :=
  MvPolynomial.aeval (fun k => if k.2=0 then
    X (k.1, 0) + C Complex.I * X (k.1, 1) else X (k.1, 0) - C Complex.I * X (k.1, 1))

private def realToMixedVariables (n : ℕ) : GinibreMixedPolynomial n →ₐ[ℂ] GinibreMixedPolynomial n
  :=
  MvPolynomial.aeval (fun k => if k.2=0 then
    C (1/2 : ℂ) * (X (k.1, 0) + X (k.1, 1)) else
    C (1/(2*Complex.I) : ℂ) * (X (k.1, 0)-X (k.1, 1)))

private theorem mixedToRealVariables_injective (n : ℕ) :
    Function.Injective (mixedToRealVariables n) := by
  have hi : (realToMixedVariables n).comp (mixedToRealVariables n) = AlgHom.id ℂ _ := by
    ext k : 1
    obtain ⟨j, k⟩ := k
    fin_cases k <;> simp [mixedToRealVariables, realToMixedVariables]
    all_goals
      ring_nf
      simp only [← map_pow, Complex.I_sq, map_neg, map_one]
      ring_nf
      rw [mul_right_comm]
      have hh : (C (1/2 : ℂ) : GinibreMixedPolynomial n)*2=1 := by
        calc
          _ = C (1/2 : ℂ)*C (2 : ℂ) := by rw [map_ofNat]
          _ = C ((1/2 : ℂ)*2) := (map_mul C _ _).symm
          _ = 1 := by norm_num
      rw [hh, one_mul]
  have hl : Function.LeftInverse (realToMixedVariables n) (mixedToRealVariables n) := by
    intro P
    exact congrArg (fun A : GinibreMixedPolynomial n →ₐ[ℂ] GinibreMixedPolynomial n => A P) hi
  exact hl.injective

/-- Mixed polynomial evaluation on actual coordinates and their conjugates is
injective.  No independent-variable or holomorphic-polynomial hypothesis is used. -/
theorem ginibreMixedPolynomialEval_injective (n : ℕ) :
    Function.Injective (ginibreMixedPolynomialEval (n:=n)) := by
  intro P Q he
  apply mixedToRealVariables_injective n
  apply MvPolynomial.funext_set (fun _ => Set.range Complex.ofReal)
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro x hx
  have hxreal (k : Fin n × Fin 2) : (x k).im=0 := by
    obtain ⟨r, hr⟩ := hx k (Set.mem_univ k)
    rw [← hr]
    exact Complex.ofReal_im r
  let z : Configuration n := fun j => x (j, 0) + Complex.I * x (j, 1)
  have hc (j : Fin n) : conj (z j) = x (j, 0) - Complex.I*x (j, 1) := by
    simp only [z, map_add, map_mul, Complex.conj_I]
    have h0 : conj (x (j, 0)) = x (j, 0) := Complex.conj_eq_iff_im.mpr (hxreal (j, 0))
    have h1 : conj (x (j, 1)) = x (j, 1) := Complex.conj_eq_iff_im.mpr (hxreal (j, 1))
    rw [h0, h1]
    ring
  have hv (T : GinibreMixedPolynomial n) : MvPolynomial.eval x (mixedToRealVariables n T) =
      ginibreMixedPolynomialEval T z := by
    change MvPolynomial.aeval x (mixedToRealVariables n T) =
      MvPolynomial.aeval (fun k : Fin n × Fin 2 => if k.2=0 then z k.1 else conj (z k.1)) T
    rw [mixedToRealVariables, MvPolynomial.comp_aeval_apply]
    congr 1
    ext k : 1
    simp only [MvPolynomial.aeval_X]
    split_ifs with hk
    · simp [z]
    · simp [hc]
  rw [hv P, hv Q]
  exact congrFun he z

theorem ginibreMixedPolynomialEval_continuous {n : ℕ} (P : GinibreMixedPolynomial n) :
    Continuous (ginibreMixedPolynomialEval P) := by
  apply (MvPolynomial.continuous_eval P).comp
  apply continuous_pi
  intro k
  by_cases hk : k.2=0
  · simpa only [hk, ite_true] using (continuous_apply k.1 : Continuous (fun z : Configuration n =>
    z k.1))
  · simpa only [hk, ite_false, Function.comp_def] using (Complex.continuous_conj.comp
      (continuous_apply k.1 : Continuous (fun z : Configuration n => z k.1)))

/-- Actual Gaussian almost-everywhere identities of mixed polynomial
representatives imply formal polynomial equality. -/
theorem ginibreMixedPolynomialEval_ae_injective {n : ℕ} (hn : 0 < n)
    (P Q : GinibreMixedPolynomial n)
    (he : ginibreMixedPolynomialEval P =ᵐ[complexGaussianMeasure n] ginibreMixedPolynomialEval Q) :
    P=Q := by
  apply ginibreMixedPolynomialEval_injective n
  exact continuous_eq_of_ae_eq_complexGaussian hn
    (ginibreMixedPolynomialEval_continuous P) (ginibreMixedPolynomialEval_continuous Q) he

/-- Substitution of fixed holomorphic coordinates, leaving conjugate variables formal. -/
def ginibreMixedPolynomialSpecialize {n : ℕ} (z : Configuration n) :
    GinibreMixedPolynomial n →ₐ[ℂ] ConfigurationPolynomial n :=
  MvPolynomial.aeval (fun k => if k.2=0 then C (z k.1) else X k.1)

def ginibreMixedAntiDegree {n : ℕ} (d : (Fin n × Fin 2) →₀ ℕ) : ℕ :=
  d.sum (fun k m => if k.2=0 then 0 else m)

/-- Specialization preserves the actual antiholomorphic degree bound. -/
theorem ginibreMixedPolynomialSpecialize_degree_le {n : ℕ}
    (P : GinibreMixedPolynomial n) (z : Configuration n) (K : ℕ)
    (hP : ∀ d ∈ P.support, ginibreMixedAntiDegree d ≤ K) :
    (ginibreMixedPolynomialSpecialize z P).totalDegree ≤ K := by
  classical
  rw [P.as_sum, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [ginibreMixedPolynomialSpecialize, MvPolynomial.aeval_monomial]
  have hp : (d.prod (fun k m =>
      (if k.2=0 then C (z k.1) else X k.1 : ConfigurationPolynomial n)^m)).totalDegree ≤
      ginibreMixedAntiDegree d := by
    refine (MvPolynomial.totalDegree_finsetProd d.support _).trans ?_
    apply Finset.sum_le_sum
    intro k hk
    by_cases h : k.2=0
    · simp only [h, ite_true]
      rw [←map_pow, MvPolynomial.totalDegree_C]
    · simp [h]
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add] using hp.trans
      (hP d hd))

end GinibrePoincare
