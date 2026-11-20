/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondencePolynomialCoulomb.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondencePolynomialGaussian
public import LeanPool.GinibrePoincare.Analysis.GinibreIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianIntegrationByParts
/-!
# Correspondence polynomial coulomb

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondencePolynomial_inverse_pair_memLp`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- One pair factor divides the actual Vandermonde polynomial. -/
theorem correspondencePolynomial_pair_factor {n : ℕ} (i j : Fin n) (hij : i < j) :
    ∃ Q : ConfigurationPolynomial n,
      polynomialVandermonde n = (MvPolynomial.X j - MvPolynomial.X i) * Q := by
  classical
  let p : OrderedParticlePair n := ⟨i, j, Finset.mem_Ioi.mpr hij⟩
  refine ⟨∏ q ∈ (Finset.univ : Finset (OrderedParticlePair n)).erase p, orderedPairFactor q, ?_⟩
  rw [← prod_orderedPairFactor]
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ p)).symm

/-- The inverse-distance singularity in any polynomial drift is Gaussian-
polynomial after Vandermonde multiplication, hence truly Ginibre L². -/
theorem correspondencePolynomial_inverse_pair_memLp {n : ℕ} (hn : 0 < n)
    (P : GinibreMixedPolynomial n) (i j : Fin n) (hij : i < j) :
    MemLp (fun z => ginibreMixedPolynomialEval P z / (z j-z i)) 2 (ginibreMeasure n) := by
  obtain ⟨Q, hQ⟩ := correspondencePolynomial_pair_factor i j hij
  let R : GinibreMixedPolynomial n := MvPolynomial.rename (fun k : Fin n => (k, (0 : Fin 2))) Q
  have hR (z : Configuration n) : ginibreMixedPolynomialEval R z = MvPolynomial.eval z Q := by
    unfold ginibreMixedPolynomialEval R
    rw [MvPolynomial.eval_rename]
    rfl
  apply correspondencePolynomial_memLp_of_vandermonde hn
  apply (correspondencePolynomial_gaussian_memLp n (R*P)).ae_eq
  have hcf : ∀ᵐ z ∂complexGaussianMeasure n, z ∉ collisionSet n := by
    rw [ae_iff]
    rw [show {a : Configuration n | ¬ a ∉ collisionSet n} = collisionSet n by ext a; simp]
    exact complexGaussianMeasure_collisionSet n
  filter_upwards [hcf] with z hz
  have hne : z j-z i ≠ 0 := sub_ne_zero.mpr (fun h => hz ⟨j, i, h, hij.ne.symm⟩)
  have hv : vandermonde z = (z j-z i) * MvPolynomial.eval z Q := by
    rw [← eval_polynomialVandermonde n z, hQ]
    simp only [map_mul, map_sub, MvPolynomial.eval_X]
  change ginibreMixedPolynomialEval (R*P) z = vandermonde z * (ginibreMixedPolynomialEval P z / (z
      j-z i))
  unfold ginibreMixedPolynomialEval
  rw [map_mul]
  rw [show MvPolynomial.eval (fun k => if k.2=0 then z k.1 else conj (z k.1)) R =
    MvPolynomial.eval z Q from hR z, hv]
  field_simp [hne]

end
end GinibrePoincare
