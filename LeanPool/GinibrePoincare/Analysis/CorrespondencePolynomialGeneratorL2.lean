/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondencePolynomialGeneratorL2.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondencePolynomialDifferential
public import LeanPool.GinibrePoincare.Analysis.GinibreDirectionalCoordinates
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
/-!
# Correspondence polynomial generator L 2

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondencePolynomial_gradient_memLp`,
`correspondencePolynomial_pregenerator_memLp`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff
namespace GinibrePoincare
noncomputable section

theorem correspondencePolynomial_projected_product_memLp {n : ℕ} (hn : 0 < n)
    (P Q : GinibreMixedPolynomial n) (T S : ℂ →L[ℝ] ℝ) :
    MemLp (fun z => T (ginibreMixedPolynomialEval P z) * S (ginibreMixedPolynomialEval Q z))
      2 (ginibreMeasure n) := by
  have h := ((correspondencePolynomial_ginibre_memLp hn (P*Q)).norm).const_mul (‖T‖*‖S‖)
  apply h.mono'
  · exact ((T.continuous.comp (ginibreMixedPolynomialEval_continuous P)).mul
      (S.continuous.comp (ginibreMixedPolynomialEval_continuous Q))).aestronglyMeasurable
  · filter_upwards [] with z
    rw [norm_mul]
    have he : ginibreMixedPolynomialEval (P*Q) z = ginibreMixedPolynomialEval P z *
        ginibreMixedPolynomialEval Q z := by
      unfold ginibreMixedPolynomialEval
      exact map_mul _ _ _
    rw [he, norm_mul]
    nlinarith [T.le_opNorm (ginibreMixedPolynomialEval P z), S.le_opNorm (ginibreMixedPolynomialEval
        Q z),
      norm_nonneg (T (ginibreMixedPolynomialEval P z)), norm_nonneg (S (ginibreMixedPolynomialEval Q
          z)),
      mul_nonneg (norm_nonneg T) (norm_nonneg (ginibreMixedPolynomialEval P z)),
      mul_nonneg (norm_nonneg S) (norm_nonneg (ginibreMixedPolynomialEval Q z))]

/-- Real or imaginary inverse-distance coefficients times an arbitrary
polynomial derivative are square integrable under the Ginibre law. -/
theorem correspondencePolynomial_inverse_projected_memLp {n : ℕ} (hn : 0 < n)
    (P : GinibreMixedPolynomial n) (T S : ℂ →L[ℝ] ℝ)
    (i j : Fin n) (hij : i < j) :
    MemLp (fun z => T (ginibreMixedPolynomialEval P z) * S ((z i-z j)⁻¹))
      2 (ginibreMeasure n) := by
  have h := ((correspondencePolynomial_inverse_pair_memLp hn P i j hij).norm).const_mul (‖T‖*‖S‖)
  apply h.mono'
  · exact ((T.continuous.comp (ginibreMixedPolynomialEval_continuous P)).measurable.mul
      (S.continuous.measurable.comp (((measurable_pi_apply i).sub (measurable_pi_apply
          j)).inv))).aestronglyMeasurable
  · filter_upwards [] with z
    rw [norm_mul, norm_div, div_eq_mul_inv, ← norm_inv]
    have he : ‖(z i-z j)⁻¹‖ = ‖(z j-z i)⁻¹‖ := by rw [norm_inv, norm_inv, norm_sub_rev]
    have hb := S.le_opNorm ((z i-z j)⁻¹)
    rw [he] at hb
    have ha := T.le_opNorm (ginibreMixedPolynomialEval P z)
    calc
      _ ≤ (‖T‖ * ‖ginibreMixedPolynomialEval P z‖) * (‖S‖ * ‖(z j-z i)⁻¹‖) :=
        mul_le_mul ha hb (norm_nonneg _) (by positivity)
      _ = _ := by ring

theorem correspondencePolynomial_gradient_memLp {n : ℕ} (hn : 0 < n)
    (P : GinibreMixedPolynomial n) (T : ℂ →L[ℝ] ℝ) :
    MemLp (ginibreEuclideanGradient (fun z => T (ginibreMixedPolynomialEval P z))) 2 (ginibreMeasure
        n) := by
  apply memLp_piLp_iff.mpr
  intro k
  convert correspondencePolynomial_projected_memLp hn
    (correspondencePolynomialDerivative P (ginibreCoordinateDirection k)) T using 1
  funext z
  rw [ginibreEuclideanGradient_coordinate, correspondencePolynomial_projected_derivative]

theorem correspondencePolynomial_coulomb_memLp {n : ℕ} (hn : 0 < n)
    (P : GinibreMixedPolynomial n) (T : ℂ →L[ℝ] ℝ) (i j : Fin n) (hij : i < j) :
    MemLp (fun z => fderiv ℝ (fun y => T (ginibreMixedPolynomialEval P y)) z (coulombPairDirection i
        j z))
      2 (ginibreMeasure n) := by
  let R := correspondencePolynomialDerivative P (realCoordinateDirection i) -
    correspondencePolynomialDerivative P (realCoordinateDirection j)
  let I := correspondencePolynomialDerivative P (imaginaryCoordinateDirection i) -
    correspondencePolynomialDerivative P (imaginaryCoordinateDirection j)
  have hR := correspondencePolynomial_inverse_projected_memLp hn R T Complex.reCLM i j hij
  have hI := correspondencePolynomial_inverse_projected_memLp hn I T Complex.imCLM i j hij
  convert hR.sub hI using 1
  funext z
  rw [fderiv_coulombPairDirection_eq_inverse_components]
  simp only [correspondencePolynomial_projected_derivative]
  unfold R I ginibreMixedPolynomialEval
  simp only [map_sub, Complex.reCLM_apply, Complex.imCLM_apply, Pi.sub_apply]
  ring

/-- Constant-direction second derivatives are genuinely square integrable. -/
theorem correspondencePolynomial_second_memLp {n : ℕ} (hn : 0 < n)
    (P : GinibreMixedPolynomial n) (T : ℂ →L[ℝ] ℝ) (v : Configuration n) :
    MemLp (secondDirectionalDerivative (fun z => T (ginibreMixedPolynomialEval P z)) v)
      2 (ginibreMeasure n) := by
  have he : (fun z => fderiv ℝ (fun y => T (ginibreMixedPolynomialEval P y)) z v) =
      fun z => T (ginibreMixedPolynomialEval (correspondencePolynomialDerivative P v) z) :=
    funext fun z => correspondencePolynomial_projected_derivative P T z v
  unfold secondDirectionalDerivative
  rw [he]
  have he2 : (fun z => fderiv ℝ (fun y => T (ginibreMixedPolynomialEval
      (correspondencePolynomialDerivative P v) y)) z v) =
      fun z => T (ginibreMixedPolynomialEval (correspondencePolynomialDerivative
        (correspondencePolynomialDerivative P v) v) z) :=
    funext fun z => correspondencePolynomial_projected_derivative _ T z v
  rw [he2]
  exact correspondencePolynomial_projected_memLp hn _ T

theorem correspondencePolynomial_confinement_memLp {n : ℕ} (hn : 0 < n)
    (P : GinibreMixedPolynomial n) (T : ℂ →L[ℝ] ℝ) (j : Fin n) :
    MemLp (fun z => fderiv ℝ (fun y => T (ginibreMixedPolynomialEval P y)) z
      (coordinateDirection j (z j))) 2 (ginibreMeasure n) := by
  let X : GinibreMixedPolynomial n := MvPolynomial.X (j, (0 : Fin 2))
  have hr := correspondencePolynomial_projected_product_memLp hn X
    (correspondencePolynomialDerivative P (realCoordinateDirection j)) Complex.reCLM T
  have hi := correspondencePolynomial_projected_product_memLp hn X
    (correspondencePolynomialDerivative P (imaginaryCoordinateDirection j)) Complex.imCLM T
  convert hr.add hi using 1
  funext z
  rw [fderiv_coordinateDirection_self]
  simp only [correspondencePolynomial_projected_derivative, Pi.add_apply]
  unfold X ginibreMixedPolynomialEval
  simp only [MvPolynomial.eval_X, ite_true, Complex.reCLM_apply, Complex.imCLM_apply]

/-- Every real or imaginary part of an arbitrary mixed polynomial lies in
L² together with its full singular Ginibre differential generator. -/
theorem correspondencePolynomial_pregenerator_memLp {n : ℕ} (hn : 0 < n)
    (P : GinibreMixedPolynomial n) (T : ℂ →L[ℝ] ℝ) :
    MemLp (ginibrePregenerator n (fun z => T (ginibreMixedPolynomialEval P z)))
      2 (ginibreMeasure n) := by
  have hLap : MemLp (configurationLaplacian (fun z => T (ginibreMixedPolynomialEval P z)))
      2 (ginibreMeasure n) := by
    unfold configurationLaplacian
    apply memLp_finsetSum
    intro j hj
    exact (correspondencePolynomial_second_memLp hn P T _).add
      (correspondencePolynomial_second_memLp hn P T _)
  have hCon := memLp_finsetSum (s := Finset.univ)
    (fun j _ => correspondencePolynomial_confinement_memLp hn P T j)
  have hCoul : MemLp (fun z => ∑ j : Fin n, ∑ k ∈ Finset.Ioi j,
      fderiv ℝ (fun y => T (ginibreMixedPolynomialEval P y)) z (coulombPairDirection j k z))
      2 (ginibreMeasure n) := by
    apply memLp_finsetSum
    intro j hj
    apply memLp_finsetSum
    intro k hk
    exact correspondencePolynomial_coulomb_memLp hn P T j k (Finset.mem_Ioi.mp hk)
  exact ((hLap.const_mul _).sub (hCon.const_mul _)).add (hCoul.const_mul _)

end
end GinibrePoincare
