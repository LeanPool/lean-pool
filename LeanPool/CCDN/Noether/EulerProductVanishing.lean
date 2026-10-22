/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.EulerGenericFactors
import LeanPool.CCDN.ForMathlib.Matrix
import LeanPool.CCDN.Noether.EulerPairSpecialization

/-!
Characteristic-independent vanishing on products. A generic integral
identity is proved in the fraction field and then specialized; this includes
inseparable and repeated factors in every characteristic.

A nonzero Euler kernel vector forces every maximal universal
coefficient minor to vanish after specialization.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

private theorem eulerClosedForm_minor_eq_zero_of_kernel
    {F : Type*} [Field F] (k : ℕ) (f : Polynomial (Polynomial F))
    (u : EulerPairSpace F k) (hu : u ≠ 0)
    (hker : eulerClosedFormOperator k f u = 0)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k f).submatrix rows cols).det = 0 := by
  classical
  by_contra hdet
  let A := eulerClosedFormCoefficientMatrix k f
  have hlo : (k + 2) ^ 2 - 1 ≤ A.rank := A.le_rank_of_det_submatrix_ne_zero rows cols hdet
  have hr : A.rank = Fintype.card (EulerColumns k) := by
    apply le_antisymm (Matrix.rank_le_card_width _)
    simpa only [card_eulerColumns] using hlo
  have hi : LinearIndependent F A.col := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
      ← Matrix.rank_eq_finrank_span_cols, hr]
  let T := (bivariateCoefficients F).comp (eulerClosedFormOperator k f)
  have hsum : ∑ i, (eulerPairBasis F k).repr u i • A.col i = 0 := by
    have hh := congrArg T ((eulerPairBasis F k).sum_repr u)
    rw [map_sum] at hh
    simp only [map_smul] at hh
    change (∑ i, (eulerPairBasis F k).repr u i • A.col i) =
      bivariateCoefficients F (eulerClosedFormOperator k f u) at hh
    rw [hker, map_zero] at hh
    exact hh
  have hz := Fintype.linearIndependent_iff.mp hi _ hsum
  apply hu
  apply (eulerPairBasis F k).repr.injective
  ext i
  simpa only [map_zero, Finsupp.zero_apply] using hz i

end
end CCDN

namespace CCDN
noncomputable section
open Polynomial

private lemma bivariateMap_injective {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective (bivariateMap φ) :=
  Polynomial.map_injective _ (Polynomial.map_injective φ hφ)

private theorem genericEulerProduct_minor_eq_zero
    (k a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = k + 2)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k
      (genericEulerFactorLeft a b * genericEulerFactorRight a b)).submatrix rows cols).det = 0 := by
  let R := MvPolynomial (EulerFactorParameters a b) ℤ
  let F := FractionRing R
  let φ := algebraMap R F
  let G := genericEulerFactorLeft a b
  let H := genericEulerFactorRight a b
  have hφ := IsFractionRing.injective R F
  have hmap := bivariateMap_injective φ hφ
  have hg : bivariateTotalDegree (bivariateMap φ G) ≤ a :=
    (bivariateTotalDegree_map_le φ G).trans (eulerPolynomialFromCoefficients_degree a _)
  have hh : bivariateTotalDegree (bivariateMap φ H) ≤ b :=
    (bivariateTotalDegree_map_le φ H).trans (eulerPolynomialFromCoefficients_degree b _)
  have hne : eulerFactorPair a b (bivariateMap φ G) (bivariateMap φ H) ≠ 0 := by
    intro hz
    have he := eulerFactorPair_map φ a b G H
    rw [hz] at he
    apply genericEulerFactorPair_ne_zero a b ha hb
    apply Prod.ext
    · apply hmap
      simpa only [Prod.fst_zero, map_zero] using congrArg Prod.fst he
    · apply hmap
      simpa only [Prod.snd_zero, map_zero] using congrArg Prod.snd he
  obtain ⟨u, hu, hk⟩ := exists_eulerFactorKernel k a b ha hb hab
    (bivariateMap φ G) (bivariateMap φ H) hg hh hne
  have hz := eulerClosedForm_minor_eq_zero_of_kernel k _ u hu hk rows cols
  apply hφ
  rw [map_zero, eulerClosedForm_minor_map, map_mul]
  exact hz

/-- Every maximal Euler minor vanishes on a product with two positive
degree budgets, over an arbitrary commutative coefficient ring. -/
theorem eulerClosedForm_minor_eq_zero_of_product
    {R : Type*} [CommRing R] (k a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = k + 2)
    (g h : R[X][X]) (hg : bivariateTotalDegree g ≤ a)
    (hh : bivariateTotalDegree h ≤ b)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k (g * h)).submatrix rows cols).det = 0 := by
  let φ := genericEulerFactorSpecialization a b g h
  have hz := congrArg φ (genericEulerProduct_minor_eq_zero k a b ha hb hab rows cols)
  rw [map_zero, eulerClosedForm_minor_map, map_mul,
    genericEulerFactorLeft_specialize a b g h hg,
    genericEulerFactorRight_specialize a b g h hh] at hz
  exact hz

end
end CCDN
