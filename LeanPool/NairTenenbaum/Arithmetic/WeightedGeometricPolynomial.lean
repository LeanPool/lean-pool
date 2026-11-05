/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.PowerSeries.Order

/-! # Finite geometric products and weighted multiplicity counts -/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

variable {ι : Type*} [Fintype ι]

theorem weightedMultiplicity_coordinate_le (w e : ι → ℕ) (hw : ∀ i, 0 < w i) (i : ι) :
    e i ≤ ∑ j, w j * e j := by
  exact (Nat.le_mul_of_pos_left _ (hw i)).trans (single_le_sum (f := fun j => w j * e j) (fun j _
      => Nat.zero_le _) (mem_univ i))

/-- The equivalence used to count multiplicity vectors of bounded weighted sum. -/
noncomputable def weightedMultiplicityBoundEquiv (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    {k N : ℕ} (hk : k ≤ N) :
    {e : ι → ℕ // ∑ i, w i * e i = k} ≃
      {e : ι → Fin (N + 1) // ∑ i, w i * (e i : ℕ) = k} where
  toFun e := ⟨fun i => ⟨e.1 i, by
    have H := weightedMultiplicity_coordinate_le w e.1 hw i
    rw [e.2] at H
    omega⟩, e.2⟩
  invFun e := ⟨fun i => (e.1 i : ℕ), e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite geometric polynomial encoding weighted multiplicities. -/
noncomputable def weightedGeometricPolynomial (w : ι → ℕ) (N : ℕ) : ℝ[X] :=
  ∏ i, ∑ j : Fin (N + 1), X ^ (w i * (j : ℕ))

/-- The product of the linear factors corresponding to the multiplicity weights. -/
noncomputable def weightedEulerPolynomial (w : ι → ℕ) : ℝ[X] :=
  ∏ i, (1 - X ^ w i)

theorem weightedGeometricPolynomial_coeff (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    {k N : ℕ} (hk : k ≤ N) :
    (weightedGeometricPolynomial w N).coeff k =
      (Nat.card {e : ι → ℕ // ∑ i, w i * e i = k} : ℝ) := by
  classical
  rw [Nat.card_congr (weightedMultiplicityBoundEquiv w hw hk)]
  unfold weightedGeometricPolynomial
  rw [Fintype.prod_sum]
  simp_rw [prod_pow_eq_pow_sum]
  simp [coeff_X_pow, Nat.card_eq_fintype_card, Fintype.card_subtype, eq_comm]

theorem weightedGeometricPolynomial_mul_euler (w : ι → ℕ) (N : ℕ) :
    weightedGeometricPolynomial w N * weightedEulerPolynomial w =
      ∏ i, (1 - X ^ (w i * (N + 1))) := by
  unfold weightedGeometricPolynomial weightedEulerPolynomial
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  simp_rw [pow_mul]
  rw [Fin.sum_univ_eq_sum_range]
  exact geom_sum_mul_neg (X ^ w i : ℝ[X]) (N + 1)

theorem weightedGeometricPolynomial_mul_euler_coeff (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    {k N : ℕ} (hk : k ≤ N) :
    (weightedGeometricPolynomial w N * weightedEulerPolynomial w).coeff k =
      (1 : ℝ[X]).coeff k := by
  rw [weightedGeometricPolynomial_mul_euler]
  have H := PowerSeries.coeff_mul_prod_one_sub_of_lt_order k univ (1 : PowerSeries ℝ)
    (fun i : ι => PowerSeries.X ^ (w i * (N + 1))) (by
      intro i _
      rw [PowerSeries.order_X_pow]
      exact_mod_cast (show k < w i * (N + 1) from
        lt_of_le_of_lt hk (lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_mul_of_pos_left _ (hw i)))))
  have HE : ((∏ i, (1 - X ^ (w i * (N + 1))) : ℝ[X]) : PowerSeries ℝ) =
      ∏ i, (1 - PowerSeries.X ^ (w i * (N + 1))) := by
    change Polynomial.coeToPowerSeries.ringHom (∏ i, (1 - X ^ (w i * (N + 1)))) = _
    rw [map_prod]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X]
  rw [← Polynomial.coeff_coe, ← Polynomial.coeff_coe, HE, Polynomial.coe_one]
  simpa only [one_mul] using H

end NairTenenbaum
