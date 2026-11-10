/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Series.PSeries
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

/-!
# Zeros of power series in the open unit disk

A power series `h ∈ O⟦X⟧` whose reduction `h_bar` modulo the maximal ideal is nonzero has
at most `ord h_bar` zeros in the maximal ideal (`ChabautyColeman.PSeries.zeros_le_ord`,
with finiteness `ChabautyColeman.PSeries.finite_setOf_eval_eq_zero`); indeed its zeros
are exactly the roots of the distinguished factor of its Weierstrass factorization
(`ChabautyColeman.PSeries.setOf_eval_eq_zero_eq`), all of which lie in the maximal
ideal, and there are at most `deg W = ord h_bar` of them. The key input from evaluation
calculus is that values of a power series lie in the residue class of the constant
coefficient (`ChabautyColeman.PSeries.eval_sub_constantCoeff_mem`), so units of `O⟦X⟧`
do not vanish on the maximal ideal.

Blueprint node: `cor:wprep-count`.
-/

@[expose] public section

open PowerSeries IsLocalRing Polynomial

namespace ChabautyColeman

namespace PSeries

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- Roots of a distinguished polynomial lie in the maximal ideal. -/
theorem mem_maximalIdeal_of_isRoot {W : Polynomial O}
    (hW : W.IsDistinguishedAt (maximalIdeal O)) {z : O} (hz : W.IsRoot z) :
    z ∈ maximalIdeal O := by
  refine (maximalIdeal.isMaximal O).isPrime.mem_of_pow_mem W.natDegree ?_
  rw [IsRoot, eval_eq_sum_range, Finset.sum_range_succ, hW.monic.coeff_natDegree,
    one_mul] at hz
  have hsum : ∑ i ∈ Finset.range W.natDegree, W.coeff i * z ^ i ∈ maximalIdeal O :=
    Submodule.sum_mem _ fun i hi ↦
      Ideal.mul_mem_right _ _ (hW.mem (Finset.mem_range.mp hi))
  have : z ^ W.natDegree = -∑ i ∈ Finset.range W.natDegree, W.coeff i * z ^ i := by
    linear_combination hz
  rw [this]
  exact neg_mem hsum

/-- The degree of the distinguished factor is the vanishing order of the reduction. -/
theorem natDegree_eq_order_map {h : O⟦X⟧} {W : Polynomial O} {u : O⟦X⟧}
    (hfac : h.IsWeierstrassFactorization W u) :
    (W.natDegree : ℕ∞) = (h.map (residue O)).order := by
  have hne : PowerSeries.constantCoeff u ∉ maximalIdeal O := fun hmem ↦
    hmem (isUnit_constantCoeff u hfac.isUnit)
  have hdeg := hfac.isDistinguishedAt.degree_eq_coe_lift_order_map h u hne hfac.eq_mul
  rw [degree_eq_natDegree hfac.isDistinguishedAt.monic.ne_zero] at hdeg
  have h2 : W.natDegree = ((h.map (Ideal.Quotient.mk (maximalIdeal O))).order).lift
      (PowerSeries.order_finite_iff_ne_zero.2
        (hfac.isDistinguishedAt.map_ne_zero_of_eq_mul h u hne hfac.eq_mul)) :=
    mod_cast hdeg
  rw [h2, ENat.natCast_lift]
  rfl

variable [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

variable {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O)

include hz₀ in
/-- Units of the power series ring do not vanish on the maximal ideal. -/
theorem isUnit_eval_of_isUnit {u : O⟦X⟧} (hu : IsUnit u) : IsUnit (eval z₀ u) := by
  by_contra hne
  have h2 : constantCoeff u ∈ maximalIdeal O := by
    simpa using Ideal.sub_mem _ ((mem_maximalIdeal _).mpr hne) (eval_sub_constantCoeff_mem hz₀ u)
  exact h2 (isUnit_constantCoeff u hu)

variable {h : O⟦X⟧} {W : Polynomial O} {u : O⟦X⟧}

/-- The zeros of `h` in the maximal ideal are exactly the roots of the distinguished
factor `W` of its Weierstrass factorization. -/
theorem setOf_eval_eq_zero_eq (hfac : h.IsWeierstrassFactorization W u) :
    {z ∈ maximalIdeal O | eval z h = 0} = {z | W.IsRoot z} := by
  ext z
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz, h0⟩
    rw [hfac.eq_mul, eval_mul hz, eval_coe] at h0
    exact (IsUnit.mul_left_eq_zero (isUnit_eval_of_isUnit hz hfac.isUnit)).mp h0
  · intro hroot
    have hz := mem_maximalIdeal_of_isRoot hfac.isDistinguishedAt hroot
    refine ⟨hz, ?_⟩
    rw [hfac.eq_mul, eval_mul hz, eval_coe, hroot.eq_zero, zero_mul]

/-- The number of zeros of `h` in the maximal ideal is bounded by the degree of the
distinguished factor of its Weierstrass factorization. -/
theorem ncard_setOf_eval_eq_zero_le [IsDomain O]
    (hfac : h.IsWeierstrassFactorization W u) :
    {z ∈ maximalIdeal O | eval z h = 0}.ncard ≤ W.natDegree := by
  classical
  have hW0 : W ≠ 0 := hfac.isDistinguishedAt.monic.ne_zero
  rw [setOf_eval_eq_zero_eq hfac]
  have hset : {z | W.IsRoot z} = ↑W.roots.toFinset := by
    ext z
    simp [Multiset.mem_toFinset, mem_roots hW0]
  rw [hset, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans (W.card_roots')

/-- A power series with nonzero reduction has finitely many zeros in the maximal
ideal. -/
theorem finite_setOf_eval_eq_zero [IsDomain O] (hh : h.map (residue O) ≠ 0) :
    {z ∈ maximalIdeal O | eval z h = 0}.Finite := by
  have hfac := h.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hh
  rw [setOf_eval_eq_zero_eq hfac]
  exact finite_setOfPred_isRoot hfac.isDistinguishedAt.monic.ne_zero

/-- Blueprint node `cor:wprep-count`: a power series with nonzero reduction `h_bar` has at
most `ord h_bar` zeros in the maximal ideal. -/
theorem zeros_le_ord [IsDomain O] (hh : h.map (residue O) ≠ 0) :
    {z ∈ maximalIdeal O | eval z h = 0}.ncard ≤ (h.map (residue O)).order.toNat := by
  have hfac := h.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hh
  have hdeg : (h.weierstrassDistinguished hh).natDegree = (h.map (residue O)).order.toNat := by
    rw [← natDegree_eq_order_map hfac]
    simp
  exact hdeg ▸ ncard_setOf_eval_eq_zero_le hfac

end PSeries

end ChabautyColeman

end
