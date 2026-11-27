/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145H2NumeratorData
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
C145: literal finite H1 data determine visible simple positive modes.

The two finite sizes start unrelated. Each rate family's injection, positive
rates, and each residue's nonvanishing are explicit source-class assumptions.
One cleared polynomial identity gives both rate matches and, by its formal
derivative, actual residues. The modal bijection and equal size are derived.
Positive overlap orientation is explicit. The strict-known-mu corollary fixes
only the ground modal index; H1 does not determine signed beta or the constant
ground column. In the accepted fullRates convention, successors are physical
rates, never mu plus physical rates. Empty finite families remain algebraic.
-/

@[expose] public section

noncomputable section
namespace C145.H1
open scoped BigOperators

/-- The first transfer function as simple fractions with specified modal weights. -/
def weightedTransfer {N : ℕ}
    (rates weights : Fin N → ℝ) (s : ℝ) : ℝ :=
  ∑ i, weights i / (s + rates i)

/-- The first transfer function with squared modal overlaps as its weights. -/
def firstTransfer {N : ℕ}
    (rates a : Fin N → ℝ) (s : ℝ) : ℝ :=
  weightedTransfer rates (fun i => a i ^ 2) s

/-- The common-denominator numerator of the weighted first transfer function. -/
def numerator {N : ℕ}
    (rates weights : Fin N → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (weights i) * C145.H2.Li rates i

private theorem denominator_eval_node {N : ℕ}
    (rates : Fin N → ℝ) (i : Fin N) :
    (C145.H2.D rates).eval (-rates i) = 0 := by
  rw [C145.H2.eval_D_factor rates i (-rates i)]
  simp

private theorem numerator_eval_node {N : ℕ}
    (rates weights : Fin N → ℝ) (i : Fin N) :
    (numerator rates weights).eval (-rates i) =
      weights i * C145.H2.di rates i := by
  classical
  simp [numerator, Polynomial.eval_finsetSum, C145.H2.eval_Li_grid]

private theorem clear_denominator {N : ℕ}
    (rates weights : Fin N → ℝ) (s : ℝ)
    (hRegular : ∀ i, s + rates i ≠ 0) :
    (numerator rates weights).eval s =
      (C145.H2.D rates).eval s * weightedTransfer rates weights s := by
  classical
  simp only [numerator, Polynomial.eval_finsetSum, Polynomial.eval_C_mul,
    weightedTransfer, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [C145.H2.eval_D_factor rates i s]
  field_simp [hRegular i]


private theorem cross_identity {M N : ℕ}
    (rates0 weights0 : Fin M → ℝ)
    (rates1 weights1 : Fin N → ℝ)
    (hPos0 : ∀ i, 0 < rates0 i)
    (hPos1 : ∀ j, 0 < rates1 j)
    (hData : ∀ s : ℝ, 0 < s →
      weightedTransfer rates0 weights0 s = weightedTransfer rates1 weights1 s) :
    numerator rates0 weights0 * C145.H2.D rates1 =
      numerator rates1 weights1 * C145.H2.D rates0 := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.Ioi_infinite (0 : ℝ))
  intro s hs
  change (numerator rates0 weights0 * C145.H2.D rates1).eval s =
    (numerator rates1 weights1 * C145.H2.D rates0).eval s
  rw [Polynomial.eval_mul, Polynomial.eval_mul,
    clear_denominator rates0 weights0 s
      (fun i => ne_of_gt (add_pos hs (hPos0 i))),
    clear_denominator rates1 weights1 s
      (fun j => ne_of_gt (add_pos hs (hPos1 j))), hData s hs]
  ring

private theorem rate_match_of_cross {M N : ℕ}
    (rates0 weights0 : Fin M → ℝ)
    (rates1 weights1 : Fin N → ℝ)
    (hRates0 : Function.Injective rates0)
    (hWeights0 : ∀ i, weights0 i ≠ 0)
    (hCross : numerator rates0 weights0 * C145.H2.D rates1 =
      numerator rates1 weights1 * C145.H2.D rates0)
    (i : Fin M) :
    ∃ j : Fin N, rates1 j = rates0 i := by
  classical
  have hNode := congrArg (fun P : Polynomial ℝ => P.eval (-rates0 i)) hCross
  rw [Polynomial.eval_mul, Polynomial.eval_mul, numerator_eval_node,
    denominator_eval_node rates0 i, mul_zero] at hNode
  have hDen : (C145.H2.D rates1).eval (-rates0 i) = 0 :=
    (mul_eq_zero.mp hNode).resolve_left
      (mul_ne_zero (hWeights0 i) (C145.H2.di_ne_zero rates0 hRates0 i))
  have hProd : (∏ j : Fin N, (-rates0 i + rates1 j)) = 0 := by
    simpa only [C145.H2.D, Polynomial.eval_prod, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C] using hDen
  obtain ⟨j, hj, hZero⟩ := Finset.prod_eq_zero_iff.mp hProd
  exact ⟨j, by linarith⟩

private theorem matched_weight_eq_of_cross {M N : ℕ}
    (rates0 weights0 : Fin M → ℝ)
    (rates1 weights1 : Fin N → ℝ)
    (hRates0 : Function.Injective rates0)
    (hRates1 : Function.Injective rates1)
    (hCross : numerator rates0 weights0 * C145.H2.D rates1 =
      numerator rates1 weights1 * C145.H2.D rates0)
    (i : Fin M) (j : Fin N) (hMatch : rates1 j = rates0 i) :
    weights1 j = weights0 i := by
  have hNode0 := denominator_eval_node rates0 i
  have hNode1 : (C145.H2.D rates1).eval (-rates0 i) = 0 := by
    rw [← hMatch]
    exact denominator_eval_node rates1 j
  have hNum1 : (numerator rates1 weights1).eval (-rates0 i) =
      weights1 j * C145.H2.di rates1 j := by
    rw [← hMatch]
    exact numerator_eval_node rates1 weights1 j
  have hDeriv1 : (C145.H2.D rates1).derivative.eval (-rates0 i) =
      C145.H2.di rates1 j := by
    rw [← hMatch]
    exact C145.H2.eval_derivative_D_node rates1 j
  have hDerivative :=
    congrArg (fun P : Polynomial ℝ => P.derivative.eval (-rates0 i)) hCross
  simp only [Polynomial.derivative_mul, Polynomial.eval_add,
    Polynomial.eval_mul, hNode0, hNode1, mul_zero, zero_add] at hDerivative
  rw [numerator_eval_node, hNum1, C145.H2.eval_derivative_D_node,
    hDeriv1] at hDerivative
  apply mul_right_cancel₀
    (mul_ne_zero (C145.H2.di_ne_zero rates0 hRates0 i)
      (C145.H2.di_ne_zero rates1 hRates1 j))
  calc
    weights1 j * (C145.H2.di rates0 i * C145.H2.di rates1 j) =
        (weights1 j * C145.H2.di rates1 j) * C145.H2.di rates0 i := by ring
    _ = (weights0 i * C145.H2.di rates0 i) * C145.H2.di rates1 j :=
      hDerivative.symm
    _ = weights0 i * (C145.H2.di rates0 i * C145.H2.di rates1 j) := by ring

/-- Exact visible simple-mode identification from the actual positive-s sums.
Real signed residues are allowed; only their nonvanishing is assumed. -/
theorem nonzero_weights_modal_identification {M N : ℕ}
    (rates0 weights0 : Fin M → ℝ)
    (rates1 weights1 : Fin N → ℝ)
    (hRates0 : Function.Injective rates0)
    (hRates1 : Function.Injective rates1)
    (hPos0 : ∀ i, 0 < rates0 i)
    (hPos1 : ∀ j, 0 < rates1 j)
    (hWeights0 : ∀ i, weights0 i ≠ 0)
    (hWeights1 : ∀ j, weights1 j ≠ 0)
    (hData : ∀ s : ℝ, 0 < s →
      weightedTransfer rates0 weights0 s = weightedTransfer rates1 weights1 s) :
    ∃ e : Fin M ≃ Fin N,
      M = N ∧
      (∀ i, rates1 (e i) = rates0 i) ∧
      (∀ i, weights1 (e i) = weights0 i) := by
  classical
  have hCross := cross_identity rates0 weights0 rates1 weights1 hPos0 hPos1 hData
  have hForward (i : Fin M) : ∃ j : Fin N, rates1 j = rates0 i :=
    rate_match_of_cross rates0 weights0 rates1 weights1 hRates0 hWeights0 hCross i
  have hBackward (j : Fin N) : ∃ i : Fin M, rates0 i = rates1 j :=
    rate_match_of_cross rates1 weights1 rates0 weights0 hRates1 hWeights1 hCross.symm j
  let p : Fin M → Fin N := fun i => Classical.choose (hForward i)
  have hp (i : Fin M) : rates1 (p i) = rates0 i :=
    Classical.choose_spec (hForward i)
  have hInjective : Function.Injective p := by
    intro i k h
    apply hRates0
    calc
      rates0 i = rates1 (p i) := (hp i).symm
      _ = rates1 (p k) := congrArg rates1 h
      _ = rates0 k := hp k
  have hSurjective : Function.Surjective p := by
    intro j
    obtain ⟨i, hi⟩ := hBackward j
    refine ⟨i, hRates1 ?_⟩
    exact (hp i).trans hi
  let e : Fin M ≃ Fin N := Equiv.ofBijective p ⟨hInjective, hSurjective⟩
  have heRates (i : Fin M) : rates1 (e i) = rates0 i := hp i
  refine ⟨e, ?_, heRates, ?_⟩
  · simpa only [Fintype.card_fin] using Fintype.card_congr e
  · intro i
    exact matched_weight_eq_of_cross rates0 weights0 rates1 weights1
      hRates0 hRates1 hCross i (e i) (heRates i)

/-- H1 identifies squared overlaps before any eigenvector orientation. -/
theorem overlap_squares_modal_identification {M N : ℕ}
    (rates0 a0 : Fin M → ℝ)
    (rates1 a1 : Fin N → ℝ)
    (hRates0 : Function.Injective rates0)
    (hRates1 : Function.Injective rates1)
    (hPos0 : ∀ i, 0 < rates0 i)
    (hPos1 : ∀ j, 0 < rates1 j)
    (ha0 : ∀ i, a0 i ≠ 0)
    (ha1 : ∀ j, a1 j ≠ 0)
    (hData : ∀ s : ℝ, 0 < s →
      firstTransfer rates0 a0 s = firstTransfer rates1 a1 s) :
    ∃ e : Fin M ≃ Fin N,
      M = N ∧
      (∀ i, rates1 (e i) = rates0 i) ∧
      (∀ i, a1 (e i) ^ 2 = a0 i ^ 2) := by
  exact nonzero_weights_modal_identification rates0 (fun i => a0 i ^ 2)
    rates1 (fun j => a1 j ^ 2) hRates0 hRates1 hPos0 hPos1
    (fun i => ne_of_gt (sq_pos_of_ne_zero (ha0 i)))
    (fun j => ne_of_gt (sq_pos_of_ne_zero (ha1 j))) hData

/-- Positive orientation is an explicit assumption in each representation. -/
theorem positive_overlap_modal_identification {M N : ℕ}
    (rates0 a0 : Fin M → ℝ)
    (rates1 a1 : Fin N → ℝ)
    (hRates0 : Function.Injective rates0)
    (hRates1 : Function.Injective rates1)
    (hPos0 : ∀ i, 0 < rates0 i)
    (hPos1 : ∀ j, 0 < rates1 j)
    (ha0 : ∀ i, 0 < a0 i)
    (ha1 : ∀ j, 0 < a1 j)
    (hData : ∀ s : ℝ, 0 < s →
      firstTransfer rates0 a0 s = firstTransfer rates1 a1 s) :
    ∃ e : Fin M ≃ Fin N,
      M = N ∧
      (∀ i, rates1 (e i) = rates0 i) ∧
      (∀ i, a1 (e i) = a0 i) := by
  obtain ⟨e, hCard, hRates, hSquares⟩ :=
    overlap_squares_modal_identification rates0 a0 rates1 a1
      hRates0 hRates1 hPos0 hPos1 (fun i => ne_of_gt (ha0 i))
      (fun j => ne_of_gt (ha1 j)) hData
  refine ⟨e, hCard, hRates, ?_⟩
  intro i
  apply (mul_self_inj (le_of_lt (ha1 (e i))) (le_of_lt (ha0 i))).mp
  simpa only [pow_two] using hSquares i

/-- A known strict ground minimum identifies its modal index only. -/
theorem known_ground_positive_modal_identification {m n : ℕ}
    (μ : ℝ) (hμ : 0 < μ)
    (rates0 a0 : Fin (m + 1) → ℝ)
    (rates1 a1 : Fin (n + 1) → ℝ)
    (hRates0 : Function.Injective rates0)
    (hRates1 : Function.Injective rates1)
    (hGround0 : rates0 0 = μ)
    (hGround1 : rates1 0 = μ)
    (hAbove0 : ∀ i : Fin m, μ < rates0 i.succ)
    (hAbove1 : ∀ j : Fin n, μ < rates1 j.succ)
    (ha0 : ∀ i, 0 < a0 i)
    (ha1 : ∀ j, 0 < a1 j)
    (hData : ∀ s : ℝ, 0 < s →
      firstTransfer rates0 a0 s = firstTransfer rates1 a1 s) :
    ∃ e : Fin (m + 1) ≃ Fin (n + 1),
      m = n ∧ e 0 = 0 ∧
      (∀ i, rates1 (e i) = rates0 i) ∧
      (∀ i, a1 (e i) = a0 i) := by
  have hPos0 : ∀ i, 0 < rates0 i := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
    · rw [h, hGround0]
      exact hμ
    · rw [h]
      exact lt_trans hμ (hAbove0 j)
  have hPos1 : ∀ j, 0 < rates1 j := by
    intro j
    rcases Fin.eq_zero_or_eq_succ j with h | ⟨k, h⟩
    · rw [h, hGround1]
      exact hμ
    · rw [h]
      exact lt_trans hμ (hAbove1 k)
  obtain ⟨e, hCard, hRates, hOverlaps⟩ :=
    positive_overlap_modal_identification rates0 a0 rates1 a1
      hRates0 hRates1 hPos0 hPos1 ha0 ha1 hData
  have hGroundIndex : e 0 = 0 := by
    rcases Fin.eq_zero_or_eq_succ (e 0) with h | ⟨j, h⟩
    · exact h
    · have hRateAt : rates1 j.succ = μ := by
        calc
          rates1 j.succ = rates1 (e 0) := by rw [h]
          _ = rates0 0 := hRates 0
          _ = μ := hGround0
      exact False.elim ((ne_of_gt (hAbove1 j)) hRateAt)
  exact ⟨e, Nat.succ.inj hCard, hGroundIndex, hRates, hOverlaps⟩

/-- Literal H1 is insensitive to global reversal of all overlap signs. -/
theorem firstTransfer_neg {N : ℕ}
    (rates a : Fin N → ℝ) (s : ℝ) :
    firstTransfer rates (fun i => -a i) s = firstTransfer rates a s := by
  have hSquare (i : Fin N) : (-a i) ^ 2 = a i ^ 2 := by ring
  simp only [firstTransfer, weightedTransfer, hSquare]


end C145.H1
end

end
