/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145PhysicalTraceResidue

/-!
C145: actual counting trace separates the ordinary H2 fiber through five modes.
Compile-free source proposal: no elaboration or axiom audit executed here.

The algebraic kernel permits arbitrary injective real residual rates, including
one zero rate. The accepted X^2 P argument supplies the trace-polynomial zero.
The physical corollaries retain both full orthonormal frames, both constant
grounds, and the common calibrated rates/a/c. Ground is retained in the accepted
full trace before taking the actual T Q1 a - T Q0 a difference.
-/

@[expose] public section

noncomputable section
namespace C145.H2
open MvPolynomial C145.ThreePlane
open scoped BigOperators
variable {n : ℕ}

/-- The boundary admissible quotient is a literal constant polynomial. -/
theorem admissible_four_eq_constant
    (R : P3) (hR : QAdmissible 4 R) :
    R = MvPolynomial.C (R.coeff 0) := by
  classical
  rcases hR with rfl | ⟨_, hDegree⟩
  · simp
  · have hDegreeZero : ∀ r : Fin 3, degreeOf r R ≤ 0 := by
      intro r
      simpa using hDegree r
    rw [MvPolynomial.C_apply]
    apply MvPolynomial.eq_monomial_of_support_subset_singleton
    intro m hm
    apply Finsupp.ext
    intro r
    change m r = 0
    have hmZero := (MvPolynomial.degreeOf_le_iff.mp (hDegreeZero r)) m hm
    omega

/-- The affine slope from public evaluations; no denominator is cancelled. -/
theorem tracePolynomial_constant_slope
    (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ) (k : ℝ) :
    (tracePolynomial a rates (MvPolynomial.C k)).eval 1 -
      (tracePolynomial a rates (MvPolynomial.C k)).eval 0 =
      k * ∑ j, 1 / (a j.succ ^ 2 * di rates j ^ 2) := by
  classical
  rw [tracePolynomial_eval, tracePolynomial_eval]
  simp only [MvPolynomial.eval_C]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [div_eq_mul_inv]
  ring

/-- A nonempty sum of positive squared-denominator weights kills the constant. -/
theorem tracePolynomial_constant_zero
    (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (hRates : Function.Injective rates)
    (ha : ∀ j : Fin n, a j.succ ≠ 0) (hn : 0 < n)
    (k : ℝ) (hP : tracePolynomial a rates (MvPolynomial.C k) = 0) :
    k = 0 := by
  classical
  have hWeight : 0 < ∑ j : Fin n, 1 / (a j.succ ^ 2 * di rates j ^ 2) := by
    apply Finset.sum_pos
    · intro j hj
      exact one_div_pos.mpr (mul_pos (sq_pos_of_ne_zero (ha j))
        (sq_pos_of_ne_zero (di_ne_zero rates hRates j)))
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hSlope := tracePolynomial_constant_slope a rates k
  have hProduct : k * (∑ j : Fin n, 1 / (a j.succ ^ 2 * di rates j ^ 2)) = 0 := by
    simpa only [hP, Polynomial.eval_zero, sub_self] using hSlope.symm
  exact (mul_eq_zero.mp hProduct).resolve_right (ne_of_gt hWeight)

/-- The small branch includes n=0 before a nonempty witness is introduced. -/
theorem small_trace_quotient_zero
    (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (hRates : Function.Injective rates)
    (ha : ∀ j : Fin n, a j.succ ≠ 0) (hn : n ≤ 4)
    (R : P3) (hR : QAdmissible n R)
    (hP : tracePolynomial a rates R = 0) :
    R = 0 := by
  by_cases hn3 : n ≤ 3
  · exact (admissible_small_iff_zero hn3 R).mp hR
  · have hn4 : n = 4 := by omega
    subst n
    have hConstant := admissible_four_eq_constant R hR
    have hPConstant : tracePolynomial a rates (MvPolynomial.C (R.coeff 0)) = 0 := by
      rw [← hConstant]
      exact hP
    have hk := tracePolynomial_constant_zero a rates hRates ha (by omega)
      (R.coeff 0) hPConstant
    calc
      R = MvPolynomial.C (R.coeff 0) := hConstant
      _ = 0 := by rw [hk, MvPolynomial.C_0]

/-- Exact intersection of the actual symmetric ordinary kernel and trace. -/
theorem small_ordinary_H2_counting_trace_kernel
    (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (hRates : Function.Injective rates)
    (ha : ∀ j : Fin n, a j.succ ≠ 0) (hn : n ≤ 4)
    (E : Tensor n) (hSym : FullSymTensor E) :
    (NullRegular rates E ∧ ResidualTraceFree a E) ↔ E = 0 := by
  constructor
  · intro h
    obtain ⟨R, hR, _⟩ :=
      (complete_ordinary_H2_counting_trace_kernel a rates hRates E hSym).mp h
    have hZero := small_trace_quotient_zero a rates hRates ha hn R hR.2.1 hR.2.2.2
    calc
      E = Res rates R := hR.2.2.1
      _ = 0 := by rw [hZero, res_zero]
  · rintro rfl
    constructor
    · intro s t hs ht hreg
      simp [H]
    · intro i
      simp [residualCountingTrace]

/-- Full calibrated physical tensor equality for total size n+1 ≤ 5. -/
theorem physical_small_H2_tensor_equality
    (μ : ℝ) (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (a : Fin (n + 1) → ℝ) (c : ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (ha : ∀ r, a r ≠ 0)
    (hG0 : ∀ v, Q0 v 0 = c) (hG1 : ∀ v, Q1 v 0 = c)
    (hn : n ≤ 4)
    (hH : SamePositive (fullRates μ rates)
      (C145PhysicalFrame.T Q0 a) (C145PhysicalFrame.T Q1 a)) :
    C145PhysicalFrame.T Q0 a = C145PhysicalFrame.T Q1 a := by
  obtain ⟨R, hR, _⟩ :=
    (physical_pair_H2_counting_trace_residue μ rates hRates hPos Q0 Q1 a c
      hQ0 hQ1 ha hG0 hG1).mp hH
  have hZero := small_trace_quotient_zero a rates hRates (fun j => ha j.succ)
    hn R hR.2.1 hR.2.2.2.2
  have hZeroExtension : groundZero (0 : Tensor n) = 0 := by
    funext i j k
    refine Fin.cases ?_ (fun x => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun y => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun z => ?_) k <;> rfl
  have hDifference := hR.2.2.1
  rw [hZero, res_zero, hZeroExtension] at hDifference
  exact (sub_eq_zero.mp hDifference).symm

/-- Cancel all three common nonzero modal factors in every full tensor entry. -/
theorem physical_small_H2_multiplication_equality
    (μ : ℝ) (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (a : Fin (n + 1) → ℝ) (c : ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (ha : ∀ r, a r ≠ 0)
    (hG0 : ∀ v, Q0 v 0 = c) (hG1 : ∀ v, Q1 v 0 = c)
    (hn : n ≤ 4)
    (hH : SamePositive (fullRates μ rates)
      (C145PhysicalFrame.T Q0 a) (C145PhysicalFrame.T Q1 a)) :
    C145PhysicalFrame.C Q0 = C145PhysicalFrame.C Q1 := by
  have hTensor := physical_small_H2_tensor_equality μ rates hRates hPos Q0 Q1 a c
    hQ0 hQ1 ha hG0 hG1 hn hH
  funext i j k
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (ha i) (ha j)) (ha k))
  have hEntry := congrArg (fun U : Tensor (n + 1) => U i j k) hTensor
  simpa only [C145PhysicalFrame.T] using hEntry

end C145.H2

end
