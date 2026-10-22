/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.BombieriVaaler
public import LeanPool.CCDN.Algebra.HomogeneousMonomials
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import LeanPool.CCDN.Algebra.HomogeneousEvaluation
import LeanPool.CCDN.Algebra.HomogeneousRankDichotomy
import LeanPool.CCDN.Algebra.RowSelection
import LeanPool.CCDN.AuxiliaryPolynomial.CoefficientBound
import LeanPool.CCDN.Determinant.GramDeterminant

/-!
The exact-rank Bombieri--Vaaler comparison when no integral auxiliary
polynomial exists. This is the finite-matrix step of CCDN §3.3.

The arithmetic point is that a nonzero integer multiplier has a leading coefficient of
absolute value at least one. This is the coefficient obstruction used in CCDN §3.3.
The determinant bound needed to make the auxiliary polynomial small enough remains separate.
-/

@[expose] public section

namespace CCDN

private theorem abs_leadingCoeff_le_of_dvd {n : ℕ} (order : MonomialOrder (Fin n))
    {f g : MvPolynomial (Fin n) ℤ} (hg : g ≠ 0) (hfg : f ∣ g) :
    |order.leadingCoeff f| ≤ |order.leadingCoeff g| := by
  obtain ⟨q, rfl⟩ := hfg
  have hq : q ≠ 0 := by intro h; simp [h] at hg
  have hq1 := Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hq)
  rw [MonomialOrder.leadingCoeff_mul, abs_mul]
  nlinarith [abs_nonneg (order.leadingCoeff f)]

end CCDN

namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- Without an auxiliary polynomial, selected rows have exact Hilbert
rank and their Bombieri--Vaaler bound is at least the leading coefficient. -/
theorem homogeneous_no_auxiliary_comparison {n d M t : ℕ}
    (order : MonomialOrder (Fin (n + 1)))
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → ℤ)) (hzero : ∀ i, eval (points i) f = 0)
    (hrel : ∀ g : MvPolynomial (Fin (n + 1)) ℤ, g.IsHomogeneous M →
      (∀ i, eval (points i) g = 0) → f ∣ g) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧ s < (n + M).choose M ∧
      s + (n + (M - d)).choose (M - d) = (n + M).choose M ∧
      LinearIndependent ℚ
        ((evaluationMatrix (homogeneousMonomials n M) (points ∘ a)).map ((↑) : ℤ → ℚ)).row ∧
      |((order.leadingCoeff f : ℤ) : ℝ)| ≤
        (Real.sqrt (((evaluationMatrix (homogeneousMonomials n M) (points ∘ a) *
          (evaluationMatrix (homogeneousMonomials n M) (points ∘ a))ᵀ).det : ℤ) : ℝ) /
          (Int.Matrix.minorGcd (evaluationMatrix (homogeneousMonomials n M) (points ∘ a)) : ℝ)) ^
            ((((n + M).choose M : ℝ) - s)⁻¹) := by
  classical
  obtain ⟨s, a, ha, hli, hspan, hs⟩ :=
    homogeneous_independent_evaluation_rows f hf hf0 hdM points hzero
  let mon := homogeneousMonomials n M
  let A := evaluationMatrix mon (points ∘ a)
  obtain ⟨v, hv, hAv, hsmall⟩ :=
    Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow A hli (by simpa using hs)
  simp only [Fintype.card_fin] at hsmall
  let g := polynomialOfCoefficients mon v
  have hg0 : g ≠ 0 := polynomialOfCoefficients_ne_zero mon (homogeneousMonomials_injective n M) hv
  have hghom : g.IsHomogeneous M := polynomialOfCoefficients_homogeneous n M v
  have hgvan : ∀ i, eval (points i) g = 0 := by
    intro i
    apply vanishes_of_evaluation_row_mem_span mon (points ∘ a) v hAv (points i)
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hcoeff : ∀ e, |(g.coeff e : ℝ)| ≤
      (Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / (Int.Matrix.minorGcd A : ℝ)) ^
        ((((n + M).choose M : ℝ) - s)⁻¹) := by
    apply abs_coefficient_polynomialOfCoefficients_le mon (homogeneousMonomials_injective n M) v
    · apply Real.rpow_nonneg
      have hD := Int.Matrix.one_le_minorGcd hli
      change 1 ≤ Int.Matrix.minorGcd A at hD
      exact div_nonneg (Real.sqrt_nonneg _) (by exact_mod_cast (show (0 : ℤ) ≤ _ by omega))
    · intro j
      have hj : |v j| ≤ ⨆ k, |v k| := le_ciSup (Set.finite_range (fun k => |v k|)).bddAbove j
      have hjR : |(v j : ℝ)| ≤ ((⨆ k, |v k| : ℤ) : ℝ) := by exact_mod_cast hj
      exact hjR.trans hsmall
  have hr := integer_homogeneous_evaluation_rank_eq f hf hf0 hdM points hzero hrel
  have he : ((evaluationMatrix (homogeneousMonomials n M) points).map ((↑) : ℤ → ℚ)).rank = s := by
    rw [Matrix.rank_eq_finrank_span_row, ← hspan, ← Matrix.rank_eq_finrank_span_row,
      hli.rank_matrix, Fintype.card_fin]
  rw [he] at hr
  refine ⟨s, a, ha, hs, hr, hli, ?_⟩
  have hle : |((order.leadingCoeff f : ℤ) : ℝ)| ≤ |((order.leadingCoeff g : ℤ) : ℝ)| := by
    exact_mod_cast abs_leadingCoeff_le_of_dvd order hg0 (hrel g hghom hgvan)
  exact hle.trans (hcoeff (order.degree g))

/-- Logarithmic form of the coefficient obstruction. Positivity of the Gram
determinant follows from the positive coefficient bound itself. -/
lemma log_gcd_le_of_coefficient_bound {L G D k : ℝ}
    (hL : 0 < L) (hD : 0 < D) (hk : 0 < k)
    (hbound : L ≤ (Real.sqrt G / D) ^ k⁻¹) :
    0 < G ∧ Real.log D ≤ Real.log G / 2 - k * Real.log L := by
  have hsqrt : 0 < Real.sqrt G := by
    by_contra h
    have hz : Real.sqrt G = 0 := le_antisymm (le_of_not_gt h) (Real.sqrt_nonneg G)
    rw [hz, zero_div, Real.zero_rpow (inv_ne_zero hk.ne')] at hbound
    linarith
  have hG : 0 < G := Real.sqrt_pos.mp hsqrt
  have hbase : 0 < Real.sqrt G / D := div_pos hsqrt hD
  have hlog := Real.log_le_log hL hbound
  rw [Real.log_rpow hbase, Real.log_div hsqrt.ne' hD.ne', Real.log_sqrt hG.le] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hk.le
  rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul] at hmul
  exact ⟨hG, by linarith⟩

/-- The logarithmic determinant comparison with exact Hilbert rank, derived
from the absence of an auxiliary polynomial. -/
private theorem homogeneous_no_auxiliary_log_comparison {n d M t : ℕ}
    (order : MonomialOrder (Fin (n + 1)))
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → ℤ)) (hzero : ∀ i, eval (points i) f = 0)
    (hrel : ∀ g : MvPolynomial (Fin (n + 1)) ℤ, g.IsHomogeneous M →
      (∀ i, eval (points i) g = 0) → f ∣ g) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧ s < (n + M).choose M ∧
      s + (n + (M - d)).choose (M - d) = (n + M).choose M ∧
      LinearIndependent ℚ
        ((evaluationMatrix (homogeneousMonomials n M) (points ∘ a)).map ((↑) : ℤ → ℚ)).row ∧
      let A := evaluationMatrix (homogeneousMonomials n M) (points ∘ a)
      0 < (((A * Aᵀ).det : ℤ) : ℝ) ∧
      Real.log (Int.Matrix.minorGcd A : ℝ) ≤
        Real.log (((A * Aᵀ).det : ℤ) : ℝ) / 2 -
          (((n + M).choose M : ℝ) - s) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  obtain ⟨s, a, ha, hs, hr, hi, hb⟩ :=
    homogeneous_no_auxiliary_comparison order f hf hf0 hdM points hzero hrel
  refine ⟨s, a, ha, hs, hr, hi, ?_⟩
  apply log_gcd_le_of_coefficient_bound (hbound := hb)
  · exact abs_pos.mpr (by exact_mod_cast (order.leadingCoeff_ne_zero_iff.mpr hf0))
  · have hD := Int.Matrix.one_le_minorGcd hi
    exact_mod_cast (show (0 : ℤ) < _ by omega)
  · exact sub_pos.mpr (by exact_mod_cast hs)

/-- Archimedean logarithmic bound for an integral evaluation matrix. -/
lemma evaluation_log_gram_le {n N s M : ℕ} (hN : 0 < N)
    (mon : Fin N → (Fin n →₀ ℕ)) (points : Fin s → Fin n → ℤ)
    {B : ℝ} (hB : 1 ≤ B) (hp : ∀ i, InBox (points i) B)
    (hdeg : ∀ j, (mon j).degree ≤ M)
    (hG : 0 < (((evaluationMatrix mon points * (evaluationMatrix mon points)ᵀ).det : ℤ) : ℝ)) :
    Real.log (((evaluationMatrix mon points * (evaluationMatrix mon points)ᵀ).det : ℤ) : ℝ) / 2 ≤
      Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log N + s * M * Real.log B := by
  let A := evaluationMatrix mon points
  have he : (((A * Aᵀ).det : ℤ) : ℝ) = ((A.map ((↑) : ℤ → ℝ)) * (A.map ((↑) : ℤ → ℝ))ᵀ).det := by
    change (Int.castRingHom ℝ) (A * Aᵀ).det = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.mul_apply]
  have hbound := evaluation_gram_det_le mon points hB hp hdeg
  change |((A.map ((↑) : ℤ → ℝ)) * (A.map ((↑) : ℤ → ℝ))ᵀ).det| ≤ _ at hbound
  rw [← he, abs_of_pos hG] at hbound
  have hlog := Real.log_le_log hG hbound
  have hB0 : 0 < B := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hfact : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  rw [Real.log_mul hfact.ne' (pow_pos (mul_pos hN0 (sq_pos_of_pos (pow_pos hB0 M))) s).ne',
    Real.log_pow, Real.log_mul hN0.ne' (sq_pos_of_pos (pow_pos hB0 M)).ne',
    Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  nlinarith

/-- The archimedean half of the determinant-method inequality, for
bounded integer points and exact Hilbert rank. -/
theorem homogeneous_no_auxiliary_box_comparison {n d M t : ℕ}
    (order : MonomialOrder (Fin (n + 1)))
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → ℤ)) (hzero : ∀ i, eval (points i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hp : ∀ i, InBox (points i) B)
    (hrel : ∀ g : MvPolynomial (Fin (n + 1)) ℤ, g.IsHomogeneous M →
      (∀ i, eval (points i) g = 0) → f ∣ g) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧ s < (n + M).choose M ∧
      s + (n + (M - d)).choose (M - d) = (n + M).choose M ∧
      LinearIndependent ℚ
        ((evaluationMatrix (homogeneousMonomials n M) (points ∘ a)).map ((↑) : ℤ → ℚ)).row ∧
      Real.log (Int.Matrix.minorGcd
        (evaluationMatrix (homogeneousMonomials n M) (points ∘ a)) : ℝ) ≤
        Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((n + M).choose M) +
          s * M * Real.log B -
          (((n + M).choose M : ℝ) - s) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  obtain ⟨s, a, ha, hs, hr, hi, hG, hlog⟩ :=
    homogeneous_no_auxiliary_log_comparison order f hf hf0 hdM points hzero hrel
  refine ⟨s, a, ha, hs, hr, hi, ?_⟩
  have hb := evaluation_log_gram_le (by omega : 0 < (n + M).choose M)
    (homogeneousMonomials n M) (points ∘ a) hB (fun i j => hp (a i) j)
    (fun j => (homogeneousMonomials_degree n M j).le) hG
  linarith

end
end CCDN
