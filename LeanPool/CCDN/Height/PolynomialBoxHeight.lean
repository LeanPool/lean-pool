/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Height.IntegerCoefficientHeight
public import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-! Coefficient-height bounds for evaluating a polynomial on a bounded box.
The constants depend only on total degree and the number of variables. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma polynomial_support_card_le {R σ : Type*} [CommSemiring R] [Fintype σ]
    (f : MvPolynomial σ R) :
    f.support.card ≤ (f.totalDegree + 1) ^ Fintype.card σ := by
  classical
  have hb (e : σ →₀ ℕ) (he : e ∈ f.support) (i : σ) : e i ≤ f.totalDegree := by
    have hh := (degreeOf_le_iff.mp (le_refl (f.degreeOf i))) e he
    exact hh.trans (degreeOf_le_totalDegree f i)
  let ψ : {e // e ∈ f.support} → σ → Fin (f.totalDegree + 1) :=
    fun e i => ⟨e.val i, Nat.lt_succ_of_le (hb e.val e.property i)⟩
  have hi : Function.Injective ψ := by
    intro e e' h
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg (fun v => (v i).val) h
  simpa using Fintype.card_le_of_injective ψ hi

/-- An evaluation estimate with no coefficient-dependent constants. -/
theorem polynomial_eval₂_box_bound {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℤ) (H A : ℝ) (hH : 0 ≤ H) (hA : 1 ≤ A)
    (hf : CoefficientHeightLE f H)
    (v : σ → ℝ) (hv : ∀ i, |v i| ≤ A) :
    |eval₂ (Int.castRingHom ℝ) v f| ≤
      ((f.totalDegree : ℝ) + 1) ^ Fintype.card σ * H * A ^ f.totalDegree := by
  classical
  rw [eval₂_eq']
  calc
    |∑ e ∈ f.support, (Int.castRingHom ℝ) (f.coeff e) * ∏ i, v i ^ e i| ≤
        ∑ e ∈ f.support, |(Int.castRingHom ℝ) (f.coeff e) * ∏ i, v i ^ e i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ f.support, H * A ^ f.totalDegree := by
      apply Finset.sum_le_sum
      intro e he
      have hd : ∑ i, e i ≤ f.totalDegree := by
        simpa only [Finsupp.sum_fintype e (fun _ k => k) (fun _ => rfl)] using (le_totalDegree he)
      have hp : |∏ i, v i ^ e i| ≤ A ^ f.totalDegree := by
        rw [Finset.abs_prod]
        calc
          ∏ i, |v i ^ e i| ≤ ∏ i, A ^ e i := by
            apply Finset.prod_le_prod₀
            · intro i _
              exact abs_nonneg _
            · intro i _
              rw [abs_pow]
              exact pow_le_pow_left₀ (abs_nonneg _) (hv i) _
          _ = A ^ (∑ i, e i) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ A ^ f.totalDegree := pow_le_pow_right₀ hA hd
      rw [abs_mul]
      exact mul_le_mul (hf e) hp (abs_nonneg _) hH
    _ = (f.support.card : ℝ) * H * A ^ f.totalDegree := by simp; ring
    _ ≤ ((f.totalDegree : ℝ) + 1) ^ Fintype.card σ * H * A ^ f.totalDegree := by
      have hc : (f.support.card : ℝ) ≤ ((f.totalDegree : ℝ) + 1) ^ Fintype.card σ := by
        exact_mod_cast polynomial_support_card_le f
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hH)
        (pow_nonneg (by linarith) _)

end
end CCDN
