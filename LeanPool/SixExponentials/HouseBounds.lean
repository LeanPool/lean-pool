/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.NumberTheory.NumberField.House
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Monotonicity.Lemmas

/-!
# Houses and denominators

Bounds on the house of products and monomials in a number field, with a common denominator.

From `SixExponentials/Basic/exists_denom_house_monomial_le.lean` of `carlok/six-exponentials-lean`;
see `LeanPool.SixExponentials` for provenance.
-/

@[expose] public section

namespace SixExponentials.Transcendence

/-!
# A common denominator with a house bound for monomials

Since `K` is algebraic over `ℤ`, one non-zero integer `b` makes every `b θᵢ` an algebraic integer.
If `∑ eᵢ ≤ E`, then `b ^ E ∏ θᵢ ^ eᵢ = b ^ (E - ∑ eᵢ) ∏ (b θᵢ) ^ eᵢ` is an algebraic integer, and as
the house is submultiplicative, its house is at most `H ^ E` for `H = 1 + house b + ∑ house (b θᵢ)`.
-/

open NumberField

namespace S7W4_exists_denom_house_monomial_le

/-- The house of a finite indexed product is at most the product of the houses. -/
lemma house_prod_le' {K ι : Type*} [Field K] [NumberField K] (s : Finset ι) (f : ι → K) :
    house (∏ i ∈ s, f i) ≤ ∏ i ∈ s, house (f i) := by
  simpa only [house, map_prod] using Finset.norm_prod_le s (fun i => canonicalEmbedding K (f i))

end S7W4_exists_denom_house_monomial_le

open S7W4_exists_denom_house_monomial_le in
theorem exists_denom_house_monomial_le {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
    (θ : ι → K) : ∃ b : K, b ≠ 0 ∧ IsIntegral ℤ b ∧ ∃ H : ℝ, 1 ≤ H ∧ ∀ (e : ι → ℕ) (E : ℕ),
      ∑ i, e i ≤ E →
        IsIntegral ℤ (b ^ E * ∏ i, θ i ^ e i) ∧ house (b ^ E * ∏ i, θ i ^ e i) ≤ H ^ E := by
  classical
  -- a non-zero integer clearing the denominators of all the `θ i`
  have : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
  obtain ⟨y, hy0, hy⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image θ)
  obtain ⟨b, hb0, hb, hbθ⟩ : ∃ b : K, b ≠ 0 ∧ IsIntegral ℤ b ∧ ∀ i, IsIntegral ℤ (b * θ i) :=
    ⟨y, Int.cast_ne_zero.mpr hy0, isIntegral_intCast y, fun i => by
      simpa only [zsmul_eq_mul] using hy (θ i) (Finset.mem_image_of_mem θ (Finset.mem_univ i))⟩
  -- one constant bounding `1`, `house b` and every `house (b * θ i)`
  set H : ℝ := 1 + house b + ∑ i, house (b * θ i) with hH
  have hs : 0 ≤ ∑ i, house (b * θ i) := Finset.sum_nonneg fun i _ => house_nonneg _
  have hH1 : 1 ≤ H := by linarith [house_nonneg b]
  have hHb : house b ≤ H := by linarith
  have hHθ (i : ι) : house (b * θ i) ≤ H := by
    linarith [house_nonneg b,
      Finset.single_le_sum (fun j _ => house_nonneg (b * θ j)) (Finset.mem_univ i)]
  have hpow (x : K) (h : house x ≤ H) (n : ℕ) : house (x ^ n) ≤ H ^ n := by
    simpa only [house, map_pow] using (norm_pow_le _ n).trans (pow_le_pow_left₀ (norm_nonneg _) h n)
  refine ⟨b, hb0, hb, H, hH1, fun e E hE => ?_⟩
  -- distribute the denominator over the monomial
  have key : b ^ E * ∏ i, θ i ^ e i = b ^ (E - ∑ i, e i) * ∏ i, (b * θ i) ^ e i := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hE]
  rw [key]
  refine ⟨(hb.pow _).mul (IsIntegral.prod _ fun i _ => (hbθ i).pow _), ?_⟩
  calc house (b ^ (E - ∑ i, e i) * ∏ i, (b * θ i) ^ e i)
      ≤ house (b ^ (E - ∑ i, e i)) * ∏ i, house ((b * θ i) ^ e i) :=
        (house_mul_le _ _).trans (mul_le_mul_of_nonneg_left (house_prod_le' _ _) (house_nonneg _))
    _ ≤ H ^ (E - ∑ i, e i) * ∏ i, H ^ e i := by
        -- written as norms, all the factors are visibly non-negative
        simp only [house]
        gcongr with i
        exacts [hpow b hHb _, hpow _ (hHθ i) _]
    _ = H ^ E := by rw [Finset.prod_pow_eq_pow_sum, ← pow_add, Nat.sub_add_cancel hE]

end SixExponentials.Transcendence
