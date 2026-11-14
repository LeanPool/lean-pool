/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.MainTermLowerBound
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentScales
public import LeanPool.NairTenenbaum.Sieve.SieveCutoffComparison

/-! # The sifted small-divisor sum bounded by the original main term -/

@[expose] public section

namespace NairTenenbaum

open Polynomial

/-- The main term for prime arguments, including the logarithm and constant-term correction. -/
noncomputable def primeMainTerm {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (x y : ℝ) : ℝ :=
  mainTerm P F x y * primeArgumentFactor P.total x

/-- The main expression in Theorem 3, with its constant-term correction and
reciprocal logarithm displayed explicitly. -/
theorem primeMainTerm_eq {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (x y : ℝ) :
    primeMainTerm P F x y =
      (((P.total.eval 0).natAbs : ℝ) / (P.total.eval 0).natAbs.totient) *
        (y / Real.log x) * sieveProduct P.total x * ∑ n ∈ positiveUpTo x, P.weight F n := by
  simp only [primeMainTerm, mainTerm, primeArgumentFactor, totientTwist, pow_one]
  ring

theorem primeArgumentFactor_rpow (Q : ℤ[X]) {x : ℝ} (hx : 0 < x) (α : ℝ) :
    primeArgumentFactor Q (x ^ α) = primeArgumentFactor Q x / α := by
  unfold primeArgumentFactor
  rw [Real.log_rpow hx]
  ring

theorem primeMainTerm_nonneg {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) :
    0 ≤ primeMainTerm P F x y :=
  mul_nonneg (mainTerm_nonneg P hF x hy) (primeArgumentFactor_nonneg P.total hx)

/-- The power-saving exceptional classes remain negligible after introducing
the reciprocal logarithm. The constant is independent of `Q(0)`. -/
theorem exists_powerSaving_le_primeMainTerm (g : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree ≤ g →
      P.total.eval 0 ≠ 0 → ∀ (F : ArithmeticMap k), (∀ n, 0 ≤ F n) →
      ∀ x y : ℝ, 2 ≤ x → 0 ≤ y → y * x ^ (-δ) * F 1 ≤ C * primeMainTerm P F x y := by
  obtain ⟨C, hC, H⟩ := exists_sieveProduct_inv_mul_log_le_rpow g hδ
  refine ⟨C, hC, ?_⟩
  intro k r P hdeg hzero F hF x y hx hy
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hS : 0 < sieveProduct P.total x := sieveProduct_pos P.noFixedPrime x
  have H' := mul_le_mul_of_nonneg_right (H P.total P.noFixedPrime hdeg x hx)
    (mul_nonneg (Real.rpow_nonneg hx0.le (-δ)) hS.le)
  have hcancel : x ^ δ * x ^ (-δ) = 1 := by rw [← Real.rpow_add hx0]; simp
  have hleft : ((sieveProduct P.total x)⁻¹ * Real.log x) *
      (x ^ (-δ) * sieveProduct P.total x) = x ^ (-δ) * Real.log x := by field_simp [hS.ne']
  have hright : C * x ^ δ * (x ^ (-δ) * sieveProduct P.total x) =
      C * sieveProduct P.total x := by
    calc
      _ = C * (x ^ δ * x ^ (-δ)) * sieveProduct P.total x := by ring
      _ = _ := by rw [hcancel, mul_one]
  rw [hleft, hright] at H'
  have Hbase : x ^ (-δ) ≤ C * sieveProduct P.total x / Real.log x :=
    (le_div_iff₀ hlog).mpr H'
  have Hfactor : x ^ (-δ) ≤ C * sieveProduct P.total x * primeArgumentFactor P.total x := by
    calc
      _ ≤ C * sieveProduct P.total x / Real.log x := Hbase
      _ ≤ (C * sieveProduct P.total x / Real.log x) *
          totientTwist 1 (P.total.eval 0).natAbs :=
        le_mul_of_one_le_right (div_nonneg (mul_nonneg (zero_le_one.trans hC) hS.le) hlog.le)
          (totientTwist_one_le _ (Int.natAbs_ne_zero.mpr hzero))
      _ = _ := by unfold primeArgumentFactor; ring
  have Hsum := mul_le_mul Hfactor
    (P.value_one_le_weight_sum hF (x := x) (by linarith)) (hF 1)
    (mul_nonneg (mul_nonneg (zero_le_one.trans hC) hS.le)
      (primeArgumentFactor_nonneg P.total (by linarith)))
  have Hfinal := mul_le_mul_of_nonneg_left Hsum hy
  simpa only [primeMainTerm, mainTerm, mul_assoc, mul_comm, mul_left_comm] using Hfinal

theorem primeArgumentSmallSieveCost_pos {B : ℝ} (hB : 0 < B) (σ : ℝ)
    {g D : ℕ} (hg : 0 < g) (hD : 0 < D) : 0 < primeArgumentSmallSieveCost B σ g D := by
  unfold primeArgumentSmallSieveCost primeArgumentBadSieveCost
  exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one (totientTwist_one_le (g + 1) (by omega)))
    (badPrimeMassBound_pos hB hg hD)) (totientExponentComparisonBound_pos B σ g (g + 1) D)

/-- The sifted small-divisor sum is bounded by the paper's original main term.
The constants precede the polynomial family and arithmetic function. The interval
endpoint hypotheses allow the natural rounding of a real interval. -/
theorem exists_primeSmallDivisorSiftedSum_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {ε : ℝ} (hε : 0 < ε) (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) :
    ∃ K x₀ : ℝ, 0 < K ∧ 1 ≤ x₀ ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree = g → P.total.eval 0 ≠ 0 → ∀ (A B σ : ℝ) (F : ArithmeticMap k),
      Admissible A B σ F → 0 ≤ A → 1 ≤ B → 0 < σ → (g : ℝ) ^ 2 * σ ≤ 1 / 8 →
      ∀ (x y : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      P.primeSmallDivisorSiftedSum F g N a b (x ^ ((g : ℝ) * ε / 16)) ≤
        K * primeArgumentSmallSieveCost B σ g P.badDiscriminant * primeMainTerm P F x y := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hα : 0 < (g : ℝ) * ε / 16 := by positivity
  have hα₁ : (g : ℝ) * ε / 16 ≤ 1 := by
    nlinarith [mul_nonneg hε.le (mul_nonneg (show (0 : ℝ) ≤ g by positivity)
      (sub_nonneg.mpr hg₁))]
  obtain ⟨K, x₁, hK, hx₁, H⟩ := exists_primeSmallDivisorSiftedSum_at_scales hg hε
  obtain ⟨x₂, hx₂, Hcut⟩ := exists_sieveProduct_power_cutoff_bound g hα hα₁
  let E := Real.exp (4 * (g : ℝ) * Real.log 4 / ((g : ℝ) * ε / 16))
  refine ⟨2 * K * E / ((g : ℝ) * ε / 16), max x₁ x₂, by dsimp [E]; positivity,
    hx₁.trans (le_max_left _ _), ?_⟩
  intro k r P hdeg hzero A B σ F hF hA hB hσ hσsmall x y N a b hx hN hy hab hlength hlength'
  have hx' : 1 ≤ x := hx₁.trans ((le_max_left _ _).trans hx)
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by linarith : 0 ≤ x) _).trans hy
  have hN' : (N : ℝ) ≤ x := hN.trans (by
    have he : 3 * (g : ℝ) ^ 2 * ε ≤ 1 := by linarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx' he)
  have hsum : (∑ n ∈ Finset.Icc 1 N, P.weight F n) ≤
      ∑ n ∈ positiveUpTo x, P.weight F n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      apply (mem_positiveUpTo n x).mpr
      exact (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ N).trans hN'
    · intro n _ _
      exact P.weight_nonneg hF.nonneg n
  have hs₀ : 0 ≤ ∑ n ∈ Finset.Icc 1 N, P.weight F n :=
    Finset.sum_nonneg (fun n _ => P.weight_nonneg hF.nonneg n)
  have hcost := (primeArgumentSmallSieveCost_pos (lt_of_lt_of_le zero_lt_one hB) σ hg
      P.badDiscriminant_pos).le
  have hKC : 0 ≤ K * primeArgumentSmallSieveCost B σ g P.badDiscriminant :=
    mul_nonneg (zero_le_one.trans hK) hcost
  have hS := Hcut x ((le_max_right _ _).trans hx) P.total P.noFixedPrime hdeg.le
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have H' := mul_le_mul hlength' hS (sieveProduct_pos P.noFixedPrime _).le (by
    positivity : 0 ≤ 2 * y)
  have H'' := mul_le_mul H' hsum hs₀
    (mul_nonneg (by
      positivity) (mul_nonneg (Real.exp_nonneg _) (sieveProduct_pos P.noFixedPrime x).le))
  have H''' := mul_le_mul_of_nonneg_left H'' hKC
  apply (H k r P hdeg hzero A B σ F hF hA hB hσ hσsmall x y N a b
    ((le_max_left _ _).trans hx) hN hy hab hlength).trans
  have Hfour := mul_le_mul_of_nonneg_right H'''
    (primeArgumentFactor_nonneg P.total (z := x ^ ((g : ℝ) * ε / 16))
      (Real.one_le_rpow hx' hα.le))
  rw [primeArgumentFactor_rpow P.total (by linarith : 0 < x)] at Hfour ⊢
  dsimp only [primeMainTerm, mainTerm, E] at *
  convert Hfour using 1 <;> ring

end NairTenenbaum
