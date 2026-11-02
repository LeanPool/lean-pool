/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Contributions.ShortSumDecomposition
public import LeanPool.NairTenenbaum.Smooth.LargePrefixMainTerm

/-! # Contribution estimates from an explicit polynomial-value bound

The scale `x` need not be the location of the integer interval. This allows an
affine substitution to retain the original scale and avoid a new height
hypothesis for the substituted coefficients.
-/

@[expose] public section

namespace NairTenenbaum

/-- A bound for the total value supplies the pointwise arithmetic growth bound,
including the zero-extension cases. -/
theorem PolynomialSystem.value_weight_le_of_value_bound {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hB : 0 ≤ B) (hσ : 0 ≤ σ)
    {x c : ℝ} (hx : 0 ≤ x) {t : ℤ} (hvalue : ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs) ≤ B * x ^ (c * σ) * F 1 := by
  have heq : (∏ j, ((P.Q j).eval t).natAbs) = (P.total.eval t).natAbs := by
    simp only [PolynomialSystem.total, Polynomial.eval_prod]
    exact (map_prod Int.natAbsHom _ _).symm
  have H := hF.extend_le_mass_rpow hB (fun j => ((P.Q j).eval t).natAbs)
  rw [heq] at H
  have Hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hvalue hσ
  rw [← Real.rpow_mul hx] at Hpow
  exact H.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hpow hB) (hF.nonneg 1))

/-- The small-prime exceptional contribution under a value bound. -/
theorem PolynomialSystem.primePowerContribution_le_of_value_bound {k r : ℕ} (P : PolynomialSystem
    k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hB : 0 ≤ B) (hσ : 0 ≤ σ)
    {x c z : ℝ} (hx : 0 ≤ x) (hz : 1 ≤ z) {a b : ℤ} (hab : a ≤ b)
    (hlevel : z ^ 4 ≤ (b : ℝ) - a)
    (hvalue : ∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    P.primePowerContribution F z a b ≤
      (4 * (P.total.natDegree : ℝ) * (max P.total.natDegree (P.badDiscriminant ^ 3) : ℕ) * B) *
        ((b : ℝ) - a) * (x ^ (c * σ) / z ^ 2) * F 1 := by
  let W := B * x ^ (c * σ) * F 1
  have hW : 0 ≤ W := by dsimp [W]; positivity [hF.nonneg 1]
  have H : P.primePowerContribution F z a b ≤
      ((primePowerExceptionalSet P.R z (z ^ 3) a b).card : ℝ) * W := by
    unfold primePowerContribution
    apply le_trans (Finset.sum_le_sum (fun t ht =>
      P.value_weight_le_of_value_bound hF hB hσ hx (hvalue t (Finset.mem_filter.mp ht).1)))
    simp only [Finset.sum_const, nsmul_eq_mul, W, primePowerExceptionalSet, le_refl]
  apply H.trans
  have H' := mul_le_mul_of_nonneg_right (P.primePowerExceptionalSet_cube_card_le hz hab hlevel) hW
  dsimp only [W] at H'
  convert H' using 1
  ring

/-- The fixed-smoothness exceptional contribution under a value bound. -/
theorem PolynomialSystem.smoothDivisorContribution_le_of_value_bound {k r : ℕ} (P :
    PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hB : 0 ≤ B) (hσ : 0 ≤ σ)
    {x c T : ℝ} (hx : 0 ≤ x) (hT : 0 < T) (s : Finset ℕ) (N : ℕ+)
    {a b : ℤ} (hab : a ≤ b) (hlevel : (N : ℝ) ≤ (b : ℝ) - a)
    (hvalue : ∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    P.smoothDivisorContribution F s N T a b ≤
      (2 * smoothDivisorBound P.total.natDegree P.badDiscriminant s * B) *
        ((b : ℝ) - a) * (x ^ (c * σ) * T ^ (-(1 / 2 : ℝ))) * F 1 := by
  let W := B * x ^ (c * σ) * F 1
  have hW : 0 ≤ W := by dsimp [W]; positivity [hF.nonneg 1]
  have H : P.smoothDivisorContribution F s N T a b ≤
      ((smoothDivisorExceptionalSet P.radical s N T a b).card : ℝ) * W := by
    unfold smoothDivisorContribution
    apply le_trans (Finset.sum_le_sum (fun t ht =>
      P.value_weight_le_of_value_bound hF hB hσ hx (hvalue t (Finset.mem_filter.mp ht).1)))
    simp only [Finset.sum_const, nsmul_eq_mul, W, smoothDivisorExceptionalSet, le_refl]
  apply H.trans
  have H' := mul_le_mul_of_nonneg_right (P.smoothDivisorExceptionalSet_card_le s N hT hab hlevel) hW
  dsimp only [W] at H'
  convert H' using 1
  ring

/-- Uniform rough-prefix estimate with the value-growth exponent as an input. -/
theorem exists_largeRoughContribution_value_bound {g : ℕ} (hg : 0 < g)
    {ε A : ℝ} (hε : 0 < ε) (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hA : 1 ≤ A) (c : ℝ) :
    ∃ K x₀ : ℝ, 0 < K ∧ 1 < x₀ ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree = g → ∀ (B σ : ℝ) (F : ArithmeticMap k),
      Admissible A B σ F → 1 ≤ B → 0 < σ → (g : ℝ) ^ 2 * σ ≤ 1 / 8 →
      ∀ (x y : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) →
      P.smallRoughContribution F N a b (x ^ ((g : ℝ) * ε / 16)) ≤
        K * smallDivisorSieveCost B σ g P.badDiscriminant * mainTerm P F x y := by
  obtain ⟨K, x₁, hK, _, H⟩ := exists_largePrefixSiftedSum_mainTerm_bound hg hε hsmall
  let C := A ^ (c / ((g : ℝ) * ε / 16))
  have hC : 0 < C := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hA) _
  refine ⟨C * K, max x₁ 2, mul_pos hC hK,
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro k r P hdeg B σ F hF hB hσ hσsmall x y N a b hx hN hy hab hlen hlen' hvalue
  have hx₂ : 2 ≤ x := (le_max_right _ _).trans hx
  have hα : 0 < (g : ℝ) * ε / 16 := by
    have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
    positivity
  have H' := P.smallRoughContribution_le hF hA (zero_le_one.trans hB) N a b
    (by linarith : 1 < x) hα hvalue
  have H'' := mul_le_mul_of_nonneg_left
    (H k r P hdeg A B σ F hF (zero_le_one.trans hA) hB hσ hσsmall x y N a b
      ((le_max_left _ _).trans hx) hN hy hab hlen hlen') hC.le
  exact H'.trans (by simpa only [C, mul_assoc] using H'')

/-- Uniform intermediate-band estimate under the same value-bound hypothesis. -/
theorem exists_intermediatePrefixContribution_value_bound {g : ℕ} (hg : 0 < g)
    {ε A c : ℝ} (hε : 0 < ε) (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8)
    (hA : 1 ≤ A) (hc : 0 ≤ c) :
    ∃ K x₀ κ w₀ : ℝ, 0 < K ∧ 1 < x₀ ∧ 0 < κ ∧ 1 < w₀ ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (B σ : ℝ) (F : ArithmeticMap k), Admissible A B σ F → 1 ≤ B → 0 < σ →
      (g : ℝ) ^ 2 * σ ≤ 1 / 8 → ∀ (x y : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) →
      P.intermediatePrefixContribution F N (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) w₀ x
        ((g : ℝ) * ε / 16) a b ≤
        K * smoothTailSieveCost A B κ g P.badDiscriminant * mainTerm P F x y := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hu : 0 < (g : ℝ) * ε / 16 := by positivity
  have hu₁ : (g : ℝ) * ε / 16 ≤ 1 := by
    nlinarith [mul_nonneg hε.le (mul_nonneg (show (0 : ℝ) ≤ g by positivity)
      (sub_nonneg.mpr hg₁))]
  obtain ⟨K, x₁, κ, w₀, hK, _, hκ, hw₀, H⟩ := exists_largePrefixBands_mainTerm_bound hg hε hA hc
  let x₀ : ℝ := max x₁ (Real.exp 1)
  have hxx₀ : Real.exp 1 ≤ x₀ := le_max_right _ _
  have hx₀ : 1 < x₀ := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hxx₀
  refine ⟨K, x₀, κ, w₀, hK, hx₀, hκ, hw₀, ?_⟩
  intro k r P hdeg B σ F hF hB hσ hσsmall x y N a b hxx hN hy hab hlen hlen' hvalue
  have hx : 1 < x := hx₀.trans_le hxx
  have hlog : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hxx₀.trans hxx)
  obtain ⟨J, hJ, HJ⟩ := P.intermediatePrefixContribution_le_bands hF.nonneg N
    (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) w₀ x ((g : ℝ) * ε / 16) a b hx hw₀.le
  exact HJ.trans (H k r P hdeg B σ F hF hB hσ hσsmall x y ((g : ℝ) * ε / 16) N a b J
    ((le_max_left _ _).trans hxx) hx hlog hu hu₁ le_rfl (fun j hj => (hJ j hj).le)
    hN hy hab hlen hlen' hvalue)

/-- A single growth margin gives a uniform power saving for the prime-power
exceptional set, independently of the interval's location. -/
theorem PolynomialSystem.primePowerContribution_power_saving_of_margin {k r g : ℕ}
    (P : PolynomialSystem k r) (hdeg : P.total.natDegree = g)
    {A B σ ε c x y τ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F)
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hε : 0 ≤ ε) (hx : 1 ≤ x)
    (hmargin : c * σ + τ ≤ (g : ℝ) * ε) {a b : ℤ} (hab : a ≤ b)
    (hlevel : (x ^ ((g : ℝ) * ε / 2)) ^ 4 ≤ (b : ℝ) - a)
    (hlen : (b : ℝ) - a ≤ 2 * y)
    (hvalue : ∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    P.primePowerContribution F (x ^ ((g : ℝ) * ε / 2)) a b ≤
      (8 * (g : ℝ) * (max g (P.badDiscriminant ^ 3) : ℕ) * B) *
        y * x ^ (-τ) * F 1 := by
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hz : 1 ≤ x ^ ((g : ℝ) * ε / 2) := Real.one_le_rpow hx (by positivity)
  have H := P.primePowerContribution_le_of_value_bound hF hB hσ hx₀.le hz hab hlevel hvalue
  rw [hdeg] at H
  have Hpow : x ^ (c * σ) / (x ^ ((g : ℝ) * ε / 2)) ^ 2 ≤ x ^ (-τ) := by
    have heq : (x ^ ((g : ℝ) * ε / 2)) ^ 2 = x ^ ((g : ℝ) * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx₀.le]
      congr 1
      norm_num
    rw [heq, ← Real.rpow_sub hx₀]
    apply Real.rpow_le_rpow_of_exponent_le hx
    nlinarith [mul_nonneg (Nat.cast_nonneg g : (0 : ℝ) ≤ _) hε]
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hy : 0 ≤ y := by linarith
  have H' := mul_le_mul hlen Hpow (by positivity) (by positivity : 0 ≤ 2 * y)
  have H'' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H'
    (by positivity : 0 ≤ 4 * (g : ℝ) * (max g (P.badDiscriminant ^ 3) : ℕ) * B)) (hF.nonneg 1)
  apply H.trans
  convert H'' using 1 <;> ring

/-- The same growth margin pays the smooth-divisor saving. -/
theorem PolynomialSystem.smoothDivisorContribution_power_saving_of_margin {k r g : ℕ}
    (P : PolynomialSystem k r) (hdeg : P.total.natDegree = g)
    {A B σ ε c x y τ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F)
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hx : 1 ≤ x)
    (hmargin : c * σ + τ ≤ 3 * (g : ℝ) * ε / 4) (s : Finset ℕ) (N : ℕ+)
    {a b : ℤ} (hab : a ≤ b) (hlevel : (N : ℝ) ≤ (b : ℝ) - a)
    (hlen : (b : ℝ) - a ≤ 2 * y)
    (hvalue : ∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    P.smoothDivisorContribution F s N (x ^ (3 * (g : ℝ) * ε / 2)) a b ≤
      (4 * smoothDivisorBound g P.badDiscriminant s * B) *
        y * x ^ (-τ) * F 1 := by
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have H := P.smoothDivisorContribution_le_of_value_bound (T := x ^ (3 * (g : ℝ) * ε / 2)) hF hB
      hσ hx₀.le
    (Real.rpow_pos_of_pos hx₀ _) s N hab hlevel hvalue
  rw [hdeg] at H
  have Hpow : x ^ (c * σ) * (x ^ (3 * (g : ℝ) * ε / 2)) ^ (-(1 / 2 : ℝ)) ≤
      x ^ (-τ) := by
    rw [← Real.rpow_mul hx₀.le, ← Real.rpow_add hx₀]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hy : 0 ≤ y := by linarith
  have H' := mul_le_mul hlen Hpow (by positivity) (by positivity : 0 ≤ 2 * y)
  have H'' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H'
    (by positivity [smoothDivisorBound_pos g P.badDiscriminant_pos s] :
      0 ≤ 2 * smoothDivisorBound g P.badDiscriminant s * B)) (hF.nonneg 1)
  apply H.trans
  convert H'' using 1 <;> ring

end NairTenenbaum
