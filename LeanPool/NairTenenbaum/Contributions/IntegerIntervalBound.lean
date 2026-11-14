/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Contributions.IntegerIntervalDecomposition
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentExceptional

/-! # A uniform short-sum bound from polynomial-value growth

This form keeps the analytic scale independent of the location of the integer
interval. All constants are chosen before the polynomial system; only the
upper-bound constant depends on its restricted discriminant.
-/

@[expose] public section

namespace NairTenenbaum

/-- Short sums over arbitrary integer intervals, assuming a bound on the actual
polynomial values and a positive margin between arithmetic growth and the
exceptional-set saving. -/
theorem exists_integerSum_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {A B ε σ c : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hσ : 0 < σ)
    (hσsmall : (g : ℝ) ^ 2 * σ ≤ 1 / 8) (hc : 0 ≤ c)
    (hmargin : c * σ ≤ 17 * (g : ℝ) * ε / 24) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (F : ArithmeticMap k), Admissible A B σ F →
      ∀ (x y : ℝ) (a b : ℤ), x₀ ≤ x → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) →
      P.integerSum F a b ≤ C P.badDiscriminant * mainTerm P F x y := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  obtain ⟨K₁, x₁, hK₁, hx₁, H₁⟩ := exists_largeRoughContribution_value_bound hg hε hsmall hA c
  obtain ⟨K₄, x₄, κ, w₀, hK₄, _, _, hw₀, H₄⟩ :=
    exists_intermediatePrefixContribution_value_bound hg hε hsmall hA hc
  obtain ⟨K₂, hK₂, H₂⟩ := exists_powerSaving_le_mainTerm g (by positivity : 0 < (g : ℝ) * ε / 24)
  let s := Finset.Icc 0 ⌊w₀⌋₊
  let E₂ : ℕ → ℝ := fun D => 8 * (g : ℝ) * (max g (D ^ 3) : ℕ) * B
  let E₃ : ℕ → ℝ := fun D => 4 * smoothDivisorBound g (max 1 D) s * B
  let C₁ : ℕ → ℝ := fun D => K₁ * smallDivisorSieveCost B σ g (max 1 D)
  let C₄ : ℕ → ℝ := fun D => K₄ * smoothTailSieveCost A B κ g (max 1 D)
  have hE₂ (D : ℕ) : 0 < E₂ D := by
    have hM : (0 : ℝ) < (max g (D ^ 3) : ℕ) := by exact_mod_cast hg.trans_le (le_max_left _ _)
    dsimp [E₂]
    positivity
  have hE₃ (D : ℕ) : 0 < E₃ D := by
    have HM := smoothDivisorBound_pos g (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 D)) s
    dsimp [E₃]
    positivity
  have hC₁ (D : ℕ) : 0 < C₁ D := mul_pos hK₁ (smallDivisorSieveCost_pos
    (lt_of_lt_of_le zero_lt_one hB) _ hg (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)))
  have hC₄ (D : ℕ) : 0 < C₄ D := mul_pos hK₄ (smoothTailSieveCost_pos
    (lt_of_lt_of_le zero_lt_one hB) hg (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)))
  let α : ℝ := (g : ℝ) * ε / 2
  have hα : 0 < α := by dsimp [α]; positivity
  let x₀ := max x₁ (max x₄ (max 2 ((2 : ℝ) ^ (1 / α))))
  have ⟨hxx₁, hxx₄, hxx₂, hxxα⟩ :
      x₁ ≤ x₀ ∧ x₄ ≤ x₀ ∧ 2 ≤ x₀ ∧ (2 : ℝ) ^ (1 / α) ≤ x₀ := by
    simp [x₀, le_max_iff]
  refine ⟨x₀, hx₁.trans_le hxx₁, fun D => C₁ D + E₂ D * K₂ + E₃ D * K₂ + C₄ D,
    fun D => by positivity [hC₁ D, hE₂ D, hE₃ D, hC₄ D], ?_⟩
  intro k r P hdeg F hF x y a b hx hy hab hlen hlen' hvalue
  have hx₂ : 2 ≤ x := hxx₂.trans hx
  have hx₁' : 1 ≤ x := by linarith
  have hx₀ : 0 < x := by linarith
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg hx₀.le _).trans hy
  have hz : 2 ≤ x ^ α := by
    have H := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (hxxα.trans hx) hα.le
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel hα.ne', Real.rpow_one] at H
    exact H
  have hgap : 2 ≤ x ^ ((g : ℝ) ^ 2 * ε) := hz.trans (Real.rpow_le_rpow_of_exponent_le hx₁' (by
    dsimp [α]
    nlinarith [mul_nonneg hε.le (mul_nonneg hg₀.le (sub_nonneg.mpr hg₁))]))
  have hlevel₂ := (secondContribution_sieve_level hg hε hx₁' hz hy).trans hlen
  have hlevel₃ := (largeDivisor_sieve_level hx₀ hgap hy).trans hlen
  have hT : 1 ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) := Real.one_le_rpow hx₁' (by positivity)
  let N := Nat.toPNat' ⌊x ^ (3 * (g : ℝ) ^ 2 * ε)⌋₊
  have hN : (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) := by
    dsimp only [N]
    rw [PNat.toPNat'_coe (Nat.floor_pos.mpr hT)]
    exact Nat.floor_le (zero_le_one.trans hT)
  have HD : max 1 P.badDiscriminant = P.badDiscriminant := max_eq_right P.badDiscriminant_pos
  have Hrough : P.smallRoughContribution F N a b (x ^ ((g : ℝ) * ε / 16)) ≤
      C₁ P.badDiscriminant * mainTerm P F x y := by
    simpa only [C₁, HD] using H₁ k r P hdeg B σ F hF hB hσ hσsmall x y N a b
      (hxx₁.trans hx) hN hy hab hlen hlen' hvalue
  have Hmiddle : P.intermediatePrefixContribution F N (x ^ (3 * (g : ℝ) ^ 2 * ε / 2))
      w₀ x ((g : ℝ) * ε / 16) a b ≤ C₄ P.badDiscriminant * mainTerm P F x y := by
    simpa only [C₄, HD] using H₄ k r P hdeg B σ F hF hB hσ hσsmall x y N a b
      (hxx₄.trans hx) hN hy hab hlen hlen' hvalue
  have Hsave := H₂ k r P hdeg.le F hF.nonneg x y hx₂ hy₀
  have Hprime : P.primePowerContribution F (x ^ ((g : ℝ) * ε / 2)) a b ≤
      (E₂ P.badDiscriminant * K₂) * mainTerm P F x y := by
    have H := P.primePowerContribution_primeArgument_power_saving hdeg hF (zero_le_one.trans hB)
      hσ.le hε.le hx₁' hmargin hab hlevel₂ hlen' hvalue
    apply H.trans
    simpa only [E₂, mul_assoc] using mul_le_mul_of_nonneg_left Hsave (hE₂ P.badDiscriminant).le
  have Hsmooth : P.smoothDivisorContribution F s N (x ^ (3 * (g : ℝ) * ε / 2)) a b ≤
      (E₃ P.badDiscriminant * K₂) * mainTerm P F x y := by
    have H := P.smoothDivisorContribution_primeArgument_power_saving hdeg hF (zero_le_one.trans hB)
      hσ.le hx₁' hmargin s N hab (hN.trans hlevel₃) hlen' hvalue
    apply H.trans
    simpa only [E₃, HD, mul_assoc] using mul_le_mul_of_nonneg_left Hsave (hE₃ P.badDiscriminant).le
  have H := P.integerSum_le_four_contributions hF.nonneg hε.le hx₁' hw₀.le a b
  dsimp only at H
  rw [hdeg] at H
  apply H.trans
  simpa only [N, s, add_mul] using add_le_add (add_le_add (add_le_add Hrough Hprime) Hsmooth)
      Hmiddle

/-- The elementary bound used on a bounded range of the analytic scale. -/
theorem PolynomialSystem.integerSum_le_of_value_bound {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ c x y : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F)
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hx : 0 ≤ x) {a b : ℤ} (hab : a ≤ b)
    (hlen : (b : ℝ) - a ≤ 2 * y)
    (hvalue : ∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    P.integerSum F a b ≤ 2 * B * y * x ^ (c * σ) * F 1 := by
  have hcard : ((Finset.Ioc a b).card : ℝ) = (b : ℝ) - a := by
    exact_mod_cast Int.card_Ioc_of_le a b hab
  have H : P.integerSum F a b ≤ ((Finset.Ioc a b).card : ℝ) * (B * x ^ (c * σ) * F 1) := by
    unfold integerSum
    apply le_trans (Finset.sum_le_sum (fun t ht =>
      P.value_weight_le_of_value_bound hF hB hσ hx (hvalue t ht)))
    simp only [Finset.sum_const, nsmul_eq_mul, le_refl]
  rw [hcard] at H
  apply H.trans
  have H' := mul_le_mul_of_nonneg_right hlen
    (by positivity [hF.nonneg 1] : 0 ≤ B * x ^ (c * σ) * F 1)
  convert H' using 1
  ring

/-- Enlarging the upper-bound constant handles the bounded range of `x`, so
the value-bound estimate is valid for every `x ≥ 2`. In applications this
keeps the coefficient-height threshold independent of an interval parameter. -/
theorem exists_integerSum_mainTerm_bound_all_scales {g : ℕ} (hg : 0 < g)
    {A B ε σ c : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hσ : 0 < σ)
    (hσsmall : (g : ℝ) ^ 2 * σ ≤ 1 / 8) (hc : 0 ≤ c)
    (hmargin : c * σ ≤ 17 * (g : ℝ) * ε / 24) :
    ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (F : ArithmeticMap k), Admissible A B σ F →
      ∀ (x y : ℝ) (a b : ℤ), 2 ≤ x → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y - 1 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) →
      P.integerSum F a b ≤ C P.badDiscriminant * mainTerm P F x y := by
  obtain ⟨x₁, hx₁, C, hC, H⟩ := exists_integerSum_mainTerm_bound hg hA hB hε hsmall hσ hσsmall hc
      hmargin
  obtain ⟨K, hK, HK⟩ := exists_powerSaving_le_mainTerm g (by norm_num : (0 : ℝ) < 1)
  let β : ℝ := 4 * (g : ℝ) ^ 2 * ε
  have hβ : 0 < β := by
    have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
    dsimp [β]
    positivity
  let x₀ := max x₁ ((2 : ℝ) ^ (1 / β))
  have hx₀ : 1 < x₀ := hx₁.trans_le (le_max_left _ _)
  let E := 2 * B * x₀ ^ (c * σ + 1)
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨fun D => C D + E * K, fun D => add_pos (hC D) (mul_pos hE (by linarith)), ?_⟩
  intro k r P hdeg F hF x y a b hx hy hab hlen hlen' hvalue
  have hxpos : 0 < x := by linarith
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg hxpos.le _).trans hy
  have hM : 0 ≤ mainTerm P F x y := by
    unfold mainTerm
    exact mul_nonneg (mul_nonneg hy₀ (sieveProduct_pos P.noFixedPrime x).le)
      (Finset.sum_nonneg (fun n _ => P.weight_nonneg hF.nonneg n))
  by_cases hxx : x₀ ≤ x
  · have hy₂ : 2 ≤ y := by
      have Hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        ((le_max_right _ _).trans hxx) hβ.le
      rw [← Real.rpow_mul (by
        norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel hβ.ne', Real.rpow_one] at Hpow
      exact Hpow.trans hy
    exact (H k r P hdeg F hF x y a b ((le_max_left _ _).trans hxx) hy hab
      (by linarith) hlen' hvalue).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hE.le (by linarith))) hM)
  have hxx' : x ≤ x₀ := (lt_of_not_ge hxx).le
  have Hpow : x ^ (c * σ) ≤ x₀ ^ (c * σ + 1) * x ^ (-(1 : ℝ)) := by
    have Hpow := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hxpos.le hxx' (by positivity : 0 ≤ c * σ + 1))
      (Real.rpow_nonneg hxpos.le (-(1 : ℝ)))
    rw [← Real.rpow_add hxpos] at Hpow
    simpa only [add_neg_cancel_right] using Hpow
  have Hraw := P.integerSum_le_of_value_bound hF (zero_le_one.trans hB) hσ.le hxpos.le hab hlen'
      hvalue
  have Hweighted := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left Hpow (by positivity : 0 ≤ 2 * B * y)) (hF.nonneg 1)
  have Hsave := mul_le_mul_of_nonneg_left (HK k r P hdeg.le F hF.nonneg x y hx hy₀) hE.le
  have Hsmall : P.integerSum F a b ≤ (E * K) * mainTerm P F x y := by
    apply Hraw.trans (Hweighted.trans ?_)
    simpa only [E, mul_assoc, mul_left_comm, mul_comm] using Hsave
  exact Hsmall.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hC P.badDiscriminant).le)
      hM)

end NairTenenbaum
