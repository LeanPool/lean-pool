/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentDecomposition
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentExceptional

/-! # The four prime-argument contributions assembled with uniform constants -/

@[expose] public section

namespace NairTenenbaum

theorem exists_primeIntegerSum_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {A B ε σ c : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hσ : 0 < σ)
    (hσsmall : (g : ℝ) ^ 2 * σ ≤ 1 / 8) (hc : 0 ≤ c)
    (hmargin : c * σ ≤ 17 * (g : ℝ) * ε / 24) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g → P.total.eval 0 ≠ 0 →
      ∀ (F : ArithmeticMap k), Admissible A B σ F →
      ∀ (x y : ℝ) (a b : ℤ), x₀ ≤ x → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) →
      P.primeIntegerSum F x a b ≤ C P.badDiscriminant * primeMainTerm P F x y := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  obtain ⟨K₁, x₁, hK₁, hx₁, H₁⟩ := exists_primeSmallRoughContribution_mainTerm_bound (c := c) hg
      hε hsmall hA
  obtain ⟨K₄, x₄, κ, w₀, hK₄, _, _, hw₀, H₄⟩ :=
    exists_primeIntermediatePrefixContribution_value_bound hg hε hsmall hA hc
  obtain ⟨K₂, hK₂, H₂⟩ := exists_powerSaving_le_primeMainTerm g (by
    positivity : 0 < (g : ℝ) * ε / 24)
  let s := Finset.Icc 0 ⌊w₀⌋₊
  let E₂ : ℕ → ℝ := fun D => 8 * (g : ℝ) * (max g (D ^ 3) : ℕ) * B
  let E₃ : ℕ → ℝ := fun D => 4 * smoothDivisorBound g (max 1 D) s * B
  let C₁ : ℕ → ℝ := fun D => K₁ * primeArgumentSmallSieveCost B σ g (max 1 D)
  let C₄ : ℕ → ℝ := fun D => K₄ * primeArgumentTailSieveCost A B κ g (max 1 D)
  have hE₂ (D : ℕ) : 0 < E₂ D := by
    have hM : (0 : ℝ) < (max g (D ^ 3) : ℕ) := by exact_mod_cast hg.trans_le (le_max_left _ _)
    dsimp [E₂]
    positivity
  have hE₃ (D : ℕ) : 0 < E₃ D := by
    have HM := smoothDivisorBound_pos g (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 D)) s
    dsimp [E₃]
    positivity
  have hC₁ (D : ℕ) : 0 < C₁ D := mul_pos hK₁ (primeArgumentSmallSieveCost_pos
    (lt_of_lt_of_le zero_lt_one hB) _ hg (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)))
  have hC₄ (D : ℕ) : 0 < C₄ D := mul_pos hK₄ (primeArgumentTailSieveCost_pos
    (lt_of_lt_of_le zero_lt_one hB) hg (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)))
  let α : ℝ := (g : ℝ) * ε / 2
  have hα : 0 < α := by dsimp [α]; positivity
  let x₀ := max x₁ (max x₄ (max 2 ((2 : ℝ) ^ (1 / α))))
  have ⟨hxx₁, hxx₄, hxx₂, hxxα⟩ :
      x₁ ≤ x₀ ∧ x₄ ≤ x₀ ∧ 2 ≤ x₀ ∧ (2 : ℝ) ^ (1 / α) ≤ x₀ := by
    simp [x₀, le_max_iff]
  refine ⟨x₀, hx₁.trans_le hxx₁, fun D => C₁ D + E₂ D * K₂ + E₃ D * K₂ + C₄ D,
    fun D => by positivity [hC₁ D, hE₂ D, hE₃ D, hC₄ D], ?_⟩
  intro k r P hdeg hzero F hF x y a b hx hy hab hlen hlen' hvalue
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
  have Hrough : P.primeSmallRoughContribution F N a b (x ^ ((g : ℝ) * ε / 16)) ≤
      C₁ P.badDiscriminant * primeMainTerm P F x y := by
    simpa only [C₁, HD] using H₁ k r P hdeg hzero B σ F hF hB hσ hσsmall x y N a b
      (hxx₁.trans hx) hN hy hab hlen hlen' hvalue
  have Hmiddle : P.primeIntermediatePrefixContribution F N (x ^ (3 * (g : ℝ) ^ 2 * ε / 2))
      w₀ x ((g : ℝ) * ε / 16) a b ≤ C₄ P.badDiscriminant * primeMainTerm P F x y := by
    simpa only [C₄, HD] using H₄ k r P hdeg hzero B σ F hF hB hσ hσsmall x y N a b
      (hxx₄.trans hx) hN hy hab hlen hlen' hvalue
  have Hsave := H₂ k r P hdeg.le hzero F hF.nonneg x y hx₂ hy₀
  have Hprime : P.primePowerContribution F (x ^ ((g : ℝ) * ε / 2)) a b ≤
      (E₂ P.badDiscriminant * K₂) * primeMainTerm P F x y := by
    have H := P.primePowerContribution_primeArgument_power_saving hdeg hF (zero_le_one.trans hB)
      hσ.le hε.le hx₁' hmargin hab hlevel₂ hlen' hvalue
    apply H.trans
    simpa only [E₂, mul_assoc] using mul_le_mul_of_nonneg_left Hsave (hE₂ P.badDiscriminant).le
  have Hsmooth : P.smoothDivisorContribution F s N (x ^ (3 * (g : ℝ) * ε / 2)) a b ≤
      (E₃ P.badDiscriminant * K₂) * primeMainTerm P F x y := by
    have H := P.smoothDivisorContribution_primeArgument_power_saving hdeg hF (zero_le_one.trans hB)
      hσ.le hx₁' hmargin s N hab (hN.trans hlevel₃) hlen' hvalue
    apply H.trans
    simpa only [E₃, HD, mul_assoc] using mul_le_mul_of_nonneg_left Hsave (hE₃ P.badDiscriminant).le
  have hcut : x ^ ((g : ℝ) * ε / 16) ≤ x := by
    have he : (g : ℝ) * ε / 16 ≤ 1 := by
      nlinarith [mul_nonneg hε.le (mul_nonneg hg₀.le (sub_nonneg.mpr hg₁))]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx₁' he
  have H := P.primeIntegerSum_le_four_contributions hF.nonneg hε.le hx₁' hw₀.le
    (by simpa only [hdeg] using hcut) a b
  dsimp only at H
  rw [hdeg] at H
  apply H.trans
  simpa only [N, s, add_mul] using add_le_add (add_le_add (add_le_add Hrough Hprime) Hsmooth)
      Hmiddle

end NairTenenbaum
