/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLpLarge
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigmaExpRegime.FiniteSums

/-!
# MomentBoostedLowPowerBernstein

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Internal two-regime Bernstein spine for the low-power large-cube route

This module records the finite-family estimate used before the concave `p / 2`
power in the `1 <= p <= 2` branch.  It starts from centered unit `Gamma_1`
summands, invokes only CoarseGraining's small-tilt moment/MGF lemma, and keeps
the quadratic and linear Chernoff regimes separate.  The two terms are needed
by the later concave-power transport; collapsing them first to a `Gamma_1` tail
would lose the required square-root spatial gain.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open HCPolySupport HCPolySupport.IndependentSums
open scoped BigOperators

noncomputable section

/-- The fixed first-moment MGF coefficient in the low-power Bernstein route. -/
noncomputable def momentBoostedBernsteinBase : ℝ :=
  Real.exp 1 * gammaMomentConst 1

theorem momentBoostedBernsteinBase_pos : 0 < momentBoostedBernsteinBase := by
  unfold momentBoostedBernsteinBase
  exact mul_pos (Real.exp_pos _) (gammaMomentConst_pos zero_lt_one)

theorem one_le_momentBoostedBernsteinBase : 1 ≤ momentBoostedBernsteinBase := by
  unfold momentBoostedBernsteinBase gammaMomentConst
  have hexp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hmax : (1 : ℝ) ≤ max 1 ((2 / (1 * Real.exp 1)) ^ (1 : ℝ)⁻¹) := le_max_left _ _
  calc
    (1 : ℝ) ≤ 2 * Real.exp 1 := by nlinarith
    _ = (2 * Real.exp 1) * 1 := by ring
    _ ≤ (2 * Real.exp 1) * max 1 ((2 / (1 * Real.exp 1)) ^ (1 : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    _ ≤ Real.exp 1 *
        ((2 * Real.exp 1) * max 1 ((2 / (1 * Real.exp 1)) ^ (1 : ℝ)⁻¹)) :=
      by
        have hnonneg : 0 ≤
            (2 * Real.exp 1) * max 1 ((2 / (1 * Real.exp 1)) ^ (1 : ℝ)⁻¹) := by
          positivity
        nlinarith [mul_le_mul_of_nonneg_right hexp hnonneg]

/-- The quadratic denominator in the raw finite-family Bernstein tail. -/
noncomputable def momentBoostedBernsteinQuadratic : ℝ :=
  16 * momentBoostedBernsteinBase ^ (2 : ℕ)

theorem momentBoostedBernsteinQuadratic_pos :
    0 < momentBoostedBernsteinQuadratic := by
  unfold momentBoostedBernsteinQuadratic
  exact mul_pos (by norm_num) (pow_pos momentBoostedBernsteinBase_pos _)

/-- The linear denominator in the raw finite-family Bernstein tail. -/
noncomputable def momentBoostedBernsteinLinear : ℝ :=
  4 * momentBoostedBernsteinBase

theorem momentBoostedBernsteinLinear_pos : 0 < momentBoostedBernsteinLinear := by
  unfold momentBoostedBernsteinLinear
  exact mul_pos (by norm_num) momentBoostedBernsteinBase_pos

/--
**Raw one-sided Bernstein concentration.**  A centered independent finite
family with unit two-sided `Gamma_1` control obeys the displayed quadratic plus
linear tail.  The statement is internal infrastructure: all its hypotheses are
discharged by the colored descendant application below the source-facing
surface.
-/
theorem measureReal_upperTailEvent_finset_sum_le_momentBoostedBernstein
    {Omega iota : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : iota → Omega → ℝ} {s : Finset iota} {a : ℝ}
    (h_indep : iIndepFun X mu)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty) (ha : 0 ≤ a)
    (hX : ∀ i ∈ s, IsBigO mu (gammaSigma 1) (X i) 1)
    (hmean : ∀ i ∈ s, ∫ omega, X i omega ∂mu = 0) :
    mu.real (upperTailEvent (fun omega => ∑ i ∈ s, X i omega) a) ≤
      Real.exp (-(a ^ (2 : ℕ)) /
        (momentBoostedBernsteinQuadratic * (s.card : ℝ))) +
        Real.exp (-a / momentBoostedBernsteinLinear) := by
  let B : ℝ := momentBoostedBernsteinBase
  let R : ℝ := s.card
  let M : ℝ := gammaMomentConst 1
  let l : ℝ := min ((2 * B)⁻¹) (a / (8 * B ^ (2 : ℕ) * R))
  have hB : 0 < B := by
    simpa [B] using momentBoostedBernsteinBase_pos
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast hs.card_pos
  have hM : 0 < M := by
    simpa [M] using gammaMomentConst_pos zero_lt_one
  have hBM : Real.exp 1 * M = B := by rfl
  have hl : 0 ≤ l := by
    dsimp [l]
    positivity
  have hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹ := by
    calc
      l ≤ (2 * B)⁻¹ := min_le_left _ _
      _ = (2 * Real.exp 1 * M)⁻¹ := by
        rw [← hBM]
        congr 1
        ring
  have hXmom : ∀ i ∈ s, HasGammaMomentGrowthWith mu 1 (X i) M := by
    intro i hi
    simpa [M] using hasGammaMomentGrowthWith_of_isBigO_gammaSigma
      (μ := mu) (X := X i) (K := (1 : ℝ)) (σ := (1 : ℝ))
      zero_lt_one zero_lt_one (h_meas i).aemeasurable (hX i hi)
  have htail :=
    upperTailProbability_finiteSum_le_exp_card_mul_of_iIndepFun
      (μ := mu) (X := X) (s := s) (σ := (1 : ℝ)) (M := M) (l := l) (a := a)
      h_indep h_meas le_rfl hM.le hl hl_small hmean hXmom
  by_cases hlarge : (2 * B)⁻¹ ≤ a / (8 * B ^ (2 : ℕ) * R)
  · have hl_eq : l = (2 * B)⁻¹ := by
      dsimp [l]
      exact min_eq_left hlarge
    have hthreshold : 4 * B * R ≤ a := by
      have hden : 0 ≤ 8 * B ^ (2 : ℕ) * R := by positivity
      have hmul := mul_le_mul_of_nonneg_right hlarge hden
      calc
        4 * B * R = (2 * B)⁻¹ * (8 * B ^ (2 : ℕ) * R) := by
          field_simp [hB.ne']
          ring
        _ ≤ (a / (8 * B ^ (2 : ℕ) * R)) * (8 * B ^ (2 : ℕ) * R) := hmul
        _ = a := by field_simp [hB.ne', hR.ne']
    have hRbound : R / 2 ≤ a / (8 * B) := by
      have hden : 0 < 8 * B := by positivity
      apply (le_div_iff₀ hden).2
      nlinarith [hthreshold]
    have hexp :
        -l * a + 2 * R * (Real.exp 1 * M * l) ^ (2 : ℕ) ≤
          -a / (4 * B) := by
      rw [hl_eq, hBM]
      have heq :
          -((2 * B)⁻¹) * a + 2 * R * (B * (2 * B)⁻¹) ^ (2 : ℕ) =
            -a / (2 * B) + R / 2 := by
        field_simp [hB.ne']
      rw [heq]
      field_simp [hB.ne']
      nlinarith [hthreshold]
    calc
      mu.real (upperTailEvent (fun omega => ∑ i ∈ s, X i omega) a)
          ≤ Real.exp (-l * a + 2 * R * (Real.exp 1 * M * l) ^ (2 : ℕ)) := by
            simpa [R] using htail
      _ ≤ Real.exp (-a / (4 * B)) := Real.exp_le_exp.2 hexp
      _ = Real.exp (-a / momentBoostedBernsteinLinear) := by
            simp only [momentBoostedBernsteinLinear, B]
      _ ≤ Real.exp (-(a ^ (2 : ℕ)) /
          (momentBoostedBernsteinQuadratic * (s.card : ℝ))) +
          Real.exp (-a / momentBoostedBernsteinLinear) :=
        le_add_of_nonneg_left (Real.exp_pos _).le
  · have hl_eq : l = a / (8 * B ^ (2 : ℕ) * R) := by
      dsimp [l]
      exact min_eq_right (le_of_not_ge hlarge)
    have hexp :
        -l * a + 2 * R * (Real.exp 1 * M * l) ^ (2 : ℕ) ≤
          -(a ^ (2 : ℕ)) / (16 * B ^ (2 : ℕ) * R) := by
      rw [hl_eq, hBM]
      have heq :
          -(a / (8 * B ^ (2 : ℕ) * R)) * a +
              2 * R * (B * (a / (8 * B ^ (2 : ℕ) * R))) ^ (2 : ℕ) =
            -3 * a ^ (2 : ℕ) / (32 * B ^ (2 : ℕ) * R) := by
        field_simp [hB.ne', hR.ne']
        ring
      rw [heq]
      have hden : 0 < 32 * B ^ (2 : ℕ) * R := by positivity
      have hasq : 0 ≤ a ^ (2 : ℕ) := sq_nonneg a
      have hrewrite :
          -(a ^ (2 : ℕ)) / (16 * B ^ (2 : ℕ) * R) =
            -(2 * a ^ (2 : ℕ)) / (32 * B ^ (2 : ℕ) * R) := by
        field_simp [hB.ne', hR.ne']
        ring
      rw [hrewrite]
      apply (div_le_div_iff_of_pos_right hden).2
      nlinarith
    calc
      mu.real (upperTailEvent (fun omega => ∑ i ∈ s, X i omega) a)
          ≤ Real.exp (-l * a + 2 * R * (Real.exp 1 * M * l) ^ (2 : ℕ)) := by
            simpa [R] using htail
      _ ≤ Real.exp (-(a ^ (2 : ℕ)) / (16 * B ^ (2 : ℕ) * R)) :=
        Real.exp_le_exp.2 hexp
      _ = Real.exp (-(a ^ (2 : ℕ)) /
          (momentBoostedBernsteinQuadratic * (s.card : ℝ))) := by
            simp only [momentBoostedBernsteinQuadratic, B, R]
      _ ≤ Real.exp (-(a ^ (2 : ℕ)) /
          (momentBoostedBernsteinQuadratic * (s.card : ℝ))) +
          Real.exp (-a / momentBoostedBernsteinLinear) :=
        le_add_of_nonneg_right (Real.exp_pos _).le

end

end Algsuperdiff.Section3.Provider.Stream
