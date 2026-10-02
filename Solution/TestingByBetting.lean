/-
Copyright (c) 2026 deadczarvc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: deadczarvc
-/

module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Solution: Ville's inequality for testing by betting

Challenge: `ville-testing-by-betting` (`Challenge.TestingByBetting`)
Proves: `Challenge.TestingByBetting.ville`
Solved by: deadczarvc

This module restates the challenge statement under its own name and proves it. It must not import
the challenge module: comparator exports both environments separately and checks that the statements
agree, which is what makes the verdict independent of the statement file.
-/

/-!
## Proof outline

1. The wealth `W n = ∏ i < n, (1 + lam (i + 1) * X (i + 1))` is adapted, satisfies
   `0 ≤ W n ≤ 2 ^ n`, and is a supermartingale: pulling the `ℱ n`-measurable factor out of the
   conditional expectation gives
   `E[W (n + 1) | ℱ n] = W n + W n * lam (n + 1) * E[X (n + 1) | ℱ n]`,
   which is at most `W n` under the null.
2. Finite horizon: optional stopping at the hitting time of `[c, ∞)` before `N` gives
   `E[W τ] ≤ E[W 0] = 1`, and Markov's inequality gives `c * P(∃ n ≤ N, c ≤ W n) ≤ 1`.
3. Infinite horizon: continuity of the measure from below over `N`, with `c = α⁻¹`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Challenge.TestingByBetting

section Helpers

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Wealth after `n` rounds of betting the predictable fraction `lam (i + 1)` on `X (i + 1)`. -/
private noncomputable def wealth (X lam : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range n, (1 + lam (i + 1) ω * X (i + 1) ω)

private lemma wealth_succ (X lam : ℕ → Ω → ℝ) (n : ℕ) :
    wealth X lam (n + 1) = fun ω => wealth X lam n ω * (1 + lam (n + 1) ω * X (n + 1) ω) := by
  funext ω
  simp [wealth, Finset.prod_range_succ]

private lemma factor_mem {x l : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) (hl : 0 ≤ l ∧ l ≤ 1) :
    0 ≤ 1 + l * x ∧ 1 + l * x ≤ 2 := by
  constructor <;> nlinarith [mul_nonneg hl.1 (show 0 ≤ x + 1 by linarith),
    mul_nonneg hl.1 (show 0 ≤ 1 - x by linarith)]

private lemma wealth_nonneg {X lam : ℕ → Ω → ℝ} (hXb : ∀ n ω, -1 ≤ X n ω ∧ X n ω ≤ 1)
    (hlamb : ∀ n ω, 0 ≤ lam n ω ∧ lam n ω ≤ 1) (n : ℕ) (ω : Ω) : 0 ≤ wealth X lam n ω :=
  Finset.prod_nonneg fun i _ => (factor_mem (hXb (i + 1) ω) (hlamb (i + 1) ω)).1

private lemma wealth_le {X lam : ℕ → Ω → ℝ} (hXb : ∀ n ω, -1 ≤ X n ω ∧ X n ω ≤ 1)
    (hlamb : ∀ n ω, 0 ≤ lam n ω ∧ lam n ω ≤ 1) (n : ℕ) (ω : Ω) : wealth X lam n ω ≤ 2 ^ n := by
  calc wealth X lam n ω ≤ ∏ _i ∈ Finset.range n, (2 : ℝ) :=
        Finset.prod_le_prod₀ (fun i _ => (factor_mem (hXb (i + 1) ω) (hlamb (i + 1) ω)).1)
          (fun i _ => (factor_mem (hXb (i + 1) ω) (hlamb (i + 1) ω)).2)
    _ = 2 ^ n := by simp

private lemma wealth_stronglyMeasurable {ℱ : Filtration ℕ m0} {X lam : ℕ → Ω → ℝ}
    (hX : Adapted ℱ X) (hlam : ∀ n, StronglyMeasurable[ℱ n] (lam (n + 1))) (n : ℕ) :
    StronglyMeasurable[ℱ n] (wealth X lam n) := by
  induction n with
  | zero =>
    have h0 : wealth X lam 0 = fun _ => (1 : ℝ) := by funext ω; simp [wealth]
    rw [h0]; exact stronglyMeasurable_const
  | succ n ih =>
    rw [wealth_succ]
    refine (ih.mono (ℱ.mono n.le_succ)).mul (stronglyMeasurable_const.add ?_)
    exact ((hlam n).mono (ℱ.mono n.le_succ)).mul (hX (n + 1)).stronglyMeasurable

private lemma integrable_of_bounded {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    {m : MeasurableSpace Ω} (hm : m ≤ m0) (hf : StronglyMeasurable[m] f) (C : ℝ)
    (hC : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  Integrable.of_bound (hf.mono hm).aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- The wealth process is a supermartingale under the null `E[X (n + 1) | ℱ n] ≤ 0`. -/
private theorem wealth_supermartingale (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (X lam : ℕ → Ω → ℝ)
    (hX : Adapted ℱ X) (hXb : ∀ n ω, -1 ≤ X n ω ∧ X n ω ≤ 1)
    (hlam : ∀ n, StronglyMeasurable[ℱ n] (lam (n + 1))) (hlamb : ∀ n ω, 0 ≤ lam n ω ∧ lam n ω ≤ 1)
    (hnull : ∀ n, μ[X (n + 1) | ℱ n] ≤ᵐ[μ] 0) :
    Supermartingale (wealth X lam) ℱ μ := by
  have hsm := wealth_stronglyMeasurable hX hlam
  have hint : ∀ n, Integrable (wealth X lam n) μ := fun n =>
    integrable_of_bounded (ℱ.le n) (hsm n) (2 ^ n) fun ω => by
      rw [abs_of_nonneg (wealth_nonneg hXb hlamb n ω)]; exact wealth_le hXb hlamb n ω
  refine supermartingale_nat hsm hint fun n => ?_
  set g : Ω → ℝ := fun ω => wealth X lam n ω * lam (n + 1) ω with hg_def
  have hg_sm : StronglyMeasurable[ℱ n] g := (hsm n).mul (hlam n)
  have hXi : Integrable (X (n + 1)) μ :=
    integrable_of_bounded (ℱ.le (n + 1)) (hX (n + 1)).stronglyMeasurable 1 fun ω =>
      abs_le.mpr (hXb (n + 1) ω)
  have hgX : Integrable (g * X (n + 1)) μ :=
    integrable_of_bounded (ℱ.le (n + 1))
      ((hg_sm.mono (ℱ.mono n.le_succ)).mul (hX (n + 1)).stronglyMeasurable) (2 ^ n) fun ω => by
      have h1 := wealth_nonneg hXb hlamb n ω
      have h2 := wealth_le hXb hlamb n ω
      have h3 := hlamb (n + 1) ω
      have h4 := hXb (n + 1) ω
      simp only [Pi.mul_apply, hg_def, abs_mul, abs_of_nonneg h1, abs_of_nonneg h3.1]
      have h5 : |X (n + 1) ω| ≤ 1 := abs_le.mpr h4
      calc wealth X lam n ω * lam (n + 1) ω * |X (n + 1) ω| ≤ 2 ^ n * 1 * 1 :=
            mul_le_mul (mul_le_mul h2 h3.2 h3.1 (by positivity)) h5 (abs_nonneg _) (by positivity)
      _ = 2 ^ n := by ring
  have hsplit : wealth X lam (n + 1) = wealth X lam n + g * X (n + 1) := by
    rw [wealth_succ]; funext ω; simp only [Pi.add_apply, Pi.mul_apply, hg_def]; ring
  rw [hsplit]
  filter_upwards [condExp_add (hint n) hgX (ℱ n),
    condExp_mul_of_stronglyMeasurable_left hg_sm hgX hXi, hnull n] with ω h_add h_pull h_null
  rw [h_add, Pi.add_apply, condExp_of_stronglyMeasurable (ℱ.le n) (hsm n) (hint n), h_pull,
    Pi.mul_apply]
  have hg0 : 0 ≤ g ω := mul_nonneg (wealth_nonneg hXb hlamb n ω) (hlamb (n + 1) ω).1
  have : g ω * μ[X (n + 1) | ℱ n] ω ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hg0 h_null
  linarith

/-- Finite-horizon Ville: `c * P(∃ n ≤ N, c ≤ W n) ≤ E[W 0]` for a nonnegative supermartingale. -/
private theorem ville_finite (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {W : ℕ → Ω → ℝ} (hW : Supermartingale W ℱ μ) (hW0 : ∀ n ω, 0 ≤ W n ω) {c : ℝ} (hc : 0 < c)
    (N : ℕ) : c * μ.real {ω | ∃ n ≤ N, c ≤ W n ω} ≤ ∫ ω, W 0 ω ∂μ := by
  set τ : Ω → WithTop ℕ := fun ω => ((hittingBtwn W (Set.Ici c) 0 N ω : ℕ) : WithTop ℕ)
    with hτ_def
  have hτ : IsStoppingTime ℱ τ :=
    hW.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hbdd : ∀ ω, τ ω ≤ N := fun ω => WithTop.coe_le_coe.mpr (hittingBtwn_le ω)
  have hmono := hW.neg.expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hτ
    (fun ω => WithTop.coe_le_coe.mpr (Nat.zero_le _)) hbdd
  have hneg : ∀ σ : Ω → WithTop ℕ, stoppedValue (-W) σ = -stoppedValue W σ := fun σ => rfl
  rw [hneg, hneg, integral_neg', integral_neg', neg_le_neg_iff, stoppedValue_const] at hmono
  have hint_stop : Integrable (stoppedValue W τ) μ :=
    integrable_stoppedValue ℕ hτ hW.integrable hbdd
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => hW0 _ ω) hint_stop c
  refine le_trans ?_ (hmarkov.trans hmono)
  refine mul_le_mul_of_nonneg_left (measureReal_mono ?_ (measure_ne_top _ _)) hc.le
  intro ω hω
  obtain ⟨n, hnN, hcn⟩ := hω
  exact stoppedValue_hittingBtwn_mem ⟨n, ⟨Nat.zero_le n, hnN⟩, hcn⟩

end Helpers

/-- Ville's inequality for testing by betting: under the null `E[Xₙ₊₁ | ℱₙ] ≤ 0`, the wealth of a
bettor staking a predictable fraction `λₙ₊₁ ∈ [0, 1]` reaches `1/α` with probability at most `α`. -/
theorem ville {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (X lam : ℕ → Ω → ℝ)
    (hX : Adapted ℱ X) (hXb : ∀ n ω, -1 ≤ X n ω ∧ X n ω ≤ 1)
    (hlam : ∀ n, StronglyMeasurable[ℱ n] (lam (n + 1))) (hlamb : ∀ n ω, 0 ≤ lam n ω ∧ lam n ω ≤ 1)
    (hnull : ∀ n, μ[X (n + 1) | ℱ n] ≤ᵐ[μ] 0)
    {α : ℝ} (hα : 0 < α) :
    μ {ω | ∃ n : ℕ, α⁻¹ ≤ ∏ i ∈ Finset.range n, (1 + lam (i + 1) ω * X (i + 1) ω)}
      ≤ ENNReal.ofReal α := by
  have hsup := wealth_supermartingale μ ℱ X lam hX hXb hlam hlamb hnull
  have hc : 0 < α⁻¹ := inv_pos.mpr hα
  have hW0 : ∫ ω, wealth X lam 0 ω ∂μ = 1 := by simp [wealth]
  set S : ℕ → Set Ω := fun N => {ω | ∃ n ≤ N, α⁻¹ ≤ wealth X lam n ω} with hS
  have hmonoS : Monotone S := fun N M hNM ω ⟨n, hn, h⟩ => ⟨n, hn.trans hNM, h⟩
  have hunion : {ω | ∃ n : ℕ, α⁻¹ ≤ ∏ i ∈ Finset.range n, (1 + lam (i + 1) ω * X (i + 1) ω)}
      = ⋃ N, S N := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hS]
    exact ⟨fun ⟨n, h⟩ => ⟨n, n, le_rfl, h⟩, fun ⟨_, n, _, h⟩ => ⟨n, h⟩⟩
  rw [hunion, hmonoS.measure_iUnion]
  refine iSup_le fun N => ?_
  have h := ville_finite μ ℱ hsup (wealth_nonneg hXb hlamb) hc N
  rw [hW0] at h
  have hreal : μ.real (S N) ≤ α := by
    have h' := (le_div_iff₀' hc).mpr h
    simpa using h'
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hα.le]
  simpa [measureReal_def] using hreal

end Challenge.TestingByBetting
