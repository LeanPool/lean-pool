/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system (module
-- header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with source adaptations
-- (deprecated names, proof-context visibility, the v4.35.0 `eLpNorm`/`MemLp` API) listed in
-- vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFourthMomentIncrements

/-!
# Second and fourth moments of the elementary Brownian integral

The moment recursion over the partial sums of the elementary integral of a simple integrand: one
step adds the second moment of the new tile, and in the fourth-moment recursion the odd-power
cross terms drop out because a coefficient measurable before an increment is independent of it.
Iterating gives `𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·C⁴·T²` for an integrand bounded by `C`, where `c` is
the fourth moment of the standard Gaussian, and the sharper form
`𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·(∑_j c_j² Δ_j)²` against a per-tile coefficient bound `c`, which for a
coefficient vanishing off a subinterval sees only that subinterval's length.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

namespace SimplePredictable

variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

omit [IsProbabilityMeasure P] in
/-- A real random variable in `Lᵐ` has an integrable `m`-th power. -/
private theorem integrable_pow_of_memLp {f : Ω → ℝ} {m : ℕ} (hm : m ≠ 0)
    {p : ℝ≥0∞} (hp : p = (m : ℝ≥0∞)) (h : MemLp f p P) : Integrable (fun ω => f ω ^ m) P := by
  subst hp
  refine (h.integrable_norm_pow hm).mono
    ((continuous_pow m).comp_aestronglyMeasurable h.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  simp

section Moments

/-- One step of a second-moment recursion. -/
private theorem integral_add_mul_increment_sq
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {S ξ : Ω → ℝ}
    (hS2 : MemLp S 2 P) (hSm : Measurable S)
    (hSad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) S)
    (hξm : Measurable ξ) (hξad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) ξ)
    {C : ℝ} (hC0 : 0 ≤ C) (hCξ : ∀ ω, |ξ ω| ≤ C) :
    ∫ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 2 ∂P
      = (∫ ω, S ω ^ 2 ∂P) + (∫ ω, ξ ω ^ 2 ∂P) * (b - a) := by
  have hDm : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have hD2 : MemLp (fun ω => W.W b ω - W.W a ω) 2 P := memLp_increment W ha hab 2 (by simp)
  have hSD : Integrable (fun ω => |S ω| * |W.W b ω - W.W a ω|) P := by
    have h := (hS2.abs).integrable_mul (hD2.abs)
    exact h
  have hD2int : Integrable (fun ω => (W.W b ω - W.W a ω) ^ 2) P :=
    integrable_pow_of_memLp (m := 2) (by norm_num) (by simp) hD2
  have hi1 : Integrable (fun ω => S ω ^ 2) P :=
    integrable_pow_of_memLp (m := 2) (by norm_num) (by simp) hS2
  have hi2 : Integrable (fun ω => (2 * (S ω * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := by
    refine (hSD.const_mul (2 * C)).mono
      (((measurable_const.mul (hSm.mul hξm)).mul (hDm.pow_const 1)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := hCξ ω
    have h2 := abs_nonneg (S ω)
    have h3 := abs_nonneg (W.W b ω - W.W a ω)
    rw [pow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * C * (|S ω| * |W.W b ω - W.W a ω|))]
    have h4 : |(2 : ℝ)| = 2 := by norm_num
    rw [h4]
    nlinarith [mul_nonneg (mul_nonneg h2 h3) (sub_nonneg.mpr h1)]
  have hi3 : Integrable (fun ω => ξ ω ^ 2 * (W.W b ω - W.W a ω) ^ 2) P := by
    refine (hD2int.const_mul (C ^ 2)).mono
      (((hξm.pow_const 2).mul (hDm.pow_const 2)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := hCξ ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ C ^ 2 * (W.W b ω - W.W a ω) ^ 2)]
    have h2 : |W.W b ω - W.W a ω| ^ 2 = (W.W b ω - W.W a ω) ^ 2 := by
      rw [← abs_pow, abs_of_nonneg (sq_nonneg _)]
    rw [h2]
    nlinarith [sq_nonneg (W.W b ω - W.W a ω),
      mul_le_mul h1 h1 (abs_nonneg (ξ ω)) hC0]
  have hexp : ∀ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 2
      = S ω ^ 2 + (2 * (S ω * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + ξ ω ^ 2 * (W.W b ω - W.W a ω) ^ 2 := fun ω => by ring
  have hξ2ad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) (fun ω => ξ ω ^ 2) := by
    have hfun : (fun ω => ξ ω ^ 2) = ξ * ξ := by funext ω; rw [pow_two]; rfl
    rw [hfun]; exact hξad.mul hξad
  have hi12 : Integrable
      (fun ω => S ω ^ 2 + (2 * (S ω * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := hi1.add hi2
  simp_rw [hexp]
  rw [integral_add hi12 hi3, integral_add hi1 hi2,
    integral_mul_increment_pow W ℱ hℱ ha hab (Y := fun ω => 2 * (S ω * ξ ω))
      (MeasureTheory.stronglyMeasurable_const.mul (hSad.mul hξad))
      (measurable_const.mul (hSm.mul hξm)) 1,
    integral_increment_pow_odd W ha hab odd_one, mul_zero, add_zero,
    integral_mul_increment_pow W ℱ hℱ ha hab (Y := fun ω => ξ ω ^ 2)
      hξ2ad (hξm.pow_const 2) 2,
    integral_increment_sq W ha hab]

/-- One step of a fourth-moment recursion. -/
private theorem integral_add_mul_increment_pow_four
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {S ξ : Ω → ℝ}
    (hS4 : MemLp S 4 P) (hSm : Measurable S)
    (hSad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) S)
    (hξm : Measurable ξ) (hξad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) ξ)
    {C : ℝ} (hC0 : 0 ≤ C) (hCξ : ∀ ω, |ξ ω| ≤ C) :
    ∫ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 4 ∂P
      = (∫ ω, S ω ^ 4 ∂P)
        + 6 * ((∫ ω, S ω ^ 2 * ξ ω ^ 2 ∂P) * (b - a))
        + (∫ ω, ξ ω ^ 4 ∂P) * ((b - a) ^ 2 * gaussianFourthMoment) := by
  have hDm : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have hD4 : MemLp (fun ω => W.W b ω - W.W a ω) 4 P := memLp_increment W ha hab 4 (by simp)
  have hU4 : Integrable
      (fun ω => (|S ω| + |W.W b ω - W.W a ω|) ^ 4) P :=
    integrable_pow_of_memLp (m := 4) (by norm_num) (by simp) (hS4.abs.add hD4.abs)
  have hpow : ∀ (i j : ℕ), i + j = 4 → ∀ ω,
      |S ω| ^ i * |W.W b ω - W.W a ω| ^ j ≤ (|S ω| + |W.W b ω - W.W a ω|) ^ 4 := by
    intro i j hij ω
    have hx : |S ω| ≤ |S ω| + |W.W b ω - W.W a ω| := by
      linarith [abs_nonneg (W.W b ω - W.W a ω)]
    have hy : |W.W b ω - W.W a ω| ≤ |S ω| + |W.W b ω - W.W a ω| := by
      linarith [abs_nonneg (S ω)]
    calc |S ω| ^ i * |W.W b ω - W.W a ω| ^ j
        ≤ (|S ω| + |W.W b ω - W.W a ω|) ^ i * (|S ω| + |W.W b ω - W.W a ω|) ^ j :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx i)
            (pow_le_pow_left₀ (abs_nonneg _) hy j) (by positivity) (by positivity)
      _ = (|S ω| + |W.W b ω - W.W a ω|) ^ 4 := by rw [← pow_add, hij]
  have key : ∀ (K : ℝ), 0 ≤ K → ∀ (A : Ω → ℝ), Measurable A → ∀ (i j : ℕ), i + j = 4 →
      (∀ ω, |A ω| ≤ K * |S ω| ^ i) →
      Integrable (fun ω => A ω * (W.W b ω - W.W a ω) ^ j) P := by
    intro K hK A hAm i j hij hA
    refine (hU4.const_mul K).mono ((hAm.mul (hDm.pow_const j)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_mul, abs_of_nonneg hK,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (|S ω| + |W.W b ω - W.W a ω|) ^ 4)]
    calc |A ω| * |W.W b ω - W.W a ω| ^ j
        ≤ (K * |S ω| ^ i) * |W.W b ω - W.W a ω| ^ j :=
          mul_le_mul_of_nonneg_right (hA ω) (by positivity)
      _ = K * (|S ω| ^ i * |W.W b ω - W.W a ω| ^ j) := by ring
      _ ≤ K * (|S ω| + |W.W b ω - W.W a ω|) ^ 4 :=
          mul_le_mul_of_nonneg_left (hpow i j hij ω) hK
  have hi1 : Integrable (fun ω => S ω ^ 4) P :=
    integrable_pow_of_memLp (m := 4) (by norm_num) (by simp) hS4
  have hi2 : Integrable
      (fun ω => (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := by
    refine key (4 * C) (by positivity) (fun ω => 4 * (S ω ^ 3 * ξ ω))
      (measurable_const.mul ((hSm.pow_const 3).mul hξm)) 3 1 rfl fun ω => ?_
    rw [abs_mul, abs_mul, abs_pow, show |(4 : ℝ)| = 4 from by norm_num]
    have := hCξ ω
    nlinarith [pow_nonneg (abs_nonneg (S ω)) 3, abs_nonneg (ξ ω)]
  have hi3 : Integrable
      (fun ω => (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2) P := by
    refine key (6 * C ^ 2) (by positivity) (fun ω => 6 * (S ω ^ 2 * ξ ω ^ 2))
      (measurable_const.mul ((hSm.pow_const 2).mul (hξm.pow_const 2))) 2 2 rfl fun ω => ?_
    rw [abs_mul, abs_mul, abs_pow, abs_pow, show |(6 : ℝ)| = 6 from by norm_num]
    have h := hCξ ω
    nlinarith [pow_nonneg (abs_nonneg (S ω)) 2, abs_nonneg (ξ ω),
      mul_le_mul h h (abs_nonneg (ξ ω)) hC0]
  have hi4 : Integrable
      (fun ω => (4 * (S ω * ξ ω ^ 3)) * (W.W b ω - W.W a ω) ^ 3) P := by
    refine key (4 * C ^ 3) (by positivity) (fun ω => 4 * (S ω * ξ ω ^ 3))
      (measurable_const.mul (hSm.mul (hξm.pow_const 3))) 1 3 rfl fun ω => ?_
    rw [abs_mul, abs_mul, abs_pow, show |(4 : ℝ)| = 4 from by norm_num, pow_one]
    have h3 : |ξ ω| ^ 3 ≤ C ^ 3 := pow_le_pow_left₀ (abs_nonneg _) (hCξ ω) 3
    nlinarith [mul_nonneg (abs_nonneg (S ω)) (sub_nonneg.mpr h3)]
  have hi5 : Integrable (fun ω => ξ ω ^ 4 * (W.W b ω - W.W a ω) ^ 4) P := by
    refine key (C ^ 4) (by positivity) (fun ω => ξ ω ^ 4) (hξm.pow_const 4) 0 4 rfl fun ω => ?_
    rw [abs_pow, pow_zero, mul_one]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCξ ω) 4
  have hexp : ∀ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 4
      = S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2
        + (4 * (S ω * ξ ω ^ 3)) * (W.W b ω - W.W a ω) ^ 3
        + ξ ω ^ 4 * (W.W b ω - W.W a ω) ^ 4 := fun ω => by ring
  have hi12 : Integrable
      (fun ω => S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := hi1.add hi2
  have hi123 : Integrable
      (fun ω => S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2) P := hi12.add hi3
  have hi1234 : Integrable
      (fun ω => S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2
        + (4 * (S ω * ξ ω ^ 3)) * (W.W b ω - W.W a ω) ^ 3) P := hi123.add hi4
  have hS3ξ : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a)
      (fun ω => 4 * (S ω ^ 3 * ξ ω)) := by
    have h3 : (fun ω => S ω ^ 3) = S * S * S := by funext ω; simp only [Pi.mul_apply]; ring
    exact MeasureTheory.stronglyMeasurable_const.mul ((h3 ▸ ((hSad.mul hSad).mul hSad)).mul hξad)
  have hS2ξ2 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a)
      (fun ω => 6 * (S ω ^ 2 * ξ ω ^ 2)) := by
    have h2 : (fun ω => S ω ^ 2) = S * S := by funext ω; simp only [Pi.mul_apply]; ring
    have h2' : (fun ω => ξ ω ^ 2) = ξ * ξ := by funext ω; simp only [Pi.mul_apply]; ring
    exact MeasureTheory.stronglyMeasurable_const.mul
      ((h2 ▸ (hSad.mul hSad)).mul (h2' ▸ (hξad.mul hξad)))
  have hSξ3 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a)
      (fun ω => 4 * (S ω * ξ ω ^ 3)) := by
    have h3 : (fun ω => ξ ω ^ 3) = ξ * ξ * ξ := by funext ω; simp only [Pi.mul_apply]; ring
    exact MeasureTheory.stronglyMeasurable_const.mul (hSad.mul (h3 ▸ ((hξad.mul hξad).mul hξad)))
  have hξ4 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) (fun ω => ξ ω ^ 4) := by
    have h4 : (fun ω => ξ ω ^ 4) = ξ * ξ * ξ * ξ := by funext ω; simp only [Pi.mul_apply]; ring
    exact h4 ▸ (((hξad.mul hξad).mul hξad).mul hξad)
  simp_rw [hexp]
  rw [integral_add hi1234 hi5, integral_add hi123 hi4, integral_add hi12 hi3,
    integral_add hi1 hi2,
    integral_mul_increment_pow W ℱ hℱ ha hab (Y := fun ω => 4 * (S ω ^ 3 * ξ ω)) hS3ξ
      (measurable_const.mul ((hSm.pow_const 3).mul hξm)) 1,
    integral_increment_pow_odd W ha hab odd_one, mul_zero, add_zero,
    integral_mul_increment_pow W ℱ hℱ ha hab (Y := fun ω => 6 * (S ω ^ 2 * ξ ω ^ 2)) hS2ξ2
      (measurable_const.mul ((hSm.pow_const 2).mul (hξm.pow_const 2))) 2,
    integral_increment_sq W ha hab,
    integral_mul_increment_pow W ℱ hℱ ha hab (Y := fun ω => 4 * (S ω * ξ ω ^ 3)) hSξ3
      (measurable_const.mul (hSm.mul (hξm.pow_const 3))) 3,
    integral_increment_pow_odd W ha hab (by decide : Odd 3), mul_zero, add_zero,
    integral_mul_increment_pow W ℱ hℱ ha hab (Y := fun ω => ξ ω ^ 4) hξ4
      (hξm.pow_const 4) 4,
    integral_increment_pow_four W ha hab]
  rw [integral_const_mul]
  ring

variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)

include hℱ h_adapt hC0 hC in
/-- One step of the second-moment recursion for the partial sums. -/
theorem integral_partialSum_sq_succ {k : ℕ} (hk : k < G.N) :
    ∫ ω, (G.partialSum W (k + 1) ω) ^ 2 ∂P
      = (∫ ω, (G.partialSum W k ω) ^ 2 ∂P)
        + (∫ ω, (G.ξ ⟨k, hk⟩ ω) ^ 2 ∂P)
          * (G.partition (⟨k, hk⟩ : Fin G.N).succ
            - G.partition (⟨k, hk⟩ : Fin G.N).castSucc) := by
  have hrw : ∀ ω, G.partialSum W (k + 1) ω
      = G.partialSum W k ω + G.ξ ⟨k, hk⟩ ω
        * (W.W (G.partition (⟨k, hk⟩ : Fin G.N).succ) ω
          - W.W (G.partition (⟨k, hk⟩ : Fin G.N).castSucc) ω) := fun ω => by
    rw [G.partialSum_succ W k ω, term, dite_eq_left hk]
  simp_rw [hrw]
  exact integral_add_mul_increment_sq W ℱ hℱ (G.partition_nonneg _)
    (G.partition_strictMono Fin.castSucc_lt_succ)
    (G.memLp_partialSum W hC 2 (by simp) k) (G.measurable_partialSum W k)
    (G.stronglyMeasurable_partialSum W ℱ hℱ h_adapt hk.le)
    (G.ξ_measurable _) (h_adapt ⟨k, hk⟩) hC0 (hC ⟨k, hk⟩)

include hℱ h_adapt hC0 hC in
/-- One step of the fourth-moment recursion for the partial sums. -/
theorem integral_partialSum_pow_four_succ {k : ℕ} (hk : k < G.N) :
    ∫ ω, (G.partialSum W (k + 1) ω) ^ 4 ∂P
      = (∫ ω, (G.partialSum W k ω) ^ 4 ∂P)
        + 6 * ((∫ ω, (G.partialSum W k ω) ^ 2 * (G.ξ ⟨k, hk⟩ ω) ^ 2 ∂P)
          * (G.partition (⟨k, hk⟩ : Fin G.N).succ
            - G.partition (⟨k, hk⟩ : Fin G.N).castSucc))
        + (∫ ω, (G.ξ ⟨k, hk⟩ ω) ^ 4 ∂P)
          * ((G.partition (⟨k, hk⟩ : Fin G.N).succ
            - G.partition (⟨k, hk⟩ : Fin G.N).castSucc) ^ 2 * gaussianFourthMoment) := by
  have hrw : ∀ ω, G.partialSum W (k + 1) ω
      = G.partialSum W k ω + G.ξ ⟨k, hk⟩ ω
        * (W.W (G.partition (⟨k, hk⟩ : Fin G.N).succ) ω
          - W.W (G.partition (⟨k, hk⟩ : Fin G.N).castSucc) ω) := fun ω => by
    rw [G.partialSum_succ W k ω, term, dite_eq_left hk]
  simp_rw [hrw]
  exact integral_add_mul_increment_pow_four W ℱ hℱ (G.partition_nonneg _)
    (G.partition_strictMono Fin.castSucc_lt_succ)
    (G.memLp_partialSum W hC 4 (by simp) k) (G.measurable_partialSum W k)
    (G.stronglyMeasurable_partialSum W ℱ hℱ h_adapt hk.le)
    (G.ξ_measurable _) (h_adapt ⟨k, hk⟩) hC0 (hC ⟨k, hk⟩)

/-- A coefficient bounded by `c` has even moments at most the matching power of `c`. -/
private theorem integral_xi_even_le {c : ℝ} (i : Fin G.N)
    (hci : ∀ ω, |G.ξ i ω| ≤ c) (m : ℕ) :
    ∫ ω, (G.ξ i ω) ^ (2 * m) ∂P ≤ c ^ (2 * m) := by
  have hnn : ∀ ω, (0 : ℝ) ≤ (G.ξ i ω) ^ (2 * m) := fun ω => by
    rw [pow_mul]; positivity
  have hcnn : (0 : ℝ) ≤ c ^ (2 * m) := by rw [pow_mul]; positivity
  have hpow : ∀ ω, (G.ξ i ω) ^ (2 * m) ≤ c ^ (2 * m) := fun ω => by
    have h : |G.ξ i ω| ^ (2 * m) ≤ c ^ (2 * m) :=
      pow_le_pow_left₀ (abs_nonneg _) (hci ω) _
    rwa [← abs_pow, abs_of_nonneg (hnn ω)] at h
  have hint : Integrable (fun ω => (G.ξ i ω) ^ (2 * m)) P := by
    refine (integrable_const (c ^ (2 * m))).mono
      ((G.ξ_measurable _).pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn ω), abs_of_nonneg hcnn]
    exact hpow ω
  calc ∫ ω, (G.ξ i ω) ^ (2 * m) ∂P ≤ ∫ _ω : Ω, c ^ (2 * m) ∂P :=
        integral_mono hint (integrable_const _) hpow
    _ = c ^ (2 * m) := by simp

include hC in
/-- A bounded coefficient has second moment at most `C²`. -/
private theorem integral_xi_sq_le (i : Fin G.N) : ∫ ω, (G.ξ i ω) ^ 2 ∂P ≤ C ^ 2 := by
  simpa using G.integral_xi_even_le (P := P) i (hC i) 1

include hC in
/-- A bounded coefficient has fourth moment at most `C⁴`. -/
private theorem integral_xi_pow_four_le (i : Fin G.N) : ∫ ω, (G.ξ i ω) ^ 4 ∂P ≤ C ^ 4 := by
  simpa using G.integral_xi_even_le (P := P) i (hC i) 2

include hℱ h_adapt hC0 hC in
/-- The second moment of a partial sum is at most `C²` times the elapsed time. -/
theorem integral_partialSum_sq_le : ∀ (k : ℕ) (hk : k ≤ G.N),
    ∫ ω, (G.partialSum W k ω) ^ 2 ∂P
      ≤ C ^ 2 * G.partition ⟨k, Nat.lt_succ_of_le hk⟩ := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 : ∀ ω, G.partialSum W 0 ω = 0 := G.partialSum_zero W
    have hp : G.partition (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (G.N + 1)) = 0 := G.partition_zero
    simp_rw [h0]
    simp [G.partition_zero]
  | succ n ih =>
    intro hk
    have hn : n < G.N := hk
    have hΔ0 : (0 : ℝ) ≤ G.partition (⟨n, hn⟩ : Fin G.N).succ
        - G.partition (⟨n, hn⟩ : Fin G.N).castSucc :=
      sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le
    have he1 : G.partition (⟨n, hn⟩ : Fin G.N).castSucc
        = G.partition (⟨n, Nat.lt_succ_of_le hn.le⟩ : Fin (G.N + 1)) := rfl
    have he2 : G.partition (⟨n, hn⟩ : Fin G.N).succ
        = G.partition (⟨n + 1, Nat.lt_succ_of_le hk⟩ : Fin (G.N + 1)) := rfl
    rw [G.integral_partialSum_sq_succ W ℱ hℱ h_adapt hC0 hC hn]
    have h1 := ih hn.le
    have h2 := G.integral_xi_sq_le (P := P) hC ⟨n, hn⟩
    have h3 := mul_le_mul_of_nonneg_right h2 hΔ0
    rw [he1, he2] at h3 hΔ0 ⊢
    linarith

include hℱ h_adapt hC0 hC in
/-- The fourth moment of a partial sum is controlled by the elapsed time. -/
theorem integral_partialSum_pow_four_le : ∀ (k : ℕ) (hk : k ≤ G.N),
    ∫ ω, (G.partialSum W k ω) ^ 4 ∂P
      ≤ 6 * C ^ 4 * (G.partition (Fin.last G.N)
          * G.partition ⟨k, Nat.lt_succ_of_le hk⟩)
        + gaussianFourthMoment * C ^ 4 * G.partition ⟨k, Nat.lt_succ_of_le hk⟩ ^ 2 := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 : ∀ ω, G.partialSum W 0 ω = 0 := G.partialSum_zero W
    have hp : G.partition (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (G.N + 1)) = 0 := G.partition_zero
    simp_rw [h0]
    simp [G.partition_zero]
  | succ n ih =>
    intro hk
    have hn : n < G.N := hk
    have hΔ0 : (0 : ℝ) ≤ G.partition (⟨n, hn⟩ : Fin G.N).succ
        - G.partition (⟨n, hn⟩ : Fin G.N).castSucc :=
      sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le
    have he1 : G.partition (⟨n, hn⟩ : Fin G.N).castSucc
        = G.partition (⟨n, Nat.lt_succ_of_le hn.le⟩ : Fin (G.N + 1)) := rfl
    have he2 : G.partition (⟨n, hn⟩ : Fin G.N).succ
        = G.partition (⟨n + 1, Nat.lt_succ_of_le hk⟩ : Fin (G.N + 1)) := rfl
    -- the mixed second moment
    have hSint : Integrable (fun ω => (G.partialSum W n ω) ^ 2) P :=
      integrable_pow_of_memLp (m := 2) (by norm_num) (by simp)
        (G.memLp_partialSum W hC 2 (by simp) n)
    have hmix : Integrable
        (fun ω => (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2) P := by
      refine (hSint.const_mul (C ^ 2)).mono
        (((G.measurable_partialSum W n).pow_const 2).mul
          ((G.ξ_measurable _).pow_const 2)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      have hx := hC ⟨n, hn⟩ ω
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ C ^ 2)]
      have h4 : |G.ξ ⟨n, hn⟩ ω| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
      nlinarith [pow_nonneg (abs_nonneg (G.partialSum W n ω)) 2]
    have hmix_le : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
        ≤ C ^ 2 * ∫ ω, (G.partialSum W n ω) ^ 2 ∂P := by
      have hstep : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
          ≤ ∫ ω, C ^ 2 * (G.partialSum W n ω) ^ 2 ∂P :=
        integral_mono hmix (hSint.const_mul _) fun ω => by
          have hx := hC ⟨n, hn⟩ ω
          have h4 : |G.ξ ⟨n, hn⟩ ω| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
          have h5 : (G.ξ ⟨n, hn⟩ ω) ^ 2 ≤ C ^ 2 := by
            rwa [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (G.ξ ⟨n, hn⟩ ω) ^ 2)] at h4
          nlinarith [sq_nonneg (G.partialSum W n ω)]
      rwa [integral_const_mul] at hstep
    have hS2 := G.integral_partialSum_sq_le W ℱ hℱ h_adapt hC0 hC n hn.le
    have hlast : G.partition (⟨n, Nat.lt_succ_of_le hn.le⟩ : Fin (G.N + 1))
        ≤ G.partition (Fin.last G.N) :=
      G.partition_strictMono.monotone (by rw [Fin.le_def]; simp [Fin.last]; omega)
    have hτ0 : (0 : ℝ) ≤ G.partition (⟨n, Nat.lt_succ_of_le hn.le⟩ : Fin (G.N + 1)) :=
      G.partition_nonneg _
    have hc0 : (0 : ℝ) ≤ gaussianFourthMoment := gaussianFourthMoment_nonneg
    have hξ4 := G.integral_xi_pow_four_le (P := P) hC ⟨n, hn⟩
    rw [G.integral_partialSum_pow_four_succ W ℱ hℱ h_adapt hC0 hC hn]
    have h1 := ih hn.le
    rw [he1, he2] at hΔ0 ⊢
    nlinarith [mul_nonneg (pow_nonneg hC0 4) hΔ0, sq_nonneg C,
      mul_nonneg hc0 (mul_nonneg (pow_nonneg hC0 4) (mul_nonneg hτ0 hΔ0)),
      mul_le_mul_of_nonneg_right hmix_le hΔ0,
      mul_le_mul_of_nonneg_right hS2 hΔ0,
      mul_le_mul_of_nonneg_right hξ4
        (mul_nonneg (mul_nonneg hΔ0 hΔ0) hc0)]

include hℱ h_adapt hC0 hC in
/-- **Fourth-moment bound for the elementary integral of a uniformly bounded simple
integrand.** -/
theorem integral_simpleIntegral_pow_four_le :
    ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ (6 + gaussianFourthMoment) * C ^ 4 * G.partition (Fin.last G.N) ^ 2 := by
  have hcard := G.integral_partialSum_pow_four_le W ℱ hℱ h_adapt hC0 hC G.N le_rfl
  have hfun : ∀ ω, G.partialSum W G.N ω = simpleIntegral W G T ω := G.partialSum_card W
  simp_rw [hfun] at hcard
  have hlast : G.partition (⟨G.N, Nat.lt_succ_of_le le_rfl⟩ : Fin (G.N + 1))
      = G.partition (Fin.last G.N) := rfl
  rw [hlast] at hcard
  calc ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ 6 * C ^ 4 * (G.partition (Fin.last G.N) * G.partition (Fin.last G.N))
        + gaussianFourthMoment * C ^ 4 * G.partition (Fin.last G.N) ^ 2 := hcard
    _ = (6 + gaussianFourthMoment) * C ^ 4 * G.partition (Fin.last G.N) ^ 2 := by ring

include hℱ h_adapt hC0 hC in
/-- The fourth-moment bound stated on the horizon. -/
theorem integral_simpleIntegral_pow_four_le_horizon :
    ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ (6 + gaussianFourthMoment) * C ^ 4 * T ^ 2 := by
  refine (G.integral_simpleIntegral_pow_four_le W ℱ hℱ h_adapt hC0 hC).trans ?_
  have h1 : G.partition (Fin.last G.N) ≤ T := G.partition_le_T
  have h2 : (0 : ℝ) ≤ G.partition (Fin.last G.N) := G.partition_nonneg _
  have h3 : (0 : ℝ) ≤ 6 + gaussianFourthMoment := by
    linarith [gaussianFourthMoment_nonneg]
  have h4 : G.partition (Fin.last G.N) ^ 2 ≤ T ^ 2 := by nlinarith
  nlinarith [pow_nonneg hC0 4, mul_nonneg h3 (pow_nonneg hC0 4)]


include hℱ h_adapt hC0 hC in
/-- Second moment of a partial sum against a per-tile coefficient bound. -/
theorem integral_partialSum_sq_le_varClock {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∀ (k : ℕ) (_hk : k ≤ G.N),
      ∫ ω, (G.partialSum W k ω) ^ 2 ∂P ≤ G.varClock c k := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : ∀ ω, G.partialSum W 0 ω = 0 := G.partialSum_zero W
    simp_rw [h0]
    simp [G.varClock_zero]
  | succ n ih =>
    intro hk
    have hn : n < G.N := hk
    have hΔ0 : (0 : ℝ) ≤ G.partition (⟨n, hn⟩ : Fin G.N).succ
        - G.partition (⟨n, hn⟩ : Fin G.N).castSucc :=
      sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le
    rw [G.integral_partialSum_sq_succ W ℱ hℱ h_adapt hC0 hC hn, G.varClock_succ c hn]
    have h1 := ih hn.le
    have h2 : ∫ ω, (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P ≤ c ⟨n, hn⟩ ^ 2 := by
      simpa using G.integral_xi_even_le (P := P) ⟨n, hn⟩ (hc ⟨n, hn⟩) 1
    linarith [mul_le_mul_of_nonneg_right h2 hΔ0]

include hℱ h_adapt hC0 hC in
/-- Fourth moment of a partial sum against a per-tile coefficient bound: the elapsed
variance budget `∑_{j<k} c_j² (τ_{j+1} − τ_j)` replaces `C²τ_k`. -/
theorem integral_partialSum_pow_four_le_varClock {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∀ (k : ℕ) (_hk : k ≤ G.N),
      ∫ ω, (G.partialSum W k ω) ^ 4 ∂P
        ≤ 6 * (G.varClock c G.N * G.varClock c k)
          + gaussianFourthMoment * G.varClock c k ^ 2 := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : ∀ ω, G.partialSum W 0 ω = 0 := G.partialSum_zero W
    simp_rw [h0]
    simp [G.varClock_zero]
  | succ n ih =>
    intro hk
    have hn : n < G.N := hk
    have hΔ0 : (0 : ℝ) ≤ G.partition (⟨n, hn⟩ : Fin G.N).succ
        - G.partition (⟨n, hn⟩ : Fin G.N).castSucc :=
      sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le
    have hcn2 : (0 : ℝ) ≤ c ⟨n, hn⟩ ^ 2 := sq_nonneg _
    have hxi2 : ∀ ω, (G.ξ ⟨n, hn⟩ ω) ^ 2 ≤ c ⟨n, hn⟩ ^ 2 := fun ω => by
      have h := pow_le_pow_left₀ (abs_nonneg (G.ξ ⟨n, hn⟩ ω)) (hc ⟨n, hn⟩ ω) 2
      rwa [← abs_pow, abs_of_nonneg (sq_nonneg (G.ξ ⟨n, hn⟩ ω))] at h
    have hSint : Integrable (fun ω => (G.partialSum W n ω) ^ 2) P :=
      integrable_pow_of_memLp (m := 2) (by norm_num) (by simp)
        (G.memLp_partialSum W hC 2 (by simp) n)
    have hmix : Integrable
        (fun ω => (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2) P := by
      refine (hSint.const_mul (c ⟨n, hn⟩ ^ 2)).mono
        (((G.measurable_partialSum W n).pow_const 2).mul
          ((G.ξ_measurable _).pow_const 2)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_nonneg hcn2]
      have h4 : |G.ξ ⟨n, hn⟩ ω| ^ 2 ≤ c ⟨n, hn⟩ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hc ⟨n, hn⟩ ω) 2
      nlinarith [pow_nonneg (abs_nonneg (G.partialSum W n ω)) 2]
    have hmix_le : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
        ≤ c ⟨n, hn⟩ ^ 2 * ∫ ω, (G.partialSum W n ω) ^ 2 ∂P := by
      have hstep : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
          ≤ ∫ ω, c ⟨n, hn⟩ ^ 2 * (G.partialSum W n ω) ^ 2 ∂P :=
        integral_mono hmix (hSint.const_mul _) fun ω => by
          nlinarith [sq_nonneg (G.partialSum W n ω), hxi2 ω]
      rwa [integral_const_mul] at hstep
    have hS2 := G.integral_partialSum_sq_le_varClock W ℱ hℱ h_adapt hC0 hC hc n hn.le
    have hVN : G.varClock c n ≤ G.varClock c G.N := G.varClock_mono c hn.le
    have hV0 : (0 : ℝ) ≤ G.varClock c n := G.varClock_nonneg c n
    have hcg : (0 : ℝ) ≤ gaussianFourthMoment := gaussianFourthMoment_nonneg
    have hA : (∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P)
        ≤ c ⟨n, hn⟩ ^ 2 * G.varClock c G.N :=
      hmix_le.trans (mul_le_mul_of_nonneg_left (hS2.trans hVN) hcn2)
    have hB : (∫ ω, (G.ξ ⟨n, hn⟩ ω) ^ 4 ∂P) ≤ c ⟨n, hn⟩ ^ 4 := by
      simpa using G.integral_xi_even_le (P := P) ⟨n, hn⟩ (hc ⟨n, hn⟩) 2
    rw [G.integral_partialSum_pow_four_succ W ℱ hℱ h_adapt hC0 hC hn, G.varClock_succ c hn]
    have h1 := ih hn.le
    nlinarith [mul_le_mul_of_nonneg_right hA hΔ0,
      mul_le_mul_of_nonneg_right hB
        (mul_nonneg (mul_nonneg hΔ0 hΔ0) hcg),
      mul_nonneg (mul_nonneg (mul_nonneg hcg hV0) hcn2) hΔ0]

include hℱ h_adapt hC0 hC in
/-- **Fourth-moment bound for the elementary integral against a per-tile coefficient
bound.** -/
theorem integral_simpleIntegral_pow_four_le_varClock {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ (6 + gaussianFourthMoment) * G.varClock c G.N ^ 2 := by
  have hcard := G.integral_partialSum_pow_four_le_varClock W ℱ hℱ h_adapt hC0 hC hc G.N le_rfl
  have hfun : ∀ ω, G.partialSum W G.N ω = simpleIntegral W G T ω := G.partialSum_card W
  simp_rw [hfun] at hcard
  calc ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ 6 * (G.varClock c G.N * G.varClock c G.N)
        + gaussianFourthMoment * G.varClock c G.N ^ 2 := hcard
    _ = (6 + gaussianFourthMoment) * G.varClock c G.N ^ 2 := by ring

end Moments

end SimplePredictable

end LevyStochCalc.Brownian.Ito
